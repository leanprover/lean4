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
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l_Lean_instInhabitedData__1___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_instInhabitedData__1___aux__1___closed__0;
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
static lean_once_cell_t l_Lean_instHashableFVarId_hash___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_instHashableFVarId_hash___closed__1;
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
static uint64_t _init_l_Lean_instInhabitedData__1___aux__1___closed__0(void){
_start:
{
lean_object* v___x_353_; uint64_t v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_uint64_of_nat(v___x_353_);
return v___x_354_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1___aux__1(void){
_start:
{
uint64_t v___x_355_; 
v___x_355_ = lean_uint64_once(&l_Lean_instInhabitedData__1___aux__1___closed__0, &l_Lean_instInhabitedData__1___aux__1___closed__0_once, _init_l_Lean_instInhabitedData__1___aux__1___closed__0);
return v___x_355_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1(void){
_start:
{
uint64_t v___x_356_; 
v___x_356_ = lean_uint64_once(&l_Lean_instInhabitedData__1___aux__1___closed__0, &l_Lean_instInhabitedData__1___aux__1___closed__0_once, _init_l_Lean_instInhabitedData__1___aux__1___closed__0);
return v___x_356_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_Data_hash(uint64_t v_c_357_){
_start:
{
uint32_t v___x_358_; uint64_t v___x_359_; 
v___x_358_ = lean_uint64_to_uint32(v_c_357_);
v___x_359_ = lean_uint32_to_uint64(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object* v_c_360_){
_start:
{
uint64_t v_c_boxed_361_; uint64_t v_res_362_; lean_object* v_r_363_; 
v_c_boxed_361_ = lean_unbox_uint64(v_c_360_);
lean_dec_ref(v_c_360_);
v_res_362_ = l_Lean_Expr_Data_hash(v_c_boxed_361_);
v_r_363_ = lean_box_uint64(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t v_c_366_){
_start:
{
uint64_t v___x_367_; uint64_t v___x_368_; uint64_t v___x_369_; uint64_t v___x_370_; uint8_t v___x_371_; 
v___x_367_ = 32ULL;
v___x_368_ = lean_uint64_shift_right(v_c_366_, v___x_367_);
v___x_369_ = 255ULL;
v___x_370_ = lean_uint64_land(v___x_368_, v___x_369_);
v___x_371_ = lean_uint64_to_uint8(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object* v_c_372_){
_start:
{
uint64_t v_c_boxed_373_; uint8_t v_res_374_; lean_object* v_r_375_; 
v_c_boxed_373_ = lean_unbox_uint64(v_c_372_);
lean_dec_ref(v_c_372_);
v_res_374_ = l_Lean_Expr_Data_approxDepth(v_c_boxed_373_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t v_c_376_){
_start:
{
uint64_t v___x_377_; uint64_t v___x_378_; uint32_t v___x_379_; 
v___x_377_ = 44ULL;
v___x_378_ = lean_uint64_shift_right(v_c_376_, v___x_377_);
v___x_379_ = lean_uint64_to_uint32(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object* v_c_380_){
_start:
{
uint64_t v_c_boxed_381_; uint32_t v_res_382_; lean_object* v_r_383_; 
v_c_boxed_381_ = lean_unbox_uint64(v_c_380_);
lean_dec_ref(v_c_380_);
v_res_382_ = l_Lean_Expr_Data_looseBVarRange(v_c_boxed_381_);
v_r_383_ = lean_box_uint32(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t v_c_384_){
_start:
{
uint64_t v___x_385_; uint64_t v___x_386_; uint64_t v___x_387_; uint64_t v___x_388_; uint8_t v___x_389_; 
v___x_385_ = 40ULL;
v___x_386_ = lean_uint64_shift_right(v_c_384_, v___x_385_);
v___x_387_ = 1ULL;
v___x_388_ = lean_uint64_land(v___x_386_, v___x_387_);
v___x_389_ = lean_uint64_dec_eq(v___x_388_, v___x_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object* v_c_390_){
_start:
{
uint64_t v_c_boxed_391_; uint8_t v_res_392_; lean_object* v_r_393_; 
v_c_boxed_391_ = lean_unbox_uint64(v_c_390_);
lean_dec_ref(v_c_390_);
v_res_392_ = l_Lean_Expr_Data_hasFVar(v_c_boxed_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t v_c_394_){
_start:
{
uint64_t v___x_395_; uint64_t v___x_396_; uint64_t v___x_397_; uint64_t v___x_398_; uint8_t v___x_399_; 
v___x_395_ = 41ULL;
v___x_396_ = lean_uint64_shift_right(v_c_394_, v___x_395_);
v___x_397_ = 1ULL;
v___x_398_ = lean_uint64_land(v___x_396_, v___x_397_);
v___x_399_ = lean_uint64_dec_eq(v___x_398_, v___x_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object* v_c_400_){
_start:
{
uint64_t v_c_boxed_401_; uint8_t v_res_402_; lean_object* v_r_403_; 
v_c_boxed_401_ = lean_unbox_uint64(v_c_400_);
lean_dec_ref(v_c_400_);
v_res_402_ = l_Lean_Expr_Data_hasExprMVar(v_c_boxed_401_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t v_c_404_){
_start:
{
uint64_t v___x_405_; uint64_t v___x_406_; uint64_t v___x_407_; uint64_t v___x_408_; uint8_t v___x_409_; 
v___x_405_ = 42ULL;
v___x_406_ = lean_uint64_shift_right(v_c_404_, v___x_405_);
v___x_407_ = 1ULL;
v___x_408_ = lean_uint64_land(v___x_406_, v___x_407_);
v___x_409_ = lean_uint64_dec_eq(v___x_408_, v___x_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object* v_c_410_){
_start:
{
uint64_t v_c_boxed_411_; uint8_t v_res_412_; lean_object* v_r_413_; 
v_c_boxed_411_ = lean_unbox_uint64(v_c_410_);
lean_dec_ref(v_c_410_);
v_res_412_ = l_Lean_Expr_Data_hasLevelMVar(v_c_boxed_411_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t v_c_414_){
_start:
{
uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v___x_417_; uint64_t v___x_418_; uint8_t v___x_419_; 
v___x_415_ = 43ULL;
v___x_416_ = lean_uint64_shift_right(v_c_414_, v___x_415_);
v___x_417_ = 1ULL;
v___x_418_ = lean_uint64_land(v___x_416_, v___x_417_);
v___x_419_ = lean_uint64_dec_eq(v___x_418_, v___x_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object* v_c_420_){
_start:
{
uint64_t v_c_boxed_421_; uint8_t v_res_422_; lean_object* v_r_423_; 
v_c_boxed_421_ = lean_unbox_uint64(v_c_420_);
lean_dec_ref(v_c_420_);
v_res_422_ = l_Lean_Expr_Data_hasLevelParam(v_c_boxed_421_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_425_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_426_; uint64_t v_res_427_; lean_object* v_r_428_; 
v_a_00___x40___internal___hyg_1__boxed_426_ = lean_unbox(v_a_00___x40___internal___hyg_425_);
v_res_427_ = lean_uint8_to_uint64(v_a_00___x40___internal___hyg_1__boxed_426_);
v_r_428_ = lean_box_uint64(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object* v_h_436_, lean_object* v_looseBVarRange_437_, lean_object* v_approxDepth_438_, lean_object* v_hasFVar_439_, lean_object* v_hasExprMVar_440_, lean_object* v_hasLevelMVar_441_, lean_object* v_hasLevelParam_442_){
_start:
{
uint64_t v_h_boxed_443_; uint32_t v_approxDepth_boxed_444_; uint8_t v_hasFVar_boxed_445_; uint8_t v_hasExprMVar_boxed_446_; uint8_t v_hasLevelMVar_boxed_447_; uint8_t v_hasLevelParam_boxed_448_; uint64_t v_res_449_; lean_object* v_r_450_; 
v_h_boxed_443_ = lean_unbox_uint64(v_h_436_);
lean_dec_ref(v_h_436_);
v_approxDepth_boxed_444_ = lean_unbox_uint32(v_approxDepth_438_);
lean_dec(v_approxDepth_438_);
v_hasFVar_boxed_445_ = lean_unbox(v_hasFVar_439_);
v_hasExprMVar_boxed_446_ = lean_unbox(v_hasExprMVar_440_);
v_hasLevelMVar_boxed_447_ = lean_unbox(v_hasLevelMVar_441_);
v_hasLevelParam_boxed_448_ = lean_unbox(v_hasLevelParam_442_);
v_res_449_ = lean_expr_mk_data(v_h_boxed_443_, v_looseBVarRange_437_, v_approxDepth_boxed_444_, v_hasFVar_boxed_445_, v_hasExprMVar_boxed_446_, v_hasLevelMVar_boxed_447_, v_hasLevelParam_boxed_448_);
v_r_450_ = lean_box_uint64(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object* v_fData_453_, lean_object* v_aData_454_){
_start:
{
uint64_t v_fData_boxed_455_; uint64_t v_aData_boxed_456_; uint64_t v_res_457_; lean_object* v_r_458_; 
v_fData_boxed_455_ = lean_unbox_uint64(v_fData_453_);
lean_dec_ref(v_fData_453_);
v_aData_boxed_456_ = lean_unbox_uint64(v_aData_454_);
lean_dec_ref(v_aData_454_);
v_res_457_ = lean_expr_mk_app_data(v_fData_boxed_455_, v_aData_boxed_456_);
v_r_458_ = lean_box_uint64(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint64_t v_h_459_, lean_object* v_looseBVarRange_460_, uint32_t v_approxDepth_461_, uint8_t v_hasFVar_462_, uint8_t v_hasExprMVar_463_, uint8_t v_hasLevelMVar_464_, uint8_t v_hasLevelParam_465_){
_start:
{
uint64_t v___x_466_; 
v___x_466_ = lean_expr_mk_data(v_h_459_, v_looseBVarRange_460_, v_approxDepth_461_, v_hasFVar_462_, v_hasExprMVar_463_, v_hasLevelMVar_464_, v_hasLevelParam_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object* v_h_467_, lean_object* v_looseBVarRange_468_, lean_object* v_approxDepth_469_, lean_object* v_hasFVar_470_, lean_object* v_hasExprMVar_471_, lean_object* v_hasLevelMVar_472_, lean_object* v_hasLevelParam_473_){
_start:
{
uint64_t v_h_boxed_474_; uint32_t v_approxDepth_boxed_475_; uint8_t v_hasFVar_boxed_476_; uint8_t v_hasExprMVar_boxed_477_; uint8_t v_hasLevelMVar_boxed_478_; uint8_t v_hasLevelParam_boxed_479_; uint64_t v_res_480_; lean_object* v_r_481_; 
v_h_boxed_474_ = lean_unbox_uint64(v_h_467_);
lean_dec_ref(v_h_467_);
v_approxDepth_boxed_475_ = lean_unbox_uint32(v_approxDepth_469_);
lean_dec(v_approxDepth_469_);
v_hasFVar_boxed_476_ = lean_unbox(v_hasFVar_470_);
v_hasExprMVar_boxed_477_ = lean_unbox(v_hasExprMVar_471_);
v_hasLevelMVar_boxed_478_ = lean_unbox(v_hasLevelMVar_472_);
v_hasLevelParam_boxed_479_ = lean_unbox(v_hasLevelParam_473_);
v_res_480_ = l_Lean_Expr_mkDataForBinder(v_h_boxed_474_, v_looseBVarRange_468_, v_approxDepth_boxed_475_, v_hasFVar_boxed_476_, v_hasExprMVar_boxed_477_, v_hasLevelMVar_boxed_478_, v_hasLevelParam_boxed_479_);
v_r_481_ = lean_box_uint64(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint64_t v_h_482_, lean_object* v_looseBVarRange_483_, uint32_t v_approxDepth_484_, uint8_t v_hasFVar_485_, uint8_t v_hasExprMVar_486_, uint8_t v_hasLevelMVar_487_, uint8_t v_hasLevelParam_488_){
_start:
{
uint64_t v___x_489_; 
v___x_489_ = lean_expr_mk_data(v_h_482_, v_looseBVarRange_483_, v_approxDepth_484_, v_hasFVar_485_, v_hasExprMVar_486_, v_hasLevelMVar_487_, v_hasLevelParam_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object* v_h_490_, lean_object* v_looseBVarRange_491_, lean_object* v_approxDepth_492_, lean_object* v_hasFVar_493_, lean_object* v_hasExprMVar_494_, lean_object* v_hasLevelMVar_495_, lean_object* v_hasLevelParam_496_){
_start:
{
uint64_t v_h_boxed_497_; uint32_t v_approxDepth_boxed_498_; uint8_t v_hasFVar_boxed_499_; uint8_t v_hasExprMVar_boxed_500_; uint8_t v_hasLevelMVar_boxed_501_; uint8_t v_hasLevelParam_boxed_502_; uint64_t v_res_503_; lean_object* v_r_504_; 
v_h_boxed_497_ = lean_unbox_uint64(v_h_490_);
lean_dec_ref(v_h_490_);
v_approxDepth_boxed_498_ = lean_unbox_uint32(v_approxDepth_492_);
lean_dec(v_approxDepth_492_);
v_hasFVar_boxed_499_ = lean_unbox(v_hasFVar_493_);
v_hasExprMVar_boxed_500_ = lean_unbox(v_hasExprMVar_494_);
v_hasLevelMVar_boxed_501_ = lean_unbox(v_hasLevelMVar_495_);
v_hasLevelParam_boxed_502_ = lean_unbox(v_hasLevelParam_496_);
v_res_503_ = l_Lean_Expr_mkDataForLet(v_h_boxed_497_, v_looseBVarRange_491_, v_approxDepth_boxed_498_, v_hasFVar_boxed_499_, v_hasExprMVar_boxed_500_, v_hasLevelMVar_boxed_501_, v_hasLevelParam_boxed_502_);
v_r_504_ = lean_box_uint64(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0(uint64_t v_v_514_, lean_object* v_prec_515_){
_start:
{
lean_object* v_r_517_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v_r_527_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v_r_540_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v_r_553_; lean_object* v_r_560_; lean_object* v___x_571_; uint64_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_r_575_; uint32_t v___x_576_; uint32_t v___x_577_; uint8_t v___x_578_; 
v___x_571_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__7));
v___x_572_ = l_Lean_Expr_Data_hash(v_v_514_);
v___x_573_ = lean_uint64_to_nat(v___x_572_);
v___x_574_ = l_Nat_reprFast(v___x_573_);
v_r_575_ = lean_string_append(v___x_571_, v___x_574_);
lean_dec_ref(v___x_574_);
v___x_576_ = l_Lean_Expr_Data_looseBVarRange(v_v_514_);
v___x_577_ = 0;
v___x_578_ = lean_uint32_dec_eq(v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_r_585_; 
v___x_579_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__8));
v___x_580_ = lean_string_append(v_r_575_, v___x_579_);
v___x_581_ = lean_uint32_to_nat(v___x_576_);
v___x_582_ = l_Nat_reprFast(v___x_581_);
v___x_583_ = lean_string_append(v___x_580_, v___x_582_);
lean_dec_ref(v___x_582_);
v___x_584_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_585_ = lean_string_append(v___x_583_, v___x_584_);
v_r_560_ = v_r_585_;
goto v___jp_559_;
}
else
{
v_r_560_ = v_r_575_;
goto v___jp_559_;
}
v___jp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_518_, 0, v_r_517_);
v___x_519_ = l_Repr_addAppParen(v___x_518_, v_prec_515_);
return v___x_519_;
}
v___jp_520_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v_r_525_; 
v___x_523_ = lean_string_append(v___y_521_, v___y_522_);
v___x_524_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_525_ = lean_string_append(v___x_523_, v___x_524_);
v_r_517_ = v_r_525_;
goto v___jp_516_;
}
v___jp_526_:
{
uint8_t v___x_528_; 
v___x_528_ = l_Lean_Expr_Data_hasLevelMVar(v_v_514_);
if (v___x_528_ == 0)
{
v_r_517_ = v_r_527_;
goto v___jp_516_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
v___x_530_ = lean_string_append(v_r_527_, v___x_529_);
if (v___x_528_ == 0)
{
lean_object* v___x_531_; 
v___x_531_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_521_ = v___x_530_;
v___y_522_ = v___x_531_;
goto v___jp_520_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_521_ = v___x_530_;
v___y_522_ = v___x_532_;
goto v___jp_520_;
}
}
}
v___jp_533_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_r_538_; 
v___x_536_ = lean_string_append(v___y_534_, v___y_535_);
v___x_537_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_538_ = lean_string_append(v___x_536_, v___x_537_);
v_r_527_ = v_r_538_;
goto v___jp_526_;
}
v___jp_539_:
{
uint8_t v___x_541_; 
v___x_541_ = l_Lean_Expr_Data_hasExprMVar(v_v_514_);
if (v___x_541_ == 0)
{
v_r_527_ = v_r_540_;
goto v___jp_526_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__4));
v___x_543_ = lean_string_append(v_r_540_, v___x_542_);
if (v___x_541_ == 0)
{
lean_object* v___x_544_; 
v___x_544_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_534_ = v___x_543_;
v___y_535_ = v___x_544_;
goto v___jp_533_;
}
else
{
lean_object* v___x_545_; 
v___x_545_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_534_ = v___x_543_;
v___y_535_ = v___x_545_;
goto v___jp_533_;
}
}
}
v___jp_546_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v_r_551_; 
v___x_549_ = lean_string_append(v___y_547_, v___y_548_);
v___x_550_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_551_ = lean_string_append(v___x_549_, v___x_550_);
v_r_540_ = v_r_551_;
goto v___jp_539_;
}
v___jp_552_:
{
uint8_t v___x_554_; 
v___x_554_ = l_Lean_Expr_Data_hasFVar(v_v_514_);
if (v___x_554_ == 0)
{
v_r_540_ = v_r_553_;
goto v___jp_539_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__5));
v___x_556_ = lean_string_append(v_r_553_, v___x_555_);
if (v___x_554_ == 0)
{
lean_object* v___x_557_; 
v___x_557_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_547_ = v___x_556_;
v___y_548_ = v___x_557_;
goto v___jp_546_;
}
else
{
lean_object* v___x_558_; 
v___x_558_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_547_ = v___x_556_;
v___y_548_ = v___x_558_;
goto v___jp_546_;
}
}
}
v___jp_559_:
{
uint8_t v___x_561_; uint8_t v___x_562_; uint8_t v___x_563_; 
v___x_561_ = l_Lean_Expr_Data_approxDepth(v_v_514_);
v___x_562_ = 0;
v___x_563_ = lean_uint8_dec_eq(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v_r_570_; 
v___x_564_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__6));
v___x_565_ = lean_string_append(v_r_560_, v___x_564_);
v___x_566_ = lean_uint8_to_nat(v___x_561_);
v___x_567_ = l_Nat_reprFast(v___x_566_);
v___x_568_ = lean_string_append(v___x_565_, v___x_567_);
lean_dec_ref(v___x_567_);
v___x_569_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_570_ = lean_string_append(v___x_568_, v___x_569_);
v_r_553_ = v_r_570_;
goto v___jp_552_;
}
else
{
v_r_553_ = v_r_560_;
goto v___jp_552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0___boxed(lean_object* v_v_586_, lean_object* v_prec_587_){
_start:
{
uint64_t v_v_boxed_588_; lean_object* v_res_589_; 
v_v_boxed_588_ = lean_unbox_uint64(v_v_586_);
lean_dec_ref(v_v_586_);
v_res_589_ = l_Lean_instReprData__1___lam__0(v_v_boxed_588_, v_prec_587_);
lean_dec(v_prec_587_);
return v_res_589_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId_default(void){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = lean_box(0);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId(void){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = lean_box(0);
return v___x_593_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqFVarId_beq(lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
uint8_t v___x_596_; 
v___x_596_ = lean_name_eq(v_x_594_, v_x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
uint8_t v_res_599_; lean_object* v_r_600_; 
v_res_599_ = l_Lean_instBEqFVarId_beq(v_x_597_, v_x_598_);
lean_dec(v_x_598_);
lean_dec(v_x_597_);
v_r_600_ = lean_box(v_res_599_);
return v_r_600_;
}
}
static uint64_t _init_l_Lean_instHashableFVarId_hash___closed__0(void){
_start:
{
lean_object* v___x_603_; uint64_t v___x_604_; 
v___x_603_ = lean_unsigned_to_nat(1723u);
v___x_604_ = lean_uint64_of_nat(v___x_603_);
return v___x_604_;
}
}
static uint64_t _init_l_Lean_instHashableFVarId_hash___closed__1(void){
_start:
{
uint64_t v___x_605_; uint64_t v___x_606_; uint64_t v___x_607_; 
v___x_605_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
v___x_606_ = 0ULL;
v___x_607_ = lean_uint64_mix_hash(v___x_606_, v___x_605_);
return v___x_607_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableFVarId_hash(lean_object* v_x_608_){
_start:
{
uint64_t v___x_609_; 
v___x_609_ = 0ULL;
if (lean_obj_tag(v_x_608_) == 0)
{
uint64_t v___x_610_; 
v___x_610_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__1, &l_Lean_instHashableFVarId_hash___closed__1_once, _init_l_Lean_instHashableFVarId_hash___closed__1);
return v___x_610_;
}
else
{
uint64_t v_hash_611_; uint64_t v___x_612_; 
v_hash_611_ = lean_ctor_get_uint64(v_x_608_, sizeof(void*)*2);
v___x_612_ = lean_uint64_mix_hash(v___x_609_, v_hash_611_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object* v_x_613_){
_start:
{
uint64_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = l_Lean_instHashableFVarId_hash(v_x_613_);
lean_dec(v_x_613_);
v_r_615_ = lean_box_uint64(v_res_614_);
return v_r_615_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lean_box(1);
return v___x_620_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet(void){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = lean_box(1);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = lean_box(1);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet(void){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = lean_box(1);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___aux__1(lean_object* v_e_625_){
_start:
{
lean_object* v___f_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___f_626_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_627_ = lean_box(1);
lean_inc(v_e_625_);
v___x_628_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___f_626_, v_e_625_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_box(0);
v___x_630_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_626_, v_e_625_, v___x_629_, v___x_627_);
return v___x_630_;
}
else
{
lean_dec(v_e_625_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object* v_k_631_, lean_object* v_v_632_, lean_object* v_t_633_){
_start:
{
if (lean_obj_tag(v_t_633_) == 0)
{
lean_object* v_size_634_; lean_object* v_k_635_; lean_object* v_v_636_; lean_object* v_l_637_; lean_object* v_r_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_918_; 
v_size_634_ = lean_ctor_get(v_t_633_, 0);
v_k_635_ = lean_ctor_get(v_t_633_, 1);
v_v_636_ = lean_ctor_get(v_t_633_, 2);
v_l_637_ = lean_ctor_get(v_t_633_, 3);
v_r_638_ = lean_ctor_get(v_t_633_, 4);
v_isSharedCheck_918_ = !lean_is_exclusive(v_t_633_);
if (v_isSharedCheck_918_ == 0)
{
v___x_640_ = v_t_633_;
v_isShared_641_ = v_isSharedCheck_918_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_r_638_);
lean_inc(v_l_637_);
lean_inc(v_v_636_);
lean_inc(v_k_635_);
lean_inc(v_size_634_);
lean_dec(v_t_633_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_918_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
uint8_t v___x_642_; 
v___x_642_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_631_, v_k_635_);
switch(v___x_642_)
{
case 0:
{
lean_object* v_impl_643_; lean_object* v___x_644_; 
lean_dec(v_size_634_);
v_impl_643_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_631_, v_v_632_, v_l_637_);
v___x_644_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_638_) == 0)
{
lean_object* v_size_645_; lean_object* v_size_646_; lean_object* v_k_647_; lean_object* v_v_648_; lean_object* v_l_649_; lean_object* v_r_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_size_645_ = lean_ctor_get(v_r_638_, 0);
v_size_646_ = lean_ctor_get(v_impl_643_, 0);
lean_inc(v_size_646_);
v_k_647_ = lean_ctor_get(v_impl_643_, 1);
lean_inc(v_k_647_);
v_v_648_ = lean_ctor_get(v_impl_643_, 2);
lean_inc(v_v_648_);
v_l_649_ = lean_ctor_get(v_impl_643_, 3);
lean_inc(v_l_649_);
v_r_650_ = lean_ctor_get(v_impl_643_, 4);
lean_inc(v_r_650_);
v___x_651_ = lean_unsigned_to_nat(3u);
v___x_652_ = lean_nat_mul(v___x_651_, v_size_645_);
v___x_653_ = lean_nat_dec_lt(v___x_652_, v_size_646_);
lean_dec(v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
lean_dec(v_r_650_);
lean_dec(v_l_649_);
lean_dec(v_v_648_);
lean_dec(v_k_647_);
v___x_654_ = lean_nat_add(v___x_644_, v_size_646_);
lean_dec(v_size_646_);
v___x_655_ = lean_nat_add(v___x_654_, v_size_645_);
lean_dec(v___x_654_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 3, v_impl_643_);
lean_ctor_set(v___x_640_, 0, v___x_655_);
v___x_657_ = v___x_640_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_k_635_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_v_636_);
lean_ctor_set(v_reuseFailAlloc_658_, 3, v_impl_643_);
lean_ctor_set(v_reuseFailAlloc_658_, 4, v_r_638_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
else
{
lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_724_; 
v_isSharedCheck_724_ = !lean_is_exclusive(v_impl_643_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; lean_object* v_unused_726_; lean_object* v_unused_727_; lean_object* v_unused_728_; lean_object* v_unused_729_; 
v_unused_725_ = lean_ctor_get(v_impl_643_, 4);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_impl_643_, 3);
lean_dec(v_unused_726_);
v_unused_727_ = lean_ctor_get(v_impl_643_, 2);
lean_dec(v_unused_727_);
v_unused_728_ = lean_ctor_get(v_impl_643_, 1);
lean_dec(v_unused_728_);
v_unused_729_ = lean_ctor_get(v_impl_643_, 0);
lean_dec(v_unused_729_);
v___x_660_ = v_impl_643_;
v_isShared_661_ = v_isSharedCheck_724_;
goto v_resetjp_659_;
}
else
{
lean_dec(v_impl_643_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_724_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_size_662_; lean_object* v_size_663_; lean_object* v_k_664_; lean_object* v_v_665_; lean_object* v_l_666_; lean_object* v_r_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_size_662_ = lean_ctor_get(v_l_649_, 0);
v_size_663_ = lean_ctor_get(v_r_650_, 0);
v_k_664_ = lean_ctor_get(v_r_650_, 1);
v_v_665_ = lean_ctor_get(v_r_650_, 2);
v_l_666_ = lean_ctor_get(v_r_650_, 3);
v_r_667_ = lean_ctor_get(v_r_650_, 4);
v___x_668_ = lean_unsigned_to_nat(2u);
v___x_669_ = lean_nat_mul(v___x_668_, v_size_662_);
v___x_670_ = lean_nat_dec_lt(v_size_663_, v___x_669_);
lean_dec(v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_699_; 
lean_inc(v_r_667_);
lean_inc(v_l_666_);
lean_inc(v_v_665_);
lean_inc(v_k_664_);
v_isSharedCheck_699_ = !lean_is_exclusive(v_r_650_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; lean_object* v_unused_701_; lean_object* v_unused_702_; lean_object* v_unused_703_; lean_object* v_unused_704_; 
v_unused_700_ = lean_ctor_get(v_r_650_, 4);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_r_650_, 3);
lean_dec(v_unused_701_);
v_unused_702_ = lean_ctor_get(v_r_650_, 2);
lean_dec(v_unused_702_);
v_unused_703_ = lean_ctor_get(v_r_650_, 1);
lean_dec(v_unused_703_);
v_unused_704_ = lean_ctor_get(v_r_650_, 0);
lean_dec(v_unused_704_);
v___x_672_ = v_r_650_;
v_isShared_673_ = v_isSharedCheck_699_;
goto v_resetjp_671_;
}
else
{
lean_dec(v_r_650_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_699_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___x_687_; lean_object* v___y_689_; 
v___x_674_ = lean_nat_add(v___x_644_, v_size_646_);
lean_dec(v_size_646_);
v___x_675_ = lean_nat_add(v___x_674_, v_size_645_);
lean_dec(v___x_674_);
v___x_687_ = lean_nat_add(v___x_644_, v_size_662_);
if (lean_obj_tag(v_l_666_) == 0)
{
lean_object* v_size_697_; 
v_size_697_ = lean_ctor_get(v_l_666_, 0);
lean_inc(v_size_697_);
v___y_689_ = v_size_697_;
goto v___jp_688_;
}
else
{
lean_object* v___x_698_; 
v___x_698_ = lean_unsigned_to_nat(0u);
v___y_689_ = v___x_698_;
goto v___jp_688_;
}
v___jp_676_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = lean_nat_add(v___y_677_, v___y_679_);
lean_dec(v___y_679_);
lean_dec(v___y_677_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 4, v_r_638_);
lean_ctor_set(v___x_672_, 3, v_r_667_);
lean_ctor_set(v___x_672_, 2, v_v_636_);
lean_ctor_set(v___x_672_, 1, v_k_635_);
lean_ctor_set(v___x_672_, 0, v___x_680_);
v___x_682_ = v___x_672_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_k_635_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_v_636_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v_r_667_);
lean_ctor_set(v_reuseFailAlloc_686_, 4, v_r_638_);
v___x_682_ = v_reuseFailAlloc_686_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_684_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 4, v___x_682_);
lean_ctor_set(v___x_660_, 3, v___y_678_);
lean_ctor_set(v___x_660_, 2, v_v_665_);
lean_ctor_set(v___x_660_, 1, v_k_664_);
lean_ctor_set(v___x_660_, 0, v___x_675_);
v___x_684_ = v___x_660_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_k_664_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_v_665_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v___y_678_);
lean_ctor_set(v_reuseFailAlloc_685_, 4, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
v___jp_688_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = lean_nat_add(v___x_687_, v___y_689_);
lean_dec(v___y_689_);
lean_dec(v___x_687_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v_l_666_);
lean_ctor_set(v___x_640_, 3, v_l_649_);
lean_ctor_set(v___x_640_, 2, v_v_648_);
lean_ctor_set(v___x_640_, 1, v_k_647_);
lean_ctor_set(v___x_640_, 0, v___x_690_);
v___x_692_ = v___x_640_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v_l_649_);
lean_ctor_set(v_reuseFailAlloc_696_, 4, v_l_666_);
v___x_692_ = v_reuseFailAlloc_696_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; 
v___x_693_ = lean_nat_add(v___x_644_, v_size_645_);
if (lean_obj_tag(v_r_667_) == 0)
{
lean_object* v_size_694_; 
v_size_694_ = lean_ctor_get(v_r_667_, 0);
lean_inc(v_size_694_);
v___y_677_ = v___x_693_;
v___y_678_ = v___x_692_;
v___y_679_ = v_size_694_;
goto v___jp_676_;
}
else
{
lean_object* v___x_695_; 
v___x_695_ = lean_unsigned_to_nat(0u);
v___y_677_ = v___x_693_;
v___y_678_ = v___x_692_;
v___y_679_ = v___x_695_;
goto v___jp_676_;
}
}
}
}
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
lean_del_object(v___x_640_);
v___x_705_ = lean_nat_add(v___x_644_, v_size_646_);
lean_dec(v_size_646_);
v___x_706_ = lean_nat_add(v___x_705_, v_size_645_);
lean_dec(v___x_705_);
v___x_707_ = lean_nat_add(v___x_644_, v_size_645_);
v___x_708_ = lean_nat_add(v___x_707_, v_size_663_);
lean_dec(v___x_707_);
lean_inc_ref(v_r_638_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 4, v_r_638_);
lean_ctor_set(v___x_660_, 3, v_r_650_);
lean_ctor_set(v___x_660_, 2, v_v_636_);
lean_ctor_set(v___x_660_, 1, v_k_635_);
lean_ctor_set(v___x_660_, 0, v___x_708_);
v___x_710_ = v___x_660_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_k_635_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_v_636_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_r_650_);
lean_ctor_set(v_reuseFailAlloc_723_, 4, v_r_638_);
v___x_710_ = v_reuseFailAlloc_723_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
v_isSharedCheck_717_ = !lean_is_exclusive(v_r_638_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; lean_object* v_unused_719_; lean_object* v_unused_720_; lean_object* v_unused_721_; lean_object* v_unused_722_; 
v_unused_718_ = lean_ctor_get(v_r_638_, 4);
lean_dec(v_unused_718_);
v_unused_719_ = lean_ctor_get(v_r_638_, 3);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_r_638_, 2);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v_r_638_, 1);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_r_638_, 0);
lean_dec(v_unused_722_);
v___x_712_ = v_r_638_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_dec(v_r_638_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 4, v___x_710_);
lean_ctor_set(v___x_712_, 3, v_l_649_);
lean_ctor_set(v___x_712_, 2, v_v_648_);
lean_ctor_set(v___x_712_, 1, v_k_647_);
lean_ctor_set(v___x_712_, 0, v___x_706_);
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_l_649_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v___x_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_730_; 
v_l_730_ = lean_ctor_get(v_impl_643_, 3);
lean_inc(v_l_730_);
if (lean_obj_tag(v_l_730_) == 0)
{
lean_object* v_r_731_; lean_object* v_k_732_; lean_object* v_v_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_744_; 
v_r_731_ = lean_ctor_get(v_impl_643_, 4);
v_k_732_ = lean_ctor_get(v_impl_643_, 1);
v_v_733_ = lean_ctor_get(v_impl_643_, 2);
v_isSharedCheck_744_ = !lean_is_exclusive(v_impl_643_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; lean_object* v_unused_746_; 
v_unused_745_ = lean_ctor_get(v_impl_643_, 3);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v_impl_643_, 0);
lean_dec(v_unused_746_);
v___x_735_ = v_impl_643_;
v_isShared_736_ = v_isSharedCheck_744_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_r_731_);
lean_inc(v_v_733_);
lean_inc(v_k_732_);
lean_dec(v_impl_643_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_744_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_731_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 3, v_r_731_);
lean_ctor_set(v___x_735_, 2, v_v_636_);
lean_ctor_set(v___x_735_, 1, v_k_635_);
lean_ctor_set(v___x_735_, 0, v___x_644_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_k_635_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_v_636_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v_r_731_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v_r_731_);
v___x_739_ = v_reuseFailAlloc_743_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_741_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v___x_739_);
lean_ctor_set(v___x_640_, 3, v_l_730_);
lean_ctor_set(v___x_640_, 2, v_v_733_);
lean_ctor_set(v___x_640_, 1, v_k_732_);
lean_ctor_set(v___x_640_, 0, v___x_737_);
v___x_741_ = v___x_640_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_k_732_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v_v_733_);
lean_ctor_set(v_reuseFailAlloc_742_, 3, v_l_730_);
lean_ctor_set(v_reuseFailAlloc_742_, 4, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
else
{
lean_object* v_r_747_; 
v_r_747_ = lean_ctor_get(v_impl_643_, 4);
lean_inc(v_r_747_);
if (lean_obj_tag(v_r_747_) == 0)
{
lean_object* v_k_748_; lean_object* v_v_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_772_; 
v_k_748_ = lean_ctor_get(v_impl_643_, 1);
v_v_749_ = lean_ctor_get(v_impl_643_, 2);
v_isSharedCheck_772_ = !lean_is_exclusive(v_impl_643_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; lean_object* v_unused_774_; lean_object* v_unused_775_; 
v_unused_773_ = lean_ctor_get(v_impl_643_, 4);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_impl_643_, 3);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_impl_643_, 0);
lean_dec(v_unused_775_);
v___x_751_ = v_impl_643_;
v_isShared_752_ = v_isSharedCheck_772_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_v_749_);
lean_inc(v_k_748_);
lean_dec(v_impl_643_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_772_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_k_753_; lean_object* v_v_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_768_; 
v_k_753_ = lean_ctor_get(v_r_747_, 1);
v_v_754_ = lean_ctor_get(v_r_747_, 2);
v_isSharedCheck_768_ = !lean_is_exclusive(v_r_747_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; lean_object* v_unused_770_; lean_object* v_unused_771_; 
v_unused_769_ = lean_ctor_get(v_r_747_, 4);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_r_747_, 3);
lean_dec(v_unused_770_);
v_unused_771_ = lean_ctor_get(v_r_747_, 0);
lean_dec(v_unused_771_);
v___x_756_ = v_r_747_;
v_isShared_757_ = v_isSharedCheck_768_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_v_754_);
lean_inc(v_k_753_);
lean_dec(v_r_747_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_768_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = lean_unsigned_to_nat(3u);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v_l_730_);
lean_ctor_set(v___x_756_, 3, v_l_730_);
lean_ctor_set(v___x_756_, 2, v_v_749_);
lean_ctor_set(v___x_756_, 1, v_k_748_);
lean_ctor_set(v___x_756_, 0, v___x_644_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_k_748_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_v_749_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_l_730_);
lean_ctor_set(v_reuseFailAlloc_767_, 4, v_l_730_);
v___x_760_ = v_reuseFailAlloc_767_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_762_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 4, v_l_730_);
lean_ctor_set(v___x_751_, 2, v_v_636_);
lean_ctor_set(v___x_751_, 1, v_k_635_);
lean_ctor_set(v___x_751_, 0, v___x_644_);
v___x_762_ = v___x_751_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_k_635_);
lean_ctor_set(v_reuseFailAlloc_766_, 2, v_v_636_);
lean_ctor_set(v_reuseFailAlloc_766_, 3, v_l_730_);
lean_ctor_set(v_reuseFailAlloc_766_, 4, v_l_730_);
v___x_762_ = v_reuseFailAlloc_766_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_764_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v___x_762_);
lean_ctor_set(v___x_640_, 3, v___x_760_);
lean_ctor_set(v___x_640_, 2, v_v_754_);
lean_ctor_set(v___x_640_, 1, v_k_753_);
lean_ctor_set(v___x_640_, 0, v___x_758_);
v___x_764_ = v___x_640_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_k_753_);
lean_ctor_set(v_reuseFailAlloc_765_, 2, v_v_754_);
lean_ctor_set(v_reuseFailAlloc_765_, 3, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_765_, 4, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
}
else
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = lean_unsigned_to_nat(2u);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v_r_747_);
lean_ctor_set(v___x_640_, 3, v_impl_643_);
lean_ctor_set(v___x_640_, 0, v___x_776_);
v___x_778_ = v___x_640_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_k_635_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_v_636_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_impl_643_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v_r_747_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
case 1:
{
lean_object* v___x_781_; 
lean_dec(v_v_636_);
lean_dec(v_k_635_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 2, v_v_632_);
lean_ctor_set(v___x_640_, 1, v_k_631_);
v___x_781_ = v___x_640_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_size_634_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_l_637_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v_r_638_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
default: 
{
lean_object* v_impl_783_; lean_object* v___x_784_; 
lean_dec(v_size_634_);
v_impl_783_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_631_, v_v_632_, v_r_638_);
v___x_784_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_637_) == 0)
{
lean_object* v_size_785_; lean_object* v_size_786_; lean_object* v_k_787_; lean_object* v_v_788_; lean_object* v_l_789_; lean_object* v_r_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_size_785_ = lean_ctor_get(v_l_637_, 0);
v_size_786_ = lean_ctor_get(v_impl_783_, 0);
lean_inc(v_size_786_);
v_k_787_ = lean_ctor_get(v_impl_783_, 1);
lean_inc(v_k_787_);
v_v_788_ = lean_ctor_get(v_impl_783_, 2);
lean_inc(v_v_788_);
v_l_789_ = lean_ctor_get(v_impl_783_, 3);
lean_inc(v_l_789_);
v_r_790_ = lean_ctor_get(v_impl_783_, 4);
lean_inc(v_r_790_);
v___x_791_ = lean_unsigned_to_nat(3u);
v___x_792_ = lean_nat_mul(v___x_791_, v_size_785_);
v___x_793_ = lean_nat_dec_lt(v___x_792_, v_size_786_);
lean_dec(v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
lean_dec(v_r_790_);
lean_dec(v_l_789_);
lean_dec(v_v_788_);
lean_dec(v_k_787_);
v___x_794_ = lean_nat_add(v___x_784_, v_size_785_);
v___x_795_ = lean_nat_add(v___x_794_, v_size_786_);
lean_dec(v_size_786_);
lean_dec(v___x_794_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v_impl_783_);
lean_ctor_set(v___x_640_, 0, v___x_795_);
v___x_797_ = v___x_640_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_k_635_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v_v_636_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v_l_637_);
lean_ctor_set(v_reuseFailAlloc_798_, 4, v_impl_783_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
else
{
lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_862_; 
v_isSharedCheck_862_ = !lean_is_exclusive(v_impl_783_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; lean_object* v_unused_864_; lean_object* v_unused_865_; lean_object* v_unused_866_; lean_object* v_unused_867_; 
v_unused_863_ = lean_ctor_get(v_impl_783_, 4);
lean_dec(v_unused_863_);
v_unused_864_ = lean_ctor_get(v_impl_783_, 3);
lean_dec(v_unused_864_);
v_unused_865_ = lean_ctor_get(v_impl_783_, 2);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_impl_783_, 1);
lean_dec(v_unused_866_);
v_unused_867_ = lean_ctor_get(v_impl_783_, 0);
lean_dec(v_unused_867_);
v___x_800_ = v_impl_783_;
v_isShared_801_ = v_isSharedCheck_862_;
goto v_resetjp_799_;
}
else
{
lean_dec(v_impl_783_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_862_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_size_802_; lean_object* v_k_803_; lean_object* v_v_804_; lean_object* v_l_805_; lean_object* v_r_806_; lean_object* v_size_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_size_802_ = lean_ctor_get(v_l_789_, 0);
v_k_803_ = lean_ctor_get(v_l_789_, 1);
v_v_804_ = lean_ctor_get(v_l_789_, 2);
v_l_805_ = lean_ctor_get(v_l_789_, 3);
v_r_806_ = lean_ctor_get(v_l_789_, 4);
v_size_807_ = lean_ctor_get(v_r_790_, 0);
v___x_808_ = lean_unsigned_to_nat(2u);
v___x_809_ = lean_nat_mul(v___x_808_, v_size_807_);
v___x_810_ = lean_nat_dec_lt(v_size_802_, v___x_809_);
lean_dec(v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_838_; 
lean_inc(v_r_806_);
lean_inc(v_l_805_);
lean_inc(v_v_804_);
lean_inc(v_k_803_);
v_isSharedCheck_838_ = !lean_is_exclusive(v_l_789_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; lean_object* v_unused_843_; 
v_unused_839_ = lean_ctor_get(v_l_789_, 4);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_l_789_, 3);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_l_789_, 2);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_l_789_, 1);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_l_789_, 0);
lean_dec(v_unused_843_);
v___x_812_ = v_l_789_;
v_isShared_813_ = v_isSharedCheck_838_;
goto v_resetjp_811_;
}
else
{
lean_dec(v_l_789_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_838_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_828_; 
v___x_814_ = lean_nat_add(v___x_784_, v_size_785_);
v___x_815_ = lean_nat_add(v___x_814_, v_size_786_);
lean_dec(v_size_786_);
if (lean_obj_tag(v_l_805_) == 0)
{
lean_object* v_size_836_; 
v_size_836_ = lean_ctor_get(v_l_805_, 0);
lean_inc(v_size_836_);
v___y_828_ = v_size_836_;
goto v___jp_827_;
}
else
{
lean_object* v___x_837_; 
v___x_837_ = lean_unsigned_to_nat(0u);
v___y_828_ = v___x_837_;
goto v___jp_827_;
}
v___jp_816_:
{
lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_820_ = lean_nat_add(v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec(v___y_818_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 4, v_r_790_);
lean_ctor_set(v___x_812_, 3, v_r_806_);
lean_ctor_set(v___x_812_, 2, v_v_788_);
lean_ctor_set(v___x_812_, 1, v_k_787_);
lean_ctor_set(v___x_812_, 0, v___x_820_);
v___x_822_ = v___x_812_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_k_787_);
lean_ctor_set(v_reuseFailAlloc_826_, 2, v_v_788_);
lean_ctor_set(v_reuseFailAlloc_826_, 3, v_r_806_);
lean_ctor_set(v_reuseFailAlloc_826_, 4, v_r_790_);
v___x_822_ = v_reuseFailAlloc_826_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_824_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v___x_822_);
lean_ctor_set(v___x_800_, 3, v___y_817_);
lean_ctor_set(v___x_800_, 2, v_v_804_);
lean_ctor_set(v___x_800_, 1, v_k_803_);
lean_ctor_set(v___x_800_, 0, v___x_815_);
v___x_824_ = v___x_800_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_k_803_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_v_804_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v___y_817_);
lean_ctor_set(v_reuseFailAlloc_825_, 4, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
v___jp_827_:
{
lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_829_ = lean_nat_add(v___x_814_, v___y_828_);
lean_dec(v___y_828_);
lean_dec(v___x_814_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v_l_805_);
lean_ctor_set(v___x_640_, 0, v___x_829_);
v___x_831_ = v___x_640_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_k_635_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_v_636_);
lean_ctor_set(v_reuseFailAlloc_835_, 3, v_l_637_);
lean_ctor_set(v_reuseFailAlloc_835_, 4, v_l_805_);
v___x_831_ = v_reuseFailAlloc_835_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_832_; 
v___x_832_ = lean_nat_add(v___x_784_, v_size_807_);
if (lean_obj_tag(v_r_806_) == 0)
{
lean_object* v_size_833_; 
v_size_833_ = lean_ctor_get(v_r_806_, 0);
lean_inc(v_size_833_);
v___y_817_ = v___x_831_;
v___y_818_ = v___x_832_;
v___y_819_ = v_size_833_;
goto v___jp_816_;
}
else
{
lean_object* v___x_834_; 
v___x_834_ = lean_unsigned_to_nat(0u);
v___y_817_ = v___x_831_;
v___y_818_ = v___x_832_;
v___y_819_ = v___x_834_;
goto v___jp_816_;
}
}
}
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
lean_del_object(v___x_640_);
v___x_844_ = lean_nat_add(v___x_784_, v_size_785_);
v___x_845_ = lean_nat_add(v___x_844_, v_size_786_);
lean_dec(v_size_786_);
v___x_846_ = lean_nat_add(v___x_844_, v_size_802_);
lean_dec(v___x_844_);
lean_inc_ref(v_l_637_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v_l_789_);
lean_ctor_set(v___x_800_, 3, v_l_637_);
lean_ctor_set(v___x_800_, 2, v_v_636_);
lean_ctor_set(v___x_800_, 1, v_k_635_);
lean_ctor_set(v___x_800_, 0, v___x_846_);
v___x_848_ = v___x_800_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_k_635_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_v_636_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v_l_637_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v_l_789_);
v___x_848_ = v_reuseFailAlloc_861_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_isSharedCheck_855_ = !lean_is_exclusive(v_l_637_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; lean_object* v_unused_860_; 
v_unused_856_ = lean_ctor_get(v_l_637_, 4);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_l_637_, 3);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_l_637_, 2);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_l_637_, 1);
lean_dec(v_unused_859_);
v_unused_860_ = lean_ctor_get(v_l_637_, 0);
lean_dec(v_unused_860_);
v___x_850_ = v_l_637_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_dec(v_l_637_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 4, v_r_790_);
lean_ctor_set(v___x_850_, 3, v___x_848_);
lean_ctor_set(v___x_850_, 2, v_v_788_);
lean_ctor_set(v___x_850_, 1, v_k_787_);
lean_ctor_set(v___x_850_, 0, v___x_845_);
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_k_787_);
lean_ctor_set(v_reuseFailAlloc_854_, 2, v_v_788_);
lean_ctor_set(v_reuseFailAlloc_854_, 3, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_854_, 4, v_r_790_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_868_; 
v_l_868_ = lean_ctor_get(v_impl_783_, 3);
lean_inc(v_l_868_);
if (lean_obj_tag(v_l_868_) == 0)
{
lean_object* v_r_869_; lean_object* v_k_870_; lean_object* v_v_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_894_; 
v_r_869_ = lean_ctor_get(v_impl_783_, 4);
v_k_870_ = lean_ctor_get(v_impl_783_, 1);
v_v_871_ = lean_ctor_get(v_impl_783_, 2);
v_isSharedCheck_894_ = !lean_is_exclusive(v_impl_783_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; lean_object* v_unused_896_; 
v_unused_895_ = lean_ctor_get(v_impl_783_, 3);
lean_dec(v_unused_895_);
v_unused_896_ = lean_ctor_get(v_impl_783_, 0);
lean_dec(v_unused_896_);
v___x_873_ = v_impl_783_;
v_isShared_874_ = v_isSharedCheck_894_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_r_869_);
lean_inc(v_v_871_);
lean_inc(v_k_870_);
lean_dec(v_impl_783_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_894_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v_k_875_; lean_object* v_v_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_890_; 
v_k_875_ = lean_ctor_get(v_l_868_, 1);
v_v_876_ = lean_ctor_get(v_l_868_, 2);
v_isSharedCheck_890_ = !lean_is_exclusive(v_l_868_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; lean_object* v_unused_892_; lean_object* v_unused_893_; 
v_unused_891_ = lean_ctor_get(v_l_868_, 4);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_l_868_, 3);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_l_868_, 0);
lean_dec(v_unused_893_);
v___x_878_ = v_l_868_;
v_isShared_879_ = v_isSharedCheck_890_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_v_876_);
lean_inc(v_k_875_);
lean_dec(v_l_868_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_890_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_869_, 2);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 4, v_r_869_);
lean_ctor_set(v___x_878_, 3, v_r_869_);
lean_ctor_set(v___x_878_, 2, v_v_636_);
lean_ctor_set(v___x_878_, 1, v_k_635_);
lean_ctor_set(v___x_878_, 0, v___x_784_);
v___x_882_ = v___x_878_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_k_635_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_v_636_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_r_869_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_r_869_);
v___x_882_ = v_reuseFailAlloc_889_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
lean_inc(v_r_869_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 3, v_r_869_);
lean_ctor_set(v___x_873_, 0, v___x_784_);
v___x_884_ = v___x_873_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_k_870_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_v_871_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_r_869_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_r_869_);
v___x_884_ = v_reuseFailAlloc_888_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v___x_884_);
lean_ctor_set(v___x_640_, 3, v___x_882_);
lean_ctor_set(v___x_640_, 2, v_v_876_);
lean_ctor_set(v___x_640_, 1, v_k_875_);
lean_ctor_set(v___x_640_, 0, v___x_880_);
v___x_886_ = v___x_640_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_k_875_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_v_876_);
lean_ctor_set(v_reuseFailAlloc_887_, 3, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_887_, 4, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
else
{
lean_object* v_r_897_; 
v_r_897_ = lean_ctor_get(v_impl_783_, 4);
lean_inc(v_r_897_);
if (lean_obj_tag(v_r_897_) == 0)
{
lean_object* v_k_898_; lean_object* v_v_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_910_; 
v_k_898_ = lean_ctor_get(v_impl_783_, 1);
v_v_899_ = lean_ctor_get(v_impl_783_, 2);
v_isSharedCheck_910_ = !lean_is_exclusive(v_impl_783_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; lean_object* v_unused_912_; lean_object* v_unused_913_; 
v_unused_911_ = lean_ctor_get(v_impl_783_, 4);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_impl_783_, 3);
lean_dec(v_unused_912_);
v_unused_913_ = lean_ctor_get(v_impl_783_, 0);
lean_dec(v_unused_913_);
v___x_901_ = v_impl_783_;
v_isShared_902_ = v_isSharedCheck_910_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_v_899_);
lean_inc(v_k_898_);
lean_dec(v_impl_783_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_910_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = lean_unsigned_to_nat(3u);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 4, v_l_868_);
lean_ctor_set(v___x_901_, 2, v_v_636_);
lean_ctor_set(v___x_901_, 1, v_k_635_);
lean_ctor_set(v___x_901_, 0, v___x_784_);
v___x_905_ = v___x_901_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_k_635_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v_v_636_);
lean_ctor_set(v_reuseFailAlloc_909_, 3, v_l_868_);
lean_ctor_set(v_reuseFailAlloc_909_, 4, v_l_868_);
v___x_905_ = v_reuseFailAlloc_909_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_907_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v_r_897_);
lean_ctor_set(v___x_640_, 3, v___x_905_);
lean_ctor_set(v___x_640_, 2, v_v_899_);
lean_ctor_set(v___x_640_, 1, v_k_898_);
lean_ctor_set(v___x_640_, 0, v___x_903_);
v___x_907_ = v___x_640_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_k_898_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v_v_899_);
lean_ctor_set(v_reuseFailAlloc_908_, 3, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_908_, 4, v_r_897_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = lean_unsigned_to_nat(2u);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v_impl_783_);
lean_ctor_set(v___x_640_, 3, v_r_897_);
lean_ctor_set(v___x_640_, 0, v___x_914_);
v___x_916_ = v___x_640_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_k_635_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_v_636_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v_r_897_);
lean_ctor_set(v_reuseFailAlloc_917_, 4, v_impl_783_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
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
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_unsigned_to_nat(1u);
v___x_920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v_k_631_);
lean_ctor_set(v___x_920_, 2, v_v_632_);
lean_ctor_set(v___x_920_, 3, v_t_633_);
lean_ctor_set(v___x_920_, 4, v_t_633_);
return v___x_920_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(lean_object* v_k_921_, lean_object* v_t_922_){
_start:
{
if (lean_obj_tag(v_t_922_) == 0)
{
lean_object* v_k_923_; lean_object* v_l_924_; lean_object* v_r_925_; uint8_t v___x_926_; 
v_k_923_ = lean_ctor_get(v_t_922_, 1);
v_l_924_ = lean_ctor_get(v_t_922_, 3);
v_r_925_ = lean_ctor_get(v_t_922_, 4);
v___x_926_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_921_, v_k_923_);
switch(v___x_926_)
{
case 0:
{
v_t_922_ = v_l_924_;
goto _start;
}
case 1:
{
uint8_t v___x_928_; 
v___x_928_ = 1;
return v___x_928_;
}
default: 
{
v_t_922_ = v_r_925_;
goto _start;
}
}
}
else
{
uint8_t v___x_930_; 
v___x_930_ = 0;
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg___boxed(lean_object* v_k_931_, lean_object* v_t_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_931_, v_t_932_);
lean_dec(v_t_932_);
lean_dec(v_k_931_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object* v___y_935_){
_start:
{
lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_936_ = lean_box(1);
v___x_937_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v___y_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_box(0);
v___x_939_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___y_935_, v___x_938_, v___x_936_);
return v___x_939_;
}
else
{
lean_dec(v___y_935_);
return v___x_936_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(lean_object* v_00_u03b2_942_, lean_object* v_k_943_, lean_object* v_t_944_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_943_, v_t_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___boxed(lean_object* v_00_u03b2_946_, lean_object* v_k_947_, lean_object* v_t_948_){
_start:
{
uint8_t v_res_949_; lean_object* v_r_950_; 
v_res_949_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(v_00_u03b2_946_, v_k_947_, v_t_948_);
lean_dec(v_t_948_);
lean_dec(v_k_947_);
v_r_950_ = lean_box(v_res_949_);
return v_r_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1(lean_object* v_00_u03b2_951_, lean_object* v_k_952_, lean_object* v_v_953_, lean_object* v_t_954_, lean_object* v_hl_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_952_, v_v_953_, v_t_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_957_, lean_object* v_a_958_, lean_object* v_b_959_, lean_object* v_c_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = lean_apply_2(v_f_957_, v_a_958_, v_c_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_962_, lean_object* v_____do__lift_963_){
_start:
{
lean_object* v_a_964_; lean_object* v___x_965_; 
v_a_964_ = lean_ctor_get(v_____do__lift_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref(v_____do__lift_963_);
v___x_965_ = lean_apply_2(v_toPure_962_, lean_box(0), v_a_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg(lean_object* v_inst_966_, lean_object* v_m_967_, lean_object* v_init_968_, lean_object* v_f_969_){
_start:
{
lean_object* v_toApplicative_970_; lean_object* v_toBind_971_; lean_object* v_toPure_972_; lean_object* v___f_973_; lean_object* v___x_974_; lean_object* v___f_975_; lean_object* v___x_976_; 
v_toApplicative_970_ = lean_ctor_get(v_inst_966_, 0);
v_toBind_971_ = lean_ctor_get(v_inst_966_, 1);
lean_inc(v_toBind_971_);
v_toPure_972_ = lean_ctor_get(v_toApplicative_970_, 1);
lean_inc(v_toPure_972_);
v___f_973_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_973_, 0, v_f_969_);
v___x_974_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_966_, v___f_973_, v_init_968_, v_m_967_);
v___f_975_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_975_, 0, v_toPure_972_);
v___x_976_ = lean_apply_4(v_toBind_971_, lean_box(0), lean_box(0), v___x_974_, v___f_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1(lean_object* v_m_977_, lean_object* v_inst_978_, lean_object* v_00_u03b2_979_, lean_object* v_m_980_, lean_object* v_init_981_, lean_object* v_f_982_){
_start:
{
lean_object* v_toApplicative_983_; lean_object* v_toBind_984_; lean_object* v_toPure_985_; lean_object* v___f_986_; lean_object* v___x_987_; lean_object* v___f_988_; lean_object* v___x_989_; 
v_toApplicative_983_ = lean_ctor_get(v_inst_978_, 0);
v_toBind_984_ = lean_ctor_get(v_inst_978_, 1);
lean_inc(v_toBind_984_);
v_toPure_985_ = lean_ctor_get(v_toApplicative_983_, 1);
lean_inc(v_toPure_985_);
v___f_986_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_986_, 0, v_f_982_);
v___x_987_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_978_, v___f_986_, v_init_981_, v_m_980_);
v___f_988_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_988_, 0, v_toPure_985_);
v___x_989_ = lean_apply_4(v_toBind_984_, lean_box(0), lean_box(0), v___x_987_, v___f_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___redArg(lean_object* v_inst_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_991_, 0, lean_box(0));
lean_closure_set(v___x_991_, 1, v_inst_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad(lean_object* v_m_992_, lean_object* v_inst_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_994_, 0, lean_box(0));
lean_closure_set(v___x_994_, 1, v_inst_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object* v_s_995_, lean_object* v_fvarId_996_){
_start:
{
uint8_t v___x_997_; 
v___x_997_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_fvarId_996_, v_s_995_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_box(0);
v___x_999_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_996_, v___x_998_, v_s_995_);
return v___x_999_;
}
else
{
lean_dec(v_fvarId_996_);
return v_s_995_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(lean_object* v_init_1000_, lean_object* v_x_1001_){
_start:
{
if (lean_obj_tag(v_x_1001_) == 0)
{
lean_object* v_k_1002_; lean_object* v_l_1003_; lean_object* v_r_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_k_1002_ = lean_ctor_get(v_x_1001_, 1);
lean_inc(v_k_1002_);
v_l_1003_ = lean_ctor_get(v_x_1001_, 3);
lean_inc(v_l_1003_);
v_r_1004_ = lean_ctor_get(v_x_1001_, 4);
lean_inc(v_r_1004_);
lean_dec_ref_known(v_x_1001_, 5);
v___x_1005_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_1000_, v_l_1003_);
v___x_1006_ = l_Lean_FVarIdSet_insert(v___x_1005_, v_k_1002_);
v_init_1000_ = v___x_1006_;
v_x_1001_ = v_r_1004_;
goto _start;
}
else
{
return v_init_1000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_union(lean_object* v_vs_u2081_1008_, lean_object* v_vs_u2082_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_vs_u2082_1009_, v_vs_u2081_1008_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0(lean_object* v_init_1011_, lean_object* v_t_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_1011_, v_t_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList(lean_object* v_l_1014_){
_start:
{
lean_object* v___f_1015_; lean_object* v___x_1016_; 
v___f_1015_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1016_ = l_Std_TreeSet_ofList___redArg(v_l_1014_, v___f_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList___boxed(lean_object* v_l_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_FVarIdSet_ofList(v_l_1017_);
lean_dec(v_l_1017_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object* v_l_1019_){
_start:
{
lean_object* v___f_1020_; lean_object* v___x_1021_; 
v___f_1020_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1021_ = l_Std_TreeSet_ofArray___redArg(v_l_1019_, v___f_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object* v_l_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_FVarIdSet_ofArray(v_l_1022_);
lean_dec_ref(v_l_1022_);
return v_res_1023_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = lean_box(0);
v___x_1025_ = lean_unsigned_to_nat(16u);
v___x_1026_ = lean_mk_array(v___x_1025_, v___x_1024_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0);
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_1027_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet(void){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet(void){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object* v_s_1034_, lean_object* v_fvarId_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1035_, v_a_1036_, v_s_1034_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object* v_00_u03b1_1038_, lean_object* v_s_1039_, lean_object* v_fvarId_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1040_, v_a_1041_, v_s_1039_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1(lean_object* v_00_u03b1_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_box(1);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* v_00_u03b1_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_box(1);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* v_00_u03b1_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_box(1);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId_default(void){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_box(0);
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId(void){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_box(0);
return v___x_1050_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMVarId_beq(lean_object* v_x_1051_, lean_object* v_x_1052_){
_start:
{
uint8_t v___x_1053_; 
v___x_1053_ = lean_name_eq(v_x_1051_, v_x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
uint8_t v_res_1056_; lean_object* v_r_1057_; 
v_res_1056_ = l_Lean_instBEqMVarId_beq(v_x_1054_, v_x_1055_);
lean_dec(v_x_1055_);
lean_dec(v_x_1054_);
v_r_1057_ = lean_box(v_res_1056_);
return v_r_1057_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableMVarId_hash(lean_object* v_x_1060_){
_start:
{
uint64_t v___x_1061_; 
v___x_1061_ = 0ULL;
if (lean_obj_tag(v_x_1060_) == 0)
{
uint64_t v___x_1062_; 
v___x_1062_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__1, &l_Lean_instHashableFVarId_hash___closed__1_once, _init_l_Lean_instHashableFVarId_hash___closed__1);
return v___x_1062_;
}
else
{
uint64_t v_hash_1063_; uint64_t v___x_1064_; 
v_hash_1063_ = lean_ctor_get_uint64(v_x_1060_, sizeof(void*)*2);
v___x_1064_ = lean_uint64_mix_hash(v___x_1061_, v_hash_1063_);
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object* v_x_1065_){
_start:
{
uint64_t v_res_1066_; lean_object* v_r_1067_; 
v_res_1066_ = l_Lean_instHashableMVarId_hash(v_x_1065_);
lean_dec(v_x_1065_);
v_r_1067_ = lean_box_uint64(v_res_1066_);
return v_r_1067_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_box(1);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet(void){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_box(1);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_box(1);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet(void){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_box(1);
return v___x_1074_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object* v_k_1075_, lean_object* v_t_1076_){
_start:
{
if (lean_obj_tag(v_t_1076_) == 0)
{
lean_object* v_k_1077_; lean_object* v_l_1078_; lean_object* v_r_1079_; uint8_t v___x_1080_; 
v_k_1077_ = lean_ctor_get(v_t_1076_, 1);
v_l_1078_ = lean_ctor_get(v_t_1076_, 3);
v_r_1079_ = lean_ctor_get(v_t_1076_, 4);
v___x_1080_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1075_, v_k_1077_);
switch(v___x_1080_)
{
case 0:
{
v_t_1076_ = v_l_1078_;
goto _start;
}
case 1:
{
uint8_t v___x_1082_; 
v___x_1082_ = 1;
return v___x_1082_;
}
default: 
{
v_t_1076_ = v_r_1079_;
goto _start;
}
}
}
else
{
uint8_t v___x_1084_; 
v___x_1084_ = 0;
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object* v_k_1085_, lean_object* v_t_1086_){
_start:
{
uint8_t v_res_1087_; lean_object* v_r_1088_; 
v_res_1087_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1085_, v_t_1086_);
lean_dec(v_t_1086_);
lean_dec(v_k_1085_);
v_r_1088_ = lean_box(v_res_1087_);
return v_r_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object* v_k_1089_, lean_object* v_v_1090_, lean_object* v_t_1091_){
_start:
{
if (lean_obj_tag(v_t_1091_) == 0)
{
lean_object* v_size_1092_; lean_object* v_k_1093_; lean_object* v_v_1094_; lean_object* v_l_1095_; lean_object* v_r_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1376_; 
v_size_1092_ = lean_ctor_get(v_t_1091_, 0);
v_k_1093_ = lean_ctor_get(v_t_1091_, 1);
v_v_1094_ = lean_ctor_get(v_t_1091_, 2);
v_l_1095_ = lean_ctor_get(v_t_1091_, 3);
v_r_1096_ = lean_ctor_get(v_t_1091_, 4);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_t_1091_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1098_ = v_t_1091_;
v_isShared_1099_ = v_isSharedCheck_1376_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_r_1096_);
lean_inc(v_l_1095_);
lean_inc(v_v_1094_);
lean_inc(v_k_1093_);
lean_inc(v_size_1092_);
lean_dec(v_t_1091_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1376_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
uint8_t v___x_1100_; 
v___x_1100_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1089_, v_k_1093_);
switch(v___x_1100_)
{
case 0:
{
lean_object* v_impl_1101_; lean_object* v___x_1102_; 
lean_dec(v_size_1092_);
v_impl_1101_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1089_, v_v_1090_, v_l_1095_);
v___x_1102_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1096_) == 0)
{
lean_object* v_size_1103_; lean_object* v_size_1104_; lean_object* v_k_1105_; lean_object* v_v_1106_; lean_object* v_l_1107_; lean_object* v_r_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v_size_1103_ = lean_ctor_get(v_r_1096_, 0);
v_size_1104_ = lean_ctor_get(v_impl_1101_, 0);
lean_inc(v_size_1104_);
v_k_1105_ = lean_ctor_get(v_impl_1101_, 1);
lean_inc(v_k_1105_);
v_v_1106_ = lean_ctor_get(v_impl_1101_, 2);
lean_inc(v_v_1106_);
v_l_1107_ = lean_ctor_get(v_impl_1101_, 3);
lean_inc(v_l_1107_);
v_r_1108_ = lean_ctor_get(v_impl_1101_, 4);
lean_inc(v_r_1108_);
v___x_1109_ = lean_unsigned_to_nat(3u);
v___x_1110_ = lean_nat_mul(v___x_1109_, v_size_1103_);
v___x_1111_ = lean_nat_dec_lt(v___x_1110_, v_size_1104_);
lean_dec(v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
lean_dec(v_r_1108_);
lean_dec(v_l_1107_);
lean_dec(v_v_1106_);
lean_dec(v_k_1105_);
v___x_1112_ = lean_nat_add(v___x_1102_, v_size_1104_);
lean_dec(v_size_1104_);
v___x_1113_ = lean_nat_add(v___x_1112_, v_size_1103_);
lean_dec(v___x_1112_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 3, v_impl_1101_);
lean_ctor_set(v___x_1098_, 0, v___x_1113_);
v___x_1115_ = v___x_1098_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_k_1093_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_v_1094_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v_impl_1101_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v_r_1096_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
else
{
lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1182_; 
v_isSharedCheck_1182_ = !lean_is_exclusive(v_impl_1101_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; lean_object* v_unused_1184_; lean_object* v_unused_1185_; lean_object* v_unused_1186_; lean_object* v_unused_1187_; 
v_unused_1183_ = lean_ctor_get(v_impl_1101_, 4);
lean_dec(v_unused_1183_);
v_unused_1184_ = lean_ctor_get(v_impl_1101_, 3);
lean_dec(v_unused_1184_);
v_unused_1185_ = lean_ctor_get(v_impl_1101_, 2);
lean_dec(v_unused_1185_);
v_unused_1186_ = lean_ctor_get(v_impl_1101_, 1);
lean_dec(v_unused_1186_);
v_unused_1187_ = lean_ctor_get(v_impl_1101_, 0);
lean_dec(v_unused_1187_);
v___x_1118_ = v_impl_1101_;
v_isShared_1119_ = v_isSharedCheck_1182_;
goto v_resetjp_1117_;
}
else
{
lean_dec(v_impl_1101_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1182_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v_size_1120_; lean_object* v_size_1121_; lean_object* v_k_1122_; lean_object* v_v_1123_; lean_object* v_l_1124_; lean_object* v_r_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v_size_1120_ = lean_ctor_get(v_l_1107_, 0);
v_size_1121_ = lean_ctor_get(v_r_1108_, 0);
v_k_1122_ = lean_ctor_get(v_r_1108_, 1);
v_v_1123_ = lean_ctor_get(v_r_1108_, 2);
v_l_1124_ = lean_ctor_get(v_r_1108_, 3);
v_r_1125_ = lean_ctor_get(v_r_1108_, 4);
v___x_1126_ = lean_unsigned_to_nat(2u);
v___x_1127_ = lean_nat_mul(v___x_1126_, v_size_1120_);
v___x_1128_ = lean_nat_dec_lt(v_size_1121_, v___x_1127_);
lean_dec(v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1157_; 
lean_inc(v_r_1125_);
lean_inc(v_l_1124_);
lean_inc(v_v_1123_);
lean_inc(v_k_1122_);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_r_1108_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; lean_object* v_unused_1159_; lean_object* v_unused_1160_; lean_object* v_unused_1161_; lean_object* v_unused_1162_; 
v_unused_1158_ = lean_ctor_get(v_r_1108_, 4);
lean_dec(v_unused_1158_);
v_unused_1159_ = lean_ctor_get(v_r_1108_, 3);
lean_dec(v_unused_1159_);
v_unused_1160_ = lean_ctor_get(v_r_1108_, 2);
lean_dec(v_unused_1160_);
v_unused_1161_ = lean_ctor_get(v_r_1108_, 1);
lean_dec(v_unused_1161_);
v_unused_1162_ = lean_ctor_get(v_r_1108_, 0);
lean_dec(v_unused_1162_);
v___x_1130_ = v_r_1108_;
v_isShared_1131_ = v_isSharedCheck_1157_;
goto v_resetjp_1129_;
}
else
{
lean_dec(v_r_1108_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1157_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___x_1145_; lean_object* v___y_1147_; 
v___x_1132_ = lean_nat_add(v___x_1102_, v_size_1104_);
lean_dec(v_size_1104_);
v___x_1133_ = lean_nat_add(v___x_1132_, v_size_1103_);
lean_dec(v___x_1132_);
v___x_1145_ = lean_nat_add(v___x_1102_, v_size_1120_);
if (lean_obj_tag(v_l_1124_) == 0)
{
lean_object* v_size_1155_; 
v_size_1155_ = lean_ctor_get(v_l_1124_, 0);
lean_inc(v_size_1155_);
v___y_1147_ = v_size_1155_;
goto v___jp_1146_;
}
else
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_unsigned_to_nat(0u);
v___y_1147_ = v___x_1156_;
goto v___jp_1146_;
}
v___jp_1134_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_nat_add(v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec(v___y_1136_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 4, v_r_1096_);
lean_ctor_set(v___x_1130_, 3, v_r_1125_);
lean_ctor_set(v___x_1130_, 2, v_v_1094_);
lean_ctor_set(v___x_1130_, 1, v_k_1093_);
lean_ctor_set(v___x_1130_, 0, v___x_1138_);
v___x_1140_ = v___x_1130_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_k_1093_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_v_1094_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_r_1125_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_r_1096_);
v___x_1140_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 4, v___x_1140_);
lean_ctor_set(v___x_1118_, 3, v___y_1135_);
lean_ctor_set(v___x_1118_, 2, v_v_1123_);
lean_ctor_set(v___x_1118_, 1, v_k_1122_);
lean_ctor_set(v___x_1118_, 0, v___x_1133_);
v___x_1142_ = v___x_1118_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_k_1122_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_v_1123_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v___y_1135_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
v___jp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = lean_nat_add(v___x_1145_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec(v___x_1145_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v_l_1124_);
lean_ctor_set(v___x_1098_, 3, v_l_1107_);
lean_ctor_set(v___x_1098_, 2, v_v_1106_);
lean_ctor_set(v___x_1098_, 1, v_k_1105_);
lean_ctor_set(v___x_1098_, 0, v___x_1148_);
v___x_1150_ = v___x_1098_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_k_1105_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_v_1106_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v_l_1107_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v_l_1124_);
v___x_1150_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_nat_add(v___x_1102_, v_size_1103_);
if (lean_obj_tag(v_r_1125_) == 0)
{
lean_object* v_size_1152_; 
v_size_1152_ = lean_ctor_get(v_r_1125_, 0);
lean_inc(v_size_1152_);
v___y_1135_ = v___x_1150_;
v___y_1136_ = v___x_1151_;
v___y_1137_ = v_size_1152_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_unsigned_to_nat(0u);
v___y_1135_ = v___x_1150_;
v___y_1136_ = v___x_1151_;
v___y_1137_ = v___x_1153_;
goto v___jp_1134_;
}
}
}
}
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
lean_del_object(v___x_1098_);
v___x_1163_ = lean_nat_add(v___x_1102_, v_size_1104_);
lean_dec(v_size_1104_);
v___x_1164_ = lean_nat_add(v___x_1163_, v_size_1103_);
lean_dec(v___x_1163_);
v___x_1165_ = lean_nat_add(v___x_1102_, v_size_1103_);
v___x_1166_ = lean_nat_add(v___x_1165_, v_size_1121_);
lean_dec(v___x_1165_);
lean_inc_ref(v_r_1096_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 4, v_r_1096_);
lean_ctor_set(v___x_1118_, 3, v_r_1108_);
lean_ctor_set(v___x_1118_, 2, v_v_1094_);
lean_ctor_set(v___x_1118_, 1, v_k_1093_);
lean_ctor_set(v___x_1118_, 0, v___x_1166_);
v___x_1168_ = v___x_1118_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_k_1093_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_v_1094_);
lean_ctor_set(v_reuseFailAlloc_1181_, 3, v_r_1108_);
lean_ctor_set(v_reuseFailAlloc_1181_, 4, v_r_1096_);
v___x_1168_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
v_isSharedCheck_1175_ = !lean_is_exclusive(v_r_1096_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; lean_object* v_unused_1177_; lean_object* v_unused_1178_; lean_object* v_unused_1179_; lean_object* v_unused_1180_; 
v_unused_1176_ = lean_ctor_get(v_r_1096_, 4);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_r_1096_, 3);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_r_1096_, 2);
lean_dec(v_unused_1178_);
v_unused_1179_ = lean_ctor_get(v_r_1096_, 1);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_r_1096_, 0);
lean_dec(v_unused_1180_);
v___x_1170_ = v_r_1096_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_dec(v_r_1096_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 4, v___x_1168_);
lean_ctor_set(v___x_1170_, 3, v_l_1107_);
lean_ctor_set(v___x_1170_, 2, v_v_1106_);
lean_ctor_set(v___x_1170_, 1, v_k_1105_);
lean_ctor_set(v___x_1170_, 0, v___x_1164_);
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_k_1105_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v_v_1106_);
lean_ctor_set(v_reuseFailAlloc_1174_, 3, v_l_1107_);
lean_ctor_set(v_reuseFailAlloc_1174_, 4, v___x_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1188_; 
v_l_1188_ = lean_ctor_get(v_impl_1101_, 3);
lean_inc(v_l_1188_);
if (lean_obj_tag(v_l_1188_) == 0)
{
lean_object* v_r_1189_; lean_object* v_k_1190_; lean_object* v_v_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1202_; 
v_r_1189_ = lean_ctor_get(v_impl_1101_, 4);
v_k_1190_ = lean_ctor_get(v_impl_1101_, 1);
v_v_1191_ = lean_ctor_get(v_impl_1101_, 2);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_impl_1101_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; lean_object* v_unused_1204_; 
v_unused_1203_ = lean_ctor_get(v_impl_1101_, 3);
lean_dec(v_unused_1203_);
v_unused_1204_ = lean_ctor_get(v_impl_1101_, 0);
lean_dec(v_unused_1204_);
v___x_1193_ = v_impl_1101_;
v_isShared_1194_ = v_isSharedCheck_1202_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_r_1189_);
lean_inc(v_v_1191_);
lean_inc(v_k_1190_);
lean_dec(v_impl_1101_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1202_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1189_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 3, v_r_1189_);
lean_ctor_set(v___x_1193_, 2, v_v_1094_);
lean_ctor_set(v___x_1193_, 1, v_k_1093_);
lean_ctor_set(v___x_1193_, 0, v___x_1102_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_k_1093_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_v_1094_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v_r_1189_);
lean_ctor_set(v_reuseFailAlloc_1201_, 4, v_r_1189_);
v___x_1197_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v___x_1197_);
lean_ctor_set(v___x_1098_, 3, v_l_1188_);
lean_ctor_set(v___x_1098_, 2, v_v_1191_);
lean_ctor_set(v___x_1098_, 1, v_k_1190_);
lean_ctor_set(v___x_1098_, 0, v___x_1195_);
v___x_1199_ = v___x_1098_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_k_1190_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_v_1191_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_l_1188_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
lean_object* v_r_1205_; 
v_r_1205_ = lean_ctor_get(v_impl_1101_, 4);
lean_inc(v_r_1205_);
if (lean_obj_tag(v_r_1205_) == 0)
{
lean_object* v_k_1206_; lean_object* v_v_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1230_; 
v_k_1206_ = lean_ctor_get(v_impl_1101_, 1);
v_v_1207_ = lean_ctor_get(v_impl_1101_, 2);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_impl_1101_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; lean_object* v_unused_1232_; lean_object* v_unused_1233_; 
v_unused_1231_ = lean_ctor_get(v_impl_1101_, 4);
lean_dec(v_unused_1231_);
v_unused_1232_ = lean_ctor_get(v_impl_1101_, 3);
lean_dec(v_unused_1232_);
v_unused_1233_ = lean_ctor_get(v_impl_1101_, 0);
lean_dec(v_unused_1233_);
v___x_1209_ = v_impl_1101_;
v_isShared_1210_ = v_isSharedCheck_1230_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_v_1207_);
lean_inc(v_k_1206_);
lean_dec(v_impl_1101_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1230_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v_k_1211_; lean_object* v_v_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1226_; 
v_k_1211_ = lean_ctor_get(v_r_1205_, 1);
v_v_1212_ = lean_ctor_get(v_r_1205_, 2);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_r_1205_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; lean_object* v_unused_1228_; lean_object* v_unused_1229_; 
v_unused_1227_ = lean_ctor_get(v_r_1205_, 4);
lean_dec(v_unused_1227_);
v_unused_1228_ = lean_ctor_get(v_r_1205_, 3);
lean_dec(v_unused_1228_);
v_unused_1229_ = lean_ctor_get(v_r_1205_, 0);
lean_dec(v_unused_1229_);
v___x_1214_ = v_r_1205_;
v_isShared_1215_ = v_isSharedCheck_1226_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_v_1212_);
lean_inc(v_k_1211_);
lean_dec(v_r_1205_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1226_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = lean_unsigned_to_nat(3u);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 4, v_l_1188_);
lean_ctor_set(v___x_1214_, 3, v_l_1188_);
lean_ctor_set(v___x_1214_, 2, v_v_1207_);
lean_ctor_set(v___x_1214_, 1, v_k_1206_);
lean_ctor_set(v___x_1214_, 0, v___x_1102_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_k_1206_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_v_1207_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_l_1188_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_l_1188_);
v___x_1218_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1220_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 4, v_l_1188_);
lean_ctor_set(v___x_1209_, 2, v_v_1094_);
lean_ctor_set(v___x_1209_, 1, v_k_1093_);
lean_ctor_set(v___x_1209_, 0, v___x_1102_);
v___x_1220_ = v___x_1209_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_k_1093_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_v_1094_);
lean_ctor_set(v_reuseFailAlloc_1224_, 3, v_l_1188_);
lean_ctor_set(v_reuseFailAlloc_1224_, 4, v_l_1188_);
v___x_1220_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1222_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v___x_1220_);
lean_ctor_set(v___x_1098_, 3, v___x_1218_);
lean_ctor_set(v___x_1098_, 2, v_v_1212_);
lean_ctor_set(v___x_1098_, 1, v_k_1211_);
lean_ctor_set(v___x_1098_, 0, v___x_1216_);
v___x_1222_ = v___x_1098_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_k_1211_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_v_1212_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1223_, 4, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1234_ = lean_unsigned_to_nat(2u);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v_r_1205_);
lean_ctor_set(v___x_1098_, 3, v_impl_1101_);
lean_ctor_set(v___x_1098_, 0, v___x_1234_);
v___x_1236_ = v___x_1098_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_k_1093_);
lean_ctor_set(v_reuseFailAlloc_1237_, 2, v_v_1094_);
lean_ctor_set(v_reuseFailAlloc_1237_, 3, v_impl_1101_);
lean_ctor_set(v_reuseFailAlloc_1237_, 4, v_r_1205_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1239_; 
lean_dec(v_v_1094_);
lean_dec(v_k_1093_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 2, v_v_1090_);
lean_ctor_set(v___x_1098_, 1, v_k_1089_);
v___x_1239_ = v___x_1098_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_size_1092_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_k_1089_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_v_1090_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_l_1095_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_r_1096_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
default: 
{
lean_object* v_impl_1241_; lean_object* v___x_1242_; 
lean_dec(v_size_1092_);
v_impl_1241_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1089_, v_v_1090_, v_r_1096_);
v___x_1242_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1095_) == 0)
{
lean_object* v_size_1243_; lean_object* v_size_1244_; lean_object* v_k_1245_; lean_object* v_v_1246_; lean_object* v_l_1247_; lean_object* v_r_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_size_1243_ = lean_ctor_get(v_l_1095_, 0);
v_size_1244_ = lean_ctor_get(v_impl_1241_, 0);
lean_inc(v_size_1244_);
v_k_1245_ = lean_ctor_get(v_impl_1241_, 1);
lean_inc(v_k_1245_);
v_v_1246_ = lean_ctor_get(v_impl_1241_, 2);
lean_inc(v_v_1246_);
v_l_1247_ = lean_ctor_get(v_impl_1241_, 3);
lean_inc(v_l_1247_);
v_r_1248_ = lean_ctor_get(v_impl_1241_, 4);
lean_inc(v_r_1248_);
v___x_1249_ = lean_unsigned_to_nat(3u);
v___x_1250_ = lean_nat_mul(v___x_1249_, v_size_1243_);
v___x_1251_ = lean_nat_dec_lt(v___x_1250_, v_size_1244_);
lean_dec(v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
lean_dec(v_r_1248_);
lean_dec(v_l_1247_);
lean_dec(v_v_1246_);
lean_dec(v_k_1245_);
v___x_1252_ = lean_nat_add(v___x_1242_, v_size_1243_);
v___x_1253_ = lean_nat_add(v___x_1252_, v_size_1244_);
lean_dec(v_size_1244_);
lean_dec(v___x_1252_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v_impl_1241_);
lean_ctor_set(v___x_1098_, 0, v___x_1253_);
v___x_1255_ = v___x_1098_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_k_1093_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v_v_1094_);
lean_ctor_set(v_reuseFailAlloc_1256_, 3, v_l_1095_);
lean_ctor_set(v_reuseFailAlloc_1256_, 4, v_impl_1241_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
else
{
lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1320_; 
v_isSharedCheck_1320_ = !lean_is_exclusive(v_impl_1241_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; lean_object* v_unused_1322_; lean_object* v_unused_1323_; lean_object* v_unused_1324_; lean_object* v_unused_1325_; 
v_unused_1321_ = lean_ctor_get(v_impl_1241_, 4);
lean_dec(v_unused_1321_);
v_unused_1322_ = lean_ctor_get(v_impl_1241_, 3);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v_impl_1241_, 2);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v_impl_1241_, 1);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v_impl_1241_, 0);
lean_dec(v_unused_1325_);
v___x_1258_ = v_impl_1241_;
v_isShared_1259_ = v_isSharedCheck_1320_;
goto v_resetjp_1257_;
}
else
{
lean_dec(v_impl_1241_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1320_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v_size_1260_; lean_object* v_k_1261_; lean_object* v_v_1262_; lean_object* v_l_1263_; lean_object* v_r_1264_; lean_object* v_size_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_size_1260_ = lean_ctor_get(v_l_1247_, 0);
v_k_1261_ = lean_ctor_get(v_l_1247_, 1);
v_v_1262_ = lean_ctor_get(v_l_1247_, 2);
v_l_1263_ = lean_ctor_get(v_l_1247_, 3);
v_r_1264_ = lean_ctor_get(v_l_1247_, 4);
v_size_1265_ = lean_ctor_get(v_r_1248_, 0);
v___x_1266_ = lean_unsigned_to_nat(2u);
v___x_1267_ = lean_nat_mul(v___x_1266_, v_size_1265_);
v___x_1268_ = lean_nat_dec_lt(v_size_1260_, v___x_1267_);
lean_dec(v___x_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1296_; 
lean_inc(v_r_1264_);
lean_inc(v_l_1263_);
lean_inc(v_v_1262_);
lean_inc(v_k_1261_);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_l_1247_);
if (v_isSharedCheck_1296_ == 0)
{
lean_object* v_unused_1297_; lean_object* v_unused_1298_; lean_object* v_unused_1299_; lean_object* v_unused_1300_; lean_object* v_unused_1301_; 
v_unused_1297_ = lean_ctor_get(v_l_1247_, 4);
lean_dec(v_unused_1297_);
v_unused_1298_ = lean_ctor_get(v_l_1247_, 3);
lean_dec(v_unused_1298_);
v_unused_1299_ = lean_ctor_get(v_l_1247_, 2);
lean_dec(v_unused_1299_);
v_unused_1300_ = lean_ctor_get(v_l_1247_, 1);
lean_dec(v_unused_1300_);
v_unused_1301_ = lean_ctor_get(v_l_1247_, 0);
lean_dec(v_unused_1301_);
v___x_1270_ = v_l_1247_;
v_isShared_1271_ = v_isSharedCheck_1296_;
goto v_resetjp_1269_;
}
else
{
lean_dec(v_l_1247_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1296_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1286_; 
v___x_1272_ = lean_nat_add(v___x_1242_, v_size_1243_);
v___x_1273_ = lean_nat_add(v___x_1272_, v_size_1244_);
lean_dec(v_size_1244_);
if (lean_obj_tag(v_l_1263_) == 0)
{
lean_object* v_size_1294_; 
v_size_1294_ = lean_ctor_get(v_l_1263_, 0);
lean_inc(v_size_1294_);
v___y_1286_ = v_size_1294_;
goto v___jp_1285_;
}
else
{
lean_object* v___x_1295_; 
v___x_1295_ = lean_unsigned_to_nat(0u);
v___y_1286_ = v___x_1295_;
goto v___jp_1285_;
}
v___jp_1274_:
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1278_ = lean_nat_add(v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 4, v_r_1248_);
lean_ctor_set(v___x_1270_, 3, v_r_1264_);
lean_ctor_set(v___x_1270_, 2, v_v_1246_);
lean_ctor_set(v___x_1270_, 1, v_k_1245_);
lean_ctor_set(v___x_1270_, 0, v___x_1278_);
v___x_1280_ = v___x_1270_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_v_1246_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_r_1264_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_r_1248_);
v___x_1280_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1282_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 4, v___x_1280_);
lean_ctor_set(v___x_1258_, 3, v___y_1275_);
lean_ctor_set(v___x_1258_, 2, v_v_1262_);
lean_ctor_set(v___x_1258_, 1, v_k_1261_);
lean_ctor_set(v___x_1258_, 0, v___x_1273_);
v___x_1282_ = v___x_1258_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1283_, 3, v___y_1275_);
lean_ctor_set(v_reuseFailAlloc_1283_, 4, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
v___jp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = lean_nat_add(v___x_1272_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec(v___x_1272_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v_l_1263_);
lean_ctor_set(v___x_1098_, 0, v___x_1287_);
v___x_1289_ = v___x_1098_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_k_1093_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_v_1094_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v_l_1095_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v_l_1263_);
v___x_1289_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_nat_add(v___x_1242_, v_size_1265_);
if (lean_obj_tag(v_r_1264_) == 0)
{
lean_object* v_size_1291_; 
v_size_1291_ = lean_ctor_get(v_r_1264_, 0);
lean_inc(v_size_1291_);
v___y_1275_ = v___x_1289_;
v___y_1276_ = v___x_1290_;
v___y_1277_ = v_size_1291_;
goto v___jp_1274_;
}
else
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_unsigned_to_nat(0u);
v___y_1275_ = v___x_1289_;
v___y_1276_ = v___x_1290_;
v___y_1277_ = v___x_1292_;
goto v___jp_1274_;
}
}
}
}
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
lean_del_object(v___x_1098_);
v___x_1302_ = lean_nat_add(v___x_1242_, v_size_1243_);
v___x_1303_ = lean_nat_add(v___x_1302_, v_size_1244_);
lean_dec(v_size_1244_);
v___x_1304_ = lean_nat_add(v___x_1302_, v_size_1260_);
lean_dec(v___x_1302_);
lean_inc_ref(v_l_1095_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 4, v_l_1247_);
lean_ctor_set(v___x_1258_, 3, v_l_1095_);
lean_ctor_set(v___x_1258_, 2, v_v_1094_);
lean_ctor_set(v___x_1258_, 1, v_k_1093_);
lean_ctor_set(v___x_1258_, 0, v___x_1304_);
v___x_1306_ = v___x_1258_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_k_1093_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_v_1094_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_l_1095_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_l_1247_);
v___x_1306_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
v_isSharedCheck_1313_ = !lean_is_exclusive(v_l_1095_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; lean_object* v_unused_1315_; lean_object* v_unused_1316_; lean_object* v_unused_1317_; lean_object* v_unused_1318_; 
v_unused_1314_ = lean_ctor_get(v_l_1095_, 4);
lean_dec(v_unused_1314_);
v_unused_1315_ = lean_ctor_get(v_l_1095_, 3);
lean_dec(v_unused_1315_);
v_unused_1316_ = lean_ctor_get(v_l_1095_, 2);
lean_dec(v_unused_1316_);
v_unused_1317_ = lean_ctor_get(v_l_1095_, 1);
lean_dec(v_unused_1317_);
v_unused_1318_ = lean_ctor_get(v_l_1095_, 0);
lean_dec(v_unused_1318_);
v___x_1308_ = v_l_1095_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_dec(v_l_1095_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 4, v_r_1248_);
lean_ctor_set(v___x_1308_, 3, v___x_1306_);
lean_ctor_set(v___x_1308_, 2, v_v_1246_);
lean_ctor_set(v___x_1308_, 1, v_k_1245_);
lean_ctor_set(v___x_1308_, 0, v___x_1303_);
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1312_, 2, v_v_1246_);
lean_ctor_set(v_reuseFailAlloc_1312_, 3, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1312_, 4, v_r_1248_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1326_; 
v_l_1326_ = lean_ctor_get(v_impl_1241_, 3);
lean_inc(v_l_1326_);
if (lean_obj_tag(v_l_1326_) == 0)
{
lean_object* v_r_1327_; lean_object* v_k_1328_; lean_object* v_v_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1352_; 
v_r_1327_ = lean_ctor_get(v_impl_1241_, 4);
v_k_1328_ = lean_ctor_get(v_impl_1241_, 1);
v_v_1329_ = lean_ctor_get(v_impl_1241_, 2);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_impl_1241_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; lean_object* v_unused_1354_; 
v_unused_1353_ = lean_ctor_get(v_impl_1241_, 3);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_impl_1241_, 0);
lean_dec(v_unused_1354_);
v___x_1331_ = v_impl_1241_;
v_isShared_1332_ = v_isSharedCheck_1352_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_r_1327_);
lean_inc(v_v_1329_);
lean_inc(v_k_1328_);
lean_dec(v_impl_1241_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1352_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v_k_1333_; lean_object* v_v_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1348_; 
v_k_1333_ = lean_ctor_get(v_l_1326_, 1);
v_v_1334_ = lean_ctor_get(v_l_1326_, 2);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_l_1326_);
if (v_isSharedCheck_1348_ == 0)
{
lean_object* v_unused_1349_; lean_object* v_unused_1350_; lean_object* v_unused_1351_; 
v_unused_1349_ = lean_ctor_get(v_l_1326_, 4);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v_l_1326_, 3);
lean_dec(v_unused_1350_);
v_unused_1351_ = lean_ctor_get(v_l_1326_, 0);
lean_dec(v_unused_1351_);
v___x_1336_ = v_l_1326_;
v_isShared_1337_ = v_isSharedCheck_1348_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_v_1334_);
lean_inc(v_k_1333_);
lean_dec(v_l_1326_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1348_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1338_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1327_, 2);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 4, v_r_1327_);
lean_ctor_set(v___x_1336_, 3, v_r_1327_);
lean_ctor_set(v___x_1336_, 2, v_v_1094_);
lean_ctor_set(v___x_1336_, 1, v_k_1093_);
lean_ctor_set(v___x_1336_, 0, v___x_1242_);
v___x_1340_ = v___x_1336_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_k_1093_);
lean_ctor_set(v_reuseFailAlloc_1347_, 2, v_v_1094_);
lean_ctor_set(v_reuseFailAlloc_1347_, 3, v_r_1327_);
lean_ctor_set(v_reuseFailAlloc_1347_, 4, v_r_1327_);
v___x_1340_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1342_; 
lean_inc(v_r_1327_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 3, v_r_1327_);
lean_ctor_set(v___x_1331_, 0, v___x_1242_);
v___x_1342_ = v___x_1331_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_k_1328_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_v_1329_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_r_1327_);
lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_r_1327_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1344_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v___x_1342_);
lean_ctor_set(v___x_1098_, 3, v___x_1340_);
lean_ctor_set(v___x_1098_, 2, v_v_1334_);
lean_ctor_set(v___x_1098_, 1, v_k_1333_);
lean_ctor_set(v___x_1098_, 0, v___x_1338_);
v___x_1344_ = v___x_1098_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_k_1333_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_v_1334_);
lean_ctor_set(v_reuseFailAlloc_1345_, 3, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1345_, 4, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
}
else
{
lean_object* v_r_1355_; 
v_r_1355_ = lean_ctor_get(v_impl_1241_, 4);
lean_inc(v_r_1355_);
if (lean_obj_tag(v_r_1355_) == 0)
{
lean_object* v_k_1356_; lean_object* v_v_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1368_; 
v_k_1356_ = lean_ctor_get(v_impl_1241_, 1);
v_v_1357_ = lean_ctor_get(v_impl_1241_, 2);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_impl_1241_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; lean_object* v_unused_1370_; lean_object* v_unused_1371_; 
v_unused_1369_ = lean_ctor_get(v_impl_1241_, 4);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v_impl_1241_, 3);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_impl_1241_, 0);
lean_dec(v_unused_1371_);
v___x_1359_ = v_impl_1241_;
v_isShared_1360_ = v_isSharedCheck_1368_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_v_1357_);
lean_inc(v_k_1356_);
lean_dec(v_impl_1241_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1368_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1361_ = lean_unsigned_to_nat(3u);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 4, v_l_1326_);
lean_ctor_set(v___x_1359_, 2, v_v_1094_);
lean_ctor_set(v___x_1359_, 1, v_k_1093_);
lean_ctor_set(v___x_1359_, 0, v___x_1242_);
v___x_1363_ = v___x_1359_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_k_1093_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_v_1094_);
lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_l_1326_);
lean_ctor_set(v_reuseFailAlloc_1367_, 4, v_l_1326_);
v___x_1363_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v_r_1355_);
lean_ctor_set(v___x_1098_, 3, v___x_1363_);
lean_ctor_set(v___x_1098_, 2, v_v_1357_);
lean_ctor_set(v___x_1098_, 1, v_k_1356_);
lean_ctor_set(v___x_1098_, 0, v___x_1361_);
v___x_1365_ = v___x_1098_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1356_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1357_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_r_1355_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1372_ = lean_unsigned_to_nat(2u);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v_impl_1241_);
lean_ctor_set(v___x_1098_, 3, v_r_1355_);
lean_ctor_set(v___x_1098_, 0, v___x_1372_);
v___x_1374_ = v___x_1098_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_k_1093_);
lean_ctor_set(v_reuseFailAlloc_1375_, 2, v_v_1094_);
lean_ctor_set(v_reuseFailAlloc_1375_, 3, v_r_1355_);
lean_ctor_set(v_reuseFailAlloc_1375_, 4, v_impl_1241_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
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
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_unsigned_to_nat(1u);
v___x_1378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v_k_1089_);
lean_ctor_set(v___x_1378_, 2, v_v_1090_);
lean_ctor_set(v___x_1378_, 3, v_t_1091_);
lean_ctor_set(v___x_1378_, 4, v_t_1091_);
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object* v_s_1379_, lean_object* v_mvarId_1380_){
_start:
{
uint8_t v___x_1381_; 
v___x_1381_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_mvarId_1380_, v_s_1379_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1380_, v___x_1382_, v_s_1379_);
return v___x_1383_;
}
else
{
lean_dec(v_mvarId_1380_);
return v_s_1379_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object* v_00_u03b2_1384_, lean_object* v_k_1385_, lean_object* v_t_1386_){
_start:
{
uint8_t v___x_1387_; 
v___x_1387_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1385_, v_t_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object* v_00_u03b2_1388_, lean_object* v_k_1389_, lean_object* v_t_1390_){
_start:
{
uint8_t v_res_1391_; lean_object* v_r_1392_; 
v_res_1391_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(v_00_u03b2_1388_, v_k_1389_, v_t_1390_);
lean_dec(v_t_1390_);
lean_dec(v_k_1389_);
v_r_1392_ = lean_box(v_res_1391_);
return v_r_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object* v_00_u03b2_1393_, lean_object* v_k_1394_, lean_object* v_v_1395_, lean_object* v_t_1396_, lean_object* v_hl_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1394_, v_v_1395_, v_t_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object* v_l_1399_){
_start:
{
lean_object* v___f_1400_; lean_object* v___x_1401_; 
v___f_1400_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1401_ = l_Std_TreeSet_ofList___redArg(v_l_1399_, v___f_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList___boxed(lean_object* v_l_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_MVarIdSet_ofList(v_l_1402_);
lean_dec(v_l_1402_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object* v_l_1404_){
_start:
{
lean_object* v___f_1405_; lean_object* v___x_1406_; 
v___f_1405_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1406_ = l_Std_TreeSet_ofArray___redArg(v_l_1404_, v___f_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object* v_l_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_MVarIdSet_ofArray(v_l_1407_);
lean_dec_ref(v_l_1407_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1409_, lean_object* v_m_1410_, lean_object* v_init_1411_, lean_object* v_f_1412_){
_start:
{
lean_object* v_toApplicative_1413_; lean_object* v_toBind_1414_; lean_object* v_toPure_1415_; lean_object* v___f_1416_; lean_object* v___x_1417_; lean_object* v___f_1418_; lean_object* v___x_1419_; 
v_toApplicative_1413_ = lean_ctor_get(v_inst_1409_, 0);
v_toBind_1414_ = lean_ctor_get(v_inst_1409_, 1);
lean_inc(v_toBind_1414_);
v_toPure_1415_ = lean_ctor_get(v_toApplicative_1413_, 1);
lean_inc(v_toPure_1415_);
v___f_1416_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1416_, 0, v_f_1412_);
v___x_1417_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1409_, v___f_1416_, v_init_1411_, v_m_1410_);
v___f_1418_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1418_, 0, v_toPure_1415_);
v___x_1419_ = lean_apply_4(v_toBind_1414_, lean_box(0), lean_box(0), v___x_1417_, v___f_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1(lean_object* v_m_1420_, lean_object* v_inst_1421_, lean_object* v_00_u03b2_1422_, lean_object* v_m_1423_, lean_object* v_init_1424_, lean_object* v_f_1425_){
_start:
{
lean_object* v_toApplicative_1426_; lean_object* v_toBind_1427_; lean_object* v_toPure_1428_; lean_object* v___f_1429_; lean_object* v___x_1430_; lean_object* v___f_1431_; lean_object* v___x_1432_; 
v_toApplicative_1426_ = lean_ctor_get(v_inst_1421_, 0);
v_toBind_1427_ = lean_ctor_get(v_inst_1421_, 1);
lean_inc(v_toBind_1427_);
v_toPure_1428_ = lean_ctor_get(v_toApplicative_1426_, 1);
lean_inc(v_toPure_1428_);
v___f_1429_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1429_, 0, v_f_1425_);
v___x_1430_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1421_, v___f_1429_, v_init_1424_, v_m_1423_);
v___f_1431_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1431_, 0, v_toPure_1428_);
v___x_1432_ = lean_apply_4(v_toBind_1427_, lean_box(0), lean_box(0), v___x_1430_, v___f_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object* v_inst_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1434_, 0, lean_box(0));
lean_closure_set(v___x_1434_, 1, v_inst_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object* v_m_1435_, lean_object* v_inst_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1437_, 0, lean_box(0));
lean_closure_set(v___x_1437_, 1, v_inst_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object* v_s_1438_, lean_object* v_mvarId_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1439_, v_a_1440_, v_s_1438_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object* v_00_u03b1_1442_, lean_object* v_s_1443_, lean_object* v_mvarId_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1444_, v_a_1445_, v_s_1443_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object* v_00_u03b1_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_box(1);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* v_00_u03b1_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_box(1);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_1451_, lean_object* v_a_1452_, lean_object* v_b_1453_, lean_object* v_c_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v_a_1452_);
lean_ctor_set(v___x_1455_, 1, v_b_1453_);
v___x_1456_ = lean_apply_2(v_f_1451_, v___x_1455_, v_c_1454_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1457_, lean_object* v_m_1458_, lean_object* v_init_1459_, lean_object* v_f_1460_){
_start:
{
lean_object* v_toApplicative_1461_; lean_object* v_toBind_1462_; lean_object* v_toPure_1463_; lean_object* v___f_1464_; lean_object* v___x_1465_; lean_object* v___f_1466_; lean_object* v___x_1467_; 
v_toApplicative_1461_ = lean_ctor_get(v_inst_1457_, 0);
v_toBind_1462_ = lean_ctor_get(v_inst_1457_, 1);
lean_inc(v_toBind_1462_);
v_toPure_1463_ = lean_ctor_get(v_toApplicative_1461_, 1);
lean_inc(v_toPure_1463_);
v___f_1464_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1464_, 0, v_f_1460_);
v___x_1465_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1457_, v___f_1464_, v_init_1459_, v_m_1458_);
v___f_1466_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1466_, 0, v_toPure_1463_);
v___x_1467_ = lean_apply_4(v_toBind_1462_, lean_box(0), lean_box(0), v___x_1465_, v___f_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object* v_m_1468_, lean_object* v_00_u03b1_1469_, lean_object* v_inst_1470_, lean_object* v_00_u03b2_1471_, lean_object* v_m_1472_, lean_object* v_init_1473_, lean_object* v_f_1474_){
_start:
{
lean_object* v_toApplicative_1475_; lean_object* v_toBind_1476_; lean_object* v_toPure_1477_; lean_object* v___f_1478_; lean_object* v___x_1479_; lean_object* v___f_1480_; lean_object* v___x_1481_; 
v_toApplicative_1475_ = lean_ctor_get(v_inst_1470_, 0);
v_toBind_1476_ = lean_ctor_get(v_inst_1470_, 1);
lean_inc(v_toBind_1476_);
v_toPure_1477_ = lean_ctor_get(v_toApplicative_1475_, 1);
lean_inc(v_toPure_1477_);
v___f_1478_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1478_, 0, v_f_1474_);
v___x_1479_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1470_, v___f_1478_, v_init_1473_, v_m_1472_);
v___f_1480_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1480_, 0, v_toPure_1477_);
v___x_1481_ = lean_apply_4(v_toBind_1476_, lean_box(0), lean_box(0), v___x_1479_, v___f_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object* v_inst_1482_){
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
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object* v_m_1484_, lean_object* v_00_u03b1_1485_, lean_object* v_inst_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1487_, 0, lean_box(0));
lean_closure_set(v___x_1487_, 1, lean_box(0));
lean_closure_set(v___x_1487_, 2, v_inst_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* v_00_u03b1_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_box(1);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx(lean_object* v_x_1490_){
_start:
{
switch(lean_obj_tag(v_x_1490_))
{
case 0:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_unsigned_to_nat(0u);
return v___x_1491_;
}
case 1:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_unsigned_to_nat(1u);
return v___x_1492_;
}
case 2:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_unsigned_to_nat(2u);
return v___x_1493_;
}
case 3:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_unsigned_to_nat(3u);
return v___x_1494_;
}
case 4:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_unsigned_to_nat(4u);
return v___x_1495_;
}
case 5:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_unsigned_to_nat(5u);
return v___x_1496_;
}
case 6:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_unsigned_to_nat(6u);
return v___x_1497_;
}
case 7:
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_unsigned_to_nat(7u);
return v___x_1498_;
}
case 8:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_unsigned_to_nat(8u);
return v___x_1499_;
}
case 9:
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_unsigned_to_nat(9u);
return v___x_1500_;
}
case 10:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_unsigned_to_nat(10u);
return v___x_1501_;
}
default: 
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_unsigned_to_nat(11u);
return v___x_1502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___boxed(lean_object* v_x_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_Expr_ctorIdx(v_x_1503_);
lean_dec_ref(v_x_1503_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object* v_t_1505_, lean_object* v_k_1506_){
_start:
{
switch(lean_obj_tag(v_t_1505_))
{
case 4:
{
lean_object* v_declName_1507_; lean_object* v_us_1508_; lean_object* v___x_1509_; 
v_declName_1507_ = lean_ctor_get(v_t_1505_, 0);
lean_inc(v_declName_1507_);
v_us_1508_ = lean_ctor_get(v_t_1505_, 1);
lean_inc(v_us_1508_);
lean_dec_ref_known(v_t_1505_, 2);
v___x_1509_ = lean_apply_2(v_k_1506_, v_declName_1507_, v_us_1508_);
return v___x_1509_;
}
case 5:
{
lean_object* v_fn_1510_; lean_object* v_arg_1511_; lean_object* v___x_1512_; 
v_fn_1510_ = lean_ctor_get(v_t_1505_, 0);
lean_inc_ref(v_fn_1510_);
v_arg_1511_ = lean_ctor_get(v_t_1505_, 1);
lean_inc_ref(v_arg_1511_);
lean_dec_ref_known(v_t_1505_, 2);
v___x_1512_ = lean_apply_2(v_k_1506_, v_fn_1510_, v_arg_1511_);
return v___x_1512_;
}
case 6:
{
lean_object* v_binderName_1513_; lean_object* v_binderType_1514_; lean_object* v_body_1515_; uint8_t v_binderInfo_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v_binderName_1513_ = lean_ctor_get(v_t_1505_, 0);
lean_inc(v_binderName_1513_);
v_binderType_1514_ = lean_ctor_get(v_t_1505_, 1);
lean_inc_ref(v_binderType_1514_);
v_body_1515_ = lean_ctor_get(v_t_1505_, 2);
lean_inc_ref(v_body_1515_);
v_binderInfo_1516_ = lean_ctor_get_uint8(v_t_1505_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1505_, 3);
v___x_1517_ = lean_box(v_binderInfo_1516_);
v___x_1518_ = lean_apply_4(v_k_1506_, v_binderName_1513_, v_binderType_1514_, v_body_1515_, v___x_1517_);
return v___x_1518_;
}
case 7:
{
lean_object* v_binderName_1519_; lean_object* v_binderType_1520_; lean_object* v_body_1521_; uint8_t v_binderInfo_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_binderName_1519_ = lean_ctor_get(v_t_1505_, 0);
lean_inc(v_binderName_1519_);
v_binderType_1520_ = lean_ctor_get(v_t_1505_, 1);
lean_inc_ref(v_binderType_1520_);
v_body_1521_ = lean_ctor_get(v_t_1505_, 2);
lean_inc_ref(v_body_1521_);
v_binderInfo_1522_ = lean_ctor_get_uint8(v_t_1505_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1505_, 3);
v___x_1523_ = lean_box(v_binderInfo_1522_);
v___x_1524_ = lean_apply_4(v_k_1506_, v_binderName_1519_, v_binderType_1520_, v_body_1521_, v___x_1523_);
return v___x_1524_;
}
case 8:
{
lean_object* v_declName_1525_; lean_object* v_type_1526_; lean_object* v_value_1527_; lean_object* v_body_1528_; uint8_t v_nondep_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v_declName_1525_ = lean_ctor_get(v_t_1505_, 0);
lean_inc(v_declName_1525_);
v_type_1526_ = lean_ctor_get(v_t_1505_, 1);
lean_inc_ref(v_type_1526_);
v_value_1527_ = lean_ctor_get(v_t_1505_, 2);
lean_inc_ref(v_value_1527_);
v_body_1528_ = lean_ctor_get(v_t_1505_, 3);
lean_inc_ref(v_body_1528_);
v_nondep_1529_ = lean_ctor_get_uint8(v_t_1505_, sizeof(void*)*4);
lean_dec_ref_known(v_t_1505_, 4);
v___x_1530_ = lean_box(v_nondep_1529_);
v___x_1531_ = lean_apply_5(v_k_1506_, v_declName_1525_, v_type_1526_, v_value_1527_, v_body_1528_, v___x_1530_);
return v___x_1531_;
}
case 9:
{
lean_object* v_a_1532_; lean_object* v___x_1533_; 
v_a_1532_ = lean_ctor_get(v_t_1505_, 0);
lean_inc_ref(v_a_1532_);
lean_dec_ref_known(v_t_1505_, 1);
v___x_1533_ = lean_apply_1(v_k_1506_, v_a_1532_);
return v___x_1533_;
}
case 10:
{
lean_object* v_data_1534_; lean_object* v_expr_1535_; lean_object* v___x_1536_; 
v_data_1534_ = lean_ctor_get(v_t_1505_, 0);
lean_inc(v_data_1534_);
v_expr_1535_ = lean_ctor_get(v_t_1505_, 1);
lean_inc_ref(v_expr_1535_);
lean_dec_ref_known(v_t_1505_, 2);
v___x_1536_ = lean_apply_2(v_k_1506_, v_data_1534_, v_expr_1535_);
return v___x_1536_;
}
case 11:
{
lean_object* v_typeName_1537_; lean_object* v_idx_1538_; lean_object* v_struct_1539_; lean_object* v___x_1540_; 
v_typeName_1537_ = lean_ctor_get(v_t_1505_, 0);
lean_inc(v_typeName_1537_);
v_idx_1538_ = lean_ctor_get(v_t_1505_, 1);
lean_inc(v_idx_1538_);
v_struct_1539_ = lean_ctor_get(v_t_1505_, 2);
lean_inc_ref(v_struct_1539_);
lean_dec_ref_known(v_t_1505_, 3);
v___x_1540_ = lean_apply_3(v_k_1506_, v_typeName_1537_, v_idx_1538_, v_struct_1539_);
return v___x_1540_;
}
default: 
{
lean_object* v_deBruijnIndex_1541_; lean_object* v___x_1542_; 
v_deBruijnIndex_1541_ = lean_ctor_get(v_t_1505_, 0);
lean_inc(v_deBruijnIndex_1541_);
lean_dec_ref(v_t_1505_);
v___x_1542_ = lean_apply_1(v_k_1506_, v_deBruijnIndex_1541_);
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object* v_motive_1543_, lean_object* v_ctorIdx_1544_, lean_object* v_t_1545_, lean_object* v_h_1546_, lean_object* v_k_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_Expr_ctorElim___redArg(v_t_1545_, v_k_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object* v_motive_1549_, lean_object* v_ctorIdx_1550_, lean_object* v_t_1551_, lean_object* v_h_1552_, lean_object* v_k_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_Expr_ctorElim(v_motive_1549_, v_ctorIdx_1550_, v_t_1551_, v_h_1552_, v_k_1553_);
lean_dec(v_ctorIdx_1550_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object* v_t_1555_, lean_object* v_bvar_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Expr_ctorElim___redArg(v_t_1555_, v_bvar_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object* v_motive_1558_, lean_object* v_t_1559_, lean_object* v_h_1560_, lean_object* v_bvar_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Expr_ctorElim___redArg(v_t_1559_, v_bvar_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object* v_t_1563_, lean_object* v_fvar_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Expr_ctorElim___redArg(v_t_1563_, v_fvar_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object* v_motive_1566_, lean_object* v_t_1567_, lean_object* v_h_1568_, lean_object* v_fvar_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Expr_ctorElim___redArg(v_t_1567_, v_fvar_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object* v_t_1571_, lean_object* v_mvar_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Expr_ctorElim___redArg(v_t_1571_, v_mvar_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object* v_motive_1574_, lean_object* v_t_1575_, lean_object* v_h_1576_, lean_object* v_mvar_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Expr_ctorElim___redArg(v_t_1575_, v_mvar_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object* v_t_1579_, lean_object* v_sort_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Expr_ctorElim___redArg(v_t_1579_, v_sort_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object* v_motive_1582_, lean_object* v_t_1583_, lean_object* v_h_1584_, lean_object* v_sort_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Expr_ctorElim___redArg(v_t_1583_, v_sort_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object* v_t_1587_, lean_object* v_const_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Expr_ctorElim___redArg(v_t_1587_, v_const_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object* v_motive_1590_, lean_object* v_t_1591_, lean_object* v_h_1592_, lean_object* v_const_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Expr_ctorElim___redArg(v_t_1591_, v_const_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object* v_t_1595_, lean_object* v_app_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Expr_ctorElim___redArg(v_t_1595_, v_app_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object* v_motive_1598_, lean_object* v_t_1599_, lean_object* v_h_1600_, lean_object* v_app_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_Expr_ctorElim___redArg(v_t_1599_, v_app_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object* v_t_1603_, lean_object* v_lam_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_Expr_ctorElim___redArg(v_t_1603_, v_lam_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object* v_motive_1606_, lean_object* v_t_1607_, lean_object* v_h_1608_, lean_object* v_lam_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Expr_ctorElim___redArg(v_t_1607_, v_lam_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object* v_t_1611_, lean_object* v_forallE_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_Expr_ctorElim___redArg(v_t_1611_, v_forallE_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object* v_motive_1614_, lean_object* v_t_1615_, lean_object* v_h_1616_, lean_object* v_forallE_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_Expr_ctorElim___redArg(v_t_1615_, v_forallE_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object* v_t_1619_, lean_object* v_letE_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Expr_ctorElim___redArg(v_t_1619_, v_letE_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object* v_motive_1622_, lean_object* v_t_1623_, lean_object* v_h_1624_, lean_object* v_letE_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Expr_ctorElim___redArg(v_t_1623_, v_letE_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object* v_t_1627_, lean_object* v_lit_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_Expr_ctorElim___redArg(v_t_1627_, v_lit_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object* v_motive_1630_, lean_object* v_t_1631_, lean_object* v_h_1632_, lean_object* v_lit_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Expr_ctorElim___redArg(v_t_1631_, v_lit_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object* v_t_1635_, lean_object* v_mdata_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Expr_ctorElim___redArg(v_t_1635_, v_mdata_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object* v_motive_1638_, lean_object* v_t_1639_, lean_object* v_h_1640_, lean_object* v_mdata_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Expr_ctorElim___redArg(v_t_1639_, v_mdata_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object* v_t_1643_, lean_object* v_proj_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Expr_ctorElim___redArg(v_t_1643_, v_proj_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object* v_motive_1646_, lean_object* v_t_1647_, lean_object* v_h_1648_, lean_object* v_proj_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Expr_ctorElim___redArg(v_t_1647_, v_proj_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* v_a_00___x40___internal___hyg_1652_){
_start:
{
uint64_t v_res_1653_; lean_object* v_r_1654_; 
v_res_1653_ = lean_expr_data(v_a_00___x40___internal___hyg_1652_);
lean_dec_ref(v_a_00___x40___internal___hyg_1652_);
v_r_1654_ = lean_box_uint64(v_res_1653_);
return v_r_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object* v_t_1655_, lean_object* v_bvar_1656_, lean_object* v_fvar_1657_, lean_object* v_mvar_1658_, lean_object* v_sort_1659_, lean_object* v_const_1660_, lean_object* v_app_1661_, lean_object* v_lam_1662_, lean_object* v_forallE_1663_, lean_object* v_letE_1664_, lean_object* v_lit_1665_, lean_object* v_mdata_1666_, lean_object* v_proj_1667_){
_start:
{
switch(lean_obj_tag(v_t_1655_))
{
case 0:
{
lean_object* v_deBruijnIndex_1668_; lean_object* v___x_1669_; 
lean_dec(v_proj_1667_);
lean_dec(v_mdata_1666_);
lean_dec(v_lit_1665_);
lean_dec(v_letE_1664_);
lean_dec(v_forallE_1663_);
lean_dec(v_lam_1662_);
lean_dec(v_app_1661_);
lean_dec(v_const_1660_);
lean_dec(v_sort_1659_);
lean_dec(v_mvar_1658_);
lean_dec(v_fvar_1657_);
v_deBruijnIndex_1668_ = lean_ctor_get(v_t_1655_, 0);
lean_inc(v_deBruijnIndex_1668_);
lean_dec_ref_known(v_t_1655_, 1);
v___x_1669_ = lean_apply_1(v_bvar_1656_, v_deBruijnIndex_1668_);
return v___x_1669_;
}
case 1:
{
lean_object* v_fvarId_1670_; lean_object* v___x_1671_; 
lean_dec(v_proj_1667_);
lean_dec(v_mdata_1666_);
lean_dec(v_lit_1665_);
lean_dec(v_letE_1664_);
lean_dec(v_forallE_1663_);
lean_dec(v_lam_1662_);
lean_dec(v_app_1661_);
lean_dec(v_const_1660_);
lean_dec(v_sort_1659_);
lean_dec(v_mvar_1658_);
lean_dec(v_bvar_1656_);
v_fvarId_1670_ = lean_ctor_get(v_t_1655_, 0);
lean_inc(v_fvarId_1670_);
lean_dec_ref_known(v_t_1655_, 1);
v___x_1671_ = lean_apply_1(v_fvar_1657_, v_fvarId_1670_);
return v___x_1671_;
}
case 2:
{
lean_object* v_mvarId_1672_; lean_object* v___x_1673_; 
lean_dec(v_proj_1667_);
lean_dec(v_mdata_1666_);
lean_dec(v_lit_1665_);
lean_dec(v_letE_1664_);
lean_dec(v_forallE_1663_);
lean_dec(v_lam_1662_);
lean_dec(v_app_1661_);
lean_dec(v_const_1660_);
lean_dec(v_sort_1659_);
lean_dec(v_fvar_1657_);
lean_dec(v_bvar_1656_);
v_mvarId_1672_ = lean_ctor_get(v_t_1655_, 0);
lean_inc(v_mvarId_1672_);
lean_dec_ref_known(v_t_1655_, 1);
v___x_1673_ = lean_apply_1(v_mvar_1658_, v_mvarId_1672_);
return v___x_1673_;
}
case 3:
{
lean_object* v_u_1674_; lean_object* v___x_1675_; 
lean_dec(v_proj_1667_);
lean_dec(v_mdata_1666_);
lean_dec(v_lit_1665_);
lean_dec(v_letE_1664_);
lean_dec(v_forallE_1663_);
lean_dec(v_lam_1662_);
lean_dec(v_app_1661_);
lean_dec(v_const_1660_);
lean_dec(v_mvar_1658_);
lean_dec(v_fvar_1657_);
lean_dec(v_bvar_1656_);
v_u_1674_ = lean_ctor_get(v_t_1655_, 0);
lean_inc(v_u_1674_);
lean_dec_ref_known(v_t_1655_, 1);
v___x_1675_ = lean_apply_1(v_sort_1659_, v_u_1674_);
return v___x_1675_;
}
case 4:
{
lean_object* v_declName_1676_; lean_object* v_us_1677_; lean_object* v___x_1678_; 
lean_dec(v_proj_1667_);
lean_dec(v_mdata_1666_);
lean_dec(v_lit_1665_);
lean_dec(v_letE_1664_);
lean_dec(v_forallE_1663_);
lean_dec(v_lam_1662_);
lean_dec(v_app_1661_);
lean_dec(v_sort_1659_);
lean_dec(v_mvar_1658_);
lean_dec(v_fvar_1657_);
lean_dec(v_bvar_1656_);
v_declName_1676_ = lean_ctor_get(v_t_1655_, 0);
lean_inc(v_declName_1676_);
v_us_1677_ = lean_ctor_get(v_t_1655_, 1);
lean_inc(v_us_1677_);
lean_dec_ref_known(v_t_1655_, 2);
v___x_1678_ = lean_apply_2(v_const_1660_, v_declName_1676_, v_us_1677_);
return v___x_1678_;
}
case 5:
{
lean_object* v_fn_1679_; lean_object* v_arg_1680_; lean_object* v___x_1681_; 
lean_dec(v_proj_1667_);
lean_dec(v_mdata_1666_);
lean_dec(v_lit_1665_);
lean_dec(v_letE_1664_);
lean_dec(v_forallE_1663_);
lean_dec(v_lam_1662_);
lean_dec(v_const_1660_);
lean_dec(v_sort_1659_);
lean_dec(v_mvar_1658_);
lean_dec(v_fvar_1657_);
lean_dec(v_bvar_1656_);
v_fn_1679_ = lean_ctor_get(v_t_1655_, 0);
lean_inc_ref(v_fn_1679_);
v_arg_1680_ = lean_ctor_get(v_t_1655_, 1);
lean_inc_ref(v_arg_1680_);
lean_dec_ref_known(v_t_1655_, 2);
v___x_1681_ = lean_apply_2(v_app_1661_, v_fn_1679_, v_arg_1680_);
return v___x_1681_;
}
case 6:
{
lean_object* v_binderName_1682_; lean_object* v_binderType_1683_; lean_object* v_body_1684_; uint8_t v_binderInfo_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec(v_proj_1667_);
lean_dec(v_mdata_1666_);
lean_dec(v_lit_1665_);
lean_dec(v_letE_1664_);
lean_dec(v_forallE_1663_);
lean_dec(v_app_1661_);
lean_dec(v_const_1660_);
lean_dec(v_sort_1659_);
lean_dec(v_mvar_1658_);
lean_dec(v_fvar_1657_);
lean_dec(v_bvar_1656_);
v_binderName_1682_ = lean_ctor_get(v_t_1655_, 0);
lean_inc(v_binderName_1682_);
v_binderType_1683_ = lean_ctor_get(v_t_1655_, 1);
lean_inc_ref(v_binderType_1683_);
v_body_1684_ = lean_ctor_get(v_t_1655_, 2);
lean_inc_ref(v_body_1684_);
v_binderInfo_1685_ = lean_ctor_get_uint8(v_t_1655_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1655_, 3);
v___x_1686_ = lean_box(v_binderInfo_1685_);
v___x_1687_ = lean_apply_4(v_lam_1662_, v_binderName_1682_, v_binderType_1683_, v_body_1684_, v___x_1686_);
return v___x_1687_;
}
case 7:
{
lean_object* v_binderName_1688_; lean_object* v_binderType_1689_; lean_object* v_body_1690_; uint8_t v_binderInfo_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec(v_proj_1667_);
lean_dec(v_mdata_1666_);
lean_dec(v_lit_1665_);
lean_dec(v_letE_1664_);
lean_dec(v_lam_1662_);
lean_dec(v_app_1661_);
lean_dec(v_const_1660_);
lean_dec(v_sort_1659_);
lean_dec(v_mvar_1658_);
lean_dec(v_fvar_1657_);
lean_dec(v_bvar_1656_);
v_binderName_1688_ = lean_ctor_get(v_t_1655_, 0);
lean_inc(v_binderName_1688_);
v_binderType_1689_ = lean_ctor_get(v_t_1655_, 1);
lean_inc_ref(v_binderType_1689_);
v_body_1690_ = lean_ctor_get(v_t_1655_, 2);
lean_inc_ref(v_body_1690_);
v_binderInfo_1691_ = lean_ctor_get_uint8(v_t_1655_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1655_, 3);
v___x_1692_ = lean_box(v_binderInfo_1691_);
v___x_1693_ = lean_apply_4(v_forallE_1663_, v_binderName_1688_, v_binderType_1689_, v_body_1690_, v___x_1692_);
return v___x_1693_;
}
case 8:
{
lean_object* v_declName_1694_; lean_object* v_type_1695_; lean_object* v_value_1696_; lean_object* v_body_1697_; uint8_t v_nondep_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_dec(v_proj_1667_);
lean_dec(v_mdata_1666_);
lean_dec(v_lit_1665_);
lean_dec(v_forallE_1663_);
lean_dec(v_lam_1662_);
lean_dec(v_app_1661_);
lean_dec(v_const_1660_);
lean_dec(v_sort_1659_);
lean_dec(v_mvar_1658_);
lean_dec(v_fvar_1657_);
lean_dec(v_bvar_1656_);
v_declName_1694_ = lean_ctor_get(v_t_1655_, 0);
lean_inc(v_declName_1694_);
v_type_1695_ = lean_ctor_get(v_t_1655_, 1);
lean_inc_ref(v_type_1695_);
v_value_1696_ = lean_ctor_get(v_t_1655_, 2);
lean_inc_ref(v_value_1696_);
v_body_1697_ = lean_ctor_get(v_t_1655_, 3);
lean_inc_ref(v_body_1697_);
v_nondep_1698_ = lean_ctor_get_uint8(v_t_1655_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1655_, 4);
v___x_1699_ = lean_box(v_nondep_1698_);
v___x_1700_ = lean_apply_5(v_letE_1664_, v_declName_1694_, v_type_1695_, v_value_1696_, v_body_1697_, v___x_1699_);
return v___x_1700_;
}
case 9:
{
lean_object* v_a_1701_; lean_object* v___x_1702_; 
lean_dec(v_proj_1667_);
lean_dec(v_mdata_1666_);
lean_dec(v_letE_1664_);
lean_dec(v_forallE_1663_);
lean_dec(v_lam_1662_);
lean_dec(v_app_1661_);
lean_dec(v_const_1660_);
lean_dec(v_sort_1659_);
lean_dec(v_mvar_1658_);
lean_dec(v_fvar_1657_);
lean_dec(v_bvar_1656_);
v_a_1701_ = lean_ctor_get(v_t_1655_, 0);
lean_inc_ref(v_a_1701_);
lean_dec_ref_known(v_t_1655_, 1);
v___x_1702_ = lean_apply_1(v_lit_1665_, v_a_1701_);
return v___x_1702_;
}
case 10:
{
lean_object* v_data_1703_; lean_object* v_expr_1704_; lean_object* v___x_1705_; 
lean_dec(v_proj_1667_);
lean_dec(v_lit_1665_);
lean_dec(v_letE_1664_);
lean_dec(v_forallE_1663_);
lean_dec(v_lam_1662_);
lean_dec(v_app_1661_);
lean_dec(v_const_1660_);
lean_dec(v_sort_1659_);
lean_dec(v_mvar_1658_);
lean_dec(v_fvar_1657_);
lean_dec(v_bvar_1656_);
v_data_1703_ = lean_ctor_get(v_t_1655_, 0);
lean_inc(v_data_1703_);
v_expr_1704_ = lean_ctor_get(v_t_1655_, 1);
lean_inc_ref(v_expr_1704_);
lean_dec_ref_known(v_t_1655_, 2);
v___x_1705_ = lean_apply_2(v_mdata_1666_, v_data_1703_, v_expr_1704_);
return v___x_1705_;
}
default: 
{
lean_object* v_typeName_1706_; lean_object* v_idx_1707_; lean_object* v_struct_1708_; lean_object* v___x_1709_; 
lean_dec(v_mdata_1666_);
lean_dec(v_lit_1665_);
lean_dec(v_letE_1664_);
lean_dec(v_forallE_1663_);
lean_dec(v_lam_1662_);
lean_dec(v_app_1661_);
lean_dec(v_const_1660_);
lean_dec(v_sort_1659_);
lean_dec(v_mvar_1658_);
lean_dec(v_fvar_1657_);
lean_dec(v_bvar_1656_);
v_typeName_1706_ = lean_ctor_get(v_t_1655_, 0);
lean_inc(v_typeName_1706_);
v_idx_1707_ = lean_ctor_get(v_t_1655_, 1);
lean_inc(v_idx_1707_);
v_struct_1708_ = lean_ctor_get(v_t_1655_, 2);
lean_inc_ref(v_struct_1708_);
lean_dec_ref_known(v_t_1655_, 3);
v___x_1709_ = lean_apply_3(v_proj_1667_, v_typeName_1706_, v_idx_1707_, v_struct_1708_);
return v___x_1709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* v_motive_1710_, lean_object* v_t_1711_, lean_object* v_bvar_1712_, lean_object* v_fvar_1713_, lean_object* v_mvar_1714_, lean_object* v_sort_1715_, lean_object* v_const_1716_, lean_object* v_app_1717_, lean_object* v_lam_1718_, lean_object* v_forallE_1719_, lean_object* v_letE_1720_, lean_object* v_lit_1721_, lean_object* v_mdata_1722_, lean_object* v_proj_1723_){
_start:
{
switch(lean_obj_tag(v_t_1711_))
{
case 0:
{
lean_object* v_deBruijnIndex_1724_; lean_object* v___x_1725_; 
lean_dec(v_proj_1723_);
lean_dec(v_mdata_1722_);
lean_dec(v_lit_1721_);
lean_dec(v_letE_1720_);
lean_dec(v_forallE_1719_);
lean_dec(v_lam_1718_);
lean_dec(v_app_1717_);
lean_dec(v_const_1716_);
lean_dec(v_sort_1715_);
lean_dec(v_mvar_1714_);
lean_dec(v_fvar_1713_);
v_deBruijnIndex_1724_ = lean_ctor_get(v_t_1711_, 0);
lean_inc(v_deBruijnIndex_1724_);
lean_dec_ref_known(v_t_1711_, 1);
v___x_1725_ = lean_apply_1(v_bvar_1712_, v_deBruijnIndex_1724_);
return v___x_1725_;
}
case 1:
{
lean_object* v_fvarId_1726_; lean_object* v___x_1727_; 
lean_dec(v_proj_1723_);
lean_dec(v_mdata_1722_);
lean_dec(v_lit_1721_);
lean_dec(v_letE_1720_);
lean_dec(v_forallE_1719_);
lean_dec(v_lam_1718_);
lean_dec(v_app_1717_);
lean_dec(v_const_1716_);
lean_dec(v_sort_1715_);
lean_dec(v_mvar_1714_);
lean_dec(v_bvar_1712_);
v_fvarId_1726_ = lean_ctor_get(v_t_1711_, 0);
lean_inc(v_fvarId_1726_);
lean_dec_ref_known(v_t_1711_, 1);
v___x_1727_ = lean_apply_1(v_fvar_1713_, v_fvarId_1726_);
return v___x_1727_;
}
case 2:
{
lean_object* v_mvarId_1728_; lean_object* v___x_1729_; 
lean_dec(v_proj_1723_);
lean_dec(v_mdata_1722_);
lean_dec(v_lit_1721_);
lean_dec(v_letE_1720_);
lean_dec(v_forallE_1719_);
lean_dec(v_lam_1718_);
lean_dec(v_app_1717_);
lean_dec(v_const_1716_);
lean_dec(v_sort_1715_);
lean_dec(v_fvar_1713_);
lean_dec(v_bvar_1712_);
v_mvarId_1728_ = lean_ctor_get(v_t_1711_, 0);
lean_inc(v_mvarId_1728_);
lean_dec_ref_known(v_t_1711_, 1);
v___x_1729_ = lean_apply_1(v_mvar_1714_, v_mvarId_1728_);
return v___x_1729_;
}
case 3:
{
lean_object* v_u_1730_; lean_object* v___x_1731_; 
lean_dec(v_proj_1723_);
lean_dec(v_mdata_1722_);
lean_dec(v_lit_1721_);
lean_dec(v_letE_1720_);
lean_dec(v_forallE_1719_);
lean_dec(v_lam_1718_);
lean_dec(v_app_1717_);
lean_dec(v_const_1716_);
lean_dec(v_mvar_1714_);
lean_dec(v_fvar_1713_);
lean_dec(v_bvar_1712_);
v_u_1730_ = lean_ctor_get(v_t_1711_, 0);
lean_inc(v_u_1730_);
lean_dec_ref_known(v_t_1711_, 1);
v___x_1731_ = lean_apply_1(v_sort_1715_, v_u_1730_);
return v___x_1731_;
}
case 4:
{
lean_object* v_declName_1732_; lean_object* v_us_1733_; lean_object* v___x_1734_; 
lean_dec(v_proj_1723_);
lean_dec(v_mdata_1722_);
lean_dec(v_lit_1721_);
lean_dec(v_letE_1720_);
lean_dec(v_forallE_1719_);
lean_dec(v_lam_1718_);
lean_dec(v_app_1717_);
lean_dec(v_sort_1715_);
lean_dec(v_mvar_1714_);
lean_dec(v_fvar_1713_);
lean_dec(v_bvar_1712_);
v_declName_1732_ = lean_ctor_get(v_t_1711_, 0);
lean_inc(v_declName_1732_);
v_us_1733_ = lean_ctor_get(v_t_1711_, 1);
lean_inc(v_us_1733_);
lean_dec_ref_known(v_t_1711_, 2);
v___x_1734_ = lean_apply_2(v_const_1716_, v_declName_1732_, v_us_1733_);
return v___x_1734_;
}
case 5:
{
lean_object* v_fn_1735_; lean_object* v_arg_1736_; lean_object* v___x_1737_; 
lean_dec(v_proj_1723_);
lean_dec(v_mdata_1722_);
lean_dec(v_lit_1721_);
lean_dec(v_letE_1720_);
lean_dec(v_forallE_1719_);
lean_dec(v_lam_1718_);
lean_dec(v_const_1716_);
lean_dec(v_sort_1715_);
lean_dec(v_mvar_1714_);
lean_dec(v_fvar_1713_);
lean_dec(v_bvar_1712_);
v_fn_1735_ = lean_ctor_get(v_t_1711_, 0);
lean_inc_ref(v_fn_1735_);
v_arg_1736_ = lean_ctor_get(v_t_1711_, 1);
lean_inc_ref(v_arg_1736_);
lean_dec_ref_known(v_t_1711_, 2);
v___x_1737_ = lean_apply_2(v_app_1717_, v_fn_1735_, v_arg_1736_);
return v___x_1737_;
}
case 6:
{
lean_object* v_binderName_1738_; lean_object* v_binderType_1739_; lean_object* v_body_1740_; uint8_t v_binderInfo_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_dec(v_proj_1723_);
lean_dec(v_mdata_1722_);
lean_dec(v_lit_1721_);
lean_dec(v_letE_1720_);
lean_dec(v_forallE_1719_);
lean_dec(v_app_1717_);
lean_dec(v_const_1716_);
lean_dec(v_sort_1715_);
lean_dec(v_mvar_1714_);
lean_dec(v_fvar_1713_);
lean_dec(v_bvar_1712_);
v_binderName_1738_ = lean_ctor_get(v_t_1711_, 0);
lean_inc(v_binderName_1738_);
v_binderType_1739_ = lean_ctor_get(v_t_1711_, 1);
lean_inc_ref(v_binderType_1739_);
v_body_1740_ = lean_ctor_get(v_t_1711_, 2);
lean_inc_ref(v_body_1740_);
v_binderInfo_1741_ = lean_ctor_get_uint8(v_t_1711_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1711_, 3);
v___x_1742_ = lean_box(v_binderInfo_1741_);
v___x_1743_ = lean_apply_4(v_lam_1718_, v_binderName_1738_, v_binderType_1739_, v_body_1740_, v___x_1742_);
return v___x_1743_;
}
case 7:
{
lean_object* v_binderName_1744_; lean_object* v_binderType_1745_; lean_object* v_body_1746_; uint8_t v_binderInfo_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v_proj_1723_);
lean_dec(v_mdata_1722_);
lean_dec(v_lit_1721_);
lean_dec(v_letE_1720_);
lean_dec(v_lam_1718_);
lean_dec(v_app_1717_);
lean_dec(v_const_1716_);
lean_dec(v_sort_1715_);
lean_dec(v_mvar_1714_);
lean_dec(v_fvar_1713_);
lean_dec(v_bvar_1712_);
v_binderName_1744_ = lean_ctor_get(v_t_1711_, 0);
lean_inc(v_binderName_1744_);
v_binderType_1745_ = lean_ctor_get(v_t_1711_, 1);
lean_inc_ref(v_binderType_1745_);
v_body_1746_ = lean_ctor_get(v_t_1711_, 2);
lean_inc_ref(v_body_1746_);
v_binderInfo_1747_ = lean_ctor_get_uint8(v_t_1711_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1711_, 3);
v___x_1748_ = lean_box(v_binderInfo_1747_);
v___x_1749_ = lean_apply_4(v_forallE_1719_, v_binderName_1744_, v_binderType_1745_, v_body_1746_, v___x_1748_);
return v___x_1749_;
}
case 8:
{
lean_object* v_declName_1750_; lean_object* v_type_1751_; lean_object* v_value_1752_; lean_object* v_body_1753_; uint8_t v_nondep_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v_proj_1723_);
lean_dec(v_mdata_1722_);
lean_dec(v_lit_1721_);
lean_dec(v_forallE_1719_);
lean_dec(v_lam_1718_);
lean_dec(v_app_1717_);
lean_dec(v_const_1716_);
lean_dec(v_sort_1715_);
lean_dec(v_mvar_1714_);
lean_dec(v_fvar_1713_);
lean_dec(v_bvar_1712_);
v_declName_1750_ = lean_ctor_get(v_t_1711_, 0);
lean_inc(v_declName_1750_);
v_type_1751_ = lean_ctor_get(v_t_1711_, 1);
lean_inc_ref(v_type_1751_);
v_value_1752_ = lean_ctor_get(v_t_1711_, 2);
lean_inc_ref(v_value_1752_);
v_body_1753_ = lean_ctor_get(v_t_1711_, 3);
lean_inc_ref(v_body_1753_);
v_nondep_1754_ = lean_ctor_get_uint8(v_t_1711_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1711_, 4);
v___x_1755_ = lean_box(v_nondep_1754_);
v___x_1756_ = lean_apply_5(v_letE_1720_, v_declName_1750_, v_type_1751_, v_value_1752_, v_body_1753_, v___x_1755_);
return v___x_1756_;
}
case 9:
{
lean_object* v_a_1757_; lean_object* v___x_1758_; 
lean_dec(v_proj_1723_);
lean_dec(v_mdata_1722_);
lean_dec(v_letE_1720_);
lean_dec(v_forallE_1719_);
lean_dec(v_lam_1718_);
lean_dec(v_app_1717_);
lean_dec(v_const_1716_);
lean_dec(v_sort_1715_);
lean_dec(v_mvar_1714_);
lean_dec(v_fvar_1713_);
lean_dec(v_bvar_1712_);
v_a_1757_ = lean_ctor_get(v_t_1711_, 0);
lean_inc_ref(v_a_1757_);
lean_dec_ref_known(v_t_1711_, 1);
v___x_1758_ = lean_apply_1(v_lit_1721_, v_a_1757_);
return v___x_1758_;
}
case 10:
{
lean_object* v_data_1759_; lean_object* v_expr_1760_; lean_object* v___x_1761_; 
lean_dec(v_proj_1723_);
lean_dec(v_lit_1721_);
lean_dec(v_letE_1720_);
lean_dec(v_forallE_1719_);
lean_dec(v_lam_1718_);
lean_dec(v_app_1717_);
lean_dec(v_const_1716_);
lean_dec(v_sort_1715_);
lean_dec(v_mvar_1714_);
lean_dec(v_fvar_1713_);
lean_dec(v_bvar_1712_);
v_data_1759_ = lean_ctor_get(v_t_1711_, 0);
lean_inc(v_data_1759_);
v_expr_1760_ = lean_ctor_get(v_t_1711_, 1);
lean_inc_ref(v_expr_1760_);
lean_dec_ref_known(v_t_1711_, 2);
v___x_1761_ = lean_apply_2(v_mdata_1722_, v_data_1759_, v_expr_1760_);
return v___x_1761_;
}
default: 
{
lean_object* v_typeName_1762_; lean_object* v_idx_1763_; lean_object* v_struct_1764_; lean_object* v___x_1765_; 
lean_dec(v_mdata_1722_);
lean_dec(v_lit_1721_);
lean_dec(v_letE_1720_);
lean_dec(v_forallE_1719_);
lean_dec(v_lam_1718_);
lean_dec(v_app_1717_);
lean_dec(v_const_1716_);
lean_dec(v_sort_1715_);
lean_dec(v_mvar_1714_);
lean_dec(v_fvar_1713_);
lean_dec(v_bvar_1712_);
v_typeName_1762_ = lean_ctor_get(v_t_1711_, 0);
lean_inc(v_typeName_1762_);
v_idx_1763_ = lean_ctor_get(v_t_1711_, 1);
lean_inc(v_idx_1763_);
v_struct_1764_ = lean_ctor_get(v_t_1711_, 2);
lean_inc_ref(v_struct_1764_);
lean_dec_ref_known(v_t_1711_, 3);
v___x_1765_ = lean_apply_3(v_proj_1723_, v_typeName_1762_, v_idx_1763_, v_struct_1764_);
return v___x_1765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* v_deBruijnIndex_1766_){
_start:
{
uint64_t v___x_1767_; uint64_t v___x_1768_; uint64_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; uint32_t v___x_1772_; uint8_t v___x_1773_; uint64_t v___x_1774_; lean_object* v___x_1775_; 
v___x_1767_ = 7ULL;
v___x_1768_ = lean_uint64_of_nat(v_deBruijnIndex_1766_);
v___x_1769_ = lean_uint64_mix_hash(v___x_1767_, v___x_1768_);
v___x_1770_ = lean_unsigned_to_nat(1u);
v___x_1771_ = lean_nat_add(v_deBruijnIndex_1766_, v___x_1770_);
v___x_1772_ = 0;
v___x_1773_ = 0;
v___x_1774_ = lean_expr_mk_data(v___x_1769_, v___x_1771_, v___x_1772_, v___x_1773_, v___x_1773_, v___x_1773_, v___x_1773_);
v___x_1775_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1775_, 0, v_deBruijnIndex_1766_);
lean_ctor_set_uint64(v___x_1775_, sizeof(void*)*1, v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* v_fvarId_1776_){
_start:
{
uint64_t v___x_1777_; uint64_t v___x_1778_; uint64_t v___x_1779_; lean_object* v___x_1780_; uint32_t v___x_1781_; uint8_t v___x_1782_; uint8_t v___x_1783_; uint64_t v___x_1784_; lean_object* v___x_1785_; 
v___x_1777_ = 13ULL;
v___x_1778_ = l_Lean_instHashableFVarId_hash(v_fvarId_1776_);
v___x_1779_ = lean_uint64_mix_hash(v___x_1777_, v___x_1778_);
v___x_1780_ = lean_unsigned_to_nat(0u);
v___x_1781_ = 0;
v___x_1782_ = 1;
v___x_1783_ = 0;
v___x_1784_ = lean_expr_mk_data(v___x_1779_, v___x_1780_, v___x_1781_, v___x_1782_, v___x_1783_, v___x_1783_, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_1785_, 0, v_fvarId_1776_);
lean_ctor_set_uint64(v___x_1785_, sizeof(void*)*1, v___x_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* v_mvarId_1786_){
_start:
{
uint64_t v___x_1787_; uint64_t v___x_1788_; uint64_t v___x_1789_; lean_object* v___x_1790_; uint32_t v___x_1791_; uint8_t v___x_1792_; uint8_t v___x_1793_; uint64_t v___x_1794_; lean_object* v___x_1795_; 
v___x_1787_ = 17ULL;
v___x_1788_ = l_Lean_instHashableMVarId_hash(v_mvarId_1786_);
v___x_1789_ = lean_uint64_mix_hash(v___x_1787_, v___x_1788_);
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = 0;
v___x_1792_ = 0;
v___x_1793_ = 1;
v___x_1794_ = lean_expr_mk_data(v___x_1789_, v___x_1790_, v___x_1791_, v___x_1792_, v___x_1793_, v___x_1792_, v___x_1792_);
v___x_1795_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_1795_, 0, v_mvarId_1786_);
lean_ctor_set_uint64(v___x_1795_, sizeof(void*)*1, v___x_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* v_u_1796_){
_start:
{
uint64_t v___x_1797_; uint64_t v___x_1798_; uint64_t v___x_1799_; lean_object* v___x_1800_; uint32_t v___x_1801_; uint8_t v___x_1802_; uint8_t v___x_1803_; uint8_t v___x_1804_; uint64_t v___x_1805_; lean_object* v___x_1806_; 
v___x_1797_ = 11ULL;
v___x_1798_ = l_Lean_Level_hash(v_u_1796_);
v___x_1799_ = lean_uint64_mix_hash(v___x_1797_, v___x_1798_);
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = 0;
v___x_1802_ = 0;
v___x_1803_ = l_Lean_Level_hasMVar(v_u_1796_);
v___x_1804_ = l_Lean_Level_hasParam(v_u_1796_);
v___x_1805_ = lean_expr_mk_data(v___x_1799_, v___x_1800_, v___x_1801_, v___x_1802_, v___x_1802_, v___x_1803_, v___x_1804_);
v___x_1806_ = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(v___x_1806_, 0, v_u_1796_);
lean_ctor_set_uint64(v___x_1806_, sizeof(void*)*1, v___x_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* v_fn_1807_, lean_object* v_arg_1808_){
_start:
{
uint64_t v___x_1809_; uint64_t v___x_1810_; uint64_t v___x_1811_; lean_object* v___x_1812_; 
v___x_1809_ = lean_expr_data(v_fn_1807_);
v___x_1810_ = lean_expr_data(v_arg_1808_);
v___x_1811_ = lean_expr_mk_app_data(v___x_1809_, v___x_1810_);
v___x_1812_ = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(v___x_1812_, 0, v_fn_1807_);
lean_ctor_set(v___x_1812_, 1, v_arg_1808_);
lean_ctor_set_uint64(v___x_1812_, sizeof(void*)*2, v___x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object* v_binderName_1813_, lean_object* v_binderType_1814_, lean_object* v_body_1815_, uint8_t v_binderInfo_1816_){
_start:
{
uint8_t v___y_1818_; uint8_t v___y_1819_; lean_object* v___y_1820_; uint8_t v___y_1821_; uint64_t v___y_1822_; uint32_t v___y_1823_; uint8_t v___y_1824_; uint64_t v___x_1827_; uint8_t v___x_1828_; uint32_t v___x_1829_; uint64_t v___x_1830_; uint8_t v___y_1832_; lean_object* v___y_1833_; uint8_t v___y_1834_; uint64_t v___y_1835_; uint32_t v___y_1836_; uint8_t v___y_1837_; uint8_t v___y_1841_; lean_object* v___y_1842_; uint64_t v___y_1843_; uint32_t v___y_1844_; uint8_t v___y_1845_; lean_object* v___y_1849_; uint64_t v___y_1850_; uint32_t v___y_1851_; uint8_t v___y_1852_; uint64_t v___y_1856_; uint32_t v___y_1857_; lean_object* v___y_1858_; uint32_t v___y_1862_; uint8_t v___x_1877_; uint32_t v___x_1878_; uint8_t v___x_1879_; 
v___x_1827_ = lean_expr_data(v_binderType_1814_);
v___x_1828_ = l_Lean_Expr_Data_approxDepth(v___x_1827_);
v___x_1829_ = lean_uint8_to_uint32(v___x_1828_);
v___x_1830_ = lean_expr_data(v_body_1815_);
v___x_1877_ = l_Lean_Expr_Data_approxDepth(v___x_1830_);
v___x_1878_ = lean_uint8_to_uint32(v___x_1877_);
v___x_1879_ = lean_uint32_dec_le(v___x_1829_, v___x_1878_);
if (v___x_1879_ == 0)
{
v___y_1862_ = v___x_1829_;
goto v___jp_1861_;
}
else
{
v___y_1862_ = v___x_1878_;
goto v___jp_1861_;
}
v___jp_1817_:
{
uint64_t v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_expr_mk_data(v___y_1822_, v___y_1820_, v___y_1823_, v___y_1818_, v___y_1819_, v___y_1821_, v___y_1824_);
v___x_1826_ = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(v___x_1826_, 0, v_binderName_1813_);
lean_ctor_set(v___x_1826_, 1, v_binderType_1814_);
lean_ctor_set(v___x_1826_, 2, v_body_1815_);
lean_ctor_set_uint64(v___x_1826_, sizeof(void*)*3, v___x_1825_);
lean_ctor_set_uint8(v___x_1826_, sizeof(void*)*3 + 8, v_binderInfo_1816_);
return v___x_1826_;
}
v___jp_1831_:
{
uint8_t v___x_1838_; 
v___x_1838_ = l_Lean_Expr_Data_hasLevelParam(v___x_1827_);
if (v___x_1838_ == 0)
{
uint8_t v___x_1839_; 
v___x_1839_ = l_Lean_Expr_Data_hasLevelParam(v___x_1830_);
v___y_1818_ = v___y_1832_;
v___y_1819_ = v___y_1834_;
v___y_1820_ = v___y_1833_;
v___y_1821_ = v___y_1837_;
v___y_1822_ = v___y_1835_;
v___y_1823_ = v___y_1836_;
v___y_1824_ = v___x_1839_;
goto v___jp_1817_;
}
else
{
v___y_1818_ = v___y_1832_;
v___y_1819_ = v___y_1834_;
v___y_1820_ = v___y_1833_;
v___y_1821_ = v___y_1837_;
v___y_1822_ = v___y_1835_;
v___y_1823_ = v___y_1836_;
v___y_1824_ = v___x_1838_;
goto v___jp_1817_;
}
}
v___jp_1840_:
{
uint8_t v___x_1846_; 
v___x_1846_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1827_);
if (v___x_1846_ == 0)
{
uint8_t v___x_1847_; 
v___x_1847_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1830_);
v___y_1832_ = v___y_1841_;
v___y_1833_ = v___y_1842_;
v___y_1834_ = v___y_1845_;
v___y_1835_ = v___y_1843_;
v___y_1836_ = v___y_1844_;
v___y_1837_ = v___x_1847_;
goto v___jp_1831_;
}
else
{
v___y_1832_ = v___y_1841_;
v___y_1833_ = v___y_1842_;
v___y_1834_ = v___y_1845_;
v___y_1835_ = v___y_1843_;
v___y_1836_ = v___y_1844_;
v___y_1837_ = v___x_1846_;
goto v___jp_1831_;
}
}
v___jp_1848_:
{
uint8_t v___x_1853_; 
v___x_1853_ = l_Lean_Expr_Data_hasExprMVar(v___x_1827_);
if (v___x_1853_ == 0)
{
uint8_t v___x_1854_; 
v___x_1854_ = l_Lean_Expr_Data_hasExprMVar(v___x_1830_);
v___y_1841_ = v___y_1852_;
v___y_1842_ = v___y_1849_;
v___y_1843_ = v___y_1850_;
v___y_1844_ = v___y_1851_;
v___y_1845_ = v___x_1854_;
goto v___jp_1840_;
}
else
{
v___y_1841_ = v___y_1852_;
v___y_1842_ = v___y_1849_;
v___y_1843_ = v___y_1850_;
v___y_1844_ = v___y_1851_;
v___y_1845_ = v___x_1853_;
goto v___jp_1840_;
}
}
v___jp_1855_:
{
uint8_t v___x_1859_; 
v___x_1859_ = l_Lean_Expr_Data_hasFVar(v___x_1827_);
if (v___x_1859_ == 0)
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Lean_Expr_Data_hasFVar(v___x_1830_);
v___y_1849_ = v___y_1858_;
v___y_1850_ = v___y_1856_;
v___y_1851_ = v___y_1857_;
v___y_1852_ = v___x_1860_;
goto v___jp_1848_;
}
else
{
v___y_1849_ = v___y_1858_;
v___y_1850_ = v___y_1856_;
v___y_1851_ = v___y_1857_;
v___y_1852_ = v___x_1859_;
goto v___jp_1848_;
}
}
v___jp_1861_:
{
lean_object* v___x_1863_; uint32_t v___x_1864_; uint32_t v___x_1865_; uint64_t v___x_1866_; uint64_t v___x_1867_; uint64_t v___x_1868_; uint64_t v___x_1869_; uint64_t v___x_1870_; uint32_t v___x_1871_; lean_object* v___x_1872_; uint32_t v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1863_ = lean_unsigned_to_nat(1u);
v___x_1864_ = 1;
v___x_1865_ = lean_uint32_add(v___y_1862_, v___x_1864_);
v___x_1866_ = lean_uint32_to_uint64(v___x_1865_);
v___x_1867_ = l_Lean_Expr_Data_hash(v___x_1827_);
v___x_1868_ = l_Lean_Expr_Data_hash(v___x_1830_);
v___x_1869_ = lean_uint64_mix_hash(v___x_1867_, v___x_1868_);
v___x_1870_ = lean_uint64_mix_hash(v___x_1866_, v___x_1869_);
v___x_1871_ = l_Lean_Expr_Data_looseBVarRange(v___x_1827_);
v___x_1872_ = lean_uint32_to_nat(v___x_1871_);
v___x_1873_ = l_Lean_Expr_Data_looseBVarRange(v___x_1830_);
v___x_1874_ = lean_uint32_to_nat(v___x_1873_);
v___x_1875_ = lean_nat_sub(v___x_1874_, v___x_1863_);
lean_dec(v___x_1874_);
v___x_1876_ = lean_nat_dec_le(v___x_1872_, v___x_1875_);
if (v___x_1876_ == 0)
{
lean_dec(v___x_1875_);
v___y_1856_ = v___x_1870_;
v___y_1857_ = v___x_1865_;
v___y_1858_ = v___x_1872_;
goto v___jp_1855_;
}
else
{
lean_dec(v___x_1872_);
v___y_1856_ = v___x_1870_;
v___y_1857_ = v___x_1865_;
v___y_1858_ = v___x_1875_;
goto v___jp_1855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* v_binderName_1880_, lean_object* v_binderType_1881_, lean_object* v_body_1882_, lean_object* v_binderInfo_1883_){
_start:
{
uint8_t v_binderInfo_boxed_1884_; lean_object* v_res_1885_; 
v_binderInfo_boxed_1884_ = lean_unbox(v_binderInfo_1883_);
v_res_1885_ = l_Lean_Expr_lam___override(v_binderName_1880_, v_binderType_1881_, v_body_1882_, v_binderInfo_boxed_1884_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object* v_binderName_1886_, lean_object* v_binderType_1887_, lean_object* v_body_1888_, uint8_t v_binderInfo_1889_){
_start:
{
uint64_t v___y_1891_; uint8_t v___y_1892_; lean_object* v___y_1893_; uint8_t v___y_1894_; uint32_t v___y_1895_; uint8_t v___y_1896_; uint8_t v___y_1897_; uint64_t v___x_1900_; uint8_t v___x_1901_; uint32_t v___x_1902_; uint64_t v___x_1903_; uint64_t v___y_1905_; uint8_t v___y_1906_; lean_object* v___y_1907_; uint32_t v___y_1908_; uint8_t v___y_1909_; uint8_t v___y_1910_; uint64_t v___y_1914_; lean_object* v___y_1915_; uint32_t v___y_1916_; uint8_t v___y_1917_; uint8_t v___y_1918_; uint64_t v___y_1922_; lean_object* v___y_1923_; uint32_t v___y_1924_; uint8_t v___y_1925_; uint64_t v___y_1929_; uint32_t v___y_1930_; lean_object* v___y_1931_; uint32_t v___y_1935_; uint8_t v___x_1950_; uint32_t v___x_1951_; uint8_t v___x_1952_; 
v___x_1900_ = lean_expr_data(v_binderType_1887_);
v___x_1901_ = l_Lean_Expr_Data_approxDepth(v___x_1900_);
v___x_1902_ = lean_uint8_to_uint32(v___x_1901_);
v___x_1903_ = lean_expr_data(v_body_1888_);
v___x_1950_ = l_Lean_Expr_Data_approxDepth(v___x_1903_);
v___x_1951_ = lean_uint8_to_uint32(v___x_1950_);
v___x_1952_ = lean_uint32_dec_le(v___x_1902_, v___x_1951_);
if (v___x_1952_ == 0)
{
v___y_1935_ = v___x_1902_;
goto v___jp_1934_;
}
else
{
v___y_1935_ = v___x_1951_;
goto v___jp_1934_;
}
v___jp_1890_:
{
uint64_t v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_expr_mk_data(v___y_1891_, v___y_1893_, v___y_1895_, v___y_1896_, v___y_1892_, v___y_1894_, v___y_1897_);
v___x_1899_ = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(v___x_1899_, 0, v_binderName_1886_);
lean_ctor_set(v___x_1899_, 1, v_binderType_1887_);
lean_ctor_set(v___x_1899_, 2, v_body_1888_);
lean_ctor_set_uint64(v___x_1899_, sizeof(void*)*3, v___x_1898_);
lean_ctor_set_uint8(v___x_1899_, sizeof(void*)*3 + 8, v_binderInfo_1889_);
return v___x_1899_;
}
v___jp_1904_:
{
uint8_t v___x_1911_; 
v___x_1911_ = l_Lean_Expr_Data_hasLevelParam(v___x_1900_);
if (v___x_1911_ == 0)
{
uint8_t v___x_1912_; 
v___x_1912_ = l_Lean_Expr_Data_hasLevelParam(v___x_1903_);
v___y_1891_ = v___y_1905_;
v___y_1892_ = v___y_1906_;
v___y_1893_ = v___y_1907_;
v___y_1894_ = v___y_1910_;
v___y_1895_ = v___y_1908_;
v___y_1896_ = v___y_1909_;
v___y_1897_ = v___x_1912_;
goto v___jp_1890_;
}
else
{
v___y_1891_ = v___y_1905_;
v___y_1892_ = v___y_1906_;
v___y_1893_ = v___y_1907_;
v___y_1894_ = v___y_1910_;
v___y_1895_ = v___y_1908_;
v___y_1896_ = v___y_1909_;
v___y_1897_ = v___x_1911_;
goto v___jp_1890_;
}
}
v___jp_1913_:
{
uint8_t v___x_1919_; 
v___x_1919_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1900_);
if (v___x_1919_ == 0)
{
uint8_t v___x_1920_; 
v___x_1920_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1903_);
v___y_1905_ = v___y_1914_;
v___y_1906_ = v___y_1918_;
v___y_1907_ = v___y_1915_;
v___y_1908_ = v___y_1916_;
v___y_1909_ = v___y_1917_;
v___y_1910_ = v___x_1920_;
goto v___jp_1904_;
}
else
{
v___y_1905_ = v___y_1914_;
v___y_1906_ = v___y_1918_;
v___y_1907_ = v___y_1915_;
v___y_1908_ = v___y_1916_;
v___y_1909_ = v___y_1917_;
v___y_1910_ = v___x_1919_;
goto v___jp_1904_;
}
}
v___jp_1921_:
{
uint8_t v___x_1926_; 
v___x_1926_ = l_Lean_Expr_Data_hasExprMVar(v___x_1900_);
if (v___x_1926_ == 0)
{
uint8_t v___x_1927_; 
v___x_1927_ = l_Lean_Expr_Data_hasExprMVar(v___x_1903_);
v___y_1914_ = v___y_1922_;
v___y_1915_ = v___y_1923_;
v___y_1916_ = v___y_1924_;
v___y_1917_ = v___y_1925_;
v___y_1918_ = v___x_1927_;
goto v___jp_1913_;
}
else
{
v___y_1914_ = v___y_1922_;
v___y_1915_ = v___y_1923_;
v___y_1916_ = v___y_1924_;
v___y_1917_ = v___y_1925_;
v___y_1918_ = v___x_1926_;
goto v___jp_1913_;
}
}
v___jp_1928_:
{
uint8_t v___x_1932_; 
v___x_1932_ = l_Lean_Expr_Data_hasFVar(v___x_1900_);
if (v___x_1932_ == 0)
{
uint8_t v___x_1933_; 
v___x_1933_ = l_Lean_Expr_Data_hasFVar(v___x_1903_);
v___y_1922_ = v___y_1929_;
v___y_1923_ = v___y_1931_;
v___y_1924_ = v___y_1930_;
v___y_1925_ = v___x_1933_;
goto v___jp_1921_;
}
else
{
v___y_1922_ = v___y_1929_;
v___y_1923_ = v___y_1931_;
v___y_1924_ = v___y_1930_;
v___y_1925_ = v___x_1932_;
goto v___jp_1921_;
}
}
v___jp_1934_:
{
lean_object* v___x_1936_; uint32_t v___x_1937_; uint32_t v___x_1938_; uint64_t v___x_1939_; uint64_t v___x_1940_; uint64_t v___x_1941_; uint64_t v___x_1942_; uint64_t v___x_1943_; uint32_t v___x_1944_; lean_object* v___x_1945_; uint32_t v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1936_ = lean_unsigned_to_nat(1u);
v___x_1937_ = 1;
v___x_1938_ = lean_uint32_add(v___y_1935_, v___x_1937_);
v___x_1939_ = lean_uint32_to_uint64(v___x_1938_);
v___x_1940_ = l_Lean_Expr_Data_hash(v___x_1900_);
v___x_1941_ = l_Lean_Expr_Data_hash(v___x_1903_);
v___x_1942_ = lean_uint64_mix_hash(v___x_1940_, v___x_1941_);
v___x_1943_ = lean_uint64_mix_hash(v___x_1939_, v___x_1942_);
v___x_1944_ = l_Lean_Expr_Data_looseBVarRange(v___x_1900_);
v___x_1945_ = lean_uint32_to_nat(v___x_1944_);
v___x_1946_ = l_Lean_Expr_Data_looseBVarRange(v___x_1903_);
v___x_1947_ = lean_uint32_to_nat(v___x_1946_);
v___x_1948_ = lean_nat_sub(v___x_1947_, v___x_1936_);
lean_dec(v___x_1947_);
v___x_1949_ = lean_nat_dec_le(v___x_1945_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_dec(v___x_1948_);
v___y_1929_ = v___x_1943_;
v___y_1930_ = v___x_1938_;
v___y_1931_ = v___x_1945_;
goto v___jp_1928_;
}
else
{
lean_dec(v___x_1945_);
v___y_1929_ = v___x_1943_;
v___y_1930_ = v___x_1938_;
v___y_1931_ = v___x_1948_;
goto v___jp_1928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* v_binderName_1953_, lean_object* v_binderType_1954_, lean_object* v_body_1955_, lean_object* v_binderInfo_1956_){
_start:
{
uint8_t v_binderInfo_boxed_1957_; lean_object* v_res_1958_; 
v_binderInfo_boxed_1957_ = lean_unbox(v_binderInfo_1956_);
v_res_1958_ = l_Lean_Expr_forallE___override(v_binderName_1953_, v_binderType_1954_, v_body_1955_, v_binderInfo_boxed_1957_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object* v_declName_1959_, lean_object* v_type_1960_, lean_object* v_value_1961_, lean_object* v_body_1962_, uint8_t v_nondep_1963_){
_start:
{
uint8_t v___y_1965_; uint64_t v___y_1966_; uint8_t v___y_1967_; uint32_t v___y_1968_; lean_object* v___y_1969_; uint8_t v___y_1970_; uint8_t v___y_1971_; uint8_t v___y_1975_; uint64_t v___y_1976_; uint8_t v___y_1977_; lean_object* v___y_1978_; uint32_t v___y_1979_; uint8_t v___y_1980_; uint64_t v___y_1981_; uint8_t v___y_1982_; uint64_t v___x_1984_; uint8_t v___x_1985_; uint32_t v___x_1986_; uint64_t v___x_1987_; uint8_t v___y_1989_; uint64_t v___y_1990_; uint8_t v___y_1991_; lean_object* v___y_1992_; uint32_t v___y_1993_; uint64_t v___y_1994_; uint8_t v___y_1995_; uint8_t v___y_1999_; uint64_t v___y_2000_; uint8_t v___y_2001_; uint32_t v___y_2002_; lean_object* v___y_2003_; uint64_t v___y_2004_; uint8_t v___y_2005_; uint8_t v___y_2008_; uint64_t v___y_2009_; uint32_t v___y_2010_; lean_object* v___y_2011_; uint64_t v___y_2012_; uint8_t v___y_2013_; uint8_t v___y_2017_; uint64_t v___y_2018_; lean_object* v___y_2019_; uint32_t v___y_2020_; uint64_t v___y_2021_; uint8_t v___y_2022_; uint64_t v___y_2025_; lean_object* v___y_2026_; uint32_t v___y_2027_; uint64_t v___y_2028_; uint8_t v___y_2029_; uint64_t v___y_2033_; uint32_t v___y_2034_; lean_object* v___y_2035_; uint64_t v___y_2036_; uint8_t v___y_2037_; uint64_t v___y_2040_; uint32_t v___y_2041_; uint64_t v___y_2042_; lean_object* v___y_2043_; uint64_t v___y_2047_; lean_object* v___y_2048_; uint32_t v___y_2049_; uint64_t v___y_2050_; lean_object* v___y_2051_; uint64_t v___y_2057_; uint32_t v___y_2058_; uint32_t v___y_2075_; uint8_t v___x_2080_; uint32_t v___x_2081_; uint8_t v___x_2082_; 
v___x_1984_ = lean_expr_data(v_type_1960_);
v___x_1985_ = l_Lean_Expr_Data_approxDepth(v___x_1984_);
v___x_1986_ = lean_uint8_to_uint32(v___x_1985_);
v___x_1987_ = lean_expr_data(v_value_1961_);
v___x_2080_ = l_Lean_Expr_Data_approxDepth(v___x_1987_);
v___x_2081_ = lean_uint8_to_uint32(v___x_2080_);
v___x_2082_ = lean_uint32_dec_le(v___x_1986_, v___x_2081_);
if (v___x_2082_ == 0)
{
v___y_2075_ = v___x_1986_;
goto v___jp_2074_;
}
else
{
v___y_2075_ = v___x_2081_;
goto v___jp_2074_;
}
v___jp_1964_:
{
uint64_t v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = lean_expr_mk_data(v___y_1966_, v___y_1969_, v___y_1968_, v___y_1965_, v___y_1967_, v___y_1970_, v___y_1971_);
v___x_1973_ = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(v___x_1973_, 0, v_declName_1959_);
lean_ctor_set(v___x_1973_, 1, v_type_1960_);
lean_ctor_set(v___x_1973_, 2, v_value_1961_);
lean_ctor_set(v___x_1973_, 3, v_body_1962_);
lean_ctor_set_uint64(v___x_1973_, sizeof(void*)*4, v___x_1972_);
lean_ctor_set_uint8(v___x_1973_, sizeof(void*)*4 + 8, v_nondep_1963_);
return v___x_1973_;
}
v___jp_1974_:
{
if (v___y_1982_ == 0)
{
uint8_t v___x_1983_; 
v___x_1983_ = l_Lean_Expr_Data_hasLevelParam(v___y_1981_);
v___y_1965_ = v___y_1975_;
v___y_1966_ = v___y_1976_;
v___y_1967_ = v___y_1977_;
v___y_1968_ = v___y_1979_;
v___y_1969_ = v___y_1978_;
v___y_1970_ = v___y_1980_;
v___y_1971_ = v___x_1983_;
goto v___jp_1964_;
}
else
{
v___y_1965_ = v___y_1975_;
v___y_1966_ = v___y_1976_;
v___y_1967_ = v___y_1977_;
v___y_1968_ = v___y_1979_;
v___y_1969_ = v___y_1978_;
v___y_1970_ = v___y_1980_;
v___y_1971_ = v___y_1982_;
goto v___jp_1964_;
}
}
v___jp_1988_:
{
uint8_t v___x_1996_; 
v___x_1996_ = l_Lean_Expr_Data_hasLevelParam(v___x_1984_);
if (v___x_1996_ == 0)
{
uint8_t v___x_1997_; 
v___x_1997_ = l_Lean_Expr_Data_hasLevelParam(v___x_1987_);
v___y_1975_ = v___y_1989_;
v___y_1976_ = v___y_1990_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1992_;
v___y_1979_ = v___y_1993_;
v___y_1980_ = v___y_1995_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___x_1997_;
goto v___jp_1974_;
}
else
{
v___y_1975_ = v___y_1989_;
v___y_1976_ = v___y_1990_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1992_;
v___y_1979_ = v___y_1993_;
v___y_1980_ = v___y_1995_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___x_1996_;
goto v___jp_1974_;
}
}
v___jp_1998_:
{
if (v___y_2005_ == 0)
{
uint8_t v___x_2006_; 
v___x_2006_ = l_Lean_Expr_Data_hasLevelMVar(v___y_2004_);
v___y_1989_ = v___y_1999_;
v___y_1990_ = v___y_2000_;
v___y_1991_ = v___y_2001_;
v___y_1992_ = v___y_2003_;
v___y_1993_ = v___y_2002_;
v___y_1994_ = v___y_2004_;
v___y_1995_ = v___x_2006_;
goto v___jp_1988_;
}
else
{
v___y_1989_ = v___y_1999_;
v___y_1990_ = v___y_2000_;
v___y_1991_ = v___y_2001_;
v___y_1992_ = v___y_2003_;
v___y_1993_ = v___y_2002_;
v___y_1994_ = v___y_2004_;
v___y_1995_ = v___y_2005_;
goto v___jp_1988_;
}
}
v___jp_2007_:
{
uint8_t v___x_2014_; 
v___x_2014_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1984_);
if (v___x_2014_ == 0)
{
uint8_t v___x_2015_; 
v___x_2015_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1987_);
v___y_1999_ = v___y_2008_;
v___y_2000_ = v___y_2009_;
v___y_2001_ = v___y_2013_;
v___y_2002_ = v___y_2010_;
v___y_2003_ = v___y_2011_;
v___y_2004_ = v___y_2012_;
v___y_2005_ = v___x_2015_;
goto v___jp_1998_;
}
else
{
v___y_1999_ = v___y_2008_;
v___y_2000_ = v___y_2009_;
v___y_2001_ = v___y_2013_;
v___y_2002_ = v___y_2010_;
v___y_2003_ = v___y_2011_;
v___y_2004_ = v___y_2012_;
v___y_2005_ = v___x_2014_;
goto v___jp_1998_;
}
}
v___jp_2016_:
{
if (v___y_2022_ == 0)
{
uint8_t v___x_2023_; 
v___x_2023_ = l_Lean_Expr_Data_hasExprMVar(v___y_2021_);
v___y_2008_ = v___y_2017_;
v___y_2009_ = v___y_2018_;
v___y_2010_ = v___y_2020_;
v___y_2011_ = v___y_2019_;
v___y_2012_ = v___y_2021_;
v___y_2013_ = v___x_2023_;
goto v___jp_2007_;
}
else
{
v___y_2008_ = v___y_2017_;
v___y_2009_ = v___y_2018_;
v___y_2010_ = v___y_2020_;
v___y_2011_ = v___y_2019_;
v___y_2012_ = v___y_2021_;
v___y_2013_ = v___y_2022_;
goto v___jp_2007_;
}
}
v___jp_2024_:
{
uint8_t v___x_2030_; 
v___x_2030_ = l_Lean_Expr_Data_hasExprMVar(v___x_1984_);
if (v___x_2030_ == 0)
{
uint8_t v___x_2031_; 
v___x_2031_ = l_Lean_Expr_Data_hasExprMVar(v___x_1987_);
v___y_2017_ = v___y_2029_;
v___y_2018_ = v___y_2025_;
v___y_2019_ = v___y_2026_;
v___y_2020_ = v___y_2027_;
v___y_2021_ = v___y_2028_;
v___y_2022_ = v___x_2031_;
goto v___jp_2016_;
}
else
{
v___y_2017_ = v___y_2029_;
v___y_2018_ = v___y_2025_;
v___y_2019_ = v___y_2026_;
v___y_2020_ = v___y_2027_;
v___y_2021_ = v___y_2028_;
v___y_2022_ = v___x_2030_;
goto v___jp_2016_;
}
}
v___jp_2032_:
{
if (v___y_2037_ == 0)
{
uint8_t v___x_2038_; 
v___x_2038_ = l_Lean_Expr_Data_hasFVar(v___y_2036_);
v___y_2025_ = v___y_2033_;
v___y_2026_ = v___y_2035_;
v___y_2027_ = v___y_2034_;
v___y_2028_ = v___y_2036_;
v___y_2029_ = v___x_2038_;
goto v___jp_2024_;
}
else
{
v___y_2025_ = v___y_2033_;
v___y_2026_ = v___y_2035_;
v___y_2027_ = v___y_2034_;
v___y_2028_ = v___y_2036_;
v___y_2029_ = v___y_2037_;
goto v___jp_2024_;
}
}
v___jp_2039_:
{
uint8_t v___x_2044_; 
v___x_2044_ = l_Lean_Expr_Data_hasFVar(v___x_1984_);
if (v___x_2044_ == 0)
{
uint8_t v___x_2045_; 
v___x_2045_ = l_Lean_Expr_Data_hasFVar(v___x_1987_);
v___y_2033_ = v___y_2040_;
v___y_2034_ = v___y_2041_;
v___y_2035_ = v___y_2043_;
v___y_2036_ = v___y_2042_;
v___y_2037_ = v___x_2045_;
goto v___jp_2032_;
}
else
{
v___y_2033_ = v___y_2040_;
v___y_2034_ = v___y_2041_;
v___y_2035_ = v___y_2043_;
v___y_2036_ = v___y_2042_;
v___y_2037_ = v___x_2044_;
goto v___jp_2032_;
}
}
v___jp_2046_:
{
uint32_t v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2052_ = l_Lean_Expr_Data_looseBVarRange(v___y_2050_);
v___x_2053_ = lean_uint32_to_nat(v___x_2052_);
v___x_2054_ = lean_nat_sub(v___x_2053_, v___y_2048_);
lean_dec(v___x_2053_);
v___x_2055_ = lean_nat_dec_le(v___y_2051_, v___x_2054_);
if (v___x_2055_ == 0)
{
lean_dec(v___x_2054_);
v___y_2040_ = v___y_2047_;
v___y_2041_ = v___y_2049_;
v___y_2042_ = v___y_2050_;
v___y_2043_ = v___y_2051_;
goto v___jp_2039_;
}
else
{
lean_dec(v___y_2051_);
v___y_2040_ = v___y_2047_;
v___y_2041_ = v___y_2049_;
v___y_2042_ = v___y_2050_;
v___y_2043_ = v___x_2054_;
goto v___jp_2039_;
}
}
v___jp_2056_:
{
lean_object* v___x_2059_; uint32_t v___x_2060_; uint32_t v___x_2061_; uint64_t v___x_2062_; uint64_t v___x_2063_; uint64_t v___x_2064_; uint64_t v___x_2065_; uint64_t v___x_2066_; uint64_t v___x_2067_; uint64_t v___x_2068_; uint32_t v___x_2069_; lean_object* v___x_2070_; uint32_t v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2059_ = lean_unsigned_to_nat(1u);
v___x_2060_ = 1;
v___x_2061_ = lean_uint32_add(v___y_2058_, v___x_2060_);
v___x_2062_ = lean_uint32_to_uint64(v___x_2061_);
v___x_2063_ = l_Lean_Expr_Data_hash(v___x_1984_);
v___x_2064_ = l_Lean_Expr_Data_hash(v___x_1987_);
v___x_2065_ = l_Lean_Expr_Data_hash(v___y_2057_);
v___x_2066_ = lean_uint64_mix_hash(v___x_2064_, v___x_2065_);
v___x_2067_ = lean_uint64_mix_hash(v___x_2063_, v___x_2066_);
v___x_2068_ = lean_uint64_mix_hash(v___x_2062_, v___x_2067_);
v___x_2069_ = l_Lean_Expr_Data_looseBVarRange(v___x_1984_);
v___x_2070_ = lean_uint32_to_nat(v___x_2069_);
v___x_2071_ = l_Lean_Expr_Data_looseBVarRange(v___x_1987_);
v___x_2072_ = lean_uint32_to_nat(v___x_2071_);
v___x_2073_ = lean_nat_dec_le(v___x_2070_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_dec(v___x_2072_);
v___y_2047_ = v___x_2068_;
v___y_2048_ = v___x_2059_;
v___y_2049_ = v___x_2061_;
v___y_2050_ = v___y_2057_;
v___y_2051_ = v___x_2070_;
goto v___jp_2046_;
}
else
{
lean_dec(v___x_2070_);
v___y_2047_ = v___x_2068_;
v___y_2048_ = v___x_2059_;
v___y_2049_ = v___x_2061_;
v___y_2050_ = v___y_2057_;
v___y_2051_ = v___x_2072_;
goto v___jp_2046_;
}
}
v___jp_2074_:
{
uint64_t v___x_2076_; uint8_t v___x_2077_; uint32_t v___x_2078_; uint8_t v___x_2079_; 
v___x_2076_ = lean_expr_data(v_body_1962_);
v___x_2077_ = l_Lean_Expr_Data_approxDepth(v___x_2076_);
v___x_2078_ = lean_uint8_to_uint32(v___x_2077_);
v___x_2079_ = lean_uint32_dec_le(v___y_2075_, v___x_2078_);
if (v___x_2079_ == 0)
{
v___y_2057_ = v___x_2076_;
v___y_2058_ = v___y_2075_;
goto v___jp_2056_;
}
else
{
v___y_2057_ = v___x_2076_;
v___y_2058_ = v___x_2078_;
goto v___jp_2056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* v_declName_2083_, lean_object* v_type_2084_, lean_object* v_value_2085_, lean_object* v_body_2086_, lean_object* v_nondep_2087_){
_start:
{
uint8_t v_nondep_boxed_2088_; lean_object* v_res_2089_; 
v_nondep_boxed_2088_ = lean_unbox(v_nondep_2087_);
v_res_2089_ = l_Lean_Expr_letE___override(v_declName_2083_, v_type_2084_, v_value_2085_, v_body_2086_, v_nondep_boxed_2088_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* v_a_2090_){
_start:
{
uint64_t v___x_2091_; uint64_t v___x_2092_; uint64_t v___x_2093_; lean_object* v___x_2094_; uint32_t v___x_2095_; uint8_t v___x_2096_; uint64_t v___x_2097_; lean_object* v___x_2098_; 
v___x_2091_ = 3ULL;
v___x_2092_ = l_Lean_Literal_hash(v_a_2090_);
v___x_2093_ = lean_uint64_mix_hash(v___x_2091_, v___x_2092_);
v___x_2094_ = lean_unsigned_to_nat(0u);
v___x_2095_ = 0;
v___x_2096_ = 0;
v___x_2097_ = lean_expr_mk_data(v___x_2093_, v___x_2094_, v___x_2095_, v___x_2096_, v___x_2096_, v___x_2096_, v___x_2096_);
v___x_2098_ = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(v___x_2098_, 0, v_a_2090_);
lean_ctor_set_uint64(v___x_2098_, sizeof(void*)*1, v___x_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* v_data_2099_, lean_object* v_expr_2100_){
_start:
{
uint64_t v___x_2101_; uint8_t v___x_2102_; uint32_t v___x_2103_; uint32_t v___x_2104_; uint32_t v___x_2105_; uint64_t v___x_2106_; uint64_t v___x_2107_; uint64_t v___x_2108_; uint32_t v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; uint8_t v___x_2112_; uint8_t v___x_2113_; uint8_t v___x_2114_; uint64_t v___x_2115_; lean_object* v___x_2116_; 
v___x_2101_ = lean_expr_data(v_expr_2100_);
v___x_2102_ = l_Lean_Expr_Data_approxDepth(v___x_2101_);
v___x_2103_ = lean_uint8_to_uint32(v___x_2102_);
v___x_2104_ = 1;
v___x_2105_ = lean_uint32_add(v___x_2103_, v___x_2104_);
v___x_2106_ = lean_uint32_to_uint64(v___x_2105_);
v___x_2107_ = l_Lean_Expr_Data_hash(v___x_2101_);
v___x_2108_ = lean_uint64_mix_hash(v___x_2106_, v___x_2107_);
v___x_2109_ = l_Lean_Expr_Data_looseBVarRange(v___x_2101_);
v___x_2110_ = lean_uint32_to_nat(v___x_2109_);
v___x_2111_ = l_Lean_Expr_Data_hasFVar(v___x_2101_);
v___x_2112_ = l_Lean_Expr_Data_hasExprMVar(v___x_2101_);
v___x_2113_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2101_);
v___x_2114_ = l_Lean_Expr_Data_hasLevelParam(v___x_2101_);
v___x_2115_ = lean_expr_mk_data(v___x_2108_, v___x_2110_, v___x_2105_, v___x_2111_, v___x_2112_, v___x_2113_, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(v___x_2116_, 0, v_data_2099_);
lean_ctor_set(v___x_2116_, 1, v_expr_2100_);
lean_ctor_set_uint64(v___x_2116_, sizeof(void*)*2, v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* v_typeName_2117_, lean_object* v_idx_2118_, lean_object* v_struct_2119_){
_start:
{
uint64_t v___x_2120_; uint8_t v___x_2121_; uint32_t v___x_2122_; uint32_t v___x_2123_; uint32_t v___x_2124_; uint64_t v___x_2125_; uint64_t v___y_2127_; 
v___x_2120_ = lean_expr_data(v_struct_2119_);
v___x_2121_ = l_Lean_Expr_Data_approxDepth(v___x_2120_);
v___x_2122_ = lean_uint8_to_uint32(v___x_2121_);
v___x_2123_ = 1;
v___x_2124_ = lean_uint32_add(v___x_2122_, v___x_2123_);
v___x_2125_ = lean_uint32_to_uint64(v___x_2124_);
if (lean_obj_tag(v_typeName_2117_) == 0)
{
uint64_t v___x_2141_; 
v___x_2141_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
v___y_2127_ = v___x_2141_;
goto v___jp_2126_;
}
else
{
uint64_t v_hash_2142_; 
v_hash_2142_ = lean_ctor_get_uint64(v_typeName_2117_, sizeof(void*)*2);
v___y_2127_ = v_hash_2142_;
goto v___jp_2126_;
}
v___jp_2126_:
{
uint64_t v___x_2128_; uint64_t v___x_2129_; uint64_t v___x_2130_; uint64_t v___x_2131_; uint64_t v___x_2132_; uint32_t v___x_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; uint8_t v___x_2136_; uint8_t v___x_2137_; uint8_t v___x_2138_; uint64_t v___x_2139_; lean_object* v___x_2140_; 
v___x_2128_ = lean_uint64_of_nat(v_idx_2118_);
v___x_2129_ = l_Lean_Expr_Data_hash(v___x_2120_);
v___x_2130_ = lean_uint64_mix_hash(v___x_2128_, v___x_2129_);
v___x_2131_ = lean_uint64_mix_hash(v___y_2127_, v___x_2130_);
v___x_2132_ = lean_uint64_mix_hash(v___x_2125_, v___x_2131_);
v___x_2133_ = l_Lean_Expr_Data_looseBVarRange(v___x_2120_);
v___x_2134_ = lean_uint32_to_nat(v___x_2133_);
v___x_2135_ = l_Lean_Expr_Data_hasFVar(v___x_2120_);
v___x_2136_ = l_Lean_Expr_Data_hasExprMVar(v___x_2120_);
v___x_2137_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2120_);
v___x_2138_ = l_Lean_Expr_Data_hasLevelParam(v___x_2120_);
v___x_2139_ = lean_expr_mk_data(v___x_2132_, v___x_2134_, v___x_2124_, v___x_2135_, v___x_2136_, v___x_2137_, v___x_2138_);
v___x_2140_ = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(v___x_2140_, 0, v_typeName_2117_);
lean_ctor_set(v___x_2140_, 1, v_idx_2118_);
lean_ctor_set(v___x_2140_, 2, v_struct_2119_);
lean_ctor_set_uint64(v___x_2140_, sizeof(void*)*3, v___x_2139_);
return v___x_2140_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__5(lean_object* v_x_2143_){
_start:
{
if (lean_obj_tag(v_x_2143_) == 0)
{
uint8_t v___x_2144_; 
v___x_2144_ = 0;
return v___x_2144_;
}
else
{
lean_object* v_head_2145_; lean_object* v_tail_2146_; uint8_t v___x_2147_; 
v_head_2145_ = lean_ctor_get(v_x_2143_, 0);
v_tail_2146_ = lean_ctor_get(v_x_2143_, 1);
v___x_2147_ = l_Lean_Level_hasMVar(v_head_2145_);
if (v___x_2147_ == 0)
{
v_x_2143_ = v_tail_2146_;
goto _start;
}
else
{
return v___x_2147_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__5___boxed(lean_object* v_x_2149_){
_start:
{
uint8_t v_res_2150_; lean_object* v_r_2151_; 
v_res_2150_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_x_2149_);
lean_dec(v_x_2149_);
v_r_2151_ = lean_box(v_res_2150_);
return v_r_2151_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__6(lean_object* v_x_2152_){
_start:
{
if (lean_obj_tag(v_x_2152_) == 0)
{
uint8_t v___x_2153_; 
v___x_2153_ = 0;
return v___x_2153_;
}
else
{
lean_object* v_head_2154_; lean_object* v_tail_2155_; uint8_t v___x_2156_; 
v_head_2154_ = lean_ctor_get(v_x_2152_, 0);
v_tail_2155_ = lean_ctor_get(v_x_2152_, 1);
v___x_2156_ = l_Lean_Level_hasParam(v_head_2154_);
if (v___x_2156_ == 0)
{
v_x_2152_ = v_tail_2155_;
goto _start;
}
else
{
return v___x_2156_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__6___boxed(lean_object* v_x_2158_){
_start:
{
uint8_t v_res_2159_; lean_object* v_r_2160_; 
v_res_2159_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_x_2158_);
lean_dec(v_x_2158_);
v_r_2160_ = lean_box(v_res_2159_);
return v_r_2160_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t v_x_2161_, lean_object* v_x_2162_){
_start:
{
if (lean_obj_tag(v_x_2162_) == 0)
{
return v_x_2161_;
}
else
{
lean_object* v_head_2163_; lean_object* v_tail_2164_; uint64_t v___x_2165_; uint64_t v___x_2166_; 
v_head_2163_ = lean_ctor_get(v_x_2162_, 0);
v_tail_2164_ = lean_ctor_get(v_x_2162_, 1);
v___x_2165_ = l_Lean_Level_hash(v_head_2163_);
v___x_2166_ = lean_uint64_mix_hash(v_x_2161_, v___x_2165_);
v_x_2161_ = v___x_2166_;
v_x_2162_ = v_tail_2164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object* v_x_2168_, lean_object* v_x_2169_){
_start:
{
uint64_t v_x_1734__boxed_2170_; uint64_t v_res_2171_; lean_object* v_r_2172_; 
v_x_1734__boxed_2170_ = lean_unbox_uint64(v_x_2168_);
lean_dec_ref(v_x_2168_);
v_res_2171_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_1734__boxed_2170_, v_x_2169_);
lean_dec(v_x_2169_);
v_r_2172_ = lean_box_uint64(v_res_2171_);
return v_r_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* v_declName_2173_, lean_object* v_us_2174_){
_start:
{
uint64_t v___x_2175_; uint64_t v___y_2177_; 
v___x_2175_ = 5ULL;
if (lean_obj_tag(v_declName_2173_) == 0)
{
uint64_t v___x_2189_; 
v___x_2189_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
v___y_2177_ = v___x_2189_;
goto v___jp_2176_;
}
else
{
uint64_t v_hash_2190_; 
v_hash_2190_ = lean_ctor_get_uint64(v_declName_2173_, sizeof(void*)*2);
v___y_2177_ = v_hash_2190_;
goto v___jp_2176_;
}
v___jp_2176_:
{
uint64_t v___x_2178_; uint64_t v___x_2179_; uint64_t v___x_2180_; uint64_t v___x_2181_; lean_object* v___x_2182_; uint32_t v___x_2183_; uint8_t v___x_2184_; uint8_t v___x_2185_; uint8_t v___x_2186_; uint64_t v___x_2187_; lean_object* v___x_2188_; 
v___x_2178_ = 7ULL;
v___x_2179_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v___x_2178_, v_us_2174_);
v___x_2180_ = lean_uint64_mix_hash(v___y_2177_, v___x_2179_);
v___x_2181_ = lean_uint64_mix_hash(v___x_2175_, v___x_2180_);
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = 0;
v___x_2184_ = 0;
v___x_2185_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_us_2174_);
v___x_2186_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_us_2174_);
v___x_2187_ = lean_expr_mk_data(v___x_2181_, v___x_2182_, v___x_2183_, v___x_2184_, v___x_2184_, v___x_2185_, v___x_2186_);
v___x_2188_ = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(v___x_2188_, 0, v_declName_2173_);
lean_ctor_set(v___x_2188_, 1, v_us_2174_);
lean_ctor_set_uint64(v___x_2188_, sizeof(void*)*2, v___x_2187_);
return v___x_2188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = lean_unsigned_to_nat(0u);
v___x_2193_ = l_Lean_instReprLevel_repr(v___y_2191_, v___x_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2194_, lean_object* v_x_2195_, lean_object* v_x_2196_){
_start:
{
if (lean_obj_tag(v_x_2196_) == 0)
{
lean_dec(v_x_2194_);
return v_x_2195_;
}
else
{
lean_object* v_head_2197_; lean_object* v_tail_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2209_; 
v_head_2197_ = lean_ctor_get(v_x_2196_, 0);
v_tail_2198_ = lean_ctor_get(v_x_2196_, 1);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_x_2196_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2200_ = v_x_2196_;
v_isShared_2201_ = v_isSharedCheck_2209_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_tail_2198_);
lean_inc(v_head_2197_);
lean_dec(v_x_2196_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2209_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
lean_inc(v_x_2194_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set_tag(v___x_2200_, 5);
lean_ctor_set(v___x_2200_, 1, v_x_2194_);
lean_ctor_set(v___x_2200_, 0, v_x_2195_);
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_x_2195_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_x_2194_);
v___x_2203_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = l_Lean_instReprLevel_repr(v_head_2197_, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2203_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v_x_2195_ = v___x_2206_;
v_x_2196_ = v_tail_2198_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object* v_x_2210_, lean_object* v_x_2211_, lean_object* v_x_2212_){
_start:
{
if (lean_obj_tag(v_x_2212_) == 0)
{
lean_dec(v_x_2210_);
return v_x_2211_;
}
else
{
lean_object* v_head_2213_; lean_object* v_tail_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2225_; 
v_head_2213_ = lean_ctor_get(v_x_2212_, 0);
v_tail_2214_ = lean_ctor_get(v_x_2212_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_x_2212_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2216_ = v_x_2212_;
v_isShared_2217_ = v_isSharedCheck_2225_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_tail_2214_);
lean_inc(v_head_2213_);
lean_dec(v_x_2212_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2225_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
lean_inc(v_x_2210_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set_tag(v___x_2216_, 5);
lean_ctor_set(v___x_2216_, 1, v_x_2210_);
lean_ctor_set(v___x_2216_, 0, v_x_2211_);
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_x_2211_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_x_2210_);
v___x_2219_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2220_ = lean_unsigned_to_nat(0u);
v___x_2221_ = l_Lean_instReprLevel_repr(v_head_2213_, v___x_2220_);
v___x_2222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2219_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(v_x_2210_, v___x_2222_, v_tail_2214_);
return v___x_2223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object* v_x_2226_, lean_object* v_x_2227_){
_start:
{
if (lean_obj_tag(v_x_2226_) == 0)
{
lean_object* v___x_2228_; 
lean_dec(v_x_2227_);
v___x_2228_ = lean_box(0);
return v___x_2228_;
}
else
{
lean_object* v_tail_2229_; 
v_tail_2229_ = lean_ctor_get(v_x_2226_, 1);
if (lean_obj_tag(v_tail_2229_) == 0)
{
lean_object* v_head_2230_; lean_object* v___x_2231_; 
lean_dec(v_x_2227_);
v_head_2230_ = lean_ctor_get(v_x_2226_, 0);
lean_inc(v_head_2230_);
lean_dec_ref_known(v_x_2226_, 2);
v___x_2231_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2230_);
return v___x_2231_;
}
else
{
lean_object* v_head_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
lean_inc(v_tail_2229_);
v_head_2232_ = lean_ctor_get(v_x_2226_, 0);
lean_inc(v_head_2232_);
lean_dec_ref_known(v_x_2226_, 2);
v___x_2233_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2232_);
v___x_2234_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(v_x_2227_, v___x_2233_, v_tail_2229_);
return v___x_2234_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2));
v___x_2247_ = lean_string_length(v___x_2246_);
return v___x_2247_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7);
v___x_2249_ = lean_nat_to_int(v___x_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object* v_a_2254_){
_start:
{
if (lean_obj_tag(v_a_2254_) == 0)
{
lean_object* v___x_2255_; 
v___x_2255_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1));
return v___x_2255_;
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; lean_object* v___x_2265_; 
v___x_2256_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5));
v___x_2257_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(v_a_2254_, v___x_2256_);
v___x_2258_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8);
v___x_2259_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9));
v___x_2260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
lean_ctor_set(v___x_2260_, 1, v___x_2257_);
v___x_2261_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10));
v___x_2262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2260_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2258_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = 0;
v___x_2265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2265_, 0, v___x_2263_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*1, v___x_2264_);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object* v_x_2338_, lean_object* v_prec_2339_){
_start:
{
switch(lean_obj_tag(v_x_2338_))
{
case 0:
{
lean_object* v_deBruijnIndex_2340_; lean_object* v___y_2342_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v_deBruijnIndex_2340_ = lean_ctor_get(v_x_2338_, 0);
lean_inc(v_deBruijnIndex_2340_);
lean_dec_ref_known(v_x_2338_, 1);
v___x_2351_ = lean_unsigned_to_nat(1024u);
v___x_2352_ = lean_nat_dec_le(v___x_2351_, v_prec_2339_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; 
v___x_2353_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2342_ = v___x_2353_;
goto v___jp_2341_;
}
else
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2342_ = v___x_2354_;
goto v___jp_2341_;
}
v___jp_2341_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2343_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__2));
v___x_2344_ = l_Nat_reprFast(v_deBruijnIndex_2340_);
v___x_2345_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
v___x_2346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2343_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
lean_inc(v___y_2342_);
v___x_2347_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___y_2342_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = 0;
v___x_2349_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2349_, 0, v___x_2347_);
lean_ctor_set_uint8(v___x_2349_, sizeof(void*)*1, v___x_2348_);
v___x_2350_ = l_Repr_addAppParen(v___x_2349_, v_prec_2339_);
return v___x_2350_;
}
}
case 1:
{
lean_object* v_fvarId_2355_; lean_object* v___y_2357_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v_fvarId_2355_ = lean_ctor_get(v_x_2338_, 0);
lean_inc(v_fvarId_2355_);
lean_dec_ref_known(v_x_2338_, 1);
v___x_2366_ = lean_unsigned_to_nat(1024u);
v___x_2367_ = lean_nat_dec_le(v___x_2366_, v_prec_2339_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2357_ = v___x_2368_;
goto v___jp_2356_;
}
else
{
lean_object* v___x_2369_; 
v___x_2369_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2357_ = v___x_2369_;
goto v___jp_2356_;
}
v___jp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2358_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__5));
v___x_2359_ = lean_unsigned_to_nat(1024u);
v___x_2360_ = l_Lean_Name_reprPrec(v_fvarId_2355_, v___x_2359_);
v___x_2361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2358_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
lean_inc(v___y_2357_);
v___x_2362_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___y_2357_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
v___x_2363_ = 0;
v___x_2364_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2364_, 0, v___x_2362_);
lean_ctor_set_uint8(v___x_2364_, sizeof(void*)*1, v___x_2363_);
v___x_2365_ = l_Repr_addAppParen(v___x_2364_, v_prec_2339_);
return v___x_2365_;
}
}
case 2:
{
lean_object* v_mvarId_2370_; lean_object* v___y_2372_; lean_object* v___x_2381_; uint8_t v___x_2382_; 
v_mvarId_2370_ = lean_ctor_get(v_x_2338_, 0);
lean_inc(v_mvarId_2370_);
lean_dec_ref_known(v_x_2338_, 1);
v___x_2381_ = lean_unsigned_to_nat(1024u);
v___x_2382_ = lean_nat_dec_le(v___x_2381_, v_prec_2339_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2372_ = v___x_2383_;
goto v___jp_2371_;
}
else
{
lean_object* v___x_2384_; 
v___x_2384_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2372_ = v___x_2384_;
goto v___jp_2371_;
}
v___jp_2371_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2373_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__8));
v___x_2374_ = lean_unsigned_to_nat(1024u);
v___x_2375_ = l_Lean_Name_reprPrec(v_mvarId_2370_, v___x_2374_);
v___x_2376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2373_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
lean_inc(v___y_2372_);
v___x_2377_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___y_2372_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = 0;
v___x_2379_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*1, v___x_2378_);
v___x_2380_ = l_Repr_addAppParen(v___x_2379_, v_prec_2339_);
return v___x_2380_;
}
}
case 3:
{
lean_object* v_u_2385_; lean_object* v___y_2387_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v_u_2385_ = lean_ctor_get(v_x_2338_, 0);
lean_inc(v_u_2385_);
lean_dec_ref_known(v_x_2338_, 1);
v___x_2396_ = lean_unsigned_to_nat(1024u);
v___x_2397_ = lean_nat_dec_le(v___x_2396_, v_prec_2339_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2387_ = v___x_2398_;
goto v___jp_2386_;
}
else
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2387_ = v___x_2399_;
goto v___jp_2386_;
}
v___jp_2386_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2388_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__11));
v___x_2389_ = lean_unsigned_to_nat(1024u);
v___x_2390_ = l_Lean_instReprLevel_repr(v_u_2385_, v___x_2389_);
v___x_2391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2388_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
lean_inc(v___y_2387_);
v___x_2392_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___y_2387_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = 0;
v___x_2394_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*1, v___x_2393_);
v___x_2395_ = l_Repr_addAppParen(v___x_2394_, v_prec_2339_);
return v___x_2395_;
}
}
case 4:
{
lean_object* v_declName_2400_; lean_object* v_us_2401_; lean_object* v___y_2403_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v_declName_2400_ = lean_ctor_get(v_x_2338_, 0);
lean_inc(v_declName_2400_);
v_us_2401_ = lean_ctor_get(v_x_2338_, 1);
lean_inc(v_us_2401_);
lean_dec_ref_known(v_x_2338_, 2);
v___x_2416_ = lean_unsigned_to_nat(1024u);
v___x_2417_ = lean_nat_dec_le(v___x_2416_, v_prec_2339_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2403_ = v___x_2418_;
goto v___jp_2402_;
}
else
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2403_ = v___x_2419_;
goto v___jp_2402_;
}
v___jp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2404_ = lean_box(1);
v___x_2405_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__14));
v___x_2406_ = lean_unsigned_to_nat(1024u);
v___x_2407_ = l_Lean_Name_reprPrec(v_declName_2400_, v___x_2406_);
v___x_2408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2405_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
v___x_2409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
lean_ctor_set(v___x_2409_, 1, v___x_2404_);
v___x_2410_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_us_2401_);
v___x_2411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
lean_inc(v___y_2403_);
v___x_2412_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___y_2403_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = 0;
v___x_2414_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set_uint8(v___x_2414_, sizeof(void*)*1, v___x_2413_);
v___x_2415_ = l_Repr_addAppParen(v___x_2414_, v_prec_2339_);
return v___x_2415_;
}
}
case 5:
{
lean_object* v_fn_2420_; lean_object* v_arg_2421_; lean_object* v___x_2422_; lean_object* v___y_2424_; uint8_t v___x_2436_; 
v_fn_2420_ = lean_ctor_get(v_x_2338_, 0);
lean_inc_ref(v_fn_2420_);
v_arg_2421_ = lean_ctor_get(v_x_2338_, 1);
lean_inc_ref(v_arg_2421_);
lean_dec_ref_known(v_x_2338_, 2);
v___x_2422_ = lean_unsigned_to_nat(1024u);
v___x_2436_ = lean_nat_dec_le(v___x_2422_, v_prec_2339_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2424_ = v___x_2437_;
goto v___jp_2423_;
}
else
{
lean_object* v___x_2438_; 
v___x_2438_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2424_ = v___x_2438_;
goto v___jp_2423_;
}
v___jp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2425_ = lean_box(1);
v___x_2426_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__17));
v___x_2427_ = l_Lean_instReprExpr_repr(v_fn_2420_, v___x_2422_);
v___x_2428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2426_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v___x_2425_);
v___x_2430_ = l_Lean_instReprExpr_repr(v_arg_2421_, v___x_2422_);
v___x_2431_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
lean_inc(v___y_2424_);
v___x_2432_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___y_2424_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = 0;
v___x_2434_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2434_, 0, v___x_2432_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*1, v___x_2433_);
v___x_2435_ = l_Repr_addAppParen(v___x_2434_, v_prec_2339_);
return v___x_2435_;
}
}
case 6:
{
lean_object* v_binderName_2439_; lean_object* v_binderType_2440_; lean_object* v_body_2441_; uint8_t v_binderInfo_2442_; lean_object* v___x_2443_; lean_object* v___y_2445_; uint8_t v___x_2463_; 
v_binderName_2439_ = lean_ctor_get(v_x_2338_, 0);
lean_inc(v_binderName_2439_);
v_binderType_2440_ = lean_ctor_get(v_x_2338_, 1);
lean_inc_ref(v_binderType_2440_);
v_body_2441_ = lean_ctor_get(v_x_2338_, 2);
lean_inc_ref(v_body_2441_);
v_binderInfo_2442_ = lean_ctor_get_uint8(v_x_2338_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2338_, 3);
v___x_2443_ = lean_unsigned_to_nat(1024u);
v___x_2463_ = lean_nat_dec_le(v___x_2443_, v_prec_2339_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2445_ = v___x_2464_;
goto v___jp_2444_;
}
else
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2445_ = v___x_2465_;
goto v___jp_2444_;
}
v___jp_2444_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2446_ = lean_box(1);
v___x_2447_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__20));
v___x_2448_ = l_Lean_Name_reprPrec(v_binderName_2439_, v___x_2443_);
v___x_2449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2447_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
lean_ctor_set(v___x_2450_, 1, v___x_2446_);
v___x_2451_ = l_Lean_instReprExpr_repr(v_binderType_2440_, v___x_2443_);
v___x_2452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2450_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
lean_ctor_set(v___x_2453_, 1, v___x_2446_);
v___x_2454_ = l_Lean_instReprExpr_repr(v_body_2441_, v___x_2443_);
v___x_2455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2453_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
v___x_2456_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
lean_ctor_set(v___x_2456_, 1, v___x_2446_);
v___x_2457_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2442_, v___x_2443_);
v___x_2458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2456_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
lean_inc(v___y_2445_);
v___x_2459_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___y_2445_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = 0;
v___x_2461_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set_uint8(v___x_2461_, sizeof(void*)*1, v___x_2460_);
v___x_2462_ = l_Repr_addAppParen(v___x_2461_, v_prec_2339_);
return v___x_2462_;
}
}
case 7:
{
lean_object* v_binderName_2466_; lean_object* v_binderType_2467_; lean_object* v_body_2468_; uint8_t v_binderInfo_2469_; lean_object* v___x_2470_; lean_object* v___y_2472_; uint8_t v___x_2490_; 
v_binderName_2466_ = lean_ctor_get(v_x_2338_, 0);
lean_inc(v_binderName_2466_);
v_binderType_2467_ = lean_ctor_get(v_x_2338_, 1);
lean_inc_ref(v_binderType_2467_);
v_body_2468_ = lean_ctor_get(v_x_2338_, 2);
lean_inc_ref(v_body_2468_);
v_binderInfo_2469_ = lean_ctor_get_uint8(v_x_2338_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2338_, 3);
v___x_2470_ = lean_unsigned_to_nat(1024u);
v___x_2490_ = lean_nat_dec_le(v___x_2470_, v_prec_2339_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2472_ = v___x_2491_;
goto v___jp_2471_;
}
else
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2472_ = v___x_2492_;
goto v___jp_2471_;
}
v___jp_2471_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; uint8_t v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2473_ = lean_box(1);
v___x_2474_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__23));
v___x_2475_ = l_Lean_Name_reprPrec(v_binderName_2466_, v___x_2470_);
v___x_2476_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2474_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
v___x_2477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
lean_ctor_set(v___x_2477_, 1, v___x_2473_);
v___x_2478_ = l_Lean_instReprExpr_repr(v_binderType_2467_, v___x_2470_);
v___x_2479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v___x_2473_);
v___x_2481_ = l_Lean_instReprExpr_repr(v_body_2468_, v___x_2470_);
v___x_2482_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2480_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
lean_ctor_set(v___x_2483_, 1, v___x_2473_);
v___x_2484_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2469_, v___x_2470_);
v___x_2485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
lean_inc(v___y_2472_);
v___x_2486_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___y_2472_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = 0;
v___x_2488_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*1, v___x_2487_);
v___x_2489_ = l_Repr_addAppParen(v___x_2488_, v_prec_2339_);
return v___x_2489_;
}
}
case 8:
{
lean_object* v_declName_2493_; lean_object* v_type_2494_; lean_object* v_value_2495_; lean_object* v_body_2496_; uint8_t v_nondep_2497_; lean_object* v___x_2498_; lean_object* v___y_2500_; uint8_t v___x_2521_; 
v_declName_2493_ = lean_ctor_get(v_x_2338_, 0);
lean_inc(v_declName_2493_);
v_type_2494_ = lean_ctor_get(v_x_2338_, 1);
lean_inc_ref(v_type_2494_);
v_value_2495_ = lean_ctor_get(v_x_2338_, 2);
lean_inc_ref(v_value_2495_);
v_body_2496_ = lean_ctor_get(v_x_2338_, 3);
lean_inc_ref(v_body_2496_);
v_nondep_2497_ = lean_ctor_get_uint8(v_x_2338_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_x_2338_, 4);
v___x_2498_ = lean_unsigned_to_nat(1024u);
v___x_2521_ = lean_nat_dec_le(v___x_2498_, v_prec_2339_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; 
v___x_2522_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2500_ = v___x_2522_;
goto v___jp_2499_;
}
else
{
lean_object* v___x_2523_; 
v___x_2523_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2500_ = v___x_2523_;
goto v___jp_2499_;
}
v___jp_2499_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2501_ = lean_box(1);
v___x_2502_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__26));
v___x_2503_ = l_Lean_Name_reprPrec(v_declName_2493_, v___x_2498_);
v___x_2504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2502_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
lean_ctor_set(v___x_2505_, 1, v___x_2501_);
v___x_2506_ = l_Lean_instReprExpr_repr(v_type_2494_, v___x_2498_);
v___x_2507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
lean_ctor_set(v___x_2508_, 1, v___x_2501_);
v___x_2509_ = l_Lean_instReprExpr_repr(v_value_2495_, v___x_2498_);
v___x_2510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2508_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
v___x_2511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v___x_2501_);
v___x_2512_ = l_Lean_instReprExpr_repr(v_body_2496_, v___x_2498_);
v___x_2513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
lean_ctor_set(v___x_2514_, 1, v___x_2501_);
v___x_2515_ = l_Bool_repr___redArg(v_nondep_2497_);
v___x_2516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
lean_inc(v___y_2500_);
v___x_2517_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___y_2500_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = 0;
v___x_2519_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set_uint8(v___x_2519_, sizeof(void*)*1, v___x_2518_);
v___x_2520_ = l_Repr_addAppParen(v___x_2519_, v_prec_2339_);
return v___x_2520_;
}
}
case 9:
{
lean_object* v_a_2524_; lean_object* v___y_2526_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v_a_2524_ = lean_ctor_get(v_x_2338_, 0);
lean_inc_ref(v_a_2524_);
lean_dec_ref_known(v_x_2338_, 1);
v___x_2535_ = lean_unsigned_to_nat(1024u);
v___x_2536_ = lean_nat_dec_le(v___x_2535_, v_prec_2339_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; 
v___x_2537_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2526_ = v___x_2537_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2538_; 
v___x_2538_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2526_ = v___x_2538_;
goto v___jp_2525_;
}
v___jp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2527_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__29));
v___x_2528_ = lean_unsigned_to_nat(1024u);
v___x_2529_ = l_Lean_instReprLiteral_repr(v_a_2524_, v___x_2528_);
v___x_2530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2527_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
lean_inc(v___y_2526_);
v___x_2531_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___y_2526_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___x_2532_ = 0;
v___x_2533_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2533_, 0, v___x_2531_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*1, v___x_2532_);
v___x_2534_ = l_Repr_addAppParen(v___x_2533_, v_prec_2339_);
return v___x_2534_;
}
}
case 10:
{
lean_object* v_data_2539_; lean_object* v_expr_2540_; lean_object* v___x_2541_; lean_object* v___y_2543_; uint8_t v___x_2555_; 
v_data_2539_ = lean_ctor_get(v_x_2338_, 0);
lean_inc(v_data_2539_);
v_expr_2540_ = lean_ctor_get(v_x_2338_, 1);
lean_inc_ref(v_expr_2540_);
lean_dec_ref_known(v_x_2338_, 2);
v___x_2541_ = lean_unsigned_to_nat(1024u);
v___x_2555_ = lean_nat_dec_le(v___x_2541_, v_prec_2339_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; 
v___x_2556_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2543_ = v___x_2556_;
goto v___jp_2542_;
}
else
{
lean_object* v___x_2557_; 
v___x_2557_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2543_ = v___x_2557_;
goto v___jp_2542_;
}
v___jp_2542_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2544_ = lean_box(1);
v___x_2545_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__32));
v___x_2546_ = l_Lean_instReprKVMap_repr___redArg(v_data_2539_);
v___x_2547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2545_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
lean_ctor_set(v___x_2548_, 1, v___x_2544_);
v___x_2549_ = l_Lean_instReprExpr_repr(v_expr_2540_, v___x_2541_);
v___x_2550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
lean_inc(v___y_2543_);
v___x_2551_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___y_2543_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = 0;
v___x_2553_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2553_, 0, v___x_2551_);
lean_ctor_set_uint8(v___x_2553_, sizeof(void*)*1, v___x_2552_);
v___x_2554_ = l_Repr_addAppParen(v___x_2553_, v_prec_2339_);
return v___x_2554_;
}
}
default: 
{
lean_object* v_typeName_2558_; lean_object* v_idx_2559_; lean_object* v_struct_2560_; lean_object* v___x_2561_; lean_object* v___y_2563_; uint8_t v___x_2579_; 
v_typeName_2558_ = lean_ctor_get(v_x_2338_, 0);
lean_inc(v_typeName_2558_);
v_idx_2559_ = lean_ctor_get(v_x_2338_, 1);
lean_inc(v_idx_2559_);
v_struct_2560_ = lean_ctor_get(v_x_2338_, 2);
lean_inc_ref(v_struct_2560_);
lean_dec_ref_known(v_x_2338_, 3);
v___x_2561_ = lean_unsigned_to_nat(1024u);
v___x_2579_ = lean_nat_dec_le(v___x_2561_, v_prec_2339_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2563_ = v___x_2580_;
goto v___jp_2562_;
}
else
{
lean_object* v___x_2581_; 
v___x_2581_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2563_ = v___x_2581_;
goto v___jp_2562_;
}
v___jp_2562_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2564_ = lean_box(1);
v___x_2565_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__35));
v___x_2566_ = l_Lean_Name_reprPrec(v_typeName_2558_, v___x_2561_);
v___x_2567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v___x_2564_);
v___x_2569_ = l_Nat_reprFast(v_idx_2559_);
v___x_2570_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
v___x_2571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2568_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v___x_2564_);
v___x_2573_ = l_Lean_instReprExpr_repr(v_struct_2560_, v___x_2561_);
v___x_2574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
lean_inc(v___y_2563_);
v___x_2575_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___y_2563_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = 0;
v___x_2577_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2577_, 0, v___x_2575_);
lean_ctor_set_uint8(v___x_2577_, sizeof(void*)*1, v___x_2576_);
v___x_2578_ = l_Repr_addAppParen(v___x_2577_, v_prec_2339_);
return v___x_2578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object* v_x_2582_, lean_object* v_prec_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_instReprExpr_repr(v_x_2582_, v_prec_2583_);
lean_dec(v_prec_2583_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object* v_a_2585_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_nat_to_int(v_a_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object* v_a_2587_, lean_object* v_n_2588_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_a_2587_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object* v_a_2590_, lean_object* v_n_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0(v_a_2590_, v_n_2591_);
lean_dec(v_n_2591_);
return v_res_2592_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__2(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_box(0);
v___x_2599_ = ((lean_object*)(l_Lean_instInhabitedExpr___closed__1));
v___x_2600_ = l_Lean_Expr_const___override(v___x_2599_, v___x_2598_);
return v___x_2600_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr(void){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* v_x_2614_){
_start:
{
switch(lean_obj_tag(v_x_2614_))
{
case 0:
{
lean_object* v___x_2615_; 
v___x_2615_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__0));
return v___x_2615_;
}
case 1:
{
lean_object* v___x_2616_; 
v___x_2616_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__1));
return v___x_2616_;
}
case 2:
{
lean_object* v___x_2617_; 
v___x_2617_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__2));
return v___x_2617_;
}
case 3:
{
lean_object* v___x_2618_; 
v___x_2618_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__3));
return v___x_2618_;
}
case 4:
{
lean_object* v___x_2619_; 
v___x_2619_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__4));
return v___x_2619_;
}
case 5:
{
lean_object* v___x_2620_; 
v___x_2620_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__5));
return v___x_2620_;
}
case 6:
{
lean_object* v___x_2621_; 
v___x_2621_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__6));
return v___x_2621_;
}
case 7:
{
lean_object* v___x_2622_; 
v___x_2622_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__7));
return v___x_2622_;
}
case 8:
{
lean_object* v___x_2623_; 
v___x_2623_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__8));
return v___x_2623_;
}
case 9:
{
lean_object* v___x_2624_; 
v___x_2624_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__9));
return v___x_2624_;
}
case 10:
{
lean_object* v___x_2625_; 
v___x_2625_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__10));
return v___x_2625_;
}
default: 
{
lean_object* v___x_2626_; 
v___x_2626_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__11));
return v___x_2626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* v_x_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_Expr_ctorName(v_x_2627_);
lean_dec_ref(v_x_2627_);
return v_res_2628_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object* v_e_2629_){
_start:
{
uint64_t v___x_2630_; uint64_t v___x_2631_; 
v___x_2630_ = lean_expr_data(v_e_2629_);
v___x_2631_ = l_Lean_Expr_Data_hash(v___x_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* v_e_2632_){
_start:
{
uint64_t v_res_2633_; lean_object* v_r_2634_; 
v_res_2633_ = l_Lean_Expr_hash(v_e_2632_);
lean_dec_ref(v_e_2632_);
v_r_2634_ = lean_box_uint64(v_res_2633_);
return v_r_2634_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object* v_e_2637_){
_start:
{
uint64_t v___x_2638_; uint8_t v___x_2639_; 
v___x_2638_ = lean_expr_data(v_e_2637_);
v___x_2639_ = l_Lean_Expr_Data_hasFVar(v___x_2638_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* v_e_2640_){
_start:
{
uint8_t v_res_2641_; lean_object* v_r_2642_; 
v_res_2641_ = l_Lean_Expr_hasFVar(v_e_2640_);
lean_dec_ref(v_e_2640_);
v_r_2642_ = lean_box(v_res_2641_);
return v_r_2642_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object* v_e_2643_){
_start:
{
uint64_t v___x_2644_; uint8_t v___x_2645_; 
v___x_2644_ = lean_expr_data(v_e_2643_);
v___x_2645_ = l_Lean_Expr_Data_hasExprMVar(v___x_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* v_e_2646_){
_start:
{
uint8_t v_res_2647_; lean_object* v_r_2648_; 
v_res_2647_ = l_Lean_Expr_hasExprMVar(v_e_2646_);
lean_dec_ref(v_e_2646_);
v_r_2648_ = lean_box(v_res_2647_);
return v_r_2648_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object* v_e_2649_){
_start:
{
uint64_t v___x_2650_; uint8_t v___x_2651_; 
v___x_2650_ = lean_expr_data(v_e_2649_);
v___x_2651_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* v_e_2652_){
_start:
{
uint8_t v_res_2653_; lean_object* v_r_2654_; 
v_res_2653_ = l_Lean_Expr_hasLevelMVar(v_e_2652_);
lean_dec_ref(v_e_2652_);
v_r_2654_ = lean_box(v_res_2653_);
return v_r_2654_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object* v_e_2655_){
_start:
{
uint64_t v_d_2656_; uint8_t v___x_2657_; 
v_d_2656_ = lean_expr_data(v_e_2655_);
v___x_2657_ = l_Lean_Expr_Data_hasExprMVar(v_d_2656_);
if (v___x_2657_ == 0)
{
uint8_t v___x_2658_; 
v___x_2658_ = l_Lean_Expr_Data_hasLevelMVar(v_d_2656_);
return v___x_2658_;
}
else
{
return v___x_2657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* v_e_2659_){
_start:
{
uint8_t v_res_2660_; lean_object* v_r_2661_; 
v_res_2660_ = l_Lean_Expr_hasMVar(v_e_2659_);
lean_dec_ref(v_e_2659_);
v_r_2661_ = lean_box(v_res_2660_);
return v_r_2661_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object* v_e_2662_){
_start:
{
uint64_t v___x_2663_; uint8_t v___x_2664_; 
v___x_2663_ = lean_expr_data(v_e_2662_);
v___x_2664_ = l_Lean_Expr_Data_hasLevelParam(v___x_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* v_e_2665_){
_start:
{
uint8_t v_res_2666_; lean_object* v_r_2667_; 
v_res_2666_ = l_Lean_Expr_hasLevelParam(v_e_2665_);
lean_dec_ref(v_e_2665_);
v_r_2667_ = lean_box(v_res_2666_);
return v_r_2667_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object* v_e_2668_){
_start:
{
uint64_t v___x_2669_; uint8_t v___x_2670_; uint32_t v___x_2671_; 
v___x_2669_ = lean_expr_data(v_e_2668_);
v___x_2670_ = l_Lean_Expr_Data_approxDepth(v___x_2669_);
v___x_2671_ = lean_uint8_to_uint32(v___x_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* v_e_2672_){
_start:
{
uint32_t v_res_2673_; lean_object* v_r_2674_; 
v_res_2673_ = l_Lean_Expr_approxDepth(v_e_2672_);
lean_dec_ref(v_e_2672_);
v_r_2674_ = lean_box_uint32(v_res_2673_);
return v_r_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* v_e_2675_){
_start:
{
uint64_t v___x_2676_; uint32_t v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = lean_expr_data(v_e_2675_);
v___x_2677_ = l_Lean_Expr_Data_looseBVarRange(v___x_2676_);
v___x_2678_ = lean_uint32_to_nat(v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* v_e_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_Expr_looseBVarRange(v_e_2679_);
lean_dec_ref(v_e_2679_);
return v_res_2680_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object* v_e_2681_){
_start:
{
switch(lean_obj_tag(v_e_2681_))
{
case 7:
{
uint8_t v_binderInfo_2682_; 
v_binderInfo_2682_ = lean_ctor_get_uint8(v_e_2681_, sizeof(void*)*3 + 8);
return v_binderInfo_2682_;
}
case 6:
{
uint8_t v_binderInfo_2683_; 
v_binderInfo_2683_ = lean_ctor_get_uint8(v_e_2681_, sizeof(void*)*3 + 8);
return v_binderInfo_2683_;
}
default: 
{
uint8_t v___x_2684_; 
v___x_2684_ = 0;
return v___x_2684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* v_e_2685_){
_start:
{
uint8_t v_res_2686_; lean_object* v_r_2687_; 
v_res_2686_ = l_Lean_Expr_binderInfo(v_e_2685_);
lean_dec_ref(v_e_2685_);
v_r_2687_ = lean_box(v_res_2686_);
return v_r_2687_;
}
}
LEAN_EXPORT uint64_t lean_expr_hash(lean_object* v_a_2688_){
_start:
{
uint64_t v___x_2689_; 
v___x_2689_ = l_Lean_Expr_hash(v_a_2688_);
lean_dec_ref(v_a_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* v_a_2690_){
_start:
{
uint64_t v_res_2691_; lean_object* v_r_2692_; 
v_res_2691_ = lean_expr_hash(v_a_2690_);
v_r_2692_ = lean_box_uint64(v_res_2691_);
return v_r_2692_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object* v_e_2693_){
_start:
{
uint8_t v___x_2694_; 
v___x_2694_ = l_Lean_Expr_hasFVar(v_e_2693_);
lean_dec_ref(v_e_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* v_e_2695_){
_start:
{
uint8_t v_res_2696_; lean_object* v_r_2697_; 
v_res_2696_ = lean_expr_has_fvar(v_e_2695_);
v_r_2697_ = lean_box(v_res_2696_);
return v_r_2697_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object* v_e_2698_){
_start:
{
uint8_t v___x_2699_; 
v___x_2699_ = l_Lean_Expr_hasExprMVar(v_e_2698_);
lean_dec_ref(v_e_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* v_e_2700_){
_start:
{
uint8_t v_res_2701_; lean_object* v_r_2702_; 
v_res_2701_ = lean_expr_has_expr_mvar(v_e_2700_);
v_r_2702_ = lean_box(v_res_2701_);
return v_r_2702_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object* v_e_2703_){
_start:
{
uint8_t v___x_2704_; 
v___x_2704_ = l_Lean_Expr_hasLevelMVar(v_e_2703_);
lean_dec_ref(v_e_2703_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* v_e_2705_){
_start:
{
uint8_t v_res_2706_; lean_object* v_r_2707_; 
v_res_2706_ = lean_expr_has_level_mvar(v_e_2705_);
v_r_2707_ = lean_box(v_res_2706_);
return v_r_2707_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* v_e_2708_){
_start:
{
uint8_t v___x_2709_; 
v___x_2709_ = l_Lean_Expr_hasLevelParam(v_e_2708_);
lean_dec_ref(v_e_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* v_e_2710_){
_start:
{
uint8_t v_res_2711_; lean_object* v_r_2712_; 
v_res_2711_ = lean_expr_has_level_param(v_e_2710_);
v_r_2712_ = lean_box(v_res_2711_);
return v_r_2712_;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* v_e_2713_){
_start:
{
uint64_t v___x_2714_; uint32_t v___x_2715_; 
v___x_2714_ = lean_expr_data(v_e_2713_);
lean_dec_ref(v_e_2713_);
v___x_2715_ = l_Lean_Expr_Data_looseBVarRange(v___x_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* v_e_2716_){
_start:
{
uint32_t v_res_2717_; lean_object* v_r_2718_; 
v_res_2717_ = lean_expr_loose_bvar_range(v_e_2716_);
v_r_2718_ = lean_box_uint32(v_res_2717_);
return v_r_2718_;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* v_e_2719_){
_start:
{
uint8_t v___x_2720_; 
v___x_2720_ = l_Lean_Expr_binderInfo(v_e_2719_);
lean_dec_ref(v_e_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* v_e_2721_){
_start:
{
uint8_t v_res_2722_; lean_object* v_r_2723_; 
v_res_2722_ = lean_expr_binder_info(v_e_2721_);
v_r_2723_ = lean_box(v_res_2722_);
return v_r_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* v_declName_2724_, lean_object* v_us_2725_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_Expr_const___override(v_declName_2724_, v_us_2725_);
return v___x_2726_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2730_ = lean_box(0);
v___x_2731_ = ((lean_object*)(l_Lean_Literal_type___closed__1));
v___x_2732_ = l_Lean_Expr_const___override(v___x_2731_, v___x_2730_);
return v___x_2732_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = lean_box(0);
v___x_2737_ = ((lean_object*)(l_Lean_Literal_type___closed__4));
v___x_2738_ = l_Lean_Expr_const___override(v___x_2737_, v___x_2736_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* v_x_2739_){
_start:
{
if (lean_obj_tag(v_x_2739_) == 0)
{
lean_object* v___x_2740_; 
v___x_2740_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_2740_;
}
else
{
lean_object* v___x_2741_; 
v___x_2741_ = lean_obj_once(&l_Lean_Literal_type___closed__5, &l_Lean_Literal_type___closed__5_once, _init_l_Lean_Literal_type___closed__5);
return v___x_2741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* v_x_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_Literal_type(v_x_2742_);
lean_dec_ref(v_x_2742_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* v_a_2744_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_Literal_type(v_a_2744_);
lean_dec_ref(v_a_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* v_idx_2746_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_Expr_bvar___override(v_idx_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* v_u_2748_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_Expr_sort___override(v_u_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* v_fvarId_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_Expr_fvar___override(v_fvarId_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* v_mvarId_2752_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Lean_Expr_mvar___override(v_mvarId_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* v_m_2754_, lean_object* v_e_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Lean_Expr_mdata___override(v_m_2754_, v_e_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* v_structName_2757_, lean_object* v_idx_2758_, lean_object* v_struct_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_Expr_proj___override(v_structName_2757_, v_idx_2758_, v_struct_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* v_f_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_Expr_app___override(v_f_2761_, v_a_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* v_x_2764_, uint8_t v_bi_2765_, lean_object* v_t_2766_, lean_object* v_b_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Lean_Expr_lam___override(v_x_2764_, v_t_2766_, v_b_2767_, v_bi_2765_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* v_x_2769_, lean_object* v_bi_2770_, lean_object* v_t_2771_, lean_object* v_b_2772_){
_start:
{
uint8_t v_bi_boxed_2773_; lean_object* v_res_2774_; 
v_bi_boxed_2773_ = lean_unbox(v_bi_2770_);
v_res_2774_ = l_Lean_mkLambda(v_x_2769_, v_bi_boxed_2773_, v_t_2771_, v_b_2772_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* v_x_2775_, uint8_t v_bi_2776_, lean_object* v_t_2777_, lean_object* v_b_2778_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Lean_Expr_forallE___override(v_x_2775_, v_t_2777_, v_b_2778_, v_bi_2776_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* v_x_2780_, lean_object* v_bi_2781_, lean_object* v_t_2782_, lean_object* v_b_2783_){
_start:
{
uint8_t v_bi_boxed_2784_; lean_object* v_res_2785_; 
v_bi_boxed_2784_ = lean_unbox(v_bi_2781_);
v_res_2785_ = l_Lean_mkForall(v_x_2780_, v_bi_boxed_2784_, v_t_2782_, v_b_2783_);
return v_res_2785_;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__4(void){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2792_ = lean_box(0);
v___x_2793_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__3));
v___x_2794_ = l_Lean_Expr_const___override(v___x_2793_, v___x_2792_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* v_type_2795_){
_start:
{
lean_object* v___x_2796_; uint8_t v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2796_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2797_ = 0;
v___x_2798_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2799_ = l_Lean_Expr_forallE___override(v___x_2796_, v___x_2798_, v_type_2795_, v___x_2797_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* v_type_2800_){
_start:
{
lean_object* v___x_2801_; uint8_t v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2801_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2802_ = 0;
v___x_2803_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2804_ = l_Lean_Expr_lam___override(v___x_2801_, v___x_2803_, v_type_2800_, v___x_2802_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* v_x_2805_, lean_object* v_t_2806_, lean_object* v_v_2807_, lean_object* v_b_2808_, uint8_t v_nondep_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Lean_Expr_letE___override(v_x_2805_, v_t_2806_, v_v_2807_, v_b_2808_, v_nondep_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* v_x_2811_, lean_object* v_t_2812_, lean_object* v_v_2813_, lean_object* v_b_2814_, lean_object* v_nondep_2815_){
_start:
{
uint8_t v_nondep_boxed_2816_; lean_object* v_res_2817_; 
v_nondep_boxed_2816_ = lean_unbox(v_nondep_2815_);
v_res_2817_ = l_Lean_mkLet(v_x_2811_, v_t_2812_, v_v_2813_, v_b_2814_, v_nondep_boxed_2816_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object* v_x_2818_, lean_object* v_t_2819_, lean_object* v_v_2820_, lean_object* v_b_2821_){
_start:
{
uint8_t v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = 1;
v___x_2823_ = l_Lean_Expr_letE___override(v_x_2818_, v_t_2819_, v_v_2820_, v_b_2821_, v___x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* v_f_2824_, lean_object* v_a_2825_, lean_object* v_b_2826_){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = l_Lean_Expr_app___override(v_f_2824_, v_a_2825_);
v___x_2828_ = l_Lean_Expr_app___override(v___x_2827_, v_b_2826_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* v_f_2829_, lean_object* v_a_2830_, lean_object* v_b_2831_){
_start:
{
lean_object* v___x_2832_; 
v___x_2832_ = l_Lean_mkAppB(v_f_2829_, v_a_2830_, v_b_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* v_f_2833_, lean_object* v_a_2834_, lean_object* v_b_2835_, lean_object* v_c_2836_){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = l_Lean_mkAppB(v_f_2833_, v_a_2834_, v_b_2835_);
v___x_2838_ = l_Lean_Expr_app___override(v___x_2837_, v_c_2836_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* v_f_2839_, lean_object* v_a_2840_, lean_object* v_b_2841_, lean_object* v_c_2842_, lean_object* v_d_2843_){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = l_Lean_mkAppB(v_f_2839_, v_a_2840_, v_b_2841_);
v___x_2845_ = l_Lean_mkAppB(v___x_2844_, v_c_2842_, v_d_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* v_f_2846_, lean_object* v_a_2847_, lean_object* v_b_2848_, lean_object* v_c_2849_, lean_object* v_d_2850_, lean_object* v_e_2851_){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = l_Lean_mkApp4(v_f_2846_, v_a_2847_, v_b_2848_, v_c_2849_, v_d_2850_);
v___x_2853_ = l_Lean_Expr_app___override(v___x_2852_, v_e_2851_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* v_f_2854_, lean_object* v_a_2855_, lean_object* v_b_2856_, lean_object* v_c_2857_, lean_object* v_d_2858_, lean_object* v_e_u2081_2859_, lean_object* v_e_u2082_2860_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = l_Lean_mkApp4(v_f_2854_, v_a_2855_, v_b_2856_, v_c_2857_, v_d_2858_);
v___x_2862_ = l_Lean_mkAppB(v___x_2861_, v_e_u2081_2859_, v_e_u2082_2860_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* v_f_2863_, lean_object* v_a_2864_, lean_object* v_b_2865_, lean_object* v_c_2866_, lean_object* v_d_2867_, lean_object* v_e_u2081_2868_, lean_object* v_e_u2082_2869_, lean_object* v_e_u2083_2870_){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = l_Lean_mkApp4(v_f_2863_, v_a_2864_, v_b_2865_, v_c_2866_, v_d_2867_);
v___x_2872_ = l_Lean_mkApp3(v___x_2871_, v_e_u2081_2868_, v_e_u2082_2869_, v_e_u2083_2870_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* v_f_2873_, lean_object* v_a_2874_, lean_object* v_b_2875_, lean_object* v_c_2876_, lean_object* v_d_2877_, lean_object* v_e_u2081_2878_, lean_object* v_e_u2082_2879_, lean_object* v_e_u2083_2880_, lean_object* v_e_u2084_2881_){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = l_Lean_mkApp4(v_f_2873_, v_a_2874_, v_b_2875_, v_c_2876_, v_d_2877_);
v___x_2883_ = l_Lean_mkApp4(v___x_2882_, v_e_u2081_2878_, v_e_u2082_2879_, v_e_u2083_2880_, v_e_u2084_2881_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* v_f_2884_, lean_object* v_a_2885_, lean_object* v_b_2886_, lean_object* v_c_2887_, lean_object* v_d_2888_, lean_object* v_e_u2081_2889_, lean_object* v_e_u2082_2890_, lean_object* v_e_u2083_2891_, lean_object* v_e_u2084_2892_, lean_object* v_e_u2085_2893_){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = l_Lean_mkApp4(v_f_2884_, v_a_2885_, v_b_2886_, v_c_2887_, v_d_2888_);
v___x_2895_ = l_Lean_mkApp5(v___x_2894_, v_e_u2081_2889_, v_e_u2082_2890_, v_e_u2083_2891_, v_e_u2084_2892_, v_e_u2085_2893_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* v_f_2896_, lean_object* v_a_2897_, lean_object* v_b_2898_, lean_object* v_c_2899_, lean_object* v_d_2900_, lean_object* v_e_u2081_2901_, lean_object* v_e_u2082_2902_, lean_object* v_e_u2083_2903_, lean_object* v_e_u2084_2904_, lean_object* v_e_u2085_2905_, lean_object* v_e_u2086_2906_){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = l_Lean_mkApp4(v_f_2896_, v_a_2897_, v_b_2898_, v_c_2899_, v_d_2900_);
v___x_2908_ = l_Lean_mkApp6(v___x_2907_, v_e_u2081_2901_, v_e_u2082_2902_, v_e_u2083_2903_, v_e_u2084_2904_, v_e_u2085_2905_, v_e_u2086_2906_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* v_l_2909_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Lean_Expr_lit___override(v_l_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* v_n_2911_){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_n_2911_);
v___x_2913_ = l_Lean_Expr_lit___override(v___x_2912_);
return v___x_2913_;
}
}
static lean_object* _init_l_Lean_mkInstOfNatNat___closed__2(void){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2917_ = lean_box(0);
v___x_2918_ = ((lean_object*)(l_Lean_mkInstOfNatNat___closed__1));
v___x_2919_ = l_Lean_Expr_const___override(v___x_2918_, v___x_2917_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object* v_n_2920_){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = lean_obj_once(&l_Lean_mkInstOfNatNat___closed__2, &l_Lean_mkInstOfNatNat___closed__2_once, _init_l_Lean_mkInstOfNatNat___closed__2);
v___x_2922_ = l_Lean_Expr_app___override(v___x_2921_, v_n_2920_);
return v___x_2922_;
}
}
static lean_object* _init_l_Lean_mkNatLitCore___closed__4(void){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_2932_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_2933_ = l_Lean_Expr_const___override(v___x_2932_, v___x_2931_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object* v_n_2934_){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2935_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_2936_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
lean_inc_ref(v_n_2934_);
v___x_2937_ = l_Lean_mkInstOfNatNat(v_n_2934_);
v___x_2938_ = l_Lean_mkApp3(v___x_2935_, v___x_2936_, v_n_2934_, v___x_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* v_n_2939_){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = l_Lean_mkRawNatLit(v_n_2939_);
v___x_2941_ = l_Lean_mkNatLitCore(v___x_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* v_s_2942_){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_s_2942_);
v___x_2944_ = l_Lean_Expr_lit___override(v___x_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* v_idx_2945_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_Expr_bvar___override(v_idx_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* v_fvarId_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Expr_fvar___override(v_fvarId_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object* v_mvarId_2949_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Lean_Expr_mvar___override(v_mvarId_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_2951_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_Expr_sort___override(v_u_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_2953_, lean_object* v_lvls_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Expr_const___override(v_c_2953_, v_lvls_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_Expr_app___override(v_f_2956_, v_a_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* v_n_2959_, lean_object* v_d_2960_, lean_object* v_b_2961_, uint8_t v_bi_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_Expr_lam___override(v_n_2959_, v_d_2960_, v_b_2961_, v_bi_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_2964_, lean_object* v_d_2965_, lean_object* v_b_2966_, lean_object* v_bi_2967_){
_start:
{
uint8_t v_bi_boxed_2968_; lean_object* v_res_2969_; 
v_bi_boxed_2968_ = lean_unbox(v_bi_2967_);
v_res_2969_ = lean_expr_mk_lambda(v_n_2964_, v_d_2965_, v_b_2966_, v_bi_boxed_2968_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* v_n_2970_, lean_object* v_d_2971_, lean_object* v_b_2972_, uint8_t v_bi_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_Expr_forallE___override(v_n_2970_, v_d_2971_, v_b_2972_, v_bi_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_2975_, lean_object* v_d_2976_, lean_object* v_b_2977_, lean_object* v_bi_2978_){
_start:
{
uint8_t v_bi_boxed_2979_; lean_object* v_res_2980_; 
v_bi_boxed_2979_ = lean_unbox(v_bi_2978_);
v_res_2980_ = lean_expr_mk_forall(v_n_2975_, v_d_2976_, v_b_2977_, v_bi_boxed_2979_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* v_n_2981_, lean_object* v_t_2982_, lean_object* v_v_2983_, lean_object* v_b_2984_, uint8_t v_nondep_2985_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Lean_Expr_letE___override(v_n_2981_, v_t_2982_, v_v_2983_, v_b_2984_, v_nondep_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_2987_, lean_object* v_t_2988_, lean_object* v_v_2989_, lean_object* v_b_2990_, lean_object* v_nondep_2991_){
_start:
{
uint8_t v_nondep_boxed_2992_; lean_object* v_res_2993_; 
v_nondep_boxed_2992_ = lean_unbox(v_nondep_2991_);
v_res_2993_ = lean_expr_mk_let(v_n_2987_, v_t_2988_, v_v_2989_, v_b_2990_, v_nondep_boxed_2992_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_2994_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Lean_Expr_lit___override(v_l_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_2996_, lean_object* v_e_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_Expr_mdata___override(v_m_2996_, v_e_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_2999_, lean_object* v_idx_3000_, lean_object* v_struct_3001_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = l_Lean_Expr_proj___override(v_structName_2999_, v_idx_3000_, v_struct_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_3003_, size_t v_i_3004_, size_t v_stop_3005_, lean_object* v_b_3006_){
_start:
{
uint8_t v___x_3007_; 
v___x_3007_ = lean_usize_dec_eq(v_i_3004_, v_stop_3005_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; size_t v___x_3010_; size_t v___x_3011_; 
v___x_3008_ = lean_array_uget_borrowed(v_as_3003_, v_i_3004_);
lean_inc(v___x_3008_);
v___x_3009_ = l_Lean_Expr_app___override(v_b_3006_, v___x_3008_);
v___x_3010_ = ((size_t)1ULL);
v___x_3011_ = lean_usize_add(v_i_3004_, v___x_3010_);
v_i_3004_ = v___x_3011_;
v_b_3006_ = v___x_3009_;
goto _start;
}
else
{
return v_b_3006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_3013_, lean_object* v_i_3014_, lean_object* v_stop_3015_, lean_object* v_b_3016_){
_start:
{
size_t v_i_boxed_3017_; size_t v_stop_boxed_3018_; lean_object* v_res_3019_; 
v_i_boxed_3017_ = lean_unbox_usize(v_i_3014_);
lean_dec(v_i_3014_);
v_stop_boxed_3018_ = lean_unbox_usize(v_stop_3015_);
lean_dec(v_stop_3015_);
v_res_3019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_3013_, v_i_boxed_3017_, v_stop_boxed_3018_, v_b_3016_);
lean_dec_ref(v_as_3013_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_3020_, lean_object* v_args_3021_){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; 
v___x_3022_ = lean_unsigned_to_nat(0u);
v___x_3023_ = lean_array_get_size(v_args_3021_);
v___x_3024_ = lean_nat_dec_lt(v___x_3022_, v___x_3023_);
if (v___x_3024_ == 0)
{
return v_f_3020_;
}
else
{
uint8_t v___x_3025_; 
v___x_3025_ = lean_nat_dec_le(v___x_3023_, v___x_3023_);
if (v___x_3025_ == 0)
{
if (v___x_3024_ == 0)
{
return v_f_3020_;
}
else
{
size_t v___x_3026_; size_t v___x_3027_; lean_object* v___x_3028_; 
v___x_3026_ = ((size_t)0ULL);
v___x_3027_ = lean_usize_of_nat(v___x_3023_);
v___x_3028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3021_, v___x_3026_, v___x_3027_, v_f_3020_);
return v___x_3028_;
}
}
else
{
size_t v___x_3029_; size_t v___x_3030_; lean_object* v___x_3031_; 
v___x_3029_ = ((size_t)0ULL);
v___x_3030_ = lean_usize_of_nat(v___x_3023_);
v___x_3031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3021_, v___x_3029_, v___x_3030_, v_f_3020_);
return v___x_3031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_3032_, lean_object* v_args_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Lean_mkAppN(v_f_3032_, v_args_3033_);
lean_dec_ref(v_args_3033_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_3035_, lean_object* v_args_3036_, lean_object* v_i_3037_, lean_object* v_e_3038_){
_start:
{
uint8_t v___x_3039_; 
v___x_3039_ = lean_nat_dec_lt(v_i_3037_, v_n_3035_);
if (v___x_3039_ == 0)
{
lean_dec(v_i_3037_);
return v_e_3038_;
}
else
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3040_ = lean_unsigned_to_nat(1u);
v___x_3041_ = lean_nat_add(v_i_3037_, v___x_3040_);
v___x_3042_ = l_Lean_instInhabitedExpr;
v___x_3043_ = lean_array_get_borrowed(v___x_3042_, v_args_3036_, v_i_3037_);
lean_dec(v_i_3037_);
lean_inc(v___x_3043_);
v___x_3044_ = l_Lean_Expr_app___override(v_e_3038_, v___x_3043_);
v_i_3037_ = v___x_3041_;
v_e_3038_ = v___x_3044_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_3046_, lean_object* v_args_3047_, lean_object* v_i_3048_, lean_object* v_e_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_3046_, v_args_3047_, v_i_3048_, v_e_3049_);
lean_dec_ref(v_args_3047_);
lean_dec(v_n_3046_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_3051_, lean_object* v_i_3052_, lean_object* v_j_3053_, lean_object* v_args_3054_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_3053_, v_args_3054_, v_i_3052_, v_f_3051_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_3056_, lean_object* v_i_3057_, lean_object* v_j_3058_, lean_object* v_args_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lean_mkAppRange(v_f_3056_, v_i_3057_, v_j_3058_, v_args_3059_);
lean_dec_ref(v_args_3059_);
lean_dec(v_j_3058_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_3061_, size_t v_i_3062_, size_t v_stop_3063_, lean_object* v_b_3064_){
_start:
{
uint8_t v___x_3065_; 
v___x_3065_ = lean_usize_dec_eq(v_i_3062_, v_stop_3063_);
if (v___x_3065_ == 0)
{
size_t v___x_3066_; size_t v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3066_ = ((size_t)1ULL);
v___x_3067_ = lean_usize_sub(v_i_3062_, v___x_3066_);
v___x_3068_ = lean_array_uget_borrowed(v_as_3061_, v___x_3067_);
lean_inc(v___x_3068_);
v___x_3069_ = l_Lean_Expr_app___override(v_b_3064_, v___x_3068_);
v_i_3062_ = v___x_3067_;
v_b_3064_ = v___x_3069_;
goto _start;
}
else
{
return v_b_3064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_3071_, lean_object* v_i_3072_, lean_object* v_stop_3073_, lean_object* v_b_3074_){
_start:
{
size_t v_i_boxed_3075_; size_t v_stop_boxed_3076_; lean_object* v_res_3077_; 
v_i_boxed_3075_ = lean_unbox_usize(v_i_3072_);
lean_dec(v_i_3072_);
v_stop_boxed_3076_ = lean_unbox_usize(v_stop_3073_);
lean_dec(v_stop_3073_);
v_res_3077_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3071_, v_i_boxed_3075_, v_stop_boxed_3076_, v_b_3074_);
lean_dec_ref(v_as_3071_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_3078_, lean_object* v_revArgs_3079_){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; uint8_t v___x_3082_; 
v___x_3080_ = lean_array_get_size(v_revArgs_3079_);
v___x_3081_ = lean_unsigned_to_nat(0u);
v___x_3082_ = lean_nat_dec_lt(v___x_3081_, v___x_3080_);
if (v___x_3082_ == 0)
{
return v_fn_3078_;
}
else
{
size_t v___x_3083_; size_t v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_usize_of_nat(v___x_3080_);
v___x_3084_ = ((size_t)0ULL);
v___x_3085_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_3079_, v___x_3083_, v___x_3084_, v_fn_3078_);
return v___x_3085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_3086_, lean_object* v_revArgs_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_mkAppRev(v_fn_3086_, v_revArgs_3087_);
lean_dec_ref(v_revArgs_3087_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = lean_expr_dbg_to_string(v_e_3090_);
lean_dec_ref(v_e_3090_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_3094_, lean_object* v_b_3095_){
_start:
{
uint8_t v_res_3096_; lean_object* v_r_3097_; 
v_res_3096_ = lean_expr_quick_lt(v_a_3094_, v_b_3095_);
lean_dec_ref(v_b_3095_);
lean_dec_ref(v_a_3094_);
v_r_3097_ = lean_box(v_res_3096_);
return v_r_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_3100_, lean_object* v_b_3101_){
_start:
{
uint8_t v_res_3102_; lean_object* v_r_3103_; 
v_res_3102_ = lean_expr_lt(v_a_3100_, v_b_3101_);
lean_dec_ref(v_b_3101_);
lean_dec_ref(v_a_3100_);
v_r_3103_ = lean_box(v_res_3102_);
return v_r_3103_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* v_a_3104_, lean_object* v_b_3105_){
_start:
{
uint8_t v___x_3106_; 
v___x_3106_ = lean_expr_quick_lt(v_a_3104_, v_b_3105_);
if (v___x_3106_ == 0)
{
uint8_t v___x_3107_; 
v___x_3107_ = lean_expr_quick_lt(v_b_3105_, v_a_3104_);
if (v___x_3107_ == 0)
{
uint8_t v___x_3108_; 
v___x_3108_ = 1;
return v___x_3108_;
}
else
{
uint8_t v___x_3109_; 
v___x_3109_ = 2;
return v___x_3109_;
}
}
else
{
uint8_t v___x_3110_; 
v___x_3110_ = 0;
return v___x_3110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_3111_, lean_object* v_b_3112_){
_start:
{
uint8_t v_res_3113_; lean_object* v_r_3114_; 
v_res_3113_ = l_Lean_Expr_quickComp(v_a_3111_, v_b_3112_);
lean_dec_ref(v_b_3112_);
lean_dec_ref(v_a_3111_);
v_r_3114_ = lean_box(v_res_3113_);
return v_r_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_3117_, lean_object* v_b_3118_){
_start:
{
uint8_t v_res_3119_; lean_object* v_r_3120_; 
v_res_3119_ = lean_expr_eqv(v_a_3117_, v_b_3118_);
lean_dec_ref(v_b_3118_);
lean_dec_ref(v_a_3117_);
v_r_3120_ = lean_box(v_res_3119_);
return v_r_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3125_, lean_object* v_b_3126_){
_start:
{
uint8_t v_res_3127_; lean_object* v_r_3128_; 
v_res_3127_ = lean_expr_equal(v_a_3125_, v_b_3126_);
lean_dec_ref(v_b_3126_);
lean_dec_ref(v_a_3125_);
v_r_3128_ = lean_box(v_res_3127_);
return v_r_3128_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* v_x_3129_){
_start:
{
if (lean_obj_tag(v_x_3129_) == 3)
{
uint8_t v___x_3130_; 
v___x_3130_ = 1;
return v___x_3130_;
}
else
{
uint8_t v___x_3131_; 
v___x_3131_ = 0;
return v___x_3131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3132_){
_start:
{
uint8_t v_res_3133_; lean_object* v_r_3134_; 
v_res_3133_ = l_Lean_Expr_isSort(v_x_3132_);
lean_dec_ref(v_x_3132_);
v_r_3134_ = lean_box(v_res_3133_);
return v_r_3134_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* v_x_3135_){
_start:
{
if (lean_obj_tag(v_x_3135_) == 3)
{
lean_object* v_u_3136_; 
v_u_3136_ = lean_ctor_get(v_x_3135_, 0);
if (lean_obj_tag(v_u_3136_) == 1)
{
uint8_t v___x_3137_; 
v___x_3137_ = 1;
return v___x_3137_;
}
else
{
uint8_t v___x_3138_; 
v___x_3138_ = 0;
return v___x_3138_;
}
}
else
{
uint8_t v___x_3139_; 
v___x_3139_ = 0;
return v___x_3139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3140_){
_start:
{
uint8_t v_res_3141_; lean_object* v_r_3142_; 
v_res_3141_ = l_Lean_Expr_isType(v_x_3140_);
lean_dec_ref(v_x_3140_);
v_r_3142_ = lean_box(v_res_3141_);
return v_r_3142_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* v_x_3143_){
_start:
{
if (lean_obj_tag(v_x_3143_) == 3)
{
lean_object* v_u_3144_; 
v_u_3144_ = lean_ctor_get(v_x_3143_, 0);
if (lean_obj_tag(v_u_3144_) == 1)
{
lean_object* v_a_3145_; 
v_a_3145_ = lean_ctor_get(v_u_3144_, 0);
if (lean_obj_tag(v_a_3145_) == 0)
{
uint8_t v___x_3146_; 
v___x_3146_ = 1;
return v___x_3146_;
}
else
{
uint8_t v___x_3147_; 
v___x_3147_ = 0;
return v___x_3147_;
}
}
else
{
uint8_t v___x_3148_; 
v___x_3148_ = 0;
return v___x_3148_;
}
}
else
{
uint8_t v___x_3149_; 
v___x_3149_ = 0;
return v___x_3149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3150_){
_start:
{
uint8_t v_res_3151_; lean_object* v_r_3152_; 
v_res_3151_ = l_Lean_Expr_isType0(v_x_3150_);
lean_dec_ref(v_x_3150_);
v_r_3152_ = lean_box(v_res_3151_);
return v_r_3152_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* v_x_3153_){
_start:
{
if (lean_obj_tag(v_x_3153_) == 3)
{
lean_object* v_u_3154_; 
v_u_3154_ = lean_ctor_get(v_x_3153_, 0);
if (lean_obj_tag(v_u_3154_) == 0)
{
uint8_t v___x_3155_; 
v___x_3155_ = 1;
return v___x_3155_;
}
else
{
uint8_t v___x_3156_; 
v___x_3156_ = 0;
return v___x_3156_;
}
}
else
{
uint8_t v___x_3157_; 
v___x_3157_ = 0;
return v___x_3157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3158_){
_start:
{
uint8_t v_res_3159_; lean_object* v_r_3160_; 
v_res_3159_ = l_Lean_Expr_isProp(v_x_3158_);
lean_dec_ref(v_x_3158_);
v_r_3160_ = lean_box(v_res_3159_);
return v_r_3160_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3161_){
_start:
{
if (lean_obj_tag(v_x_3161_) == 0)
{
uint8_t v___x_3162_; 
v___x_3162_ = 1;
return v___x_3162_;
}
else
{
uint8_t v___x_3163_; 
v___x_3163_ = 0;
return v___x_3163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3164_){
_start:
{
uint8_t v_res_3165_; lean_object* v_r_3166_; 
v_res_3165_ = l_Lean_Expr_isBVar(v_x_3164_);
lean_dec_ref(v_x_3164_);
v_r_3166_ = lean_box(v_res_3165_);
return v_r_3166_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3167_){
_start:
{
if (lean_obj_tag(v_x_3167_) == 2)
{
uint8_t v___x_3168_; 
v___x_3168_ = 1;
return v___x_3168_;
}
else
{
uint8_t v___x_3169_; 
v___x_3169_ = 0;
return v___x_3169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3170_){
_start:
{
uint8_t v_res_3171_; lean_object* v_r_3172_; 
v_res_3171_ = l_Lean_Expr_isMVar(v_x_3170_);
lean_dec_ref(v_x_3170_);
v_r_3172_ = lean_box(v_res_3171_);
return v_r_3172_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3173_){
_start:
{
if (lean_obj_tag(v_x_3173_) == 1)
{
uint8_t v___x_3174_; 
v___x_3174_ = 1;
return v___x_3174_;
}
else
{
uint8_t v___x_3175_; 
v___x_3175_ = 0;
return v___x_3175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3176_){
_start:
{
uint8_t v_res_3177_; lean_object* v_r_3178_; 
v_res_3177_ = l_Lean_Expr_isFVar(v_x_3176_);
lean_dec_ref(v_x_3176_);
v_r_3178_ = lean_box(v_res_3177_);
return v_r_3178_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* v_x_3179_){
_start:
{
if (lean_obj_tag(v_x_3179_) == 5)
{
uint8_t v___x_3180_; 
v___x_3180_ = 1;
return v___x_3180_;
}
else
{
uint8_t v___x_3181_; 
v___x_3181_ = 0;
return v___x_3181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3182_){
_start:
{
uint8_t v_res_3183_; lean_object* v_r_3184_; 
v_res_3183_ = l_Lean_Expr_isApp(v_x_3182_);
lean_dec_ref(v_x_3182_);
v_r_3184_ = lean_box(v_res_3183_);
return v_r_3184_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* v_x_3185_){
_start:
{
if (lean_obj_tag(v_x_3185_) == 11)
{
uint8_t v___x_3186_; 
v___x_3186_ = 1;
return v___x_3186_;
}
else
{
uint8_t v___x_3187_; 
v___x_3187_ = 0;
return v___x_3187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3188_){
_start:
{
uint8_t v_res_3189_; lean_object* v_r_3190_; 
v_res_3189_ = l_Lean_Expr_isProj(v_x_3188_);
lean_dec_ref(v_x_3188_);
v_r_3190_ = lean_box(v_res_3189_);
return v_r_3190_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* v_x_3191_){
_start:
{
if (lean_obj_tag(v_x_3191_) == 4)
{
uint8_t v___x_3192_; 
v___x_3192_ = 1;
return v___x_3192_;
}
else
{
uint8_t v___x_3193_; 
v___x_3193_ = 0;
return v___x_3193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3194_){
_start:
{
uint8_t v_res_3195_; lean_object* v_r_3196_; 
v_res_3195_ = l_Lean_Expr_isConst(v_x_3194_);
lean_dec_ref(v_x_3194_);
v_r_3196_ = lean_box(v_res_3195_);
return v_r_3196_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3197_, lean_object* v_x_3198_){
_start:
{
if (lean_obj_tag(v_x_3197_) == 4)
{
lean_object* v_declName_3199_; uint8_t v___x_3200_; 
v_declName_3199_ = lean_ctor_get(v_x_3197_, 0);
v___x_3200_ = lean_name_eq(v_declName_3199_, v_x_3198_);
return v___x_3200_;
}
else
{
uint8_t v___x_3201_; 
v___x_3201_ = 0;
return v___x_3201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3202_, lean_object* v_x_3203_){
_start:
{
uint8_t v_res_3204_; lean_object* v_r_3205_; 
v_res_3204_ = l_Lean_Expr_isConstOf(v_x_3202_, v_x_3203_);
lean_dec(v_x_3203_);
lean_dec_ref(v_x_3202_);
v_r_3205_ = lean_box(v_res_3204_);
return v_r_3205_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3206_, lean_object* v_x_3207_){
_start:
{
if (lean_obj_tag(v_x_3206_) == 1)
{
lean_object* v_fvarId_3208_; uint8_t v___x_3209_; 
v_fvarId_3208_ = lean_ctor_get(v_x_3206_, 0);
v___x_3209_ = lean_name_eq(v_fvarId_3208_, v_x_3207_);
return v___x_3209_;
}
else
{
uint8_t v___x_3210_; 
v___x_3210_ = 0;
return v___x_3210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3211_, lean_object* v_x_3212_){
_start:
{
uint8_t v_res_3213_; lean_object* v_r_3214_; 
v_res_3213_ = l_Lean_Expr_isFVarOf(v_x_3211_, v_x_3212_);
lean_dec(v_x_3212_);
lean_dec_ref(v_x_3211_);
v_r_3214_ = lean_box(v_res_3213_);
return v_r_3214_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* v_x_3215_){
_start:
{
if (lean_obj_tag(v_x_3215_) == 7)
{
uint8_t v___x_3216_; 
v___x_3216_ = 1;
return v___x_3216_;
}
else
{
uint8_t v___x_3217_; 
v___x_3217_ = 0;
return v___x_3217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3218_){
_start:
{
uint8_t v_res_3219_; lean_object* v_r_3220_; 
v_res_3219_ = l_Lean_Expr_isForall(v_x_3218_);
lean_dec_ref(v_x_3218_);
v_r_3220_ = lean_box(v_res_3219_);
return v_r_3220_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3221_){
_start:
{
if (lean_obj_tag(v_x_3221_) == 6)
{
uint8_t v___x_3222_; 
v___x_3222_ = 1;
return v___x_3222_;
}
else
{
uint8_t v___x_3223_; 
v___x_3223_ = 0;
return v___x_3223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3224_){
_start:
{
uint8_t v_res_3225_; lean_object* v_r_3226_; 
v_res_3225_ = l_Lean_Expr_isLambda(v_x_3224_);
lean_dec_ref(v_x_3224_);
v_r_3226_ = lean_box(v_res_3225_);
return v_r_3226_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3227_){
_start:
{
switch(lean_obj_tag(v_x_3227_))
{
case 6:
{
uint8_t v___x_3228_; 
v___x_3228_ = 1;
return v___x_3228_;
}
case 7:
{
uint8_t v___x_3229_; 
v___x_3229_ = 1;
return v___x_3229_;
}
default: 
{
uint8_t v___x_3230_; 
v___x_3230_ = 0;
return v___x_3230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3231_){
_start:
{
uint8_t v_res_3232_; lean_object* v_r_3233_; 
v_res_3232_ = l_Lean_Expr_isBinding(v_x_3231_);
lean_dec_ref(v_x_3231_);
v_r_3233_ = lean_box(v_res_3232_);
return v_r_3233_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* v_x_3234_){
_start:
{
if (lean_obj_tag(v_x_3234_) == 8)
{
uint8_t v___x_3235_; 
v___x_3235_ = 1;
return v___x_3235_;
}
else
{
uint8_t v___x_3236_; 
v___x_3236_ = 0;
return v___x_3236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3237_){
_start:
{
uint8_t v_res_3238_; lean_object* v_r_3239_; 
v_res_3238_ = l_Lean_Expr_isLet(v_x_3237_);
lean_dec_ref(v_x_3237_);
v_r_3239_ = lean_box(v_res_3238_);
return v_r_3239_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object* v_x_3240_){
_start:
{
if (lean_obj_tag(v_x_3240_) == 8)
{
uint8_t v_nondep_3241_; 
v_nondep_3241_ = lean_ctor_get_uint8(v_x_3240_, sizeof(void*)*4 + 8);
return v_nondep_3241_;
}
else
{
uint8_t v___x_3242_; 
v___x_3242_ = 0;
return v___x_3242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3243_){
_start:
{
uint8_t v_res_3244_; lean_object* v_r_3245_; 
v_res_3244_ = l_Lean_Expr_isHave(v_x_3243_);
lean_dec_ref(v_x_3243_);
v_r_3245_ = lean_box(v_res_3244_);
return v_r_3245_;
}
}
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object* v_a_3246_){
_start:
{
uint8_t v___x_3247_; 
v___x_3247_ = l_Lean_Expr_isHave(v_a_3246_);
lean_dec_ref(v_a_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3248_){
_start:
{
uint8_t v_res_3249_; lean_object* v_r_3250_; 
v_res_3249_ = lean_expr_is_have(v_a_3248_);
v_r_3250_ = lean_box(v_res_3249_);
return v_r_3250_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* v_x_3251_){
_start:
{
if (lean_obj_tag(v_x_3251_) == 10)
{
uint8_t v___x_3252_; 
v___x_3252_ = 1;
return v___x_3252_;
}
else
{
uint8_t v___x_3253_; 
v___x_3253_ = 0;
return v___x_3253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3254_){
_start:
{
uint8_t v_res_3255_; lean_object* v_r_3256_; 
v_res_3255_ = l_Lean_Expr_isMData(v_x_3254_);
lean_dec_ref(v_x_3254_);
v_r_3256_ = lean_box(v_res_3255_);
return v_r_3256_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* v_x_3257_){
_start:
{
if (lean_obj_tag(v_x_3257_) == 9)
{
uint8_t v___x_3258_; 
v___x_3258_ = 1;
return v___x_3258_;
}
else
{
uint8_t v___x_3259_; 
v___x_3259_ = 0;
return v___x_3259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3260_){
_start:
{
uint8_t v_res_3261_; lean_object* v_r_3262_; 
v_res_3261_ = l_Lean_Expr_isLit(v_x_3260_);
lean_dec_ref(v_x_3260_);
v_r_3262_ = lean_box(v_res_3261_);
return v_r_3262_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3263_){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3264_ = l_Lean_instInhabitedExpr;
v___x_3265_ = lean_panic_fn_borrowed(v___x_3264_, v_msg_3263_);
return v___x_3265_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3269_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3270_ = lean_unsigned_to_nat(15u);
v___x_3271_ = lean_unsigned_to_nat(932u);
v___x_3272_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3273_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3274_ = l_mkPanicMessageWithDecl(v___x_3273_, v___x_3272_, v___x_3271_, v___x_3270_, v___x_3269_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3275_){
_start:
{
if (lean_obj_tag(v_x_3275_) == 5)
{
lean_object* v_fn_3276_; 
v_fn_3276_ = lean_ctor_get(v_x_3275_, 0);
lean_inc_ref(v_fn_3276_);
return v_fn_3276_;
}
else
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3278_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3277_);
return v___x_3278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Lean_Expr_appFn_x21(v_x_3279_);
lean_dec_ref(v_x_3279_);
return v_res_3280_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3282_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3283_ = lean_unsigned_to_nat(15u);
v___x_3284_ = lean_unsigned_to_nat(936u);
v___x_3285_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3286_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3287_ = l_mkPanicMessageWithDecl(v___x_3286_, v___x_3285_, v___x_3284_, v___x_3283_, v___x_3282_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3288_){
_start:
{
if (lean_obj_tag(v_x_3288_) == 5)
{
lean_object* v_arg_3289_; 
v_arg_3289_ = lean_ctor_get(v_x_3288_, 1);
lean_inc_ref(v_arg_3289_);
return v_arg_3289_;
}
else
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3291_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3290_);
return v___x_3291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Lean_Expr_appArg_x21(v_x_3292_);
lean_dec_ref(v_x_3292_);
return v_res_3293_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3295_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3296_ = lean_unsigned_to_nat(17u);
v___x_3297_ = lean_unsigned_to_nat(941u);
v___x_3298_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3299_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3300_ = l_mkPanicMessageWithDecl(v___x_3299_, v___x_3298_, v___x_3297_, v___x_3296_, v___x_3295_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3301_){
_start:
{
switch(lean_obj_tag(v_x_3301_))
{
case 10:
{
lean_object* v_expr_3302_; 
v_expr_3302_ = lean_ctor_get(v_x_3301_, 1);
v_x_3301_ = v_expr_3302_;
goto _start;
}
case 5:
{
lean_object* v_fn_3304_; 
v_fn_3304_ = lean_ctor_get(v_x_3301_, 0);
lean_inc_ref(v_fn_3304_);
return v_fn_3304_;
}
default: 
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3306_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3305_);
return v___x_3306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_Expr_appFn_x21_x27(v_x_3307_);
lean_dec_ref(v_x_3307_);
return v_res_3308_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3310_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3311_ = lean_unsigned_to_nat(17u);
v___x_3312_ = lean_unsigned_to_nat(946u);
v___x_3313_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3314_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3315_ = l_mkPanicMessageWithDecl(v___x_3314_, v___x_3313_, v___x_3312_, v___x_3311_, v___x_3310_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3316_){
_start:
{
switch(lean_obj_tag(v_x_3316_))
{
case 10:
{
lean_object* v_expr_3317_; 
v_expr_3317_ = lean_ctor_get(v_x_3316_, 1);
v_x_3316_ = v_expr_3317_;
goto _start;
}
case 5:
{
lean_object* v_arg_3319_; 
v_arg_3319_ = lean_ctor_get(v_x_3316_, 1);
lean_inc_ref(v_arg_3319_);
return v_arg_3319_;
}
default: 
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3320_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3321_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3320_);
return v___x_3321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_Expr_appArg_x21_x27(v_x_3322_);
lean_dec_ref(v_x_3322_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3324_){
_start:
{
lean_object* v_arg_3325_; 
v_arg_3325_ = lean_ctor_get(v_e_3324_, 1);
lean_inc_ref(v_arg_3325_);
return v_arg_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_Lean_Expr_appArg___redArg(v_e_3326_);
lean_dec_ref(v_e_3326_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3328_, lean_object* v_h_3329_){
_start:
{
lean_object* v_arg_3330_; 
v_arg_3330_ = lean_ctor_get(v_e_3328_, 1);
lean_inc_ref(v_arg_3330_);
return v_arg_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3331_, lean_object* v_h_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_Expr_appArg(v_e_3331_, v_h_3332_);
lean_dec_ref(v_e_3331_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3334_){
_start:
{
lean_object* v_fn_3335_; 
v_fn_3335_ = lean_ctor_get(v_e_3334_, 0);
lean_inc_ref(v_fn_3335_);
return v_fn_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Lean_Expr_appFn___redArg(v_e_3336_);
lean_dec_ref(v_e_3336_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3338_, lean_object* v_h_3339_){
_start:
{
lean_object* v_fn_3340_; 
v_fn_3340_ = lean_ctor_get(v_e_3338_, 0);
lean_inc_ref(v_fn_3340_);
return v_fn_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3341_, lean_object* v_h_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_Expr_appFn(v_e_3341_, v_h_3342_);
lean_dec_ref(v_e_3341_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3344_){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = lean_box(0);
v___x_3346_ = lean_panic_fn_borrowed(v___x_3345_, v_msg_3344_);
return v___x_3346_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3349_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3350_ = lean_unsigned_to_nat(14u);
v___x_3351_ = lean_unsigned_to_nat(958u);
v___x_3352_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3353_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3354_ = l_mkPanicMessageWithDecl(v___x_3353_, v___x_3352_, v___x_3351_, v___x_3350_, v___x_3349_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3355_){
_start:
{
if (lean_obj_tag(v_x_3355_) == 3)
{
lean_object* v_u_3356_; 
v_u_3356_ = lean_ctor_get(v_x_3355_, 0);
lean_inc(v_u_3356_);
return v_u_3356_;
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3358_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3357_);
return v___x_3358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_Expr_sortLevel_x21(v_x_3359_);
lean_dec_ref(v_x_3359_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3361_){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3362_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3363_ = lean_panic_fn_borrowed(v___x_3362_, v_msg_3361_);
return v___x_3363_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3366_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3367_ = lean_unsigned_to_nat(13u);
v___x_3368_ = lean_unsigned_to_nat(962u);
v___x_3369_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3370_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3371_ = l_mkPanicMessageWithDecl(v___x_3370_, v___x_3369_, v___x_3368_, v___x_3367_, v___x_3366_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3372_){
_start:
{
if (lean_obj_tag(v_x_3372_) == 9)
{
lean_object* v_a_3373_; 
v_a_3373_ = lean_ctor_get(v_x_3372_, 0);
lean_inc_ref(v_a_3373_);
return v_a_3373_;
}
else
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3374_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3375_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3374_);
return v___x_3375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_Expr_litValue_x21(v_x_3376_);
lean_dec_ref(v_x_3376_);
return v_res_3377_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3378_){
_start:
{
if (lean_obj_tag(v_x_3378_) == 9)
{
lean_object* v_a_3379_; 
v_a_3379_ = lean_ctor_get(v_x_3378_, 0);
if (lean_obj_tag(v_a_3379_) == 0)
{
uint8_t v___x_3380_; 
v___x_3380_ = 1;
return v___x_3380_;
}
else
{
uint8_t v___x_3381_; 
v___x_3381_ = 0;
return v___x_3381_;
}
}
else
{
uint8_t v___x_3382_; 
v___x_3382_ = 0;
return v___x_3382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3383_){
_start:
{
uint8_t v_res_3384_; lean_object* v_r_3385_; 
v_res_3384_ = l_Lean_Expr_isRawNatLit(v_x_3383_);
lean_dec_ref(v_x_3383_);
v_r_3385_ = lean_box(v_res_3384_);
return v_r_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3386_){
_start:
{
if (lean_obj_tag(v_x_3386_) == 9)
{
lean_object* v_a_3387_; 
v_a_3387_ = lean_ctor_get(v_x_3386_, 0);
lean_inc_ref(v_a_3387_);
lean_dec_ref_known(v_x_3386_, 1);
if (lean_obj_tag(v_a_3387_) == 0)
{
lean_object* v_val_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
v_val_3388_ = lean_ctor_get(v_a_3387_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_a_3387_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v_a_3387_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_val_3388_);
lean_dec(v_a_3387_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
lean_ctor_set_tag(v___x_3390_, 1);
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_val_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
else
{
lean_object* v___x_3396_; 
lean_dec_ref(v_a_3387_);
v___x_3396_ = lean_box(0);
return v___x_3396_;
}
}
else
{
lean_object* v___x_3397_; 
lean_dec_ref(v_x_3386_);
v___x_3397_ = lean_box(0);
return v___x_3397_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3398_){
_start:
{
if (lean_obj_tag(v_x_3398_) == 9)
{
lean_object* v_a_3399_; 
v_a_3399_ = lean_ctor_get(v_x_3398_, 0);
if (lean_obj_tag(v_a_3399_) == 1)
{
uint8_t v___x_3400_; 
v___x_3400_ = 1;
return v___x_3400_;
}
else
{
uint8_t v___x_3401_; 
v___x_3401_ = 0;
return v___x_3401_;
}
}
else
{
uint8_t v___x_3402_; 
v___x_3402_ = 0;
return v___x_3402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3403_){
_start:
{
uint8_t v_res_3404_; lean_object* v_r_3405_; 
v_res_3404_ = l_Lean_Expr_isStringLit(v_x_3403_);
lean_dec_ref(v_x_3403_);
v_r_3405_ = lean_box(v_res_3404_);
return v_r_3405_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3410_){
_start:
{
if (lean_obj_tag(v_x_3410_) == 5)
{
lean_object* v_fn_3411_; 
v_fn_3411_ = lean_ctor_get(v_x_3410_, 0);
if (lean_obj_tag(v_fn_3411_) == 4)
{
lean_object* v_arg_3412_; lean_object* v_declName_3413_; lean_object* v___x_3414_; uint8_t v___x_3415_; 
v_arg_3412_ = lean_ctor_get(v_x_3410_, 1);
v_declName_3413_ = lean_ctor_get(v_fn_3411_, 0);
v___x_3414_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3415_ = lean_name_eq(v_declName_3413_, v___x_3414_);
if (v___x_3415_ == 0)
{
return v___x_3415_;
}
else
{
uint8_t v___x_3416_; 
v___x_3416_ = l_Lean_Expr_isRawNatLit(v_arg_3412_);
return v___x_3416_;
}
}
else
{
uint8_t v___x_3417_; 
v___x_3417_ = 0;
return v___x_3417_;
}
}
else
{
uint8_t v___x_3418_; 
v___x_3418_ = 0;
return v___x_3418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3419_){
_start:
{
uint8_t v_res_3420_; lean_object* v_r_3421_; 
v_res_3420_ = l_Lean_Expr_isCharLit(v_x_3419_);
lean_dec_ref(v_x_3419_);
v_r_3421_ = lean_box(v_res_3420_);
return v_r_3421_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3422_){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = lean_box(0);
v___x_3424_ = lean_panic_fn_borrowed(v___x_3423_, v_msg_3422_);
return v___x_3424_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3427_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3428_ = lean_unsigned_to_nat(17u);
v___x_3429_ = lean_unsigned_to_nat(986u);
v___x_3430_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3431_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3432_ = l_mkPanicMessageWithDecl(v___x_3431_, v___x_3430_, v___x_3429_, v___x_3428_, v___x_3427_);
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3433_){
_start:
{
if (lean_obj_tag(v_x_3433_) == 4)
{
lean_object* v_declName_3434_; 
v_declName_3434_ = lean_ctor_get(v_x_3433_, 0);
lean_inc(v_declName_3434_);
return v_declName_3434_;
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3436_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3435_);
return v___x_3436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_Expr_constName_x21(v_x_3437_);
lean_dec_ref(v_x_3437_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3439_){
_start:
{
if (lean_obj_tag(v_x_3439_) == 4)
{
lean_object* v_declName_3440_; lean_object* v___x_3441_; 
v_declName_3440_ = lean_ctor_get(v_x_3439_, 0);
lean_inc(v_declName_3440_);
v___x_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3441_, 0, v_declName_3440_);
return v___x_3441_;
}
else
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_box(0);
return v___x_3442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_Expr_constName_x3f(v_x_3443_);
lean_dec_ref(v_x_3443_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3445_){
_start:
{
lean_object* v___x_3446_; 
v___x_3446_ = l_Lean_Expr_constName_x3f(v_e_3445_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_box(0);
return v___x_3447_;
}
else
{
lean_object* v_val_3448_; 
v_val_3448_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_val_3448_);
lean_dec_ref_known(v___x_3446_, 1);
return v_val_3448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Expr_constName(v_e_3449_);
lean_dec_ref(v_e_3449_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3451_){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3452_ = lean_box(0);
v___x_3453_ = lean_panic_fn_borrowed(v___x_3452_, v_msg_3451_);
return v___x_3453_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3455_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3456_ = lean_unsigned_to_nat(18u);
v___x_3457_ = lean_unsigned_to_nat(1006u);
v___x_3458_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3459_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3460_ = l_mkPanicMessageWithDecl(v___x_3459_, v___x_3458_, v___x_3457_, v___x_3456_, v___x_3455_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3461_){
_start:
{
if (lean_obj_tag(v_x_3461_) == 4)
{
lean_object* v_us_3462_; 
v_us_3462_ = lean_ctor_get(v_x_3461_, 1);
lean_inc(v_us_3462_);
return v_us_3462_;
}
else
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3464_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3463_);
return v___x_3464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3465_){
_start:
{
lean_object* v_res_3466_; 
v_res_3466_ = l_Lean_Expr_constLevels_x21(v_x_3465_);
lean_dec_ref(v_x_3465_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3467_){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = lean_unsigned_to_nat(0u);
v___x_3469_ = lean_panic_fn_borrowed(v___x_3468_, v_msg_3467_);
return v___x_3469_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3472_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3473_ = lean_unsigned_to_nat(16u);
v___x_3474_ = lean_unsigned_to_nat(1010u);
v___x_3475_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3476_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3477_ = l_mkPanicMessageWithDecl(v___x_3476_, v___x_3475_, v___x_3474_, v___x_3473_, v___x_3472_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3478_){
_start:
{
if (lean_obj_tag(v_x_3478_) == 0)
{
lean_object* v_deBruijnIndex_3479_; 
v_deBruijnIndex_3479_ = lean_ctor_get(v_x_3478_, 0);
lean_inc(v_deBruijnIndex_3479_);
return v_deBruijnIndex_3479_;
}
else
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3481_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3480_);
return v___x_3481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Lean_Expr_bvarIdx_x21(v_x_3482_);
lean_dec_ref(v_x_3482_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3484_){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3485_ = lean_box(0);
v___x_3486_ = lean_panic_fn_borrowed(v___x_3485_, v_msg_3484_);
return v___x_3486_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3489_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3490_ = lean_unsigned_to_nat(14u);
v___x_3491_ = lean_unsigned_to_nat(1014u);
v___x_3492_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3493_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3494_ = l_mkPanicMessageWithDecl(v___x_3493_, v___x_3492_, v___x_3491_, v___x_3490_, v___x_3489_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3495_){
_start:
{
if (lean_obj_tag(v_x_3495_) == 1)
{
lean_object* v_fvarId_3496_; 
v_fvarId_3496_ = lean_ctor_get(v_x_3495_, 0);
lean_inc(v_fvarId_3496_);
return v_fvarId_3496_;
}
else
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3498_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3497_);
return v___x_3498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_Expr_fvarId_x21(v_x_3499_);
lean_dec_ref(v_x_3499_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3501_){
_start:
{
if (lean_obj_tag(v_x_3501_) == 1)
{
lean_object* v_fvarId_3502_; lean_object* v___x_3503_; 
v_fvarId_3502_ = lean_ctor_get(v_x_3501_, 0);
lean_inc(v_fvarId_3502_);
v___x_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3503_, 0, v_fvarId_3502_);
return v___x_3503_;
}
else
{
lean_object* v___x_3504_; 
v___x_3504_ = lean_box(0);
return v___x_3504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l_Lean_Expr_fvarId_x3f(v_x_3505_);
lean_dec_ref(v_x_3505_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3507_){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = lean_box(0);
v___x_3509_ = lean_panic_fn_borrowed(v___x_3508_, v_msg_3507_);
return v___x_3509_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3512_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3513_ = lean_unsigned_to_nat(14u);
v___x_3514_ = lean_unsigned_to_nat(1022u);
v___x_3515_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3516_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3517_ = l_mkPanicMessageWithDecl(v___x_3516_, v___x_3515_, v___x_3514_, v___x_3513_, v___x_3512_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3518_){
_start:
{
if (lean_obj_tag(v_x_3518_) == 2)
{
lean_object* v_mvarId_3519_; 
v_mvarId_3519_ = lean_ctor_get(v_x_3518_, 0);
lean_inc(v_mvarId_3519_);
return v_mvarId_3519_;
}
else
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3521_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3520_);
return v___x_3521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Lean_Expr_mvarId_x21(v_x_3522_);
lean_dec_ref(v_x_3522_);
return v_res_3523_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3526_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3527_ = lean_unsigned_to_nat(23u);
v___x_3528_ = lean_unsigned_to_nat(1027u);
v___x_3529_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3530_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3531_ = l_mkPanicMessageWithDecl(v___x_3530_, v___x_3529_, v___x_3528_, v___x_3527_, v___x_3526_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3532_){
_start:
{
switch(lean_obj_tag(v_x_3532_))
{
case 7:
{
lean_object* v_binderName_3533_; 
v_binderName_3533_ = lean_ctor_get(v_x_3532_, 0);
lean_inc(v_binderName_3533_);
return v_binderName_3533_;
}
case 6:
{
lean_object* v_binderName_3534_; 
v_binderName_3534_ = lean_ctor_get(v_x_3532_, 0);
lean_inc(v_binderName_3534_);
return v_binderName_3534_;
}
default: 
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3536_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3535_);
return v___x_3536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Lean_Expr_bindingName_x21(v_x_3537_);
lean_dec_ref(v_x_3537_);
return v_res_3538_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3540_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3541_ = lean_unsigned_to_nat(23u);
v___x_3542_ = lean_unsigned_to_nat(1032u);
v___x_3543_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3544_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3545_ = l_mkPanicMessageWithDecl(v___x_3544_, v___x_3543_, v___x_3542_, v___x_3541_, v___x_3540_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3546_){
_start:
{
switch(lean_obj_tag(v_x_3546_))
{
case 7:
{
lean_object* v_binderType_3547_; 
v_binderType_3547_ = lean_ctor_get(v_x_3546_, 1);
lean_inc_ref(v_binderType_3547_);
return v_binderType_3547_;
}
case 6:
{
lean_object* v_binderType_3548_; 
v_binderType_3548_ = lean_ctor_get(v_x_3546_, 1);
lean_inc_ref(v_binderType_3548_);
return v_binderType_3548_;
}
default: 
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3550_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3549_);
return v___x_3550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l_Lean_Expr_bindingDomain_x21(v_x_3551_);
lean_dec_ref(v_x_3551_);
return v_res_3552_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3554_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3555_ = lean_unsigned_to_nat(23u);
v___x_3556_ = lean_unsigned_to_nat(1037u);
v___x_3557_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3558_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3559_ = l_mkPanicMessageWithDecl(v___x_3558_, v___x_3557_, v___x_3556_, v___x_3555_, v___x_3554_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3560_){
_start:
{
switch(lean_obj_tag(v_x_3560_))
{
case 7:
{
lean_object* v_body_3561_; 
v_body_3561_ = lean_ctor_get(v_x_3560_, 2);
lean_inc_ref(v_body_3561_);
return v_body_3561_;
}
case 6:
{
lean_object* v_body_3562_; 
v_body_3562_ = lean_ctor_get(v_x_3560_, 2);
lean_inc_ref(v_body_3562_);
return v_body_3562_;
}
default: 
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3564_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3563_);
return v___x_3564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l_Lean_Expr_bindingBody_x21(v_x_3565_);
lean_dec_ref(v_x_3565_);
return v_res_3566_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3567_){
_start:
{
uint8_t v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v___x_3568_ = 0;
v___x_3569_ = lean_box(v___x_3568_);
v___x_3570_ = lean_panic_fn_borrowed(v___x_3569_, v_msg_3567_);
lean_dec(v___x_3569_);
v___x_3571_ = lean_unbox(v___x_3570_);
lean_dec(v___x_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3572_){
_start:
{
uint8_t v_res_3573_; lean_object* v_r_3574_; 
v_res_3573_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3572_);
v_r_3574_ = lean_box(v_res_3573_);
return v_r_3574_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3576_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3577_ = lean_unsigned_to_nat(24u);
v___x_3578_ = lean_unsigned_to_nat(1042u);
v___x_3579_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3580_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3581_ = l_mkPanicMessageWithDecl(v___x_3580_, v___x_3579_, v___x_3578_, v___x_3577_, v___x_3576_);
return v___x_3581_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3582_){
_start:
{
switch(lean_obj_tag(v_x_3582_))
{
case 7:
{
uint8_t v_binderInfo_3583_; 
v_binderInfo_3583_ = lean_ctor_get_uint8(v_x_3582_, sizeof(void*)*3 + 8);
return v_binderInfo_3583_;
}
case 6:
{
uint8_t v_binderInfo_3584_; 
v_binderInfo_3584_ = lean_ctor_get_uint8(v_x_3582_, sizeof(void*)*3 + 8);
return v_binderInfo_3584_;
}
default: 
{
lean_object* v___x_3585_; uint8_t v___x_3586_; 
v___x_3585_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3586_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3585_);
return v___x_3586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3587_){
_start:
{
uint8_t v_res_3588_; lean_object* v_r_3589_; 
v_res_3588_ = l_Lean_Expr_bindingInfo_x21(v_x_3587_);
lean_dec_ref(v_x_3587_);
v_r_3589_ = lean_box(v_res_3588_);
return v_r_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3590_){
_start:
{
lean_object* v_binderName_3591_; 
v_binderName_3591_ = lean_ctor_get(v_x_3590_, 0);
lean_inc(v_binderName_3591_);
return v_binderName_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Lean_Expr_forallName___redArg(v_x_3592_);
lean_dec_ref(v_x_3592_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3594_, lean_object* v_x_3595_){
_start:
{
lean_object* v_binderName_3596_; 
v_binderName_3596_ = lean_ctor_get(v_x_3594_, 0);
lean_inc(v_binderName_3596_);
return v_binderName_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3597_, lean_object* v_x_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_Expr_forallName(v_x_3597_, v_x_3598_);
lean_dec_ref(v_x_3597_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3600_){
_start:
{
lean_object* v_binderType_3601_; 
v_binderType_3601_ = lean_ctor_get(v_x_3600_, 1);
lean_inc_ref(v_binderType_3601_);
return v_binderType_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_Lean_Expr_forallDomain___redArg(v_x_3602_);
lean_dec_ref(v_x_3602_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3604_, lean_object* v_x_3605_){
_start:
{
lean_object* v_binderType_3606_; 
v_binderType_3606_ = lean_ctor_get(v_x_3604_, 1);
lean_inc_ref(v_binderType_3606_);
return v_binderType_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3607_, lean_object* v_x_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_Expr_forallDomain(v_x_3607_, v_x_3608_);
lean_dec_ref(v_x_3607_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3610_){
_start:
{
lean_object* v_body_3611_; 
v_body_3611_ = lean_ctor_get(v_x_3610_, 2);
lean_inc_ref(v_body_3611_);
return v_body_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_Expr_forallBody___redArg(v_x_3612_);
lean_dec_ref(v_x_3612_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3614_, lean_object* v_x_3615_){
_start:
{
lean_object* v_body_3616_; 
v_body_3616_ = lean_ctor_get(v_x_3614_, 2);
lean_inc_ref(v_body_3616_);
return v_body_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3617_, lean_object* v_x_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_Expr_forallBody(v_x_3617_, v_x_3618_);
lean_dec_ref(v_x_3617_);
return v_res_3619_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3620_){
_start:
{
uint8_t v_binderInfo_3621_; 
v_binderInfo_3621_ = lean_ctor_get_uint8(v_x_3620_, sizeof(void*)*3 + 8);
return v_binderInfo_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3622_){
_start:
{
uint8_t v_res_3623_; lean_object* v_r_3624_; 
v_res_3623_ = l_Lean_Expr_forallInfo___redArg(v_x_3622_);
lean_dec_ref(v_x_3622_);
v_r_3624_ = lean_box(v_res_3623_);
return v_r_3624_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3625_, lean_object* v_x_3626_){
_start:
{
uint8_t v_binderInfo_3627_; 
v_binderInfo_3627_ = lean_ctor_get_uint8(v_x_3625_, sizeof(void*)*3 + 8);
return v_binderInfo_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3628_, lean_object* v_x_3629_){
_start:
{
uint8_t v_res_3630_; lean_object* v_r_3631_; 
v_res_3630_ = l_Lean_Expr_forallInfo(v_x_3628_, v_x_3629_);
lean_dec_ref(v_x_3628_);
v_r_3631_ = lean_box(v_res_3630_);
return v_r_3631_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3634_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3635_ = lean_unsigned_to_nat(17u);
v___x_3636_ = lean_unsigned_to_nat(1058u);
v___x_3637_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3638_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3639_ = l_mkPanicMessageWithDecl(v___x_3638_, v___x_3637_, v___x_3636_, v___x_3635_, v___x_3634_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3640_){
_start:
{
if (lean_obj_tag(v_x_3640_) == 8)
{
lean_object* v_declName_3641_; 
v_declName_3641_ = lean_ctor_get(v_x_3640_, 0);
lean_inc(v_declName_3641_);
return v_declName_3641_;
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3642_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3643_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3642_);
return v___x_3643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Lean_Expr_letName_x21(v_x_3644_);
lean_dec_ref(v_x_3644_);
return v_res_3645_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3647_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3648_ = lean_unsigned_to_nat(19u);
v___x_3649_ = lean_unsigned_to_nat(1062u);
v___x_3650_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3651_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3652_ = l_mkPanicMessageWithDecl(v___x_3651_, v___x_3650_, v___x_3649_, v___x_3648_, v___x_3647_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3653_){
_start:
{
if (lean_obj_tag(v_x_3653_) == 8)
{
lean_object* v_type_3654_; 
v_type_3654_ = lean_ctor_get(v_x_3653_, 1);
lean_inc_ref(v_type_3654_);
return v_type_3654_;
}
else
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3656_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3655_);
return v___x_3656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Lean_Expr_letType_x21(v_x_3657_);
lean_dec_ref(v_x_3657_);
return v_res_3658_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3660_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3661_ = lean_unsigned_to_nat(21u);
v___x_3662_ = lean_unsigned_to_nat(1066u);
v___x_3663_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3664_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3665_ = l_mkPanicMessageWithDecl(v___x_3664_, v___x_3663_, v___x_3662_, v___x_3661_, v___x_3660_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3666_){
_start:
{
if (lean_obj_tag(v_x_3666_) == 8)
{
lean_object* v_value_3667_; 
v_value_3667_ = lean_ctor_get(v_x_3666_, 2);
lean_inc_ref(v_value_3667_);
return v_value_3667_;
}
else
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3669_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3668_);
return v___x_3669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lean_Expr_letValue_x21(v_x_3670_);
lean_dec_ref(v_x_3670_);
return v_res_3671_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3673_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3674_ = lean_unsigned_to_nat(23u);
v___x_3675_ = lean_unsigned_to_nat(1070u);
v___x_3676_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3677_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3678_ = l_mkPanicMessageWithDecl(v___x_3677_, v___x_3676_, v___x_3675_, v___x_3674_, v___x_3673_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3679_){
_start:
{
if (lean_obj_tag(v_x_3679_) == 8)
{
lean_object* v_body_3680_; 
v_body_3680_ = lean_ctor_get(v_x_3679_, 3);
lean_inc_ref(v_body_3680_);
return v_body_3680_;
}
else
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3682_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3681_);
return v___x_3682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l_Lean_Expr_letBody_x21(v_x_3683_);
lean_dec_ref(v_x_3683_);
return v_res_3684_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3685_){
_start:
{
uint8_t v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; uint8_t v___x_3689_; 
v___x_3686_ = 0;
v___x_3687_ = lean_box(v___x_3686_);
v___x_3688_ = lean_panic_fn_borrowed(v___x_3687_, v_msg_3685_);
lean_dec(v___x_3687_);
v___x_3689_ = lean_unbox(v___x_3688_);
lean_dec(v___x_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3690_){
_start:
{
uint8_t v_res_3691_; lean_object* v_r_3692_; 
v_res_3691_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3690_);
v_r_3692_ = lean_box(v_res_3691_);
return v_r_3692_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3694_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3695_ = lean_unsigned_to_nat(27u);
v___x_3696_ = lean_unsigned_to_nat(1074u);
v___x_3697_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3698_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3699_ = l_mkPanicMessageWithDecl(v___x_3698_, v___x_3697_, v___x_3696_, v___x_3695_, v___x_3694_);
return v___x_3699_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3700_){
_start:
{
if (lean_obj_tag(v_x_3700_) == 8)
{
uint8_t v_nondep_3701_; 
v_nondep_3701_ = lean_ctor_get_uint8(v_x_3700_, sizeof(void*)*4 + 8);
return v_nondep_3701_;
}
else
{
lean_object* v___x_3702_; uint8_t v___x_3703_; 
v___x_3702_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3703_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3702_);
return v___x_3703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3704_){
_start:
{
uint8_t v_res_3705_; lean_object* v_r_3706_; 
v_res_3705_ = l_Lean_Expr_letNondep_x21(v_x_3704_);
lean_dec_ref(v_x_3704_);
v_r_3706_ = lean_box(v_res_3705_);
return v_r_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3707_){
_start:
{
if (lean_obj_tag(v_x_3707_) == 10)
{
lean_object* v_expr_3708_; 
v_expr_3708_ = lean_ctor_get(v_x_3707_, 1);
v_x_3707_ = v_expr_3708_;
goto _start;
}
else
{
lean_inc_ref(v_x_3707_);
return v_x_3707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Lean_Expr_consumeMData(v_x_3710_);
lean_dec_ref(v_x_3710_);
return v_res_3711_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3714_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3715_ = lean_unsigned_to_nat(17u);
v___x_3716_ = lean_unsigned_to_nat(1082u);
v___x_3717_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3718_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3719_ = l_mkPanicMessageWithDecl(v___x_3718_, v___x_3717_, v___x_3716_, v___x_3715_, v___x_3714_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3720_){
_start:
{
if (lean_obj_tag(v_x_3720_) == 10)
{
lean_object* v_expr_3721_; 
v_expr_3721_ = lean_ctor_get(v_x_3720_, 1);
lean_inc_ref(v_expr_3721_);
return v_expr_3721_;
}
else
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3723_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3722_);
return v___x_3723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lean_Expr_mdataExpr_x21(v_x_3724_);
lean_dec_ref(v_x_3724_);
return v_res_3725_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3728_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3729_ = lean_unsigned_to_nat(18u);
v___x_3730_ = lean_unsigned_to_nat(1086u);
v___x_3731_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3732_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3733_ = l_mkPanicMessageWithDecl(v___x_3732_, v___x_3731_, v___x_3730_, v___x_3729_, v___x_3728_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3734_){
_start:
{
if (lean_obj_tag(v_x_3734_) == 11)
{
lean_object* v_struct_3735_; 
v_struct_3735_ = lean_ctor_get(v_x_3734_, 2);
lean_inc_ref(v_struct_3735_);
return v_struct_3735_;
}
else
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3737_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3736_);
return v___x_3737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l_Lean_Expr_projExpr_x21(v_x_3738_);
lean_dec_ref(v_x_3738_);
return v_res_3739_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3741_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3742_ = lean_unsigned_to_nat(18u);
v___x_3743_ = lean_unsigned_to_nat(1090u);
v___x_3744_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3745_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3746_ = l_mkPanicMessageWithDecl(v___x_3745_, v___x_3744_, v___x_3743_, v___x_3742_, v___x_3741_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3747_){
_start:
{
if (lean_obj_tag(v_x_3747_) == 11)
{
lean_object* v_idx_3748_; 
v_idx_3748_ = lean_ctor_get(v_x_3747_, 1);
lean_inc(v_idx_3748_);
return v_idx_3748_;
}
else
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3749_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3750_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3749_);
return v___x_3750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3751_){
_start:
{
lean_object* v_res_3752_; 
v_res_3752_ = l_Lean_Expr_projIdx_x21(v_x_3751_);
lean_dec_ref(v_x_3751_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3753_){
_start:
{
if (lean_obj_tag(v_x_3753_) == 7)
{
lean_object* v_body_3754_; 
v_body_3754_ = lean_ctor_get(v_x_3753_, 2);
v_x_3753_ = v_body_3754_;
goto _start;
}
else
{
lean_inc_ref(v_x_3753_);
return v_x_3753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l_Lean_Expr_getForallBody(v_x_3756_);
lean_dec_ref(v_x_3756_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3758_, lean_object* v_x_3759_){
_start:
{
lean_object* v_zero_3760_; uint8_t v_isZero_3761_; 
v_zero_3760_ = lean_unsigned_to_nat(0u);
v_isZero_3761_ = lean_nat_dec_eq(v_x_3758_, v_zero_3760_);
if (v_isZero_3761_ == 1)
{
lean_dec(v_x_3758_);
lean_inc_ref(v_x_3759_);
return v_x_3759_;
}
else
{
if (lean_obj_tag(v_x_3759_) == 7)
{
lean_object* v_body_3762_; lean_object* v_one_3763_; lean_object* v_n_3764_; 
v_body_3762_ = lean_ctor_get(v_x_3759_, 2);
v_one_3763_ = lean_unsigned_to_nat(1u);
v_n_3764_ = lean_nat_sub(v_x_3758_, v_one_3763_);
lean_dec(v_x_3758_);
v_x_3758_ = v_n_3764_;
v_x_3759_ = v_body_3762_;
goto _start;
}
else
{
lean_dec(v_x_3758_);
lean_inc_ref(v_x_3759_);
return v_x_3759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3766_, lean_object* v_x_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3766_, v_x_3767_);
lean_dec_ref(v_x_3767_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3769_){
_start:
{
if (lean_obj_tag(v_x_3769_) == 7)
{
lean_object* v_binderName_3770_; lean_object* v_body_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v_binderName_3770_ = lean_ctor_get(v_x_3769_, 0);
v_body_3771_ = lean_ctor_get(v_x_3769_, 2);
v___x_3772_ = l_Lean_Expr_getForallBinderNames(v_body_3771_);
lean_inc(v_binderName_3770_);
v___x_3773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3773_, 0, v_binderName_3770_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
return v___x_3773_;
}
else
{
lean_object* v___x_3774_; 
v___x_3774_ = lean_box(0);
return v___x_3774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Lean_Expr_getForallBinderNames(v_x_3775_);
lean_dec_ref(v_x_3775_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3777_){
_start:
{
switch(lean_obj_tag(v_x_3777_))
{
case 10:
{
lean_object* v_expr_3778_; 
v_expr_3778_ = lean_ctor_get(v_x_3777_, 1);
v_x_3777_ = v_expr_3778_;
goto _start;
}
case 7:
{
lean_object* v_body_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v_body_3780_ = lean_ctor_get(v_x_3777_, 2);
v___x_3781_ = l_Lean_Expr_getNumHeadForalls(v_body_3780_);
v___x_3782_ = lean_unsigned_to_nat(1u);
v___x_3783_ = lean_nat_add(v___x_3781_, v___x_3782_);
lean_dec(v___x_3781_);
return v___x_3783_;
}
default: 
{
lean_object* v___x_3784_; 
v___x_3784_ = lean_unsigned_to_nat(0u);
return v___x_3784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Lean_Expr_getNumHeadForalls(v_x_3785_);
lean_dec_ref(v_x_3785_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3787_){
_start:
{
if (lean_obj_tag(v_x_3787_) == 5)
{
lean_object* v_fn_3788_; 
v_fn_3788_ = lean_ctor_get(v_x_3787_, 0);
v_x_3787_ = v_fn_3788_;
goto _start;
}
else
{
lean_inc_ref(v_x_3787_);
return v_x_3787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l_Lean_Expr_getAppFn(v_x_3790_);
lean_dec_ref(v_x_3790_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3792_){
_start:
{
switch(lean_obj_tag(v_x_3792_))
{
case 5:
{
lean_object* v_fn_3793_; 
v_fn_3793_ = lean_ctor_get(v_x_3792_, 0);
v_x_3792_ = v_fn_3793_;
goto _start;
}
case 10:
{
lean_object* v_expr_3795_; 
v_expr_3795_ = lean_ctor_get(v_x_3792_, 1);
v_x_3792_ = v_expr_3795_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3792_);
return v_x_3792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l_Lean_Expr_getAppFn_x27(v_x_3797_);
lean_dec_ref(v_x_3797_);
return v_res_3798_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3799_, lean_object* v_n_3800_){
_start:
{
lean_object* v___x_3801_; 
v___x_3801_ = l_Lean_Expr_getAppFn(v_e_3799_);
if (lean_obj_tag(v___x_3801_) == 4)
{
lean_object* v_declName_3802_; uint8_t v___x_3803_; 
v_declName_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_declName_3802_);
lean_dec_ref_known(v___x_3801_, 2);
v___x_3803_ = lean_name_eq(v_declName_3802_, v_n_3800_);
lean_dec(v_declName_3802_);
return v___x_3803_;
}
else
{
uint8_t v___x_3804_; 
lean_dec_ref(v___x_3801_);
v___x_3804_ = 0;
return v___x_3804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3805_, lean_object* v_n_3806_){
_start:
{
uint8_t v_res_3807_; lean_object* v_r_3808_; 
v_res_3807_ = l_Lean_Expr_isAppOf(v_e_3805_, v_n_3806_);
lean_dec(v_n_3806_);
lean_dec_ref(v_e_3805_);
v_r_3808_ = lean_box(v_res_3807_);
return v_r_3808_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3809_, lean_object* v_x_3810_, lean_object* v_x_3811_){
_start:
{
switch(lean_obj_tag(v_x_3809_))
{
case 4:
{
lean_object* v_declName_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v_declName_3812_ = lean_ctor_get(v_x_3809_, 0);
v___x_3813_ = lean_unsigned_to_nat(0u);
v___x_3814_ = lean_nat_dec_eq(v_x_3811_, v___x_3813_);
lean_dec(v_x_3811_);
if (v___x_3814_ == 0)
{
return v___x_3814_;
}
else
{
uint8_t v___x_3815_; 
v___x_3815_ = lean_name_eq(v_declName_3812_, v_x_3810_);
return v___x_3815_;
}
}
case 5:
{
lean_object* v_fn_3816_; lean_object* v_zero_3817_; uint8_t v_isZero_3818_; 
v_fn_3816_ = lean_ctor_get(v_x_3809_, 0);
v_zero_3817_ = lean_unsigned_to_nat(0u);
v_isZero_3818_ = lean_nat_dec_eq(v_x_3811_, v_zero_3817_);
if (v_isZero_3818_ == 0)
{
lean_object* v_one_3819_; lean_object* v_n_3820_; 
v_one_3819_ = lean_unsigned_to_nat(1u);
v_n_3820_ = lean_nat_sub(v_x_3811_, v_one_3819_);
lean_dec(v_x_3811_);
v_x_3809_ = v_fn_3816_;
v_x_3811_ = v_n_3820_;
goto _start;
}
else
{
uint8_t v___x_3822_; 
lean_dec(v_x_3811_);
v___x_3822_ = 0;
return v___x_3822_;
}
}
default: 
{
uint8_t v___x_3823_; 
lean_dec(v_x_3811_);
v___x_3823_ = 0;
return v___x_3823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3824_, lean_object* v_x_3825_, lean_object* v_x_3826_){
_start:
{
uint8_t v_res_3827_; lean_object* v_r_3828_; 
v_res_3827_ = l_Lean_Expr_isAppOfArity(v_x_3824_, v_x_3825_, v_x_3826_);
lean_dec(v_x_3825_);
lean_dec_ref(v_x_3824_);
v_r_3828_ = lean_box(v_res_3827_);
return v_r_3828_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3829_, lean_object* v_x_3830_, lean_object* v_x_3831_){
_start:
{
switch(lean_obj_tag(v_x_3829_))
{
case 10:
{
lean_object* v_expr_3832_; 
v_expr_3832_ = lean_ctor_get(v_x_3829_, 1);
v_x_3829_ = v_expr_3832_;
goto _start;
}
case 4:
{
lean_object* v_declName_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; 
v_declName_3834_ = lean_ctor_get(v_x_3829_, 0);
v___x_3835_ = lean_unsigned_to_nat(0u);
v___x_3836_ = lean_nat_dec_eq(v_x_3831_, v___x_3835_);
lean_dec(v_x_3831_);
if (v___x_3836_ == 0)
{
return v___x_3836_;
}
else
{
uint8_t v___x_3837_; 
v___x_3837_ = lean_name_eq(v_declName_3834_, v_x_3830_);
return v___x_3837_;
}
}
case 5:
{
lean_object* v_fn_3838_; lean_object* v_zero_3839_; uint8_t v_isZero_3840_; 
v_fn_3838_ = lean_ctor_get(v_x_3829_, 0);
v_zero_3839_ = lean_unsigned_to_nat(0u);
v_isZero_3840_ = lean_nat_dec_eq(v_x_3831_, v_zero_3839_);
if (v_isZero_3840_ == 0)
{
lean_object* v_one_3841_; lean_object* v_n_3842_; 
v_one_3841_ = lean_unsigned_to_nat(1u);
v_n_3842_ = lean_nat_sub(v_x_3831_, v_one_3841_);
lean_dec(v_x_3831_);
v_x_3829_ = v_fn_3838_;
v_x_3831_ = v_n_3842_;
goto _start;
}
else
{
uint8_t v___x_3844_; 
lean_dec(v_x_3831_);
v___x_3844_ = 0;
return v___x_3844_;
}
}
default: 
{
uint8_t v___x_3845_; 
lean_dec(v_x_3831_);
v___x_3845_ = 0;
return v___x_3845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3846_, lean_object* v_x_3847_, lean_object* v_x_3848_){
_start:
{
uint8_t v_res_3849_; lean_object* v_r_3850_; 
v_res_3849_ = l_Lean_Expr_isAppOfArity_x27(v_x_3846_, v_x_3847_, v_x_3848_);
lean_dec(v_x_3847_);
lean_dec_ref(v_x_3846_);
v_r_3850_ = lean_box(v_res_3849_);
return v_r_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3851_, lean_object* v_x_3852_){
_start:
{
if (lean_obj_tag(v_x_3851_) == 5)
{
lean_object* v_fn_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v_fn_3853_ = lean_ctor_get(v_x_3851_, 0);
v___x_3854_ = lean_unsigned_to_nat(1u);
v___x_3855_ = lean_nat_add(v_x_3852_, v___x_3854_);
lean_dec(v_x_3852_);
v_x_3851_ = v_fn_3853_;
v_x_3852_ = v___x_3855_;
goto _start;
}
else
{
return v_x_3852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3857_, lean_object* v_x_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3857_, v_x_3858_);
lean_dec_ref(v_x_3857_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3860_){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = lean_unsigned_to_nat(0u);
v___x_3862_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3860_, v___x_3861_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Lean_Expr_getAppNumArgs(v_e_3863_);
lean_dec_ref(v_e_3863_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
switch(lean_obj_tag(v_a_3865_))
{
case 10:
{
lean_object* v_expr_3867_; 
v_expr_3867_ = lean_ctor_get(v_a_3865_, 1);
v_a_3865_ = v_expr_3867_;
goto _start;
}
case 5:
{
lean_object* v_fn_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v_fn_3869_ = lean_ctor_get(v_a_3865_, 0);
v___x_3870_ = lean_unsigned_to_nat(1u);
v___x_3871_ = lean_nat_add(v_a_3866_, v___x_3870_);
lean_dec(v_a_3866_);
v_a_3865_ = v_fn_3869_;
v_a_3866_ = v___x_3871_;
goto _start;
}
default: 
{
return v_a_3866_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3873_, v_a_3874_);
lean_dec_ref(v_a_3873_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3876_){
_start:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = lean_unsigned_to_nat(0u);
v___x_3878_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3876_, v___x_3877_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3879_);
lean_dec_ref(v_e_3879_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3881_, lean_object* v_x_3882_){
_start:
{
lean_object* v_zero_3883_; uint8_t v_isZero_3884_; 
v_zero_3883_ = lean_unsigned_to_nat(0u);
v_isZero_3884_ = lean_nat_dec_eq(v_x_3881_, v_zero_3883_);
if (v_isZero_3884_ == 0)
{
if (lean_obj_tag(v_x_3882_) == 5)
{
lean_object* v_fn_3885_; lean_object* v_one_3886_; lean_object* v_n_3887_; 
v_fn_3885_ = lean_ctor_get(v_x_3882_, 0);
v_one_3886_ = lean_unsigned_to_nat(1u);
v_n_3887_ = lean_nat_sub(v_x_3881_, v_one_3886_);
lean_dec(v_x_3881_);
v_x_3881_ = v_n_3887_;
v_x_3882_ = v_fn_3885_;
goto _start;
}
else
{
lean_dec(v_x_3881_);
lean_inc_ref(v_x_3882_);
return v_x_3882_;
}
}
else
{
lean_dec(v_x_3881_);
lean_inc_ref(v_x_3882_);
return v_x_3882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_3889_, lean_object* v_x_3890_){
_start:
{
lean_object* v_res_3891_; 
v_res_3891_ = l_Lean_Expr_getBoundedAppFn(v_x_3889_, v_x_3890_);
lean_dec_ref(v_x_3890_);
return v_res_3891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_3892_, lean_object* v_x_3893_, lean_object* v_x_3894_){
_start:
{
if (lean_obj_tag(v_x_3892_) == 5)
{
lean_object* v_fn_3895_; lean_object* v_arg_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v_fn_3895_ = lean_ctor_get(v_x_3892_, 0);
lean_inc_ref(v_fn_3895_);
v_arg_3896_ = lean_ctor_get(v_x_3892_, 1);
lean_inc_ref(v_arg_3896_);
lean_dec_ref_known(v_x_3892_, 2);
v___x_3897_ = lean_array_set(v_x_3893_, v_x_3894_, v_arg_3896_);
v___x_3898_ = lean_unsigned_to_nat(1u);
v___x_3899_ = lean_nat_sub(v_x_3894_, v___x_3898_);
lean_dec(v_x_3894_);
v_x_3892_ = v_fn_3895_;
v_x_3893_ = v___x_3897_;
v_x_3894_ = v___x_3899_;
goto _start;
}
else
{
lean_dec(v_x_3894_);
lean_dec_ref(v_x_3892_);
return v_x_3893_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_3901_; lean_object* v_dummy_3902_; 
v___x_3901_ = lean_box(0);
v_dummy_3902_ = l_Lean_Expr_sort___override(v___x_3901_);
return v_dummy_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_3903_){
_start:
{
lean_object* v_dummy_3904_; lean_object* v_nargs_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v_dummy_3904_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3905_ = l_Lean_Expr_getAppNumArgs(v_e_3903_);
lean_inc(v_nargs_3905_);
v___x_3906_ = lean_mk_array(v_nargs_3905_, v_dummy_3904_);
v___x_3907_ = lean_unsigned_to_nat(1u);
v___x_3908_ = lean_nat_sub(v_nargs_3905_, v___x_3907_);
lean_dec(v_nargs_3905_);
v___x_3909_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3903_, v___x_3906_, v___x_3908_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_3910_, lean_object* v_x_3911_, lean_object* v_x_3912_){
_start:
{
if (lean_obj_tag(v_x_3910_) == 5)
{
lean_object* v_fn_3913_; lean_object* v_arg_3914_; lean_object* v_zero_3915_; uint8_t v_isZero_3916_; 
v_fn_3913_ = lean_ctor_get(v_x_3910_, 0);
lean_inc_ref(v_fn_3913_);
v_arg_3914_ = lean_ctor_get(v_x_3910_, 1);
lean_inc_ref(v_arg_3914_);
lean_dec_ref_known(v_x_3910_, 2);
v_zero_3915_ = lean_unsigned_to_nat(0u);
v_isZero_3916_ = lean_nat_dec_eq(v_x_3912_, v_zero_3915_);
if (v_isZero_3916_ == 0)
{
lean_object* v_one_3917_; lean_object* v_n_3918_; lean_object* v___x_3919_; 
v_one_3917_ = lean_unsigned_to_nat(1u);
v_n_3918_ = lean_nat_sub(v_x_3912_, v_one_3917_);
lean_dec(v_x_3912_);
v___x_3919_ = lean_array_set(v_x_3911_, v_n_3918_, v_arg_3914_);
v_x_3910_ = v_fn_3913_;
v_x_3911_ = v___x_3919_;
v_x_3912_ = v_n_3918_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3914_);
lean_dec_ref(v_fn_3913_);
lean_dec(v_x_3912_);
return v_x_3911_;
}
}
else
{
lean_dec(v_x_3912_);
lean_dec_ref(v_x_3910_);
return v_x_3911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_3921_, lean_object* v_e_3922_){
_start:
{
lean_object* v_dummy_3923_; lean_object* v___y_3925_; lean_object* v___x_3928_; uint8_t v___x_3929_; 
v_dummy_3923_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_3928_ = l_Lean_Expr_getAppNumArgs(v_e_3922_);
v___x_3929_ = lean_nat_dec_le(v_maxArgs_3921_, v___x_3928_);
if (v___x_3929_ == 0)
{
lean_dec(v_maxArgs_3921_);
v___y_3925_ = v___x_3928_;
goto v___jp_3924_;
}
else
{
lean_dec(v___x_3928_);
v___y_3925_ = v_maxArgs_3921_;
goto v___jp_3924_;
}
v___jp_3924_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
lean_inc(v___y_3925_);
v___x_3926_ = lean_mk_array(v___y_3925_, v_dummy_3923_);
v___x_3927_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_3922_, v___x_3926_, v___y_3925_);
return v___x_3927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_3930_, lean_object* v_x_3931_){
_start:
{
if (lean_obj_tag(v_x_3930_) == 5)
{
lean_object* v_fn_3932_; lean_object* v_arg_3933_; lean_object* v___x_3934_; 
v_fn_3932_ = lean_ctor_get(v_x_3930_, 0);
lean_inc_ref(v_fn_3932_);
v_arg_3933_ = lean_ctor_get(v_x_3930_, 1);
lean_inc_ref(v_arg_3933_);
lean_dec_ref_known(v_x_3930_, 2);
v___x_3934_ = lean_array_push(v_x_3931_, v_arg_3933_);
v_x_3930_ = v_fn_3932_;
v_x_3931_ = v___x_3934_;
goto _start;
}
else
{
lean_dec_ref(v_x_3930_);
return v_x_3931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_3936_){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3937_ = l_Lean_Expr_getAppNumArgs(v_e_3936_);
v___x_3938_ = lean_mk_empty_array_with_capacity(v___x_3937_);
lean_dec(v___x_3937_);
v___x_3939_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3936_, v___x_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_3940_, lean_object* v_x_3941_, lean_object* v_x_3942_, lean_object* v_x_3943_){
_start:
{
if (lean_obj_tag(v_x_3941_) == 5)
{
lean_object* v_fn_3944_; lean_object* v_arg_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v_fn_3944_ = lean_ctor_get(v_x_3941_, 0);
lean_inc_ref(v_fn_3944_);
v_arg_3945_ = lean_ctor_get(v_x_3941_, 1);
lean_inc_ref(v_arg_3945_);
lean_dec_ref_known(v_x_3941_, 2);
v___x_3946_ = lean_array_set(v_x_3942_, v_x_3943_, v_arg_3945_);
v___x_3947_ = lean_unsigned_to_nat(1u);
v___x_3948_ = lean_nat_sub(v_x_3943_, v___x_3947_);
lean_dec(v_x_3943_);
v_x_3941_ = v_fn_3944_;
v_x_3942_ = v___x_3946_;
v_x_3943_ = v___x_3948_;
goto _start;
}
else
{
lean_object* v___x_3950_; 
lean_dec(v_x_3943_);
v___x_3950_ = lean_apply_2(v_k_3940_, v_x_3941_, v_x_3942_);
return v___x_3950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_3951_, lean_object* v_k_3952_, lean_object* v_x_3953_, lean_object* v_x_3954_, lean_object* v_x_3955_){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Lean_Expr_withAppAux___redArg(v_k_3952_, v_x_3953_, v_x_3954_, v_x_3955_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_3957_, lean_object* v_k_3958_){
_start:
{
lean_object* v_dummy_3959_; lean_object* v_nargs_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v_dummy_3959_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3960_ = l_Lean_Expr_getAppNumArgs(v_e_3957_);
lean_inc(v_nargs_3960_);
v___x_3961_ = lean_mk_array(v_nargs_3960_, v_dummy_3959_);
v___x_3962_ = lean_unsigned_to_nat(1u);
v___x_3963_ = lean_nat_sub(v_nargs_3960_, v___x_3962_);
lean_dec(v_nargs_3960_);
v___x_3964_ = l_Lean_Expr_withAppAux___redArg(v_k_3958_, v_e_3957_, v___x_3961_, v___x_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_3965_, lean_object* v_e_3966_, lean_object* v_k_3967_){
_start:
{
lean_object* v_dummy_3968_; lean_object* v_nargs_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v_dummy_3968_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3969_ = l_Lean_Expr_getAppNumArgs(v_e_3966_);
lean_inc(v_nargs_3969_);
v___x_3970_ = lean_mk_array(v_nargs_3969_, v_dummy_3968_);
v___x_3971_ = lean_unsigned_to_nat(1u);
v___x_3972_ = lean_nat_sub(v_nargs_3969_, v___x_3971_);
lean_dec(v_nargs_3969_);
v___x_3973_ = l_Lean_Expr_withAppAux___redArg(v_k_3967_, v_e_3966_, v___x_3970_, v___x_3972_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_3974_, lean_object* v_x_3975_, lean_object* v_x_3976_){
_start:
{
if (lean_obj_tag(v_x_3974_) == 5)
{
lean_object* v_fn_3977_; lean_object* v_arg_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v_fn_3977_ = lean_ctor_get(v_x_3974_, 0);
lean_inc_ref(v_fn_3977_);
v_arg_3978_ = lean_ctor_get(v_x_3974_, 1);
lean_inc_ref(v_arg_3978_);
lean_dec_ref_known(v_x_3974_, 2);
v___x_3979_ = lean_array_set(v_x_3975_, v_x_3976_, v_arg_3978_);
v___x_3980_ = lean_unsigned_to_nat(1u);
v___x_3981_ = lean_nat_sub(v_x_3976_, v___x_3980_);
lean_dec(v_x_3976_);
v_x_3974_ = v_fn_3977_;
v_x_3975_ = v___x_3979_;
v_x_3976_ = v___x_3981_;
goto _start;
}
else
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
lean_dec(v_x_3976_);
v___x_3983_ = l_Lean_Expr_constName(v_x_3974_);
lean_dec_ref(v_x_3974_);
v___x_3984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3983_);
lean_ctor_set(v___x_3984_, 1, v_x_3975_);
return v___x_3984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_3985_){
_start:
{
lean_object* v_dummy_3986_; lean_object* v_nargs_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v_dummy_3986_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3987_ = l_Lean_Expr_getAppNumArgs(v_e_3985_);
lean_inc(v_nargs_3987_);
v___x_3988_ = lean_mk_array(v_nargs_3987_, v_dummy_3986_);
v___x_3989_ = lean_unsigned_to_nat(1u);
v___x_3990_ = lean_nat_sub(v_nargs_3987_, v___x_3989_);
lean_dec(v_nargs_3987_);
v___x_3991_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_3985_, v___x_3988_, v___x_3990_);
return v___x_3991_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3992_; 
v___x_3992_ = l_Array_instInhabited(lean_box(0));
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_3993_){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3994_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_3995_ = lean_panic_fn_borrowed(v___x_3994_, v_msg_3993_);
return v___x_3995_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_3998_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_3999_ = lean_unsigned_to_nat(27u);
v___x_4000_ = lean_unsigned_to_nat(1247u);
v___x_4001_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_4002_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4003_ = l_mkPanicMessageWithDecl(v___x_4002_, v___x_4001_, v___x_4000_, v___x_3999_, v___x_3998_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_){
_start:
{
lean_object* v_zero_4007_; uint8_t v_isZero_4008_; 
v_zero_4007_ = lean_unsigned_to_nat(0u);
v_isZero_4008_ = lean_nat_dec_eq(v_a_4004_, v_zero_4007_);
if (v_isZero_4008_ == 1)
{
lean_dec_ref(v_a_4005_);
lean_dec(v_a_4004_);
return v_a_4006_;
}
else
{
if (lean_obj_tag(v_a_4005_) == 5)
{
lean_object* v_fn_4009_; lean_object* v_arg_4010_; lean_object* v_one_4011_; lean_object* v_n_4012_; lean_object* v___x_4013_; 
v_fn_4009_ = lean_ctor_get(v_a_4005_, 0);
lean_inc_ref(v_fn_4009_);
v_arg_4010_ = lean_ctor_get(v_a_4005_, 1);
lean_inc_ref(v_arg_4010_);
lean_dec_ref_known(v_a_4005_, 2);
v_one_4011_ = lean_unsigned_to_nat(1u);
v_n_4012_ = lean_nat_sub(v_a_4004_, v_one_4011_);
lean_dec(v_a_4004_);
v___x_4013_ = lean_array_set(v_a_4006_, v_n_4012_, v_arg_4010_);
v_a_4004_ = v_n_4012_;
v_a_4005_ = v_fn_4009_;
v_a_4006_ = v___x_4013_;
goto _start;
}
else
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
lean_dec_ref(v_a_4006_);
lean_dec_ref(v_a_4005_);
lean_dec(v_a_4004_);
v___x_4015_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_4016_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_4015_);
return v___x_4016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_4017_, lean_object* v_n_4018_){
_start:
{
lean_object* v_dummy_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v_dummy_4019_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_4018_);
v___x_4020_ = lean_mk_array(v_n_4018_, v_dummy_4019_);
v___x_4021_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_4018_, v_e_4017_, v___x_4020_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_4022_, lean_object* v_n_4023_){
_start:
{
lean_object* v_zero_4024_; uint8_t v_isZero_4025_; 
v_zero_4024_ = lean_unsigned_to_nat(0u);
v_isZero_4025_ = lean_nat_dec_eq(v_n_4023_, v_zero_4024_);
if (v_isZero_4025_ == 1)
{
lean_dec(v_n_4023_);
lean_inc_ref(v_e_4022_);
return v_e_4022_;
}
else
{
if (lean_obj_tag(v_e_4022_) == 5)
{
lean_object* v_fn_4026_; lean_object* v_one_4027_; lean_object* v_n_4028_; 
v_fn_4026_ = lean_ctor_get(v_e_4022_, 0);
v_one_4027_ = lean_unsigned_to_nat(1u);
v_n_4028_ = lean_nat_sub(v_n_4023_, v_one_4027_);
lean_dec(v_n_4023_);
v_e_4022_ = v_fn_4026_;
v_n_4023_ = v_n_4028_;
goto _start;
}
else
{
lean_dec(v_n_4023_);
lean_inc_ref(v_e_4022_);
return v_e_4022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_4030_, lean_object* v_n_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l_Lean_Expr_stripArgsN(v_e_4030_, v_n_4031_);
lean_dec_ref(v_e_4030_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_4033_, lean_object* v_n_4034_){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4035_ = l_Lean_Expr_getAppNumArgs(v_e_4033_);
v___x_4036_ = lean_nat_sub(v___x_4035_, v_n_4034_);
lean_dec(v___x_4035_);
v___x_4037_ = l_Lean_Expr_stripArgsN(v_e_4033_, v___x_4036_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_4038_, lean_object* v_n_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l_Lean_Expr_getAppPrefix(v_e_4038_, v_n_4039_);
lean_dec(v_n_4039_);
lean_dec_ref(v_e_4038_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_4041_, lean_object* v_inst_4042_, lean_object* v_f_4043_, lean_object* v_x_4044_){
_start:
{
size_t v_sz_4045_; size_t v___x_4046_; lean_object* v___x_4047_; 
v_sz_4045_ = lean_array_size(v_args_4041_);
v___x_4046_ = ((size_t)0ULL);
v___x_4047_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4042_, v_f_4043_, v_sz_4045_, v___x_4046_, v_args_4041_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_4049_, lean_object* v_inst_4050_, lean_object* v_f_4051_, lean_object* v_toSeq_4052_, lean_object* v_fn_4053_, lean_object* v_args_4054_){
_start:
{
lean_object* v_map_4055_; lean_object* v___f_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v_map_4055_ = lean_ctor_get(v_toFunctor_4049_, 0);
lean_inc(v_map_4055_);
lean_dec_ref(v_toFunctor_4049_);
lean_inc(v_f_4051_);
v___f_4056_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4056_, 0, v_args_4054_);
lean_closure_set(v___f_4056_, 1, v_inst_4050_);
lean_closure_set(v___f_4056_, 2, v_f_4051_);
v___x_4057_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_4058_ = lean_apply_1(v_f_4051_, v_fn_4053_);
v___x_4059_ = lean_apply_4(v_map_4055_, lean_box(0), lean_box(0), v___x_4057_, v___x_4058_);
v___x_4060_ = lean_apply_4(v_toSeq_4052_, lean_box(0), lean_box(0), v___x_4059_, v___f_4056_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_4061_, lean_object* v_f_4062_, lean_object* v_e_4063_){
_start:
{
lean_object* v_toApplicative_4064_; lean_object* v_toFunctor_4065_; lean_object* v_toSeq_4066_; lean_object* v___f_4067_; lean_object* v_dummy_4068_; lean_object* v_nargs_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v_toApplicative_4064_ = lean_ctor_get(v_inst_4061_, 0);
v_toFunctor_4065_ = lean_ctor_get(v_toApplicative_4064_, 0);
lean_inc_ref(v_toFunctor_4065_);
v_toSeq_4066_ = lean_ctor_get(v_toApplicative_4064_, 2);
lean_inc(v_toSeq_4066_);
v___f_4067_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_4067_, 0, v_toFunctor_4065_);
lean_closure_set(v___f_4067_, 1, v_inst_4061_);
lean_closure_set(v___f_4067_, 2, v_f_4062_);
lean_closure_set(v___f_4067_, 3, v_toSeq_4066_);
v_dummy_4068_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4069_ = l_Lean_Expr_getAppNumArgs(v_e_4063_);
lean_inc(v_nargs_4069_);
v___x_4070_ = lean_mk_array(v_nargs_4069_, v_dummy_4068_);
v___x_4071_ = lean_unsigned_to_nat(1u);
v___x_4072_ = lean_nat_sub(v_nargs_4069_, v___x_4071_);
lean_dec(v_nargs_4069_);
v___x_4073_ = l_Lean_Expr_withAppAux___redArg(v___f_4067_, v_e_4063_, v___x_4070_, v___x_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_4074_, lean_object* v_inst_4075_, lean_object* v_f_4076_, lean_object* v_e_4077_){
_start:
{
lean_object* v___x_4078_; 
v___x_4078_ = l_Lean_Expr_traverseApp___redArg(v_inst_4075_, v_f_4076_, v_e_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_4079_, lean_object* v_x_4080_, lean_object* v_x_4081_){
_start:
{
if (lean_obj_tag(v_x_4080_) == 5)
{
lean_object* v_fn_4082_; lean_object* v_arg_4083_; lean_object* v___x_4084_; 
v_fn_4082_ = lean_ctor_get(v_x_4080_, 0);
lean_inc_ref(v_fn_4082_);
v_arg_4083_ = lean_ctor_get(v_x_4080_, 1);
lean_inc_ref(v_arg_4083_);
lean_dec_ref_known(v_x_4080_, 2);
v___x_4084_ = lean_array_push(v_x_4081_, v_arg_4083_);
v_x_4080_ = v_fn_4082_;
v_x_4081_ = v___x_4084_;
goto _start;
}
else
{
lean_object* v___x_4086_; 
v___x_4086_ = lean_apply_2(v_k_4079_, v_x_4080_, v_x_4081_);
return v___x_4086_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_4087_, lean_object* v_k_4088_, lean_object* v_x_4089_, lean_object* v_x_4090_){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4088_, v_x_4089_, v_x_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_4092_, lean_object* v_k_4093_){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4094_ = l_Lean_Expr_getAppNumArgs(v_e_4092_);
v___x_4095_ = lean_mk_empty_array_with_capacity(v___x_4094_);
lean_dec(v___x_4094_);
v___x_4096_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4093_, v_e_4092_, v___x_4095_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_4097_, lean_object* v_e_4098_, lean_object* v_k_4099_){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4100_ = l_Lean_Expr_getAppNumArgs(v_e_4098_);
v___x_4101_ = lean_mk_empty_array_with_capacity(v___x_4100_);
lean_dec(v___x_4100_);
v___x_4102_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4099_, v_e_4098_, v___x_4101_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_4103_, lean_object* v_x_4104_, lean_object* v_x_4105_){
_start:
{
if (lean_obj_tag(v_x_4103_) == 5)
{
lean_object* v_fn_4106_; lean_object* v_arg_4107_; lean_object* v_zero_4108_; uint8_t v_isZero_4109_; 
v_fn_4106_ = lean_ctor_get(v_x_4103_, 0);
v_arg_4107_ = lean_ctor_get(v_x_4103_, 1);
v_zero_4108_ = lean_unsigned_to_nat(0u);
v_isZero_4109_ = lean_nat_dec_eq(v_x_4104_, v_zero_4108_);
if (v_isZero_4109_ == 1)
{
lean_dec(v_x_4104_);
lean_inc_ref(v_arg_4107_);
return v_arg_4107_;
}
else
{
lean_object* v_one_4110_; lean_object* v_n_4111_; 
v_one_4110_ = lean_unsigned_to_nat(1u);
v_n_4111_ = lean_nat_sub(v_x_4104_, v_one_4110_);
lean_dec(v_x_4104_);
v_x_4103_ = v_fn_4106_;
v_x_4104_ = v_n_4111_;
goto _start;
}
}
else
{
lean_dec(v_x_4104_);
lean_inc_ref(v_x_4105_);
return v_x_4105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_4113_, lean_object* v_x_4114_, lean_object* v_x_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_Expr_getRevArgD(v_x_4113_, v_x_4114_, v_x_4115_);
lean_dec_ref(v_x_4115_);
lean_dec_ref(v_x_4113_);
return v_res_4116_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4119_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4120_ = lean_unsigned_to_nat(20u);
v___x_4121_ = lean_unsigned_to_nat(1288u);
v___x_4122_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4123_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4124_ = l_mkPanicMessageWithDecl(v___x_4123_, v___x_4122_, v___x_4121_, v___x_4120_, v___x_4119_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4125_, lean_object* v_x_4126_){
_start:
{
if (lean_obj_tag(v_x_4125_) == 5)
{
lean_object* v_fn_4127_; lean_object* v_arg_4128_; lean_object* v_zero_4129_; uint8_t v_isZero_4130_; 
v_fn_4127_ = lean_ctor_get(v_x_4125_, 0);
v_arg_4128_ = lean_ctor_get(v_x_4125_, 1);
v_zero_4129_ = lean_unsigned_to_nat(0u);
v_isZero_4130_ = lean_nat_dec_eq(v_x_4126_, v_zero_4129_);
if (v_isZero_4130_ == 1)
{
lean_dec(v_x_4126_);
lean_inc_ref(v_arg_4128_);
return v_arg_4128_;
}
else
{
lean_object* v_one_4131_; lean_object* v_n_4132_; 
v_one_4131_ = lean_unsigned_to_nat(1u);
v_n_4132_ = lean_nat_sub(v_x_4126_, v_one_4131_);
lean_dec(v_x_4126_);
v_x_4125_ = v_fn_4127_;
v_x_4126_ = v_n_4132_;
goto _start;
}
}
else
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_dec(v_x_4126_);
v___x_4134_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4135_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4134_);
return v___x_4135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4136_, lean_object* v_x_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Lean_Expr_getRevArg_x21(v_x_4136_, v_x_4137_);
lean_dec_ref(v_x_4136_);
return v_res_4138_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4140_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4141_ = lean_unsigned_to_nat(20u);
v___x_4142_ = lean_unsigned_to_nat(1295u);
v___x_4143_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4144_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4145_ = l_mkPanicMessageWithDecl(v___x_4144_, v___x_4143_, v___x_4142_, v___x_4141_, v___x_4140_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4146_, lean_object* v_x_4147_){
_start:
{
switch(lean_obj_tag(v_x_4146_))
{
case 10:
{
lean_object* v_expr_4148_; 
v_expr_4148_ = lean_ctor_get(v_x_4146_, 1);
v_x_4146_ = v_expr_4148_;
goto _start;
}
case 5:
{
lean_object* v_fn_4150_; lean_object* v_arg_4151_; lean_object* v_zero_4152_; uint8_t v_isZero_4153_; 
v_fn_4150_ = lean_ctor_get(v_x_4146_, 0);
v_arg_4151_ = lean_ctor_get(v_x_4146_, 1);
v_zero_4152_ = lean_unsigned_to_nat(0u);
v_isZero_4153_ = lean_nat_dec_eq(v_x_4147_, v_zero_4152_);
if (v_isZero_4153_ == 1)
{
lean_dec(v_x_4147_);
lean_inc_ref(v_arg_4151_);
return v_arg_4151_;
}
else
{
lean_object* v_one_4154_; lean_object* v_n_4155_; 
v_one_4154_ = lean_unsigned_to_nat(1u);
v_n_4155_ = lean_nat_sub(v_x_4147_, v_one_4154_);
lean_dec(v_x_4147_);
v_x_4146_ = v_fn_4150_;
v_x_4147_ = v_n_4155_;
goto _start;
}
}
default: 
{
lean_object* v___x_4157_; lean_object* v___x_4158_; 
lean_dec(v_x_4147_);
v___x_4157_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4158_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4157_);
return v___x_4158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4159_, lean_object* v_x_4160_){
_start:
{
lean_object* v_res_4161_; 
v_res_4161_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4159_, v_x_4160_);
lean_dec_ref(v_x_4159_);
return v_res_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4162_, lean_object* v_i_4163_, lean_object* v_n_4164_){
_start:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4165_ = lean_nat_sub(v_n_4164_, v_i_4163_);
v___x_4166_ = lean_unsigned_to_nat(1u);
v___x_4167_ = lean_nat_sub(v___x_4165_, v___x_4166_);
lean_dec(v___x_4165_);
v___x_4168_ = l_Lean_Expr_getRevArg_x21(v_e_4162_, v___x_4167_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4169_, lean_object* v_i_4170_, lean_object* v_n_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_Expr_getArg_x21(v_e_4169_, v_i_4170_, v_n_4171_);
lean_dec(v_n_4171_);
lean_dec(v_i_4170_);
lean_dec_ref(v_e_4169_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4173_, lean_object* v_i_4174_, lean_object* v_n_4175_){
_start:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4176_ = lean_nat_sub(v_n_4175_, v_i_4174_);
v___x_4177_ = lean_unsigned_to_nat(1u);
v___x_4178_ = lean_nat_sub(v___x_4176_, v___x_4177_);
lean_dec(v___x_4176_);
v___x_4179_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4173_, v___x_4178_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4180_, lean_object* v_i_4181_, lean_object* v_n_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l_Lean_Expr_getArg_x21_x27(v_e_4180_, v_i_4181_, v_n_4182_);
lean_dec(v_n_4182_);
lean_dec(v_i_4181_);
lean_dec_ref(v_e_4180_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4184_, lean_object* v_i_4185_, lean_object* v_v_u2080_4186_, lean_object* v_n_4187_){
_start:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4188_ = lean_nat_sub(v_n_4187_, v_i_4185_);
v___x_4189_ = lean_unsigned_to_nat(1u);
v___x_4190_ = lean_nat_sub(v___x_4188_, v___x_4189_);
lean_dec(v___x_4188_);
v___x_4191_ = l_Lean_Expr_getRevArgD(v_e_4184_, v___x_4190_, v_v_u2080_4186_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4192_, lean_object* v_i_4193_, lean_object* v_v_u2080_4194_, lean_object* v_n_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l_Lean_Expr_getArgD(v_e_4192_, v_i_4193_, v_v_u2080_4194_, v_n_4195_);
lean_dec(v_n_4195_);
lean_dec_ref(v_v_u2080_4194_);
lean_dec(v_i_4193_);
lean_dec_ref(v_e_4192_);
return v_res_4196_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4197_){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; 
v___x_4198_ = lean_unsigned_to_nat(0u);
v___x_4199_ = l_Lean_Expr_looseBVarRange(v_e_4197_);
v___x_4200_ = lean_nat_dec_lt(v___x_4198_, v___x_4199_);
lean_dec(v___x_4199_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4201_){
_start:
{
uint8_t v_res_4202_; lean_object* v_r_4203_; 
v_res_4202_ = l_Lean_Expr_hasLooseBVars(v_e_4201_);
lean_dec_ref(v_e_4201_);
v_r_4203_ = lean_box(v_res_4202_);
return v_r_4203_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4204_){
_start:
{
if (lean_obj_tag(v_e_4204_) == 7)
{
lean_object* v_body_4205_; uint8_t v___x_4206_; 
v_body_4205_ = lean_ctor_get(v_e_4204_, 2);
v___x_4206_ = l_Lean_Expr_hasLooseBVars(v_body_4205_);
if (v___x_4206_ == 0)
{
uint8_t v___x_4207_; 
v___x_4207_ = 1;
return v___x_4207_;
}
else
{
uint8_t v___x_4208_; 
v___x_4208_ = 0;
return v___x_4208_;
}
}
else
{
uint8_t v___x_4209_; 
v___x_4209_ = 0;
return v___x_4209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4210_){
_start:
{
uint8_t v_res_4211_; lean_object* v_r_4212_; 
v_res_4211_ = l_Lean_Expr_isArrow(v_e_4210_);
lean_dec_ref(v_e_4210_);
v_r_4212_ = lean_box(v_res_4211_);
return v_r_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4215_, lean_object* v_bvarIdx_4216_){
_start:
{
uint8_t v_res_4217_; lean_object* v_r_4218_; 
v_res_4217_ = lean_expr_has_loose_bvar(v_e_4215_, v_bvarIdx_4216_);
lean_dec(v_bvarIdx_4216_);
lean_dec_ref(v_e_4215_);
v_r_4218_ = lean_box(v_res_4217_);
return v_r_4218_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4219_, lean_object* v_bvarIdx_4220_, uint8_t v_considerRange_4221_){
_start:
{
if (lean_obj_tag(v_e_4219_) == 7)
{
lean_object* v_binderType_4222_; lean_object* v_body_4223_; uint8_t v_binderInfo_4224_; uint8_t v___y_4226_; uint8_t v___x_4230_; 
v_binderType_4222_ = lean_ctor_get(v_e_4219_, 1);
v_body_4223_ = lean_ctor_get(v_e_4219_, 2);
v_binderInfo_4224_ = lean_ctor_get_uint8(v_e_4219_, sizeof(void*)*3 + 8);
v___x_4230_ = lean_expr_has_loose_bvar(v_binderType_4222_, v_bvarIdx_4220_);
if (v___x_4230_ == 0)
{
v___y_4226_ = v___x_4230_;
goto v___jp_4225_;
}
else
{
uint8_t v___x_4231_; 
v___x_4231_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4224_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4232_; uint8_t v___x_4233_; 
v___x_4232_ = lean_unsigned_to_nat(0u);
v___x_4233_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4223_, v___x_4232_, v_considerRange_4221_);
v___y_4226_ = v___x_4233_;
goto v___jp_4225_;
}
else
{
v___y_4226_ = v___x_4231_;
goto v___jp_4225_;
}
}
v___jp_4225_:
{
if (v___y_4226_ == 0)
{
lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4227_ = lean_unsigned_to_nat(1u);
v___x_4228_ = lean_nat_add(v_bvarIdx_4220_, v___x_4227_);
lean_dec(v_bvarIdx_4220_);
v_e_4219_ = v_body_4223_;
v_bvarIdx_4220_ = v___x_4228_;
goto _start;
}
else
{
lean_dec(v_bvarIdx_4220_);
return v___y_4226_;
}
}
}
else
{
if (v_considerRange_4221_ == 0)
{
lean_dec(v_bvarIdx_4220_);
return v_considerRange_4221_;
}
else
{
uint8_t v___x_4234_; 
v___x_4234_ = lean_expr_has_loose_bvar(v_e_4219_, v_bvarIdx_4220_);
lean_dec(v_bvarIdx_4220_);
return v___x_4234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4235_, lean_object* v_bvarIdx_4236_, lean_object* v_considerRange_4237_){
_start:
{
uint8_t v_considerRange_boxed_4238_; uint8_t v_res_4239_; lean_object* v_r_4240_; 
v_considerRange_boxed_4238_ = lean_unbox(v_considerRange_4237_);
v_res_4239_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4235_, v_bvarIdx_4236_, v_considerRange_boxed_4238_);
lean_dec_ref(v_e_4235_);
v_r_4240_ = lean_box(v_res_4239_);
return v_r_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4244_, lean_object* v_s_4245_, lean_object* v_d_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = lean_expr_lower_loose_bvars(v_e_4244_, v_s_4245_, v_d_4246_);
lean_dec(v_d_4246_);
lean_dec(v_s_4245_);
lean_dec_ref(v_e_4244_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4251_, lean_object* v_s_4252_, lean_object* v_d_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = lean_expr_lift_loose_bvars(v_e_4251_, v_s_4252_, v_d_4253_);
lean_dec(v_d_4253_);
lean_dec(v_s_4252_);
lean_dec_ref(v_e_4251_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4255_, lean_object* v_numParams_4256_, uint8_t v_considerRange_4257_){
_start:
{
if (lean_obj_tag(v_e_4255_) == 7)
{
lean_object* v_binderName_4258_; lean_object* v_binderType_4259_; lean_object* v_body_4260_; uint8_t v_binderInfo_4261_; lean_object* v_zero_4262_; uint8_t v_isZero_4263_; 
v_binderName_4258_ = lean_ctor_get(v_e_4255_, 0);
v_binderType_4259_ = lean_ctor_get(v_e_4255_, 1);
v_body_4260_ = lean_ctor_get(v_e_4255_, 2);
v_binderInfo_4261_ = lean_ctor_get_uint8(v_e_4255_, sizeof(void*)*3 + 8);
v_zero_4262_ = lean_unsigned_to_nat(0u);
v_isZero_4263_ = lean_nat_dec_eq(v_numParams_4256_, v_zero_4262_);
if (v_isZero_4263_ == 0)
{
lean_object* v_one_4264_; lean_object* v_n_4265_; lean_object* v_b_4266_; uint8_t v___y_4268_; uint8_t v___x_4272_; 
lean_inc_ref(v_body_4260_);
lean_inc_ref(v_binderType_4259_);
lean_inc(v_binderName_4258_);
lean_dec_ref_known(v_e_4255_, 3);
v_one_4264_ = lean_unsigned_to_nat(1u);
v_n_4265_ = lean_nat_sub(v_numParams_4256_, v_one_4264_);
v_b_4266_ = l_Lean_Expr_inferImplicit(v_body_4260_, v_n_4265_, v_considerRange_4257_);
lean_dec(v_n_4265_);
v___x_4272_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4261_);
if (v___x_4272_ == 0)
{
v___y_4268_ = v___x_4272_;
goto v___jp_4267_;
}
else
{
uint8_t v___x_4273_; 
v___x_4273_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4266_, v_zero_4262_, v_considerRange_4257_);
v___y_4268_ = v___x_4273_;
goto v___jp_4267_;
}
v___jp_4267_:
{
if (v___y_4268_ == 0)
{
lean_object* v___x_4269_; 
v___x_4269_ = l_Lean_Expr_forallE___override(v_binderName_4258_, v_binderType_4259_, v_b_4266_, v_binderInfo_4261_);
return v___x_4269_;
}
else
{
uint8_t v___x_4270_; lean_object* v___x_4271_; 
v___x_4270_ = 1;
v___x_4271_ = l_Lean_Expr_forallE___override(v_binderName_4258_, v_binderType_4259_, v_b_4266_, v___x_4270_);
return v___x_4271_;
}
}
}
else
{
return v_e_4255_;
}
}
else
{
return v_e_4255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4274_, lean_object* v_numParams_4275_, lean_object* v_considerRange_4276_){
_start:
{
uint8_t v_considerRange_boxed_4277_; lean_object* v_res_4278_; 
v_considerRange_boxed_4277_ = lean_unbox(v_considerRange_4276_);
v_res_4278_ = l_Lean_Expr_inferImplicit(v_e_4274_, v_numParams_4275_, v_considerRange_boxed_4277_);
lean_dec(v_numParams_4275_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4279_, lean_object* v_binderInfos_x3f_4280_){
_start:
{
if (lean_obj_tag(v_e_4279_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4280_) == 1)
{
lean_object* v_binderName_4281_; lean_object* v_binderType_4282_; lean_object* v_body_4283_; uint8_t v_binderInfo_4284_; lean_object* v_head_4285_; lean_object* v_tail_4286_; lean_object* v_b_4287_; 
v_binderName_4281_ = lean_ctor_get(v_e_4279_, 0);
lean_inc(v_binderName_4281_);
v_binderType_4282_ = lean_ctor_get(v_e_4279_, 1);
lean_inc_ref(v_binderType_4282_);
v_body_4283_ = lean_ctor_get(v_e_4279_, 2);
lean_inc_ref(v_body_4283_);
v_binderInfo_4284_ = lean_ctor_get_uint8(v_e_4279_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4279_, 3);
v_head_4285_ = lean_ctor_get(v_binderInfos_x3f_4280_, 0);
v_tail_4286_ = lean_ctor_get(v_binderInfos_x3f_4280_, 1);
v_b_4287_ = l_Lean_Expr_updateForallBinderInfos(v_body_4283_, v_tail_4286_);
if (lean_obj_tag(v_head_4285_) == 0)
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Lean_Expr_forallE___override(v_binderName_4281_, v_binderType_4282_, v_b_4287_, v_binderInfo_4284_);
return v___x_4288_;
}
else
{
lean_object* v_val_4289_; uint8_t v___x_4290_; lean_object* v___x_4291_; 
v_val_4289_ = lean_ctor_get(v_head_4285_, 0);
v___x_4290_ = lean_unbox(v_val_4289_);
v___x_4291_ = l_Lean_Expr_forallE___override(v_binderName_4281_, v_binderType_4282_, v_b_4287_, v___x_4290_);
return v___x_4291_;
}
}
else
{
return v_e_4279_;
}
}
else
{
return v_e_4279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4292_, lean_object* v_binderInfos_x3f_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Lean_Expr_updateForallBinderInfos(v_e_4292_, v_binderInfos_x3f_4293_);
lean_dec(v_binderInfos_x3f_4293_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4295_, lean_object* v_binderNames_x3f_4296_){
_start:
{
switch(lean_obj_tag(v_e_4295_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4296_) == 1)
{
lean_object* v_binderName_4297_; lean_object* v_binderType_4298_; lean_object* v_body_4299_; uint8_t v_binderInfo_4300_; lean_object* v_head_4301_; lean_object* v_tail_4302_; lean_object* v_b_4303_; 
v_binderName_4297_ = lean_ctor_get(v_e_4295_, 0);
lean_inc(v_binderName_4297_);
v_binderType_4298_ = lean_ctor_get(v_e_4295_, 1);
lean_inc_ref(v_binderType_4298_);
v_body_4299_ = lean_ctor_get(v_e_4295_, 2);
lean_inc_ref(v_body_4299_);
v_binderInfo_4300_ = lean_ctor_get_uint8(v_e_4295_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4295_, 3);
v_head_4301_ = lean_ctor_get(v_binderNames_x3f_4296_, 0);
lean_inc(v_head_4301_);
v_tail_4302_ = lean_ctor_get(v_binderNames_x3f_4296_, 1);
lean_inc(v_tail_4302_);
lean_dec_ref_known(v_binderNames_x3f_4296_, 2);
v_b_4303_ = l_Lean_Expr_updateBinderNames(v_body_4299_, v_tail_4302_);
if (lean_obj_tag(v_head_4301_) == 0)
{
lean_object* v___x_4304_; 
v___x_4304_ = l_Lean_Expr_forallE___override(v_binderName_4297_, v_binderType_4298_, v_b_4303_, v_binderInfo_4300_);
return v___x_4304_;
}
else
{
lean_object* v_val_4305_; lean_object* v___x_4306_; 
lean_dec(v_binderName_4297_);
v_val_4305_ = lean_ctor_get(v_head_4301_, 0);
lean_inc(v_val_4305_);
lean_dec_ref_known(v_head_4301_, 1);
v___x_4306_ = l_Lean_Expr_forallE___override(v_val_4305_, v_binderType_4298_, v_b_4303_, v_binderInfo_4300_);
return v___x_4306_;
}
}
else
{
lean_dec(v_binderNames_x3f_4296_);
return v_e_4295_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4296_) == 1)
{
lean_object* v_binderName_4307_; lean_object* v_binderType_4308_; lean_object* v_body_4309_; uint8_t v_binderInfo_4310_; lean_object* v_head_4311_; lean_object* v_tail_4312_; lean_object* v_b_4313_; 
v_binderName_4307_ = lean_ctor_get(v_e_4295_, 0);
lean_inc(v_binderName_4307_);
v_binderType_4308_ = lean_ctor_get(v_e_4295_, 1);
lean_inc_ref(v_binderType_4308_);
v_body_4309_ = lean_ctor_get(v_e_4295_, 2);
lean_inc_ref(v_body_4309_);
v_binderInfo_4310_ = lean_ctor_get_uint8(v_e_4295_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4295_, 3);
v_head_4311_ = lean_ctor_get(v_binderNames_x3f_4296_, 0);
lean_inc(v_head_4311_);
v_tail_4312_ = lean_ctor_get(v_binderNames_x3f_4296_, 1);
lean_inc(v_tail_4312_);
lean_dec_ref_known(v_binderNames_x3f_4296_, 2);
v_b_4313_ = l_Lean_Expr_updateBinderNames(v_body_4309_, v_tail_4312_);
if (lean_obj_tag(v_head_4311_) == 0)
{
lean_object* v___x_4314_; 
v___x_4314_ = l_Lean_Expr_lam___override(v_binderName_4307_, v_binderType_4308_, v_b_4313_, v_binderInfo_4310_);
return v___x_4314_;
}
else
{
lean_object* v_val_4315_; lean_object* v___x_4316_; 
lean_dec(v_binderName_4307_);
v_val_4315_ = lean_ctor_get(v_head_4311_, 0);
lean_inc(v_val_4315_);
lean_dec_ref_known(v_head_4311_, 1);
v___x_4316_ = l_Lean_Expr_lam___override(v_val_4315_, v_binderType_4308_, v_b_4313_, v_binderInfo_4310_);
return v___x_4316_;
}
}
else
{
lean_dec(v_binderNames_x3f_4296_);
return v_e_4295_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4296_);
return v_e_4295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4319_, lean_object* v_subst_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = lean_expr_instantiate(v_e_4319_, v_subst_4320_);
lean_dec_ref(v_subst_4320_);
lean_dec_ref(v_e_4319_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4324_, lean_object* v_subst_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = lean_expr_instantiate1(v_e_4324_, v_subst_4325_);
lean_dec_ref(v_subst_4325_);
lean_dec_ref(v_e_4324_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4329_, lean_object* v_subst_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = lean_expr_instantiate_rev(v_e_4329_, v_subst_4330_);
lean_dec_ref(v_subst_4330_);
lean_dec_ref(v_e_4329_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4336_, lean_object* v_beginIdx_4337_, lean_object* v_endIdx_4338_, lean_object* v_subst_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = lean_expr_instantiate_range(v_e_4336_, v_beginIdx_4337_, v_endIdx_4338_, v_subst_4339_);
lean_dec_ref(v_subst_4339_);
lean_dec(v_endIdx_4338_);
lean_dec(v_beginIdx_4337_);
lean_dec_ref(v_e_4336_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4345_, lean_object* v_beginIdx_4346_, lean_object* v_endIdx_4347_, lean_object* v_subst_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = lean_expr_instantiate_rev_range(v_e_4345_, v_beginIdx_4346_, v_endIdx_4347_, v_subst_4348_);
lean_dec_ref(v_subst_4348_);
lean_dec(v_endIdx_4347_);
lean_dec(v_beginIdx_4346_);
lean_dec_ref(v_e_4345_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4352_, lean_object* v_xs_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = lean_expr_abstract(v_e_4352_, v_xs_4353_);
lean_dec_ref(v_xs_4353_);
lean_dec_ref(v_e_4352_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4358_, lean_object* v_n_4359_, lean_object* v_xs_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = lean_expr_abstract_range(v_e_4358_, v_n_4359_, v_xs_4360_);
lean_dec_ref(v_xs_4360_);
lean_dec(v_n_4359_);
lean_dec_ref(v_e_4358_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4362_, lean_object* v_fvar_4363_, lean_object* v_v_4364_){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4365_ = lean_unsigned_to_nat(1u);
v___x_4366_ = lean_mk_empty_array_with_capacity(v___x_4365_);
v___x_4367_ = lean_array_push(v___x_4366_, v_fvar_4363_);
v___x_4368_ = lean_expr_abstract(v_e_4362_, v___x_4367_);
lean_dec_ref(v___x_4367_);
v___x_4369_ = lean_expr_instantiate1(v___x_4368_, v_v_4364_);
lean_dec_ref(v___x_4368_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4370_, lean_object* v_fvar_4371_, lean_object* v_v_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l_Lean_Expr_replaceFVar(v_e_4370_, v_fvar_4371_, v_v_4372_);
lean_dec_ref(v_v_4372_);
lean_dec_ref(v_e_4370_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4374_, lean_object* v_fvarId_4375_, lean_object* v_v_4376_){
_start:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4377_ = l_Lean_Expr_fvar___override(v_fvarId_4375_);
v___x_4378_ = l_Lean_Expr_replaceFVar(v_e_4374_, v___x_4377_, v_v_4376_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4379_, lean_object* v_fvarId_4380_, lean_object* v_v_4381_){
_start:
{
lean_object* v_res_4382_; 
v_res_4382_ = l_Lean_Expr_replaceFVarId(v_e_4379_, v_fvarId_4380_, v_v_4381_);
lean_dec_ref(v_v_4381_);
lean_dec_ref(v_e_4379_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4383_, lean_object* v_fvars_4384_, lean_object* v_vs_4385_){
_start:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4386_ = lean_expr_abstract(v_e_4383_, v_fvars_4384_);
v___x_4387_ = lean_expr_instantiate_rev(v___x_4386_, v_vs_4385_);
lean_dec_ref(v___x_4386_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4388_, lean_object* v_fvars_4389_, lean_object* v_vs_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_Lean_Expr_replaceFVars(v_e_4388_, v_fvars_4389_, v_vs_4390_);
lean_dec_ref(v_vs_4390_);
lean_dec_ref(v_fvars_4389_);
lean_dec_ref(v_e_4388_);
return v_res_4391_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4394_){
_start:
{
switch(lean_obj_tag(v_x_4394_))
{
case 4:
{
uint8_t v___x_4395_; 
v___x_4395_ = 1;
return v___x_4395_;
}
case 3:
{
uint8_t v___x_4396_; 
v___x_4396_ = 1;
return v___x_4396_;
}
case 0:
{
uint8_t v___x_4397_; 
v___x_4397_ = 1;
return v___x_4397_;
}
case 9:
{
uint8_t v___x_4398_; 
v___x_4398_ = 1;
return v___x_4398_;
}
case 2:
{
uint8_t v___x_4399_; 
v___x_4399_ = 1;
return v___x_4399_;
}
case 1:
{
uint8_t v___x_4400_; 
v___x_4400_ = 1;
return v___x_4400_;
}
default: 
{
uint8_t v___x_4401_; 
v___x_4401_ = 0;
return v___x_4401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4402_){
_start:
{
uint8_t v_res_4403_; lean_object* v_r_4404_; 
v_res_4403_ = l_Lean_Expr_isAtomic(v_x_4402_);
lean_dec_ref(v_x_4402_);
v_r_4404_ = lean_box(v_res_4403_);
return v_r_4404_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4410_ = lean_box(0);
v___x_4411_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4412_ = l_Lean_Expr_const___override(v___x_4411_, v___x_4410_);
return v___x_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4413_, lean_object* v_proof_4414_){
_start:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4415_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4416_ = l_Lean_mkAppB(v___x_4415_, v_pred_4413_, v_proof_4414_);
return v___x_4416_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4421_ = lean_box(0);
v___x_4422_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4423_ = l_Lean_Expr_const___override(v___x_4422_, v___x_4421_);
return v___x_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4424_, lean_object* v_proof_4425_){
_start:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4426_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4427_ = l_Lean_mkAppB(v___x_4426_, v_pred_4424_, v_proof_4425_);
return v___x_4427_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4428_; 
v___x_4428_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4428_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4429_; 
v___x_4429_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4430_){
_start:
{
lean_inc_ref(v_val_4430_);
return v_val_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4431_){
_start:
{
lean_object* v_res_4432_; 
v_res_4432_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4431_);
lean_dec_ref(v_val_4431_);
return v_res_4432_;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4435_, lean_object* v_x_4436_){
_start:
{
uint8_t v___x_4437_; 
v___x_4437_ = lean_expr_equal(v_x_4435_, v_x_4436_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4438_, lean_object* v_x_4439_){
_start:
{
uint8_t v_res_4440_; lean_object* v_r_4441_; 
v_res_4440_ = l_Lean_ExprStructEq_beq(v_x_4438_, v_x_4439_);
lean_dec_ref(v_x_4439_);
lean_dec_ref(v_x_4438_);
v_r_4441_ = lean_box(v_res_4440_);
return v_r_4441_;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4442_){
_start:
{
uint64_t v___x_4443_; 
v___x_4443_ = l_Lean_Expr_hash(v_x_4442_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4444_){
_start:
{
uint64_t v_res_4445_; lean_object* v_r_4446_; 
v_res_4445_ = l_Lean_ExprStructEq_hash(v_x_4444_);
lean_dec_ref(v_x_4444_);
v_r_4446_ = lean_box_uint64(v_res_4445_);
return v_r_4446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4453_, lean_object* v_start_4454_, lean_object* v_b_4455_, lean_object* v_i_4456_){
_start:
{
uint8_t v___x_4457_; 
v___x_4457_ = lean_nat_dec_le(v_i_4456_, v_start_4454_);
if (v___x_4457_ == 0)
{
lean_object* v___x_4458_; lean_object* v_i_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4458_ = lean_unsigned_to_nat(1u);
v_i_4459_ = lean_nat_sub(v_i_4456_, v___x_4458_);
lean_dec(v_i_4456_);
v___x_4460_ = l_Lean_instInhabitedExpr;
v___x_4461_ = lean_array_get_borrowed(v___x_4460_, v_revArgs_4453_, v_i_4459_);
lean_inc(v___x_4461_);
v___x_4462_ = l_Lean_Expr_app___override(v_b_4455_, v___x_4461_);
v_b_4455_ = v___x_4462_;
v_i_4456_ = v_i_4459_;
goto _start;
}
else
{
lean_dec(v_i_4456_);
return v_b_4455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4464_, lean_object* v_start_4465_, lean_object* v_b_4466_, lean_object* v_i_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4464_, v_start_4465_, v_b_4466_, v_i_4467_);
lean_dec(v_start_4465_);
lean_dec_ref(v_revArgs_4464_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4469_, lean_object* v_beginIdx_4470_, lean_object* v_endIdx_4471_, lean_object* v_revArgs_4472_){
_start:
{
lean_object* v___x_4473_; 
v___x_4473_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4472_, v_beginIdx_4470_, v_f_4469_, v_endIdx_4471_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4474_, lean_object* v_beginIdx_4475_, lean_object* v_endIdx_4476_, lean_object* v_revArgs_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l_Lean_Expr_mkAppRevRange(v_f_4474_, v_beginIdx_4475_, v_endIdx_4476_, v_revArgs_4477_);
lean_dec_ref(v_revArgs_4477_);
lean_dec(v_beginIdx_4475_);
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4479_, uint8_t v_useZeta_4480_, uint8_t v_preserveMData_4481_, lean_object* v_sz_4482_, lean_object* v_e_4483_, lean_object* v_i_4484_){
_start:
{
switch(lean_obj_tag(v_e_4483_))
{
case 6:
{
lean_object* v_body_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; uint8_t v___x_4493_; 
v_body_4490_ = lean_ctor_get(v_e_4483_, 2);
lean_inc_ref(v_body_4490_);
lean_dec_ref_known(v_e_4483_, 3);
v___x_4491_ = lean_unsigned_to_nat(1u);
v___x_4492_ = lean_nat_add(v_i_4484_, v___x_4491_);
lean_dec(v_i_4484_);
v___x_4493_ = lean_nat_dec_lt(v___x_4492_, v_sz_4482_);
if (v___x_4493_ == 0)
{
lean_object* v___x_4494_; 
lean_dec(v___x_4492_);
v___x_4494_ = lean_expr_instantiate(v_body_4490_, v_revArgs_4479_);
lean_dec_ref(v_body_4490_);
return v___x_4494_;
}
else
{
v_e_4483_ = v_body_4490_;
v_i_4484_ = v___x_4492_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4480_ == 0)
{
goto v___jp_4485_;
}
else
{
lean_object* v_value_4496_; lean_object* v_body_4497_; uint8_t v___x_4498_; 
v_value_4496_ = lean_ctor_get(v_e_4483_, 2);
v_body_4497_ = lean_ctor_get(v_e_4483_, 3);
v___x_4498_ = lean_nat_dec_lt(v_i_4484_, v_sz_4482_);
if (v___x_4498_ == 0)
{
goto v___jp_4485_;
}
else
{
lean_object* v___x_4499_; 
lean_inc_ref(v_body_4497_);
lean_inc_ref(v_value_4496_);
lean_dec_ref_known(v_e_4483_, 4);
v___x_4499_ = lean_expr_instantiate1(v_body_4497_, v_value_4496_);
lean_dec_ref(v_value_4496_);
lean_dec_ref(v_body_4497_);
v_e_4483_ = v___x_4499_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4481_ == 0)
{
lean_object* v_expr_4501_; 
v_expr_4501_ = lean_ctor_get(v_e_4483_, 1);
lean_inc_ref(v_expr_4501_);
lean_dec_ref_known(v_e_4483_, 2);
v_e_4483_ = v_expr_4501_;
goto _start;
}
else
{
goto v___jp_4485_;
}
}
default: 
{
goto v___jp_4485_;
}
}
v___jp_4485_:
{
lean_object* v_n_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v_n_4486_ = lean_nat_sub(v_sz_4482_, v_i_4484_);
lean_dec(v_i_4484_);
v___x_4487_ = lean_expr_instantiate_range(v_e_4483_, v_n_4486_, v_sz_4482_, v_revArgs_4479_);
lean_dec_ref(v_e_4483_);
v___x_4488_ = lean_unsigned_to_nat(0u);
v___x_4489_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4479_, v___x_4488_, v___x_4487_, v_n_4486_);
return v___x_4489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4503_, lean_object* v_useZeta_4504_, lean_object* v_preserveMData_4505_, lean_object* v_sz_4506_, lean_object* v_e_4507_, lean_object* v_i_4508_){
_start:
{
uint8_t v_useZeta_boxed_4509_; uint8_t v_preserveMData_boxed_4510_; lean_object* v_res_4511_; 
v_useZeta_boxed_4509_ = lean_unbox(v_useZeta_4504_);
v_preserveMData_boxed_4510_ = lean_unbox(v_preserveMData_4505_);
v_res_4511_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4503_, v_useZeta_boxed_4509_, v_preserveMData_boxed_4510_, v_sz_4506_, v_e_4507_, v_i_4508_);
lean_dec(v_sz_4506_);
lean_dec_ref(v_revArgs_4503_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4512_, lean_object* v_revArgs_4513_, uint8_t v_useZeta_4514_, uint8_t v_preserveMData_4515_){
_start:
{
lean_object* v_sz_4516_; lean_object* v___x_4517_; uint8_t v___x_4518_; 
v_sz_4516_ = lean_array_get_size(v_revArgs_4513_);
v___x_4517_ = lean_unsigned_to_nat(0u);
v___x_4518_ = lean_nat_dec_eq(v_sz_4516_, v___x_4517_);
if (v___x_4518_ == 0)
{
lean_object* v___x_4519_; 
v___x_4519_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4513_, v_useZeta_4514_, v_preserveMData_4515_, v_sz_4516_, v_f_4512_, v___x_4517_);
return v___x_4519_;
}
else
{
return v_f_4512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4520_, lean_object* v_revArgs_4521_, lean_object* v_useZeta_4522_, lean_object* v_preserveMData_4523_){
_start:
{
uint8_t v_useZeta_boxed_4524_; uint8_t v_preserveMData_boxed_4525_; lean_object* v_res_4526_; 
v_useZeta_boxed_4524_ = lean_unbox(v_useZeta_4522_);
v_preserveMData_boxed_4525_ = lean_unbox(v_preserveMData_4523_);
v_res_4526_ = l_Lean_Expr_betaRev(v_f_4520_, v_revArgs_4521_, v_useZeta_boxed_4524_, v_preserveMData_boxed_4525_);
lean_dec_ref(v_revArgs_4521_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4527_, lean_object* v_args_4528_){
_start:
{
lean_object* v___x_4529_; uint8_t v___x_4530_; lean_object* v___x_4531_; 
v___x_4529_ = l_Array_reverse___redArg(v_args_4528_);
v___x_4530_ = 0;
v___x_4531_ = l_Lean_Expr_betaRev(v_f_4527_, v___x_4529_, v___x_4530_, v___x_4530_);
lean_dec_ref(v___x_4529_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4532_){
_start:
{
switch(lean_obj_tag(v_x_4532_))
{
case 6:
{
lean_object* v_body_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v_body_4533_ = lean_ctor_get(v_x_4532_, 2);
v___x_4534_ = l_Lean_Expr_getNumHeadLambdas(v_body_4533_);
v___x_4535_ = lean_unsigned_to_nat(1u);
v___x_4536_ = lean_nat_add(v___x_4534_, v___x_4535_);
lean_dec(v___x_4534_);
return v___x_4536_;
}
case 10:
{
lean_object* v_expr_4537_; 
v_expr_4537_ = lean_ctor_get(v_x_4532_, 1);
v_x_4532_ = v_expr_4537_;
goto _start;
}
default: 
{
lean_object* v___x_4539_; 
v___x_4539_ = lean_unsigned_to_nat(0u);
return v___x_4539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l_Lean_Expr_getNumHeadLambdas(v_x_4540_);
lean_dec_ref(v_x_4540_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object* v_x_4542_){
_start:
{
switch(lean_obj_tag(v_x_4542_))
{
case 6:
{
lean_object* v_body_4543_; 
v_body_4543_ = lean_ctor_get(v_x_4542_, 2);
v_x_4542_ = v_body_4543_;
goto _start;
}
case 10:
{
lean_object* v_expr_4545_; 
v_expr_4545_ = lean_ctor_get(v_x_4542_, 1);
v_x_4542_ = v_expr_4545_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_4542_);
return v_x_4542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object* v_x_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = l_Lean_Expr_getLambdaBody(v_x_4547_);
lean_dec_ref(v_x_4547_);
return v_res_4548_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4549_, lean_object* v_x_4550_){
_start:
{
switch(lean_obj_tag(v_x_4550_))
{
case 6:
{
uint8_t v___x_4551_; 
v___x_4551_ = 1;
return v___x_4551_;
}
case 8:
{
if (v_useZeta_4549_ == 0)
{
return v_useZeta_4549_;
}
else
{
lean_object* v_body_4552_; 
v_body_4552_ = lean_ctor_get(v_x_4550_, 3);
v_x_4550_ = v_body_4552_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4554_; 
v_expr_4554_ = lean_ctor_get(v_x_4550_, 1);
v_x_4550_ = v_expr_4554_;
goto _start;
}
default: 
{
uint8_t v___x_4556_; 
v___x_4556_ = 0;
return v___x_4556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4557_, lean_object* v_x_4558_){
_start:
{
uint8_t v_useZeta_boxed_4559_; uint8_t v_res_4560_; lean_object* v_r_4561_; 
v_useZeta_boxed_4559_ = lean_unbox(v_useZeta_4557_);
v_res_4560_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4559_, v_x_4558_);
lean_dec_ref(v_x_4558_);
v_r_4561_ = lean_box(v_res_4560_);
return v_r_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4562_){
_start:
{
lean_object* v_f_4563_; uint8_t v___x_4564_; uint8_t v___x_4565_; 
v_f_4563_ = l_Lean_Expr_getAppFn(v_e_4562_);
v___x_4564_ = 0;
v___x_4565_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4564_, v_f_4563_);
if (v___x_4565_ == 0)
{
lean_dec_ref(v_f_4563_);
return v_e_4562_;
}
else
{
lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4566_ = l_Lean_Expr_getAppNumArgs(v_e_4562_);
v___x_4567_ = lean_mk_empty_array_with_capacity(v___x_4566_);
lean_dec(v___x_4566_);
v___x_4568_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4562_, v___x_4567_);
v___x_4569_ = l_Lean_Expr_betaRev(v_f_4563_, v___x_4568_, v___x_4564_, v___x_4564_);
lean_dec_ref(v___x_4568_);
return v___x_4569_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4570_, uint8_t v_useZeta_4571_){
_start:
{
uint8_t v___x_4572_; 
v___x_4572_ = l_Lean_Expr_isApp(v_e_4570_);
if (v___x_4572_ == 0)
{
return v___x_4572_;
}
else
{
lean_object* v___x_4573_; uint8_t v___x_4574_; 
v___x_4573_ = l_Lean_Expr_getAppFn(v_e_4570_);
v___x_4574_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4571_, v___x_4573_);
lean_dec_ref(v___x_4573_);
return v___x_4574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4575_, lean_object* v_useZeta_4576_){
_start:
{
uint8_t v_useZeta_boxed_4577_; uint8_t v_res_4578_; lean_object* v_r_4579_; 
v_useZeta_boxed_4577_ = lean_unbox(v_useZeta_4576_);
v_res_4578_ = l_Lean_Expr_isHeadBetaTarget(v_e_4575_, v_useZeta_boxed_4577_);
lean_dec_ref(v_e_4575_);
v_r_4579_ = lean_box(v_res_4578_);
return v_r_4579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4580_, lean_object* v_x_4581_, lean_object* v_x_4582_){
_start:
{
lean_object* v_f_4584_; 
if (lean_obj_tag(v_x_4580_) == 5)
{
lean_object* v_arg_4588_; 
v_arg_4588_ = lean_ctor_get(v_x_4580_, 1);
if (lean_obj_tag(v_arg_4588_) == 0)
{
lean_object* v_fn_4589_; lean_object* v_deBruijnIndex_4590_; lean_object* v_zero_4591_; uint8_t v_isZero_4592_; 
v_fn_4589_ = lean_ctor_get(v_x_4580_, 0);
v_deBruijnIndex_4590_ = lean_ctor_get(v_arg_4588_, 0);
v_zero_4591_ = lean_unsigned_to_nat(0u);
v_isZero_4592_ = lean_nat_dec_eq(v_x_4581_, v_zero_4591_);
if (v_isZero_4592_ == 1)
{
lean_dec(v_x_4582_);
lean_dec(v_x_4581_);
v_f_4584_ = v_x_4580_;
goto v___jp_4583_;
}
else
{
uint8_t v___x_4593_; 
lean_inc(v_deBruijnIndex_4590_);
lean_inc_ref(v_fn_4589_);
lean_dec_ref_known(v_x_4580_, 2);
v___x_4593_ = lean_nat_dec_eq(v_deBruijnIndex_4590_, v_x_4582_);
lean_dec(v_deBruijnIndex_4590_);
if (v___x_4593_ == 0)
{
lean_object* v___x_4594_; 
lean_dec_ref(v_fn_4589_);
lean_dec(v_x_4582_);
lean_dec(v_x_4581_);
v___x_4594_ = lean_box(0);
return v___x_4594_;
}
else
{
lean_object* v_one_4595_; lean_object* v_n_4596_; lean_object* v___x_4597_; 
v_one_4595_ = lean_unsigned_to_nat(1u);
v_n_4596_ = lean_nat_sub(v_x_4581_, v_one_4595_);
lean_dec(v_x_4581_);
v___x_4597_ = lean_nat_add(v_x_4582_, v_one_4595_);
lean_dec(v_x_4582_);
v_x_4580_ = v_fn_4589_;
v_x_4581_ = v_n_4596_;
v_x_4582_ = v___x_4597_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4599_; uint8_t v_isZero_4600_; 
lean_dec(v_x_4582_);
v_zero_4599_ = lean_unsigned_to_nat(0u);
v_isZero_4600_ = lean_nat_dec_eq(v_x_4581_, v_zero_4599_);
lean_dec(v_x_4581_);
if (v_isZero_4600_ == 1)
{
v_f_4584_ = v_x_4580_;
goto v___jp_4583_;
}
else
{
lean_object* v___x_4601_; 
lean_dec_ref_known(v_x_4580_, 2);
v___x_4601_ = lean_box(0);
return v___x_4601_;
}
}
}
else
{
lean_object* v_zero_4602_; uint8_t v_isZero_4603_; 
lean_dec(v_x_4582_);
v_zero_4602_ = lean_unsigned_to_nat(0u);
v_isZero_4603_ = lean_nat_dec_eq(v_x_4581_, v_zero_4602_);
lean_dec(v_x_4581_);
if (v_isZero_4603_ == 1)
{
v_f_4584_ = v_x_4580_;
goto v___jp_4583_;
}
else
{
lean_object* v___x_4604_; 
lean_dec_ref(v_x_4580_);
v___x_4604_ = lean_box(0);
return v___x_4604_;
}
}
v___jp_4583_:
{
uint8_t v___x_4585_; 
v___x_4585_ = l_Lean_Expr_hasLooseBVars(v_f_4584_);
if (v___x_4585_ == 0)
{
lean_object* v___x_4586_; 
v___x_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4586_, 0, v_f_4584_);
return v___x_4586_;
}
else
{
lean_object* v___x_4587_; 
lean_dec_ref(v_f_4584_);
v___x_4587_ = lean_box(0);
return v___x_4587_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4605_, lean_object* v_x_4606_){
_start:
{
if (lean_obj_tag(v_x_4605_) == 6)
{
lean_object* v_body_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v_body_4607_ = lean_ctor_get(v_x_4605_, 2);
lean_inc_ref(v_body_4607_);
lean_dec_ref_known(v_x_4605_, 3);
v___x_4608_ = lean_unsigned_to_nat(1u);
v___x_4609_ = lean_nat_add(v_x_4606_, v___x_4608_);
lean_dec(v_x_4606_);
v_x_4605_ = v_body_4607_;
v_x_4606_ = v___x_4609_;
goto _start;
}
else
{
lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4611_ = lean_unsigned_to_nat(0u);
v___x_4612_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4605_, v_x_4606_, v___x_4611_);
return v___x_4612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4613_){
_start:
{
lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4614_ = lean_unsigned_to_nat(0u);
v___x_4615_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4613_, v___x_4614_);
return v___x_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4616_){
_start:
{
if (lean_obj_tag(v_x_4616_) == 6)
{
lean_object* v_body_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
v_body_4617_ = lean_ctor_get(v_x_4616_, 2);
lean_inc_ref(v_body_4617_);
lean_dec_ref_known(v_x_4616_, 3);
v___x_4618_ = lean_unsigned_to_nat(1u);
v___x_4619_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4617_, v___x_4618_);
return v___x_4619_;
}
else
{
lean_object* v___x_4620_; 
lean_dec_ref(v_x_4616_);
v___x_4620_ = lean_box(0);
return v___x_4620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4624_){
_start:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; uint8_t v___x_4627_; 
v___x_4625_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4626_ = lean_unsigned_to_nat(2u);
v___x_4627_ = l_Lean_Expr_isAppOfArity(v_e_4624_, v___x_4625_, v___x_4626_);
if (v___x_4627_ == 0)
{
lean_object* v___x_4628_; 
v___x_4628_ = lean_box(0);
return v___x_4628_;
}
else
{
lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4629_ = l_Lean_Expr_appArg_x21(v_e_4624_);
v___x_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4630_, 0, v___x_4629_);
return v___x_4630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4631_){
_start:
{
lean_object* v_res_4632_; 
v_res_4632_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4631_);
lean_dec_ref(v_e_4631_);
return v_res_4632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4636_){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; uint8_t v___x_4639_; 
v___x_4637_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4638_ = lean_unsigned_to_nat(2u);
v___x_4639_ = l_Lean_Expr_isAppOfArity(v_e_4636_, v___x_4637_, v___x_4638_);
if (v___x_4639_ == 0)
{
lean_object* v___x_4640_; 
v___x_4640_ = lean_box(0);
return v___x_4640_;
}
else
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = l_Lean_Expr_appArg_x21(v_e_4636_);
v___x_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
return v___x_4642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4643_);
lean_dec_ref(v_e_4643_);
return v_res_4644_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOutParam(lean_object* v_e_4648_){
_start:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; uint8_t v___x_4651_; 
v___x_4649_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4650_ = lean_unsigned_to_nat(1u);
v___x_4651_ = l_Lean_Expr_isAppOfArity(v_e_4648_, v___x_4649_, v___x_4650_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4652_){
_start:
{
uint8_t v_res_4653_; lean_object* v_r_4654_; 
v_res_4653_ = l_Lean_Expr_isOutParam(v_e_4652_);
lean_dec_ref(v_e_4652_);
v_r_4654_ = lean_box(v_res_4653_);
return v_r_4654_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4658_){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; uint8_t v___x_4661_; 
v___x_4659_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4660_ = lean_unsigned_to_nat(1u);
v___x_4661_ = l_Lean_Expr_isAppOfArity(v_e_4658_, v___x_4659_, v___x_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4662_){
_start:
{
uint8_t v_res_4663_; lean_object* v_r_4664_; 
v_res_4663_ = l_Lean_Expr_isSemiOutParam(v_e_4662_);
lean_dec_ref(v_e_4662_);
v_r_4664_ = lean_box(v_res_4663_);
return v_r_4664_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4665_){
_start:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; 
v___x_4666_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4667_ = lean_unsigned_to_nat(2u);
v___x_4668_ = l_Lean_Expr_isAppOfArity(v_e_4665_, v___x_4666_, v___x_4667_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4669_){
_start:
{
uint8_t v_res_4670_; lean_object* v_r_4671_; 
v_res_4670_ = l_Lean_Expr_isOptParam(v_e_4669_);
lean_dec_ref(v_e_4669_);
v_r_4671_ = lean_box(v_res_4670_);
return v_r_4671_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4672_){
_start:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; uint8_t v___x_4675_; 
v___x_4673_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4674_ = lean_unsigned_to_nat(2u);
v___x_4675_ = l_Lean_Expr_isAppOfArity(v_e_4672_, v___x_4673_, v___x_4674_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4676_){
_start:
{
uint8_t v_res_4677_; lean_object* v_r_4678_; 
v_res_4677_ = l_Lean_Expr_isAutoParam(v_e_4676_);
lean_dec_ref(v_e_4676_);
v_r_4678_ = lean_box(v_res_4677_);
return v_r_4678_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4679_){
_start:
{
lean_object* v___x_4680_; 
v___x_4680_ = l_Lean_Expr_getAppFn(v_e_4679_);
if (lean_obj_tag(v___x_4680_) == 4)
{
lean_object* v_declName_4681_; uint8_t v___y_4683_; lean_object* v___x_4688_; uint8_t v___x_4689_; 
v_declName_4681_ = lean_ctor_get(v___x_4680_, 0);
lean_inc(v_declName_4681_);
lean_dec_ref_known(v___x_4680_, 2);
v___x_4688_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4689_ = lean_name_eq(v_declName_4681_, v___x_4688_);
if (v___x_4689_ == 0)
{
lean_object* v___x_4690_; uint8_t v___x_4691_; 
v___x_4690_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4691_ = lean_name_eq(v_declName_4681_, v___x_4690_);
v___y_4683_ = v___x_4691_;
goto v___jp_4682_;
}
else
{
v___y_4683_ = v___x_4689_;
goto v___jp_4682_;
}
v___jp_4682_:
{
if (v___y_4683_ == 0)
{
lean_object* v___x_4684_; uint8_t v___x_4685_; 
v___x_4684_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4685_ = lean_name_eq(v_declName_4681_, v___x_4684_);
if (v___x_4685_ == 0)
{
lean_object* v___x_4686_; uint8_t v___x_4687_; 
v___x_4686_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4687_ = lean_name_eq(v_declName_4681_, v___x_4686_);
lean_dec(v_declName_4681_);
return v___x_4687_;
}
else
{
lean_dec(v_declName_4681_);
return v___x_4685_;
}
}
else
{
lean_dec(v_declName_4681_);
return v___y_4683_;
}
}
}
else
{
uint8_t v___x_4692_; 
lean_dec_ref(v___x_4680_);
v___x_4692_ = 0;
return v___x_4692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4693_){
_start:
{
uint8_t v_res_4694_; lean_object* v_r_4695_; 
v_res_4694_ = l_Lean_Expr_isTypeAnnotation(v_e_4693_);
lean_dec_ref(v_e_4693_);
v_r_4695_ = lean_box(v_res_4694_);
return v_r_4695_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4696_){
_start:
{
uint8_t v___y_4698_; uint8_t v___y_4702_; uint8_t v___x_4708_; 
v___x_4708_ = l_Lean_Expr_isOptParam(v_e_4696_);
if (v___x_4708_ == 0)
{
uint8_t v___x_4709_; 
v___x_4709_ = l_Lean_Expr_isAutoParam(v_e_4696_);
v___y_4702_ = v___x_4709_;
goto v___jp_4701_;
}
else
{
v___y_4702_ = v___x_4708_;
goto v___jp_4701_;
}
v___jp_4697_:
{
if (v___y_4698_ == 0)
{
return v_e_4696_;
}
else
{
lean_object* v___x_4699_; 
v___x_4699_ = l_Lean_Expr_appArg_x21(v_e_4696_);
lean_dec_ref(v_e_4696_);
v_e_4696_ = v___x_4699_;
goto _start;
}
}
v___jp_4701_:
{
if (v___y_4702_ == 0)
{
uint8_t v___x_4703_; 
v___x_4703_ = l_Lean_Expr_isOutParam(v_e_4696_);
if (v___x_4703_ == 0)
{
uint8_t v___x_4704_; 
v___x_4704_ = l_Lean_Expr_isSemiOutParam(v_e_4696_);
v___y_4698_ = v___x_4704_;
goto v___jp_4697_;
}
else
{
v___y_4698_ = v___x_4703_;
goto v___jp_4697_;
}
}
else
{
lean_object* v___x_4705_; lean_object* v___x_4706_; 
v___x_4705_ = l_Lean_Expr_appFn_x21(v_e_4696_);
lean_dec_ref(v_e_4696_);
v___x_4706_ = l_Lean_Expr_appArg_x21(v___x_4705_);
lean_dec_ref(v___x_4705_);
v_e_4696_ = v___x_4706_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4710_){
_start:
{
lean_object* v___x_4711_; lean_object* v_e_x27_4712_; uint8_t v___x_4713_; 
v___x_4711_ = l_Lean_Expr_consumeMData(v_e_4710_);
v_e_x27_4712_ = lean_expr_consume_type_annotations(v___x_4711_);
v___x_4713_ = lean_expr_eqv(v_e_x27_4712_, v_e_4710_);
if (v___x_4713_ == 0)
{
lean_dec_ref(v_e_4710_);
v_e_4710_ = v_e_x27_4712_;
goto _start;
}
else
{
lean_dec_ref(v_e_x27_4712_);
return v_e_4710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4715_){
_start:
{
lean_object* v_fn_4716_; lean_object* v___x_4717_; 
v_fn_4716_ = lean_ctor_get(v_e_4715_, 0);
lean_inc_ref(v_fn_4716_);
lean_dec_ref(v_e_4715_);
v___x_4717_ = l_Lean_Expr_cleanupAnnotations(v_fn_4716_);
return v___x_4717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* v_e_4718_, lean_object* v_h_4719_){
_start:
{
lean_object* v___x_4720_; 
v___x_4720_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4718_);
return v___x_4720_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4724_){
_start:
{
lean_object* v___x_4725_; lean_object* v___x_4726_; uint8_t v___x_4727_; 
v___x_4725_ = l_Lean_Expr_cleanupAnnotations(v_e_4724_);
v___x_4726_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4727_ = l_Lean_Expr_isConstOf(v___x_4725_, v___x_4726_);
lean_dec_ref(v___x_4725_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4728_){
_start:
{
uint8_t v_res_4729_; lean_object* v_r_4730_; 
v_res_4729_ = l_Lean_Expr_isFalse(v_e_4728_);
v_r_4730_ = lean_box(v_res_4729_);
return v_r_4730_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4734_){
_start:
{
lean_object* v___x_4735_; lean_object* v___x_4736_; uint8_t v___x_4737_; 
v___x_4735_ = l_Lean_Expr_cleanupAnnotations(v_e_4734_);
v___x_4736_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4737_ = l_Lean_Expr_isConstOf(v___x_4735_, v___x_4736_);
lean_dec_ref(v___x_4735_);
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4738_){
_start:
{
uint8_t v_res_4739_; lean_object* v_r_4740_; 
v_res_4739_ = l_Lean_Expr_isTrue(v_e_4738_);
v_r_4740_ = lean_box(v_res_4739_);
return v_r_4740_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object* v_e_4745_){
_start:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; 
v___x_4746_ = l_Lean_Expr_cleanupAnnotations(v_e_4745_);
v___x_4747_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_4748_ = l_Lean_Expr_isConstOf(v___x_4746_, v___x_4747_);
lean_dec_ref(v___x_4746_);
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object* v_e_4749_){
_start:
{
uint8_t v_res_4750_; lean_object* v_r_4751_; 
v_res_4750_ = l_Lean_Expr_isBoolFalse(v_e_4749_);
v_r_4751_ = lean_box(v_res_4750_);
return v_r_4751_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object* v_e_4755_){
_start:
{
lean_object* v___x_4756_; lean_object* v___x_4757_; uint8_t v___x_4758_; 
v___x_4756_ = l_Lean_Expr_cleanupAnnotations(v_e_4755_);
v___x_4757_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_4758_ = l_Lean_Expr_isConstOf(v___x_4756_, v___x_4757_);
lean_dec_ref(v___x_4756_);
return v___x_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object* v_e_4759_){
_start:
{
uint8_t v_res_4760_; lean_object* v_r_4761_; 
v_res_4760_ = l_Lean_Expr_isBoolTrue(v_e_4759_);
v_r_4761_ = lean_box(v_res_4760_);
return v_r_4761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* v_x_4762_){
_start:
{
switch(lean_obj_tag(v_x_4762_))
{
case 10:
{
lean_object* v_expr_4763_; 
v_expr_4763_ = lean_ctor_get(v_x_4762_, 1);
lean_inc_ref(v_expr_4763_);
lean_dec_ref_known(v_x_4762_, 2);
v_x_4762_ = v_expr_4763_;
goto _start;
}
case 7:
{
lean_object* v_body_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
v_body_4765_ = lean_ctor_get(v_x_4762_, 2);
lean_inc_ref(v_body_4765_);
lean_dec_ref_known(v_x_4762_, 3);
v___x_4766_ = l_Lean_Expr_getForallArity(v_body_4765_);
v___x_4767_ = lean_unsigned_to_nat(1u);
v___x_4768_ = lean_nat_add(v___x_4766_, v___x_4767_);
lean_dec(v___x_4766_);
return v___x_4768_;
}
default: 
{
uint8_t v___x_4769_; uint8_t v___x_4770_; 
v___x_4769_ = 0;
v___x_4770_ = l_Lean_Expr_isHeadBetaTarget(v_x_4762_, v___x_4769_);
if (v___x_4770_ == 0)
{
lean_object* v_e_x27_4771_; uint8_t v___x_4772_; 
lean_inc_ref(v_x_4762_);
v_e_x27_4771_ = l_Lean_Expr_cleanupAnnotations(v_x_4762_);
v___x_4772_ = lean_expr_eqv(v_x_4762_, v_e_x27_4771_);
lean_dec_ref(v_x_4762_);
if (v___x_4772_ == 0)
{
v_x_4762_ = v_e_x27_4771_;
goto _start;
}
else
{
lean_object* v___x_4774_; 
lean_dec_ref(v_e_x27_4771_);
v___x_4774_ = lean_unsigned_to_nat(0u);
return v___x_4774_;
}
}
else
{
lean_object* v___x_4775_; 
v___x_4775_ = l_Lean_Expr_headBeta(v_x_4762_);
v_x_4762_ = v___x_4775_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4777_){
_start:
{
lean_object* v___x_4778_; uint8_t v___x_4779_; 
v___x_4778_ = l_Lean_Expr_cleanupAnnotations(v_e_4777_);
v___x_4779_ = l_Lean_Expr_isApp(v___x_4778_);
if (v___x_4779_ == 0)
{
lean_object* v___x_4780_; 
lean_dec_ref(v___x_4778_);
v___x_4780_ = lean_box(0);
return v___x_4780_;
}
else
{
lean_object* v___x_4781_; uint8_t v___x_4782_; 
v___x_4781_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4778_);
v___x_4782_ = l_Lean_Expr_isApp(v___x_4781_);
if (v___x_4782_ == 0)
{
lean_object* v___x_4783_; 
lean_dec_ref(v___x_4781_);
v___x_4783_ = lean_box(0);
return v___x_4783_;
}
else
{
lean_object* v_arg_4784_; lean_object* v___x_4785_; uint8_t v___x_4786_; 
v_arg_4784_ = lean_ctor_get(v___x_4781_, 1);
lean_inc_ref(v_arg_4784_);
v___x_4785_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4781_);
v___x_4786_ = l_Lean_Expr_isApp(v___x_4785_);
if (v___x_4786_ == 0)
{
lean_object* v___x_4787_; 
lean_dec_ref(v___x_4785_);
lean_dec_ref(v_arg_4784_);
v___x_4787_ = lean_box(0);
return v___x_4787_;
}
else
{
lean_object* v___x_4788_; lean_object* v___x_4789_; uint8_t v___x_4790_; 
v___x_4788_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4785_);
v___x_4789_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4790_ = l_Lean_Expr_isConstOf(v___x_4788_, v___x_4789_);
lean_dec_ref(v___x_4788_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; 
lean_dec_ref(v_arg_4784_);
v___x_4791_ = lean_box(0);
return v___x_4791_;
}
else
{
if (lean_obj_tag(v_arg_4784_) == 9)
{
lean_object* v_a_4792_; 
v_a_4792_ = lean_ctor_get(v_arg_4784_, 0);
lean_inc_ref(v_a_4792_);
lean_dec_ref_known(v_arg_4784_, 1);
if (lean_obj_tag(v_a_4792_) == 0)
{
lean_object* v_val_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
v_val_4793_ = lean_ctor_get(v_a_4792_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v_a_4792_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v_a_4792_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_val_4793_);
lean_dec(v_a_4792_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
lean_ctor_set_tag(v___x_4795_, 1);
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_val_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
else
{
lean_object* v___x_4801_; 
lean_dec_ref(v_a_4792_);
v___x_4801_ = lean_box(0);
return v___x_4801_;
}
}
else
{
lean_object* v___x_4802_; 
lean_dec_ref(v_arg_4784_);
v___x_4802_ = lean_box(0);
return v___x_4802_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4808_){
_start:
{
lean_object* v___x_4821_; uint8_t v___x_4822_; 
lean_inc_ref(v_e_4808_);
v___x_4821_ = l_Lean_Expr_cleanupAnnotations(v_e_4808_);
v___x_4822_ = l_Lean_Expr_isApp(v___x_4821_);
if (v___x_4822_ == 0)
{
lean_dec_ref(v___x_4821_);
goto v___jp_4809_;
}
else
{
lean_object* v_arg_4823_; lean_object* v___x_4824_; uint8_t v___x_4825_; 
v_arg_4823_ = lean_ctor_get(v___x_4821_, 1);
lean_inc_ref(v_arg_4823_);
v___x_4824_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4821_);
v___x_4825_ = l_Lean_Expr_isApp(v___x_4824_);
if (v___x_4825_ == 0)
{
lean_dec_ref(v___x_4824_);
lean_dec_ref(v_arg_4823_);
goto v___jp_4809_;
}
else
{
lean_object* v___x_4826_; uint8_t v___x_4827_; 
v___x_4826_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4824_);
v___x_4827_ = l_Lean_Expr_isApp(v___x_4826_);
if (v___x_4827_ == 0)
{
lean_dec_ref(v___x_4826_);
lean_dec_ref(v_arg_4823_);
goto v___jp_4809_;
}
else
{
lean_object* v___x_4828_; lean_object* v___x_4829_; uint8_t v___x_4830_; 
v___x_4828_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4826_);
v___x_4829_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4830_ = l_Lean_Expr_isConstOf(v___x_4828_, v___x_4829_);
lean_dec_ref(v___x_4828_);
if (v___x_4830_ == 0)
{
lean_dec_ref(v_arg_4823_);
goto v___jp_4809_;
}
else
{
lean_object* v___x_4831_; 
lean_dec_ref(v_e_4808_);
v___x_4831_ = l_Lean_Expr_nat_x3f(v_arg_4823_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_object* v___x_4832_; 
v___x_4832_ = lean_box(0);
return v___x_4832_;
}
else
{
lean_object* v_val_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4845_; 
v_val_4833_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4835_ = v___x_4831_;
v_isShared_4836_ = v_isSharedCheck_4845_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_val_4833_);
lean_dec(v___x_4831_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4845_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4837_; uint8_t v___x_4838_; 
v___x_4837_ = lean_unsigned_to_nat(0u);
v___x_4838_ = lean_nat_dec_eq(v_val_4833_, v___x_4837_);
if (v___x_4838_ == 0)
{
lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4842_; 
v___x_4839_ = lean_nat_to_int(v_val_4833_);
v___x_4840_ = lean_int_neg(v___x_4839_);
lean_dec(v___x_4839_);
if (v_isShared_4836_ == 0)
{
lean_ctor_set(v___x_4835_, 0, v___x_4840_);
v___x_4842_ = v___x_4835_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4840_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
return v___x_4842_;
}
}
else
{
lean_object* v___x_4844_; 
lean_del_object(v___x_4835_);
lean_dec(v_val_4833_);
v___x_4844_ = lean_box(0);
return v___x_4844_;
}
}
}
}
}
}
}
v___jp_4809_:
{
lean_object* v___x_4810_; 
v___x_4810_ = l_Lean_Expr_nat_x3f(v_e_4808_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v___x_4811_; 
v___x_4811_ = lean_box(0);
return v___x_4811_;
}
else
{
lean_object* v_val_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4820_; 
v_val_4812_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4814_ = v___x_4810_;
v_isShared_4815_ = v_isSharedCheck_4820_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_val_4812_);
lean_dec(v___x_4810_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4820_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4816_; lean_object* v___x_4818_; 
v___x_4816_ = lean_nat_to_int(v_val_4812_);
if (v_isShared_4815_ == 0)
{
lean_ctor_set(v___x_4814_, 0, v___x_4816_);
v___x_4818_ = v___x_4814_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v___x_4816_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4846_, lean_object* v_e_4847_){
_start:
{
uint8_t v___x_4848_; lean_object* v_d_4850_; lean_object* v_b_4851_; 
v___x_4848_ = l_Lean_Expr_hasFVar(v_e_4847_);
if (v___x_4848_ == 0)
{
lean_dec_ref(v_e_4847_);
lean_dec_ref(v_p_4846_);
return v___x_4848_;
}
else
{
switch(lean_obj_tag(v_e_4847_))
{
case 7:
{
lean_object* v_binderType_4854_; lean_object* v_body_4855_; 
v_binderType_4854_ = lean_ctor_get(v_e_4847_, 1);
lean_inc_ref(v_binderType_4854_);
v_body_4855_ = lean_ctor_get(v_e_4847_, 2);
lean_inc_ref(v_body_4855_);
lean_dec_ref_known(v_e_4847_, 3);
v_d_4850_ = v_binderType_4854_;
v_b_4851_ = v_body_4855_;
goto v___jp_4849_;
}
case 6:
{
lean_object* v_binderType_4856_; lean_object* v_body_4857_; 
v_binderType_4856_ = lean_ctor_get(v_e_4847_, 1);
lean_inc_ref(v_binderType_4856_);
v_body_4857_ = lean_ctor_get(v_e_4847_, 2);
lean_inc_ref(v_body_4857_);
lean_dec_ref_known(v_e_4847_, 3);
v_d_4850_ = v_binderType_4856_;
v_b_4851_ = v_body_4857_;
goto v___jp_4849_;
}
case 10:
{
lean_object* v_expr_4858_; 
v_expr_4858_ = lean_ctor_get(v_e_4847_, 1);
lean_inc_ref(v_expr_4858_);
lean_dec_ref_known(v_e_4847_, 2);
v_e_4847_ = v_expr_4858_;
goto _start;
}
case 8:
{
lean_object* v_type_4860_; lean_object* v_value_4861_; lean_object* v_body_4862_; uint8_t v___x_4863_; 
v_type_4860_ = lean_ctor_get(v_e_4847_, 1);
lean_inc_ref(v_type_4860_);
v_value_4861_ = lean_ctor_get(v_e_4847_, 2);
lean_inc_ref(v_value_4861_);
v_body_4862_ = lean_ctor_get(v_e_4847_, 3);
lean_inc_ref(v_body_4862_);
lean_dec_ref_known(v_e_4847_, 4);
lean_inc_ref(v_p_4846_);
v___x_4863_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4846_, v_type_4860_);
if (v___x_4863_ == 0)
{
uint8_t v___x_4864_; 
lean_inc_ref(v_p_4846_);
v___x_4864_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4846_, v_value_4861_);
if (v___x_4864_ == 0)
{
v_e_4847_ = v_body_4862_;
goto _start;
}
else
{
lean_dec_ref(v_body_4862_);
lean_dec_ref(v_p_4846_);
return v___x_4848_;
}
}
else
{
lean_dec_ref(v_body_4862_);
lean_dec_ref(v_value_4861_);
lean_dec_ref(v_p_4846_);
return v___x_4848_;
}
}
case 5:
{
lean_object* v_fn_4866_; lean_object* v_arg_4867_; uint8_t v___x_4868_; 
v_fn_4866_ = lean_ctor_get(v_e_4847_, 0);
lean_inc_ref(v_fn_4866_);
v_arg_4867_ = lean_ctor_get(v_e_4847_, 1);
lean_inc_ref(v_arg_4867_);
lean_dec_ref_known(v_e_4847_, 2);
lean_inc_ref(v_p_4846_);
v___x_4868_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4846_, v_fn_4866_);
if (v___x_4868_ == 0)
{
v_e_4847_ = v_arg_4867_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4867_);
lean_dec_ref(v_p_4846_);
return v___x_4848_;
}
}
case 11:
{
lean_object* v_struct_4870_; 
v_struct_4870_ = lean_ctor_get(v_e_4847_, 2);
lean_inc_ref(v_struct_4870_);
lean_dec_ref_known(v_e_4847_, 3);
v_e_4847_ = v_struct_4870_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4872_; lean_object* v___x_4873_; uint8_t v___x_4874_; 
v_fvarId_4872_ = lean_ctor_get(v_e_4847_, 0);
lean_inc(v_fvarId_4872_);
lean_dec_ref_known(v_e_4847_, 1);
v___x_4873_ = lean_apply_1(v_p_4846_, v_fvarId_4872_);
v___x_4874_ = lean_unbox(v___x_4873_);
return v___x_4874_;
}
default: 
{
uint8_t v___x_4875_; 
lean_dec_ref(v_e_4847_);
lean_dec_ref(v_p_4846_);
v___x_4875_ = 0;
return v___x_4875_;
}
}
}
v___jp_4849_:
{
uint8_t v___x_4852_; 
lean_inc_ref(v_p_4846_);
v___x_4852_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4846_, v_d_4850_);
if (v___x_4852_ == 0)
{
v_e_4847_ = v_b_4851_;
goto _start;
}
else
{
lean_dec_ref(v_b_4851_);
lean_dec_ref(v_p_4846_);
return v___x_4848_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_4876_, lean_object* v_e_4877_){
_start:
{
uint8_t v_res_4878_; lean_object* v_r_4879_; 
v_res_4878_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4876_, v_e_4877_);
v_r_4879_ = lean_box(v_res_4878_);
return v_r_4879_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_4880_, lean_object* v_p_4881_){
_start:
{
uint8_t v___x_4882_; 
v___x_4882_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4881_, v_e_4880_);
return v___x_4882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_4883_, lean_object* v_p_4884_){
_start:
{
uint8_t v_res_4885_; lean_object* v_r_4886_; 
v_res_4885_ = l_Lean_Expr_hasAnyFVar(v_e_4883_, v_p_4884_);
v_r_4886_ = lean_box(v_res_4885_);
return v_r_4886_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_4887_, lean_object* v_e_4888_){
_start:
{
uint8_t v___x_4889_; lean_object* v_d_4891_; lean_object* v_b_4892_; 
v___x_4889_ = l_Lean_Expr_hasFVar(v_e_4888_);
if (v___x_4889_ == 0)
{
return v___x_4889_;
}
else
{
switch(lean_obj_tag(v_e_4888_))
{
case 7:
{
lean_object* v_binderType_4895_; lean_object* v_body_4896_; 
v_binderType_4895_ = lean_ctor_get(v_e_4888_, 1);
v_body_4896_ = lean_ctor_get(v_e_4888_, 2);
v_d_4891_ = v_binderType_4895_;
v_b_4892_ = v_body_4896_;
goto v___jp_4890_;
}
case 6:
{
lean_object* v_binderType_4897_; lean_object* v_body_4898_; 
v_binderType_4897_ = lean_ctor_get(v_e_4888_, 1);
v_body_4898_ = lean_ctor_get(v_e_4888_, 2);
v_d_4891_ = v_binderType_4897_;
v_b_4892_ = v_body_4898_;
goto v___jp_4890_;
}
case 10:
{
lean_object* v_expr_4899_; 
v_expr_4899_ = lean_ctor_get(v_e_4888_, 1);
v_e_4888_ = v_expr_4899_;
goto _start;
}
case 8:
{
lean_object* v_type_4901_; lean_object* v_value_4902_; lean_object* v_body_4903_; uint8_t v___x_4904_; 
v_type_4901_ = lean_ctor_get(v_e_4888_, 1);
v_value_4902_ = lean_ctor_get(v_e_4888_, 2);
v_body_4903_ = lean_ctor_get(v_e_4888_, 3);
v___x_4904_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4887_, v_type_4901_);
if (v___x_4904_ == 0)
{
uint8_t v___x_4905_; 
v___x_4905_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4887_, v_value_4902_);
if (v___x_4905_ == 0)
{
v_e_4888_ = v_body_4903_;
goto _start;
}
else
{
return v___x_4889_;
}
}
else
{
return v___x_4889_;
}
}
case 5:
{
lean_object* v_fn_4907_; lean_object* v_arg_4908_; uint8_t v___x_4909_; 
v_fn_4907_ = lean_ctor_get(v_e_4888_, 0);
v_arg_4908_ = lean_ctor_get(v_e_4888_, 1);
v___x_4909_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4887_, v_fn_4907_);
if (v___x_4909_ == 0)
{
v_e_4888_ = v_arg_4908_;
goto _start;
}
else
{
return v___x_4889_;
}
}
case 11:
{
lean_object* v_struct_4911_; 
v_struct_4911_ = lean_ctor_get(v_e_4888_, 2);
v_e_4888_ = v_struct_4911_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4913_; uint8_t v___x_4914_; 
v_fvarId_4913_ = lean_ctor_get(v_e_4888_, 0);
v___x_4914_ = lean_name_eq(v_fvarId_4913_, v_fvarId_4887_);
return v___x_4914_;
}
default: 
{
uint8_t v___x_4915_; 
v___x_4915_ = 0;
return v___x_4915_;
}
}
}
v___jp_4890_:
{
uint8_t v___x_4893_; 
v___x_4893_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4887_, v_d_4891_);
if (v___x_4893_ == 0)
{
v_e_4888_ = v_b_4892_;
goto _start;
}
else
{
return v___x_4889_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_4916_, lean_object* v_e_4917_){
_start:
{
uint8_t v_res_4918_; lean_object* v_r_4919_; 
v_res_4918_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4916_, v_e_4917_);
lean_dec_ref(v_e_4917_);
lean_dec(v_fvarId_4916_);
v_r_4919_ = lean_box(v_res_4918_);
return v_r_4919_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_4920_, lean_object* v_fvarId_4921_){
_start:
{
uint8_t v___x_4922_; 
v___x_4922_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4921_, v_e_4920_);
return v___x_4922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_4923_, lean_object* v_fvarId_4924_){
_start:
{
uint8_t v_res_4925_; lean_object* v_r_4926_; 
v_res_4925_ = l_Lean_Expr_containsFVar(v_e_4923_, v_fvarId_4924_);
lean_dec(v_fvarId_4924_);
lean_dec_ref(v_e_4923_);
v_r_4926_ = lean_box(v_res_4925_);
return v_r_4926_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4928_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_4929_ = lean_unsigned_to_nat(18u);
v___x_4930_ = lean_unsigned_to_nat(1847u);
v___x_4931_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_4932_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4933_ = l_mkPanicMessageWithDecl(v___x_4932_, v___x_4931_, v___x_4930_, v___x_4929_, v___x_4928_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_4934_, lean_object* v_newFn_4935_, lean_object* v_newArg_4936_){
_start:
{
uint8_t v___y_4938_; 
if (lean_obj_tag(v_e_4934_) == 5)
{
lean_object* v_fn_4940_; lean_object* v_arg_4941_; size_t v___x_4942_; size_t v___x_4943_; uint8_t v___x_4944_; 
v_fn_4940_ = lean_ctor_get(v_e_4934_, 0);
v_arg_4941_ = lean_ctor_get(v_e_4934_, 1);
v___x_4942_ = lean_ptr_addr(v_fn_4940_);
v___x_4943_ = lean_ptr_addr(v_newFn_4935_);
v___x_4944_ = lean_usize_dec_eq(v___x_4942_, v___x_4943_);
if (v___x_4944_ == 0)
{
v___y_4938_ = v___x_4944_;
goto v___jp_4937_;
}
else
{
size_t v___x_4945_; size_t v___x_4946_; uint8_t v___x_4947_; 
v___x_4945_ = lean_ptr_addr(v_arg_4941_);
v___x_4946_ = lean_ptr_addr(v_newArg_4936_);
v___x_4947_ = lean_usize_dec_eq(v___x_4945_, v___x_4946_);
v___y_4938_ = v___x_4947_;
goto v___jp_4937_;
}
}
else
{
lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; 
lean_dec_ref(v_newArg_4936_);
lean_dec_ref(v_newFn_4935_);
v___x_4948_ = l_Lean_instInhabitedExpr;
v___x_4949_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_4950_ = l_panic___redArg(v___x_4948_, v___x_4949_);
return v___x_4950_;
}
v___jp_4937_:
{
if (v___y_4938_ == 0)
{
lean_object* v___x_4939_; 
v___x_4939_ = l_Lean_Expr_app___override(v_newFn_4935_, v_newArg_4936_);
return v___x_4939_;
}
else
{
lean_dec_ref(v_newArg_4936_);
lean_dec_ref(v_newFn_4935_);
lean_inc_ref(v_e_4934_);
return v_e_4934_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_4951_, lean_object* v_newFn_4952_, lean_object* v_newArg_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_4951_, v_newFn_4952_, v_newArg_4953_);
lean_dec_ref(v_e_4951_);
return v_res_4954_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4956_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_4957_ = lean_unsigned_to_nat(20u);
v___x_4958_ = lean_unsigned_to_nat(1858u);
v___x_4959_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_4960_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4961_ = l_mkPanicMessageWithDecl(v___x_4960_, v___x_4959_, v___x_4958_, v___x_4957_, v___x_4956_);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_4962_, lean_object* v_fvarIdNew_4963_){
_start:
{
if (lean_obj_tag(v_e_4962_) == 1)
{
lean_object* v_fvarId_4964_; uint8_t v___x_4965_; 
v_fvarId_4964_ = lean_ctor_get(v_e_4962_, 0);
v___x_4965_ = lean_name_eq(v_fvarId_4964_, v_fvarIdNew_4963_);
if (v___x_4965_ == 0)
{
lean_object* v___x_4966_; 
v___x_4966_ = l_Lean_Expr_fvar___override(v_fvarIdNew_4963_);
return v___x_4966_;
}
else
{
lean_dec(v_fvarIdNew_4963_);
lean_inc_ref(v_e_4962_);
return v_e_4962_;
}
}
else
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
lean_dec(v_fvarIdNew_4963_);
v___x_4967_ = l_Lean_instInhabitedExpr;
v___x_4968_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_4969_ = l_panic___redArg(v___x_4967_, v___x_4968_);
return v___x_4969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_4970_, lean_object* v_fvarIdNew_4971_){
_start:
{
lean_object* v_res_4972_; 
v_res_4972_ = l_Lean_Expr_updateFVar_x21(v_e_4970_, v_fvarIdNew_4971_);
lean_dec_ref(v_e_4970_);
return v_res_4972_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4974_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_4975_ = lean_unsigned_to_nat(18u);
v___x_4976_ = lean_unsigned_to_nat(1863u);
v___x_4977_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_4978_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4979_ = l_mkPanicMessageWithDecl(v___x_4978_, v___x_4977_, v___x_4976_, v___x_4975_, v___x_4974_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_4980_, lean_object* v_newLevels_4981_){
_start:
{
if (lean_obj_tag(v_e_4980_) == 4)
{
lean_object* v_declName_4982_; lean_object* v_us_4983_; uint8_t v___x_4984_; 
v_declName_4982_ = lean_ctor_get(v_e_4980_, 0);
v_us_4983_ = lean_ctor_get(v_e_4980_, 1);
v___x_4984_ = l_ptrEqList___redArg(v_us_4983_, v_newLevels_4981_);
if (v___x_4984_ == 0)
{
lean_object* v___x_4985_; 
lean_inc(v_declName_4982_);
lean_dec_ref_known(v_e_4980_, 2);
v___x_4985_ = l_Lean_Expr_const___override(v_declName_4982_, v_newLevels_4981_);
return v___x_4985_;
}
else
{
lean_dec(v_newLevels_4981_);
return v_e_4980_;
}
}
else
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
lean_dec(v_newLevels_4981_);
lean_dec_ref(v_e_4980_);
v___x_4986_ = l_Lean_instInhabitedExpr;
v___x_4987_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_4988_ = l_panic___redArg(v___x_4986_, v___x_4987_);
return v___x_4988_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; 
v___x_4991_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_4992_ = lean_unsigned_to_nat(14u);
v___x_4993_ = lean_unsigned_to_nat(1874u);
v___x_4994_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_4995_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4996_ = l_mkPanicMessageWithDecl(v___x_4995_, v___x_4994_, v___x_4993_, v___x_4992_, v___x_4991_);
return v___x_4996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_4997_, lean_object* v_u_x27_4998_){
_start:
{
if (lean_obj_tag(v_e_4997_) == 3)
{
lean_object* v_u_4999_; size_t v___x_5000_; size_t v___x_5001_; uint8_t v___x_5002_; 
v_u_4999_ = lean_ctor_get(v_e_4997_, 0);
v___x_5000_ = lean_ptr_addr(v_u_4999_);
v___x_5001_ = lean_ptr_addr(v_u_x27_4998_);
v___x_5002_ = lean_usize_dec_eq(v___x_5000_, v___x_5001_);
if (v___x_5002_ == 0)
{
lean_object* v___x_5003_; 
v___x_5003_ = l_Lean_Expr_sort___override(v_u_x27_4998_);
return v___x_5003_;
}
else
{
lean_dec(v_u_x27_4998_);
lean_inc_ref(v_e_4997_);
return v_e_4997_;
}
}
else
{
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
lean_dec(v_u_x27_4998_);
v___x_5004_ = l_Lean_instInhabitedExpr;
v___x_5005_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_5006_ = l_panic___redArg(v___x_5004_, v___x_5005_);
return v___x_5006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_5007_, lean_object* v_u_x27_5008_){
_start:
{
lean_object* v_res_5009_; 
v_res_5009_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_5007_, v_u_x27_5008_);
lean_dec_ref(v_e_5007_);
return v_res_5009_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5012_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_5013_ = lean_unsigned_to_nat(17u);
v___x_5014_ = lean_unsigned_to_nat(1885u);
v___x_5015_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_5016_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5017_ = l_mkPanicMessageWithDecl(v___x_5016_, v___x_5015_, v___x_5014_, v___x_5013_, v___x_5012_);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_5018_, lean_object* v_newExpr_5019_){
_start:
{
if (lean_obj_tag(v_e_5018_) == 10)
{
lean_object* v_data_5020_; lean_object* v_expr_5021_; size_t v___x_5022_; size_t v___x_5023_; uint8_t v___x_5024_; 
v_data_5020_ = lean_ctor_get(v_e_5018_, 0);
v_expr_5021_ = lean_ctor_get(v_e_5018_, 1);
v___x_5022_ = lean_ptr_addr(v_expr_5021_);
v___x_5023_ = lean_ptr_addr(v_newExpr_5019_);
v___x_5024_ = lean_usize_dec_eq(v___x_5022_, v___x_5023_);
if (v___x_5024_ == 0)
{
lean_object* v___x_5025_; 
lean_inc(v_data_5020_);
lean_dec_ref_known(v_e_5018_, 2);
v___x_5025_ = l_Lean_Expr_mdata___override(v_data_5020_, v_newExpr_5019_);
return v___x_5025_;
}
else
{
lean_dec_ref(v_newExpr_5019_);
return v_e_5018_;
}
}
else
{
lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; 
lean_dec_ref(v_newExpr_5019_);
lean_dec_ref(v_e_5018_);
v___x_5026_ = l_Lean_instInhabitedExpr;
v___x_5027_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_5028_ = l_panic___redArg(v___x_5026_, v___x_5027_);
return v___x_5028_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; 
v___x_5031_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_5032_ = lean_unsigned_to_nat(18u);
v___x_5033_ = lean_unsigned_to_nat(1896u);
v___x_5034_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_5035_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5036_ = l_mkPanicMessageWithDecl(v___x_5035_, v___x_5034_, v___x_5033_, v___x_5032_, v___x_5031_);
return v___x_5036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_5037_, lean_object* v_newExpr_5038_){
_start:
{
if (lean_obj_tag(v_e_5037_) == 11)
{
lean_object* v_typeName_5039_; lean_object* v_idx_5040_; lean_object* v_struct_5041_; size_t v___x_5042_; size_t v___x_5043_; uint8_t v___x_5044_; 
v_typeName_5039_ = lean_ctor_get(v_e_5037_, 0);
v_idx_5040_ = lean_ctor_get(v_e_5037_, 1);
v_struct_5041_ = lean_ctor_get(v_e_5037_, 2);
v___x_5042_ = lean_ptr_addr(v_struct_5041_);
v___x_5043_ = lean_ptr_addr(v_newExpr_5038_);
v___x_5044_ = lean_usize_dec_eq(v___x_5042_, v___x_5043_);
if (v___x_5044_ == 0)
{
lean_object* v___x_5045_; 
lean_inc(v_idx_5040_);
lean_inc(v_typeName_5039_);
lean_dec_ref_known(v_e_5037_, 3);
v___x_5045_ = l_Lean_Expr_proj___override(v_typeName_5039_, v_idx_5040_, v_newExpr_5038_);
return v___x_5045_;
}
else
{
lean_dec_ref(v_newExpr_5038_);
return v_e_5037_;
}
}
else
{
lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
lean_dec_ref(v_newExpr_5038_);
lean_dec_ref(v_e_5037_);
v___x_5046_ = l_Lean_instInhabitedExpr;
v___x_5047_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_5048_ = l_panic___redArg(v___x_5046_, v___x_5047_);
return v___x_5048_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5051_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5052_ = lean_unsigned_to_nat(23u);
v___x_5053_ = lean_unsigned_to_nat(1911u);
v___x_5054_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_5055_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5056_ = l_mkPanicMessageWithDecl(v___x_5055_, v___x_5054_, v___x_5053_, v___x_5052_, v___x_5051_);
return v___x_5056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_5057_, uint8_t v_newBinfo_5058_, lean_object* v_newDomain_5059_, lean_object* v_newBody_5060_){
_start:
{
if (lean_obj_tag(v_e_5057_) == 7)
{
lean_object* v_binderName_5061_; lean_object* v_binderType_5062_; lean_object* v_body_5063_; uint8_t v_binderInfo_5064_; uint8_t v___y_5066_; size_t v___x_5070_; size_t v___x_5071_; uint8_t v___x_5072_; 
v_binderName_5061_ = lean_ctor_get(v_e_5057_, 0);
v_binderType_5062_ = lean_ctor_get(v_e_5057_, 1);
v_body_5063_ = lean_ctor_get(v_e_5057_, 2);
v_binderInfo_5064_ = lean_ctor_get_uint8(v_e_5057_, sizeof(void*)*3 + 8);
v___x_5070_ = lean_ptr_addr(v_binderType_5062_);
v___x_5071_ = lean_ptr_addr(v_newDomain_5059_);
v___x_5072_ = lean_usize_dec_eq(v___x_5070_, v___x_5071_);
if (v___x_5072_ == 0)
{
v___y_5066_ = v___x_5072_;
goto v___jp_5065_;
}
else
{
size_t v___x_5073_; size_t v___x_5074_; uint8_t v___x_5075_; 
v___x_5073_ = lean_ptr_addr(v_body_5063_);
v___x_5074_ = lean_ptr_addr(v_newBody_5060_);
v___x_5075_ = lean_usize_dec_eq(v___x_5073_, v___x_5074_);
v___y_5066_ = v___x_5075_;
goto v___jp_5065_;
}
v___jp_5065_:
{
if (v___y_5066_ == 0)
{
lean_object* v___x_5067_; 
lean_inc(v_binderName_5061_);
lean_dec_ref_known(v_e_5057_, 3);
v___x_5067_ = l_Lean_Expr_forallE___override(v_binderName_5061_, v_newDomain_5059_, v_newBody_5060_, v_newBinfo_5058_);
return v___x_5067_;
}
else
{
uint8_t v___x_5068_; 
v___x_5068_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5064_, v_newBinfo_5058_);
if (v___x_5068_ == 0)
{
lean_object* v___x_5069_; 
lean_inc(v_binderName_5061_);
lean_dec_ref_known(v_e_5057_, 3);
v___x_5069_ = l_Lean_Expr_forallE___override(v_binderName_5061_, v_newDomain_5059_, v_newBody_5060_, v_newBinfo_5058_);
return v___x_5069_;
}
else
{
lean_dec_ref(v_newBody_5060_);
lean_dec_ref(v_newDomain_5059_);
return v_e_5057_;
}
}
}
}
else
{
lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; 
lean_dec_ref(v_newBody_5060_);
lean_dec_ref(v_newDomain_5059_);
lean_dec_ref(v_e_5057_);
v___x_5076_ = l_Lean_instInhabitedExpr;
v___x_5077_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_5078_ = l_panic___redArg(v___x_5076_, v___x_5077_);
return v___x_5078_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_5079_, lean_object* v_newBinfo_5080_, lean_object* v_newDomain_5081_, lean_object* v_newBody_5082_){
_start:
{
uint8_t v_newBinfo_boxed_5083_; lean_object* v_res_5084_; 
v_newBinfo_boxed_5083_ = lean_unbox(v_newBinfo_5080_);
v_res_5084_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5079_, v_newBinfo_boxed_5083_, v_newDomain_5081_, v_newBody_5082_);
return v_res_5084_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; 
v___x_5086_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5087_ = lean_unsigned_to_nat(24u);
v___x_5088_ = lean_unsigned_to_nat(1922u);
v___x_5089_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_5090_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5091_ = l_mkPanicMessageWithDecl(v___x_5090_, v___x_5089_, v___x_5088_, v___x_5087_, v___x_5086_);
return v___x_5091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_5092_, lean_object* v_newDomain_5093_, lean_object* v_newBody_5094_){
_start:
{
if (lean_obj_tag(v_e_5092_) == 7)
{
lean_object* v_binderName_5095_; lean_object* v_binderType_5096_; lean_object* v_body_5097_; uint8_t v_binderInfo_5098_; uint8_t v___y_5100_; size_t v___x_5104_; size_t v___x_5105_; uint8_t v___x_5106_; 
v_binderName_5095_ = lean_ctor_get(v_e_5092_, 0);
v_binderType_5096_ = lean_ctor_get(v_e_5092_, 1);
v_body_5097_ = lean_ctor_get(v_e_5092_, 2);
v_binderInfo_5098_ = lean_ctor_get_uint8(v_e_5092_, sizeof(void*)*3 + 8);
v___x_5104_ = lean_ptr_addr(v_binderType_5096_);
v___x_5105_ = lean_ptr_addr(v_newDomain_5093_);
v___x_5106_ = lean_usize_dec_eq(v___x_5104_, v___x_5105_);
if (v___x_5106_ == 0)
{
v___y_5100_ = v___x_5106_;
goto v___jp_5099_;
}
else
{
size_t v___x_5107_; size_t v___x_5108_; uint8_t v___x_5109_; 
v___x_5107_ = lean_ptr_addr(v_body_5097_);
v___x_5108_ = lean_ptr_addr(v_newBody_5094_);
v___x_5109_ = lean_usize_dec_eq(v___x_5107_, v___x_5108_);
v___y_5100_ = v___x_5109_;
goto v___jp_5099_;
}
v___jp_5099_:
{
if (v___y_5100_ == 0)
{
lean_object* v___x_5101_; 
lean_inc(v_binderName_5095_);
lean_dec_ref_known(v_e_5092_, 3);
v___x_5101_ = l_Lean_Expr_forallE___override(v_binderName_5095_, v_newDomain_5093_, v_newBody_5094_, v_binderInfo_5098_);
return v___x_5101_;
}
else
{
uint8_t v___x_5102_; 
v___x_5102_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5098_, v_binderInfo_5098_);
if (v___x_5102_ == 0)
{
lean_object* v___x_5103_; 
lean_inc(v_binderName_5095_);
lean_dec_ref_known(v_e_5092_, 3);
v___x_5103_ = l_Lean_Expr_forallE___override(v_binderName_5095_, v_newDomain_5093_, v_newBody_5094_, v_binderInfo_5098_);
return v___x_5103_;
}
else
{
lean_dec_ref(v_newBody_5094_);
lean_dec_ref(v_newDomain_5093_);
return v_e_5092_;
}
}
}
}
else
{
lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; 
lean_dec_ref(v_newBody_5094_);
lean_dec_ref(v_newDomain_5093_);
lean_dec_ref(v_e_5092_);
v___x_5110_ = l_Lean_instInhabitedExpr;
v___x_5111_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_5112_ = l_panic___redArg(v___x_5110_, v___x_5111_);
return v___x_5112_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5115_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5116_ = lean_unsigned_to_nat(19u);
v___x_5117_ = lean_unsigned_to_nat(1931u);
v___x_5118_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_5119_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5120_ = l_mkPanicMessageWithDecl(v___x_5119_, v___x_5118_, v___x_5117_, v___x_5116_, v___x_5115_);
return v___x_5120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_5121_, uint8_t v_newBinfo_5122_, lean_object* v_newDomain_5123_, lean_object* v_newBody_5124_){
_start:
{
if (lean_obj_tag(v_e_5121_) == 6)
{
lean_object* v_binderName_5125_; lean_object* v_binderType_5126_; lean_object* v_body_5127_; uint8_t v_binderInfo_5128_; uint8_t v___y_5130_; size_t v___x_5134_; size_t v___x_5135_; uint8_t v___x_5136_; 
v_binderName_5125_ = lean_ctor_get(v_e_5121_, 0);
v_binderType_5126_ = lean_ctor_get(v_e_5121_, 1);
v_body_5127_ = lean_ctor_get(v_e_5121_, 2);
v_binderInfo_5128_ = lean_ctor_get_uint8(v_e_5121_, sizeof(void*)*3 + 8);
v___x_5134_ = lean_ptr_addr(v_binderType_5126_);
v___x_5135_ = lean_ptr_addr(v_newDomain_5123_);
v___x_5136_ = lean_usize_dec_eq(v___x_5134_, v___x_5135_);
if (v___x_5136_ == 0)
{
v___y_5130_ = v___x_5136_;
goto v___jp_5129_;
}
else
{
size_t v___x_5137_; size_t v___x_5138_; uint8_t v___x_5139_; 
v___x_5137_ = lean_ptr_addr(v_body_5127_);
v___x_5138_ = lean_ptr_addr(v_newBody_5124_);
v___x_5139_ = lean_usize_dec_eq(v___x_5137_, v___x_5138_);
v___y_5130_ = v___x_5139_;
goto v___jp_5129_;
}
v___jp_5129_:
{
if (v___y_5130_ == 0)
{
lean_object* v___x_5131_; 
lean_inc(v_binderName_5125_);
lean_dec_ref_known(v_e_5121_, 3);
v___x_5131_ = l_Lean_Expr_lam___override(v_binderName_5125_, v_newDomain_5123_, v_newBody_5124_, v_newBinfo_5122_);
return v___x_5131_;
}
else
{
uint8_t v___x_5132_; 
v___x_5132_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5128_, v_newBinfo_5122_);
if (v___x_5132_ == 0)
{
lean_object* v___x_5133_; 
lean_inc(v_binderName_5125_);
lean_dec_ref_known(v_e_5121_, 3);
v___x_5133_ = l_Lean_Expr_lam___override(v_binderName_5125_, v_newDomain_5123_, v_newBody_5124_, v_newBinfo_5122_);
return v___x_5133_;
}
else
{
lean_dec_ref(v_newBody_5124_);
lean_dec_ref(v_newDomain_5123_);
return v_e_5121_;
}
}
}
}
else
{
lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; 
lean_dec_ref(v_newBody_5124_);
lean_dec_ref(v_newDomain_5123_);
lean_dec_ref(v_e_5121_);
v___x_5140_ = l_Lean_instInhabitedExpr;
v___x_5141_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_5142_ = l_panic___redArg(v___x_5140_, v___x_5141_);
return v___x_5142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_5143_, lean_object* v_newBinfo_5144_, lean_object* v_newDomain_5145_, lean_object* v_newBody_5146_){
_start:
{
uint8_t v_newBinfo_boxed_5147_; lean_object* v_res_5148_; 
v_newBinfo_boxed_5147_ = lean_unbox(v_newBinfo_5144_);
v_res_5148_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5143_, v_newBinfo_boxed_5147_, v_newDomain_5145_, v_newBody_5146_);
return v_res_5148_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; 
v___x_5150_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5151_ = lean_unsigned_to_nat(20u);
v___x_5152_ = lean_unsigned_to_nat(1942u);
v___x_5153_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5154_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5155_ = l_mkPanicMessageWithDecl(v___x_5154_, v___x_5153_, v___x_5152_, v___x_5151_, v___x_5150_);
return v___x_5155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5156_, lean_object* v_newDomain_5157_, lean_object* v_newBody_5158_){
_start:
{
if (lean_obj_tag(v_e_5156_) == 6)
{
lean_object* v_binderName_5159_; lean_object* v_binderType_5160_; lean_object* v_body_5161_; uint8_t v_binderInfo_5162_; uint8_t v___y_5164_; size_t v___x_5168_; size_t v___x_5169_; uint8_t v___x_5170_; 
v_binderName_5159_ = lean_ctor_get(v_e_5156_, 0);
v_binderType_5160_ = lean_ctor_get(v_e_5156_, 1);
v_body_5161_ = lean_ctor_get(v_e_5156_, 2);
v_binderInfo_5162_ = lean_ctor_get_uint8(v_e_5156_, sizeof(void*)*3 + 8);
v___x_5168_ = lean_ptr_addr(v_binderType_5160_);
v___x_5169_ = lean_ptr_addr(v_newDomain_5157_);
v___x_5170_ = lean_usize_dec_eq(v___x_5168_, v___x_5169_);
if (v___x_5170_ == 0)
{
v___y_5164_ = v___x_5170_;
goto v___jp_5163_;
}
else
{
size_t v___x_5171_; size_t v___x_5172_; uint8_t v___x_5173_; 
v___x_5171_ = lean_ptr_addr(v_body_5161_);
v___x_5172_ = lean_ptr_addr(v_newBody_5158_);
v___x_5173_ = lean_usize_dec_eq(v___x_5171_, v___x_5172_);
v___y_5164_ = v___x_5173_;
goto v___jp_5163_;
}
v___jp_5163_:
{
if (v___y_5164_ == 0)
{
lean_object* v___x_5165_; 
lean_inc(v_binderName_5159_);
lean_dec_ref_known(v_e_5156_, 3);
v___x_5165_ = l_Lean_Expr_lam___override(v_binderName_5159_, v_newDomain_5157_, v_newBody_5158_, v_binderInfo_5162_);
return v___x_5165_;
}
else
{
uint8_t v___x_5166_; 
v___x_5166_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5162_, v_binderInfo_5162_);
if (v___x_5166_ == 0)
{
lean_object* v___x_5167_; 
lean_inc(v_binderName_5159_);
lean_dec_ref_known(v_e_5156_, 3);
v___x_5167_ = l_Lean_Expr_lam___override(v_binderName_5159_, v_newDomain_5157_, v_newBody_5158_, v_binderInfo_5162_);
return v___x_5167_;
}
else
{
lean_dec_ref(v_newBody_5158_);
lean_dec_ref(v_newDomain_5157_);
return v_e_5156_;
}
}
}
}
else
{
lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; 
lean_dec_ref(v_newBody_5158_);
lean_dec_ref(v_newDomain_5157_);
lean_dec_ref(v_e_5156_);
v___x_5174_ = l_Lean_instInhabitedExpr;
v___x_5175_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5176_ = l_panic___redArg(v___x_5174_, v___x_5175_);
return v___x_5176_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; 
v___x_5178_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5179_ = lean_unsigned_to_nat(22u);
v___x_5180_ = lean_unsigned_to_nat(1951u);
v___x_5181_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5182_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5183_ = l_mkPanicMessageWithDecl(v___x_5182_, v___x_5181_, v___x_5180_, v___x_5179_, v___x_5178_);
return v___x_5183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5184_, lean_object* v_newType_5185_, lean_object* v_newVal_5186_, lean_object* v_newBody_5187_, uint8_t v_newNondep_5188_){
_start:
{
if (lean_obj_tag(v_e_5184_) == 8)
{
lean_object* v_declName_5189_; lean_object* v_type_5190_; lean_object* v_value_5191_; lean_object* v_body_5192_; uint8_t v_nondep_5193_; uint8_t v___y_5195_; size_t v___x_5203_; size_t v___x_5204_; uint8_t v___x_5205_; 
v_declName_5189_ = lean_ctor_get(v_e_5184_, 0);
v_type_5190_ = lean_ctor_get(v_e_5184_, 1);
v_value_5191_ = lean_ctor_get(v_e_5184_, 2);
v_body_5192_ = lean_ctor_get(v_e_5184_, 3);
v_nondep_5193_ = lean_ctor_get_uint8(v_e_5184_, sizeof(void*)*4 + 8);
v___x_5203_ = lean_ptr_addr(v_type_5190_);
v___x_5204_ = lean_ptr_addr(v_newType_5185_);
v___x_5205_ = lean_usize_dec_eq(v___x_5203_, v___x_5204_);
if (v___x_5205_ == 0)
{
v___y_5195_ = v___x_5205_;
goto v___jp_5194_;
}
else
{
size_t v___x_5206_; size_t v___x_5207_; uint8_t v___x_5208_; 
v___x_5206_ = lean_ptr_addr(v_value_5191_);
v___x_5207_ = lean_ptr_addr(v_newVal_5186_);
v___x_5208_ = lean_usize_dec_eq(v___x_5206_, v___x_5207_);
v___y_5195_ = v___x_5208_;
goto v___jp_5194_;
}
v___jp_5194_:
{
if (v___y_5195_ == 0)
{
lean_object* v___x_5196_; 
lean_inc(v_declName_5189_);
lean_dec_ref_known(v_e_5184_, 4);
v___x_5196_ = l_Lean_Expr_letE___override(v_declName_5189_, v_newType_5185_, v_newVal_5186_, v_newBody_5187_, v_newNondep_5188_);
return v___x_5196_;
}
else
{
size_t v___x_5197_; size_t v___x_5198_; uint8_t v___x_5199_; 
v___x_5197_ = lean_ptr_addr(v_body_5192_);
v___x_5198_ = lean_ptr_addr(v_newBody_5187_);
v___x_5199_ = lean_usize_dec_eq(v___x_5197_, v___x_5198_);
if (v___x_5199_ == 0)
{
lean_object* v___x_5200_; 
lean_inc(v_declName_5189_);
lean_dec_ref_known(v_e_5184_, 4);
v___x_5200_ = l_Lean_Expr_letE___override(v_declName_5189_, v_newType_5185_, v_newVal_5186_, v_newBody_5187_, v_newNondep_5188_);
return v___x_5200_;
}
else
{
if (v_nondep_5193_ == 0)
{
if (v_newNondep_5188_ == 0)
{
lean_dec_ref(v_newBody_5187_);
lean_dec_ref(v_newVal_5186_);
lean_dec_ref(v_newType_5185_);
return v_e_5184_;
}
else
{
lean_object* v___x_5201_; 
lean_inc(v_declName_5189_);
lean_dec_ref_known(v_e_5184_, 4);
v___x_5201_ = l_Lean_Expr_letE___override(v_declName_5189_, v_newType_5185_, v_newVal_5186_, v_newBody_5187_, v_newNondep_5188_);
return v___x_5201_;
}
}
else
{
if (v_newNondep_5188_ == 0)
{
lean_object* v___x_5202_; 
lean_inc(v_declName_5189_);
lean_dec_ref_known(v_e_5184_, 4);
v___x_5202_ = l_Lean_Expr_letE___override(v_declName_5189_, v_newType_5185_, v_newVal_5186_, v_newBody_5187_, v_newNondep_5188_);
return v___x_5202_;
}
else
{
lean_dec_ref(v_newBody_5187_);
lean_dec_ref(v_newVal_5186_);
lean_dec_ref(v_newType_5185_);
return v_e_5184_;
}
}
}
}
}
}
else
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; 
lean_dec_ref(v_newBody_5187_);
lean_dec_ref(v_newVal_5186_);
lean_dec_ref(v_newType_5185_);
lean_dec_ref(v_e_5184_);
v___x_5209_ = l_Lean_instInhabitedExpr;
v___x_5210_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5211_ = l_panic___redArg(v___x_5209_, v___x_5210_);
return v___x_5211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5212_, lean_object* v_newType_5213_, lean_object* v_newVal_5214_, lean_object* v_newBody_5215_, lean_object* v_newNondep_5216_){
_start:
{
uint8_t v_newNondep_boxed_5217_; lean_object* v_res_5218_; 
v_newNondep_boxed_5217_ = lean_unbox(v_newNondep_5216_);
v_res_5218_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5212_, v_newType_5213_, v_newVal_5214_, v_newBody_5215_, v_newNondep_boxed_5217_);
return v_res_5218_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; 
v___x_5220_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5221_ = lean_unsigned_to_nat(27u);
v___x_5222_ = lean_unsigned_to_nat(1964u);
v___x_5223_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5224_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5225_ = l_mkPanicMessageWithDecl(v___x_5224_, v___x_5223_, v___x_5222_, v___x_5221_, v___x_5220_);
return v___x_5225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5226_, lean_object* v_newType_5227_, lean_object* v_newVal_5228_, lean_object* v_newBody_5229_){
_start:
{
if (lean_obj_tag(v_e_5226_) == 8)
{
lean_object* v_declName_5230_; lean_object* v_type_5231_; lean_object* v_value_5232_; lean_object* v_body_5233_; uint8_t v_nondep_5234_; uint8_t v___y_5236_; size_t v___x_5242_; size_t v___x_5243_; uint8_t v___x_5244_; 
v_declName_5230_ = lean_ctor_get(v_e_5226_, 0);
v_type_5231_ = lean_ctor_get(v_e_5226_, 1);
v_value_5232_ = lean_ctor_get(v_e_5226_, 2);
v_body_5233_ = lean_ctor_get(v_e_5226_, 3);
v_nondep_5234_ = lean_ctor_get_uint8(v_e_5226_, sizeof(void*)*4 + 8);
v___x_5242_ = lean_ptr_addr(v_type_5231_);
v___x_5243_ = lean_ptr_addr(v_newType_5227_);
v___x_5244_ = lean_usize_dec_eq(v___x_5242_, v___x_5243_);
if (v___x_5244_ == 0)
{
v___y_5236_ = v___x_5244_;
goto v___jp_5235_;
}
else
{
size_t v___x_5245_; size_t v___x_5246_; uint8_t v___x_5247_; 
v___x_5245_ = lean_ptr_addr(v_value_5232_);
v___x_5246_ = lean_ptr_addr(v_newVal_5228_);
v___x_5247_ = lean_usize_dec_eq(v___x_5245_, v___x_5246_);
v___y_5236_ = v___x_5247_;
goto v___jp_5235_;
}
v___jp_5235_:
{
if (v___y_5236_ == 0)
{
lean_object* v___x_5237_; 
lean_inc(v_declName_5230_);
lean_dec_ref_known(v_e_5226_, 4);
v___x_5237_ = l_Lean_Expr_letE___override(v_declName_5230_, v_newType_5227_, v_newVal_5228_, v_newBody_5229_, v_nondep_5234_);
return v___x_5237_;
}
else
{
size_t v___x_5238_; size_t v___x_5239_; uint8_t v___x_5240_; 
v___x_5238_ = lean_ptr_addr(v_body_5233_);
v___x_5239_ = lean_ptr_addr(v_newBody_5229_);
v___x_5240_ = lean_usize_dec_eq(v___x_5238_, v___x_5239_);
if (v___x_5240_ == 0)
{
lean_object* v___x_5241_; 
lean_inc(v_declName_5230_);
lean_dec_ref_known(v_e_5226_, 4);
v___x_5241_ = l_Lean_Expr_letE___override(v_declName_5230_, v_newType_5227_, v_newVal_5228_, v_newBody_5229_, v_nondep_5234_);
return v___x_5241_;
}
else
{
lean_dec_ref(v_newBody_5229_);
lean_dec_ref(v_newVal_5228_);
lean_dec_ref(v_newType_5227_);
return v_e_5226_;
}
}
}
}
else
{
lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; 
lean_dec_ref(v_newBody_5229_);
lean_dec_ref(v_newVal_5228_);
lean_dec_ref(v_newType_5227_);
lean_dec_ref(v_e_5226_);
v___x_5248_ = l_Lean_instInhabitedExpr;
v___x_5249_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5250_ = l_panic___redArg(v___x_5248_, v___x_5249_);
return v___x_5250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5251_, lean_object* v_x_5252_){
_start:
{
if (lean_obj_tag(v_x_5251_) == 5)
{
lean_object* v_fn_5253_; lean_object* v_arg_5254_; lean_object* v___x_5255_; uint8_t v___y_5257_; size_t v___x_5259_; size_t v___x_5260_; uint8_t v___x_5261_; 
v_fn_5253_ = lean_ctor_get(v_x_5251_, 0);
v_arg_5254_ = lean_ctor_get(v_x_5251_, 1);
lean_inc_ref(v_fn_5253_);
v___x_5255_ = l_Lean_Expr_updateFn(v_fn_5253_, v_x_5252_);
v___x_5259_ = lean_ptr_addr(v_fn_5253_);
v___x_5260_ = lean_ptr_addr(v___x_5255_);
v___x_5261_ = lean_usize_dec_eq(v___x_5259_, v___x_5260_);
if (v___x_5261_ == 0)
{
v___y_5257_ = v___x_5261_;
goto v___jp_5256_;
}
else
{
size_t v___x_5262_; uint8_t v___x_5263_; 
v___x_5262_ = lean_ptr_addr(v_arg_5254_);
v___x_5263_ = lean_usize_dec_eq(v___x_5262_, v___x_5262_);
v___y_5257_ = v___x_5263_;
goto v___jp_5256_;
}
v___jp_5256_:
{
if (v___y_5257_ == 0)
{
lean_object* v___x_5258_; 
lean_inc_ref(v_arg_5254_);
lean_dec_ref_known(v_x_5251_, 2);
v___x_5258_ = l_Lean_Expr_app___override(v___x_5255_, v_arg_5254_);
return v___x_5258_;
}
else
{
lean_dec_ref(v___x_5255_);
return v_x_5251_;
}
}
}
else
{
lean_dec_ref(v_x_5251_);
lean_inc_ref(v_x_5252_);
return v_x_5252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5264_, lean_object* v_x_5265_){
_start:
{
lean_object* v_res_5266_; 
v_res_5266_ = l_Lean_Expr_updateFn(v_x_5264_, v_x_5265_);
lean_dec_ref(v_x_5265_);
return v_res_5266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5267_){
_start:
{
if (lean_obj_tag(v_e_5267_) == 6)
{
lean_object* v_binderName_5268_; lean_object* v_binderType_5269_; lean_object* v_body_5270_; uint8_t v_binderInfo_5271_; lean_object* v_b_x27_5272_; uint8_t v___y_5274_; uint8_t v___y_5279_; 
v_binderName_5268_ = lean_ctor_get(v_e_5267_, 0);
v_binderType_5269_ = lean_ctor_get(v_e_5267_, 1);
v_body_5270_ = lean_ctor_get(v_e_5267_, 2);
v_binderInfo_5271_ = lean_ctor_get_uint8(v_e_5267_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5270_);
v_b_x27_5272_ = l_Lean_Expr_eta(v_body_5270_);
if (lean_obj_tag(v_b_x27_5272_) == 5)
{
lean_object* v_arg_5289_; 
v_arg_5289_ = lean_ctor_get(v_b_x27_5272_, 1);
lean_inc_ref(v_arg_5289_);
if (lean_obj_tag(v_arg_5289_) == 0)
{
lean_object* v_fn_5290_; lean_object* v_deBruijnIndex_5291_; lean_object* v___x_5292_; uint8_t v___x_5293_; 
v_fn_5290_ = lean_ctor_get(v_b_x27_5272_, 0);
lean_inc_ref(v_fn_5290_);
v_deBruijnIndex_5291_ = lean_ctor_get(v_arg_5289_, 0);
lean_inc(v_deBruijnIndex_5291_);
lean_dec_ref_known(v_arg_5289_, 1);
v___x_5292_ = lean_unsigned_to_nat(0u);
v___x_5293_ = lean_nat_dec_eq(v_deBruijnIndex_5291_, v___x_5292_);
lean_dec(v_deBruijnIndex_5291_);
if (v___x_5293_ == 0)
{
lean_dec_ref(v_fn_5290_);
goto v___jp_5283_;
}
else
{
uint8_t v___x_5294_; 
v___x_5294_ = lean_expr_has_loose_bvar(v_fn_5290_, v___x_5292_);
if (v___x_5294_ == 0)
{
lean_object* v___x_5295_; lean_object* v___x_5296_; 
lean_dec_ref_known(v_b_x27_5272_, 2);
lean_dec_ref_known(v_e_5267_, 3);
v___x_5295_ = lean_unsigned_to_nat(1u);
v___x_5296_ = lean_expr_lower_loose_bvars(v_fn_5290_, v___x_5295_, v___x_5295_);
lean_dec_ref(v_fn_5290_);
return v___x_5296_;
}
else
{
size_t v___x_5297_; uint8_t v___x_5298_; 
lean_dec_ref(v_fn_5290_);
v___x_5297_ = lean_ptr_addr(v_binderType_5269_);
v___x_5298_ = lean_usize_dec_eq(v___x_5297_, v___x_5297_);
if (v___x_5298_ == 0)
{
v___y_5274_ = v___x_5298_;
goto v___jp_5273_;
}
else
{
size_t v___x_5299_; size_t v___x_5300_; uint8_t v___x_5301_; 
v___x_5299_ = lean_ptr_addr(v_body_5270_);
v___x_5300_ = lean_ptr_addr(v_b_x27_5272_);
v___x_5301_ = lean_usize_dec_eq(v___x_5299_, v___x_5300_);
v___y_5274_ = v___x_5301_;
goto v___jp_5273_;
}
}
}
}
else
{
lean_dec_ref(v_arg_5289_);
goto v___jp_5283_;
}
}
else
{
goto v___jp_5283_;
}
v___jp_5273_:
{
if (v___y_5274_ == 0)
{
lean_object* v___x_5275_; 
lean_inc_ref(v_binderType_5269_);
lean_inc(v_binderName_5268_);
lean_dec_ref_known(v_e_5267_, 3);
v___x_5275_ = l_Lean_Expr_lam___override(v_binderName_5268_, v_binderType_5269_, v_b_x27_5272_, v_binderInfo_5271_);
return v___x_5275_;
}
else
{
uint8_t v___x_5276_; 
v___x_5276_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5271_, v_binderInfo_5271_);
if (v___x_5276_ == 0)
{
lean_object* v___x_5277_; 
lean_inc_ref(v_binderType_5269_);
lean_inc(v_binderName_5268_);
lean_dec_ref_known(v_e_5267_, 3);
v___x_5277_ = l_Lean_Expr_lam___override(v_binderName_5268_, v_binderType_5269_, v_b_x27_5272_, v_binderInfo_5271_);
return v___x_5277_;
}
else
{
lean_dec_ref(v_b_x27_5272_);
return v_e_5267_;
}
}
}
v___jp_5278_:
{
if (v___y_5279_ == 0)
{
lean_object* v___x_5280_; 
lean_inc_ref(v_binderType_5269_);
lean_inc(v_binderName_5268_);
lean_dec_ref_known(v_e_5267_, 3);
v___x_5280_ = l_Lean_Expr_lam___override(v_binderName_5268_, v_binderType_5269_, v_b_x27_5272_, v_binderInfo_5271_);
return v___x_5280_;
}
else
{
uint8_t v___x_5281_; 
v___x_5281_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5271_, v_binderInfo_5271_);
if (v___x_5281_ == 0)
{
lean_object* v___x_5282_; 
lean_inc_ref(v_binderType_5269_);
lean_inc(v_binderName_5268_);
lean_dec_ref_known(v_e_5267_, 3);
v___x_5282_ = l_Lean_Expr_lam___override(v_binderName_5268_, v_binderType_5269_, v_b_x27_5272_, v_binderInfo_5271_);
return v___x_5282_;
}
else
{
lean_dec_ref(v_b_x27_5272_);
return v_e_5267_;
}
}
}
v___jp_5283_:
{
size_t v___x_5284_; uint8_t v___x_5285_; 
v___x_5284_ = lean_ptr_addr(v_binderType_5269_);
v___x_5285_ = lean_usize_dec_eq(v___x_5284_, v___x_5284_);
if (v___x_5285_ == 0)
{
v___y_5279_ = v___x_5285_;
goto v___jp_5278_;
}
else
{
size_t v___x_5286_; size_t v___x_5287_; uint8_t v___x_5288_; 
v___x_5286_ = lean_ptr_addr(v_body_5270_);
v___x_5287_ = lean_ptr_addr(v_b_x27_5272_);
v___x_5288_ = lean_usize_dec_eq(v___x_5286_, v___x_5287_);
v___y_5279_ = v___x_5288_;
goto v___jp_5278_;
}
}
}
else
{
return v_e_5267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5302_, lean_object* v_optionName_5303_, lean_object* v_inst_5304_, lean_object* v_val_5305_){
_start:
{
lean_object* v_toDataValue_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; 
v_toDataValue_5306_ = lean_ctor_get(v_inst_5304_, 0);
lean_inc_ref(v_toDataValue_5306_);
lean_dec_ref(v_inst_5304_);
v___x_5307_ = lean_box(0);
v___x_5308_ = lean_apply_1(v_toDataValue_5306_, v_val_5305_);
v___x_5309_ = l_Lean_KVMap_insert(v___x_5307_, v_optionName_5303_, v___x_5308_);
v___x_5310_ = l_Lean_Expr_mdata___override(v___x_5309_, v_e_5302_);
return v___x_5310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5311_, lean_object* v_e_5312_, lean_object* v_optionName_5313_, lean_object* v_inst_5314_, lean_object* v_val_5315_){
_start:
{
lean_object* v___x_5316_; 
v___x_5316_ = l_Lean_Expr_setOption___redArg(v_e_5312_, v_optionName_5313_, v_inst_5314_, v_val_5315_);
return v___x_5316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5317_, lean_object* v_optionName_5318_, uint8_t v_val_5319_){
_start:
{
lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; 
v___x_5320_ = lean_box(0);
v___x_5321_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5321_, 0, v_val_5319_);
v___x_5322_ = l_Lean_KVMap_insert(v___x_5320_, v_optionName_5318_, v___x_5321_);
v___x_5323_ = l_Lean_Expr_mdata___override(v___x_5322_, v_e_5317_);
return v___x_5323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5324_, lean_object* v_optionName_5325_, lean_object* v_val_5326_){
_start:
{
uint8_t v_val_boxed_5327_; lean_object* v_res_5328_; 
v_val_boxed_5327_ = lean_unbox(v_val_5326_);
v_res_5328_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5324_, v_optionName_5325_, v_val_boxed_5327_);
return v_res_5328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5334_, uint8_t v_flag_5335_){
_start:
{
lean_object* v___x_5336_; lean_object* v___x_5337_; 
v___x_5336_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5337_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5334_, v___x_5336_, v_flag_5335_);
return v___x_5337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5338_, lean_object* v_flag_5339_){
_start:
{
uint8_t v_flag_boxed_5340_; lean_object* v_res_5341_; 
v_flag_boxed_5340_ = lean_unbox(v_flag_5339_);
v_res_5341_ = l_Lean_Expr_setPPExplicit(v_e_5338_, v_flag_boxed_5340_);
return v_res_5341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5346_, uint8_t v_flag_5347_){
_start:
{
lean_object* v___x_5348_; lean_object* v___x_5349_; 
v___x_5348_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5349_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5346_, v___x_5348_, v_flag_5347_);
return v___x_5349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5350_, lean_object* v_flag_5351_){
_start:
{
uint8_t v_flag_boxed_5352_; lean_object* v_res_5353_; 
v_flag_boxed_5352_ = lean_unbox(v_flag_5351_);
v_res_5353_ = l_Lean_Expr_setPPUniverses(v_e_5350_, v_flag_boxed_5352_);
return v_res_5353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5358_, uint8_t v_flag_5359_){
_start:
{
lean_object* v___x_5360_; lean_object* v___x_5361_; 
v___x_5360_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5361_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5358_, v___x_5360_, v_flag_5359_);
return v___x_5361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5362_, lean_object* v_flag_5363_){
_start:
{
uint8_t v_flag_boxed_5364_; lean_object* v_res_5365_; 
v_flag_boxed_5364_ = lean_unbox(v_flag_5363_);
v_res_5365_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5362_, v_flag_boxed_5364_);
return v_res_5365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5370_, uint8_t v_flag_5371_){
_start:
{
lean_object* v___x_5372_; lean_object* v___x_5373_; 
v___x_5372_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5373_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5370_, v___x_5372_, v_flag_5371_);
return v___x_5373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5374_, lean_object* v_flag_5375_){
_start:
{
uint8_t v_flag_boxed_5376_; lean_object* v_res_5377_; 
v_flag_boxed_5376_ = lean_unbox(v_flag_5375_);
v_res_5377_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5374_, v_flag_boxed_5376_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5382_, uint8_t v_flag_5383_){
_start:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; 
v___x_5384_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5385_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5382_, v___x_5384_, v_flag_5383_);
return v___x_5385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5386_, lean_object* v_flag_5387_){
_start:
{
uint8_t v_flag_boxed_5388_; lean_object* v_res_5389_; 
v_flag_boxed_5388_ = lean_unbox(v_flag_5387_);
v_res_5389_ = l_Lean_Expr_setPPNumericTypes(v_e_5386_, v_flag_boxed_5388_);
return v_res_5389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5390_, size_t v_i_5391_, lean_object* v_bs_5392_){
_start:
{
uint8_t v___x_5393_; 
v___x_5393_ = lean_usize_dec_lt(v_i_5391_, v_sz_5390_);
if (v___x_5393_ == 0)
{
return v_bs_5392_;
}
else
{
uint8_t v___x_5394_; lean_object* v_v_5395_; lean_object* v___x_5396_; lean_object* v_bs_x27_5397_; lean_object* v___x_5398_; size_t v___x_5399_; size_t v___x_5400_; lean_object* v___x_5401_; 
v___x_5394_ = 0;
v_v_5395_ = lean_array_uget(v_bs_5392_, v_i_5391_);
v___x_5396_ = lean_unsigned_to_nat(0u);
v_bs_x27_5397_ = lean_array_uset(v_bs_5392_, v_i_5391_, v___x_5396_);
v___x_5398_ = l_Lean_Expr_setPPExplicit(v_v_5395_, v___x_5394_);
v___x_5399_ = ((size_t)1ULL);
v___x_5400_ = lean_usize_add(v_i_5391_, v___x_5399_);
v___x_5401_ = lean_array_uset(v_bs_x27_5397_, v_i_5391_, v___x_5398_);
v_i_5391_ = v___x_5400_;
v_bs_5392_ = v___x_5401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5403_, lean_object* v_i_5404_, lean_object* v_bs_5405_){
_start:
{
size_t v_sz_boxed_5406_; size_t v_i_boxed_5407_; lean_object* v_res_5408_; 
v_sz_boxed_5406_ = lean_unbox_usize(v_sz_5403_);
lean_dec(v_sz_5403_);
v_i_boxed_5407_ = lean_unbox_usize(v_i_5404_);
lean_dec(v_i_5404_);
v_res_5408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5406_, v_i_boxed_5407_, v_bs_5405_);
return v_res_5408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5409_){
_start:
{
if (lean_obj_tag(v_e_5409_) == 5)
{
lean_object* v___x_5410_; uint8_t v___x_5411_; lean_object* v_f_5412_; lean_object* v_dummy_5413_; lean_object* v_nargs_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; size_t v_sz_5419_; size_t v___x_5420_; lean_object* v_args_5421_; lean_object* v___x_5422_; uint8_t v___x_5423_; lean_object* v___x_5424_; 
v___x_5410_ = l_Lean_Expr_getAppFn(v_e_5409_);
v___x_5411_ = 0;
v_f_5412_ = l_Lean_Expr_setPPExplicit(v___x_5410_, v___x_5411_);
v_dummy_5413_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5414_ = l_Lean_Expr_getAppNumArgs(v_e_5409_);
lean_inc(v_nargs_5414_);
v___x_5415_ = lean_mk_array(v_nargs_5414_, v_dummy_5413_);
v___x_5416_ = lean_unsigned_to_nat(1u);
v___x_5417_ = lean_nat_sub(v_nargs_5414_, v___x_5416_);
lean_dec(v_nargs_5414_);
v___x_5418_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5409_, v___x_5415_, v___x_5417_);
v_sz_5419_ = lean_array_size(v___x_5418_);
v___x_5420_ = ((size_t)0ULL);
v_args_5421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5419_, v___x_5420_, v___x_5418_);
v___x_5422_ = l_Lean_mkAppN(v_f_5412_, v_args_5421_);
lean_dec_ref(v_args_5421_);
v___x_5423_ = 1;
v___x_5424_ = l_Lean_Expr_setPPExplicit(v___x_5422_, v___x_5423_);
return v___x_5424_;
}
else
{
return v_e_5409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5425_, size_t v_i_5426_, lean_object* v_bs_5427_){
_start:
{
uint8_t v___x_5428_; 
v___x_5428_ = lean_usize_dec_lt(v_i_5426_, v_sz_5425_);
if (v___x_5428_ == 0)
{
return v_bs_5427_;
}
else
{
lean_object* v_v_5429_; lean_object* v___x_5430_; lean_object* v_bs_x27_5431_; lean_object* v___y_5433_; uint8_t v___x_5438_; 
v_v_5429_ = lean_array_uget(v_bs_5427_, v_i_5426_);
v___x_5430_ = lean_unsigned_to_nat(0u);
v_bs_x27_5431_ = lean_array_uset(v_bs_5427_, v_i_5426_, v___x_5430_);
v___x_5438_ = l_Lean_Expr_hasMVar(v_v_5429_);
if (v___x_5438_ == 0)
{
lean_object* v___x_5439_; 
v___x_5439_ = l_Lean_Expr_setPPExplicit(v_v_5429_, v___x_5438_);
v___y_5433_ = v___x_5439_;
goto v___jp_5432_;
}
else
{
v___y_5433_ = v_v_5429_;
goto v___jp_5432_;
}
v___jp_5432_:
{
size_t v___x_5434_; size_t v___x_5435_; lean_object* v___x_5436_; 
v___x_5434_ = ((size_t)1ULL);
v___x_5435_ = lean_usize_add(v_i_5426_, v___x_5434_);
v___x_5436_ = lean_array_uset(v_bs_x27_5431_, v_i_5426_, v___y_5433_);
v_i_5426_ = v___x_5435_;
v_bs_5427_ = v___x_5436_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5440_, lean_object* v_i_5441_, lean_object* v_bs_5442_){
_start:
{
size_t v_sz_boxed_5443_; size_t v_i_boxed_5444_; lean_object* v_res_5445_; 
v_sz_boxed_5443_ = lean_unbox_usize(v_sz_5440_);
lean_dec(v_sz_5440_);
v_i_boxed_5444_ = lean_unbox_usize(v_i_5441_);
lean_dec(v_i_5441_);
v_res_5445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5443_, v_i_boxed_5444_, v_bs_5442_);
return v_res_5445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5446_){
_start:
{
if (lean_obj_tag(v_e_5446_) == 5)
{
lean_object* v___x_5447_; uint8_t v___x_5448_; lean_object* v_f_5449_; lean_object* v_dummy_5450_; lean_object* v_nargs_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; size_t v_sz_5456_; size_t v___x_5457_; lean_object* v_args_5458_; lean_object* v___x_5459_; uint8_t v___x_5460_; lean_object* v___x_5461_; 
v___x_5447_ = l_Lean_Expr_getAppFn(v_e_5446_);
v___x_5448_ = 0;
v_f_5449_ = l_Lean_Expr_setPPExplicit(v___x_5447_, v___x_5448_);
v_dummy_5450_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5451_ = l_Lean_Expr_getAppNumArgs(v_e_5446_);
lean_inc(v_nargs_5451_);
v___x_5452_ = lean_mk_array(v_nargs_5451_, v_dummy_5450_);
v___x_5453_ = lean_unsigned_to_nat(1u);
v___x_5454_ = lean_nat_sub(v_nargs_5451_, v___x_5453_);
lean_dec(v_nargs_5451_);
v___x_5455_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5446_, v___x_5452_, v___x_5454_);
v_sz_5456_ = lean_array_size(v___x_5455_);
v___x_5457_ = ((size_t)0ULL);
v_args_5458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5456_, v___x_5457_, v___x_5455_);
v___x_5459_ = l_Lean_mkAppN(v_f_5449_, v_args_5458_);
lean_dec_ref(v_args_5458_);
v___x_5460_ = 1;
v___x_5461_ = l_Lean_Expr_setPPExplicit(v___x_5459_, v___x_5460_);
return v___x_5461_;
}
else
{
return v_e_5446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5462_, lean_object* v_body_5463_, lean_object* v_x_5464_){
_start:
{
lean_object* v___x_5465_; 
v___x_5465_ = lean_apply_1(v_f_5462_, v_body_5463_);
return v___x_5465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5466_, lean_object* v_binderType_5467_, lean_object* v_x_5468_){
_start:
{
lean_object* v___x_5469_; 
v___x_5469_ = lean_apply_1(v_f_5466_, v_binderType_5467_);
return v___x_5469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5470_, lean_object* v_value_5471_, lean_object* v_x_5472_){
_start:
{
lean_object* v___x_5473_; 
v___x_5473_ = lean_apply_1(v_f_5470_, v_value_5471_);
return v___x_5473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5474_, lean_object* v_type_5475_, lean_object* v_x_5476_){
_start:
{
lean_object* v___x_5477_; 
v___x_5477_ = lean_apply_1(v_f_5474_, v_type_5475_);
return v___x_5477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5478_, lean_object* v_arg_5479_, lean_object* v_x_5480_){
_start:
{
lean_object* v___x_5481_; 
v___x_5481_ = lean_apply_1(v_f_5478_, v_arg_5479_);
return v___x_5481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5482_, lean_object* v_fn_5483_, lean_object* v_x_5484_){
_start:
{
lean_object* v___x_5485_; 
v___x_5485_ = lean_apply_1(v_f_5482_, v_fn_5483_);
return v___x_5485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5486_, lean_object* v_f_5487_, lean_object* v_x_5488_){
_start:
{
switch(lean_obj_tag(v_x_5488_))
{
case 7:
{
lean_object* v_toPure_5489_; lean_object* v_toSeq_5490_; lean_object* v_binderType_5491_; lean_object* v_body_5492_; lean_object* v___f_5493_; lean_object* v___f_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; 
v_toPure_5489_ = lean_ctor_get(v_inst_5486_, 1);
lean_inc(v_toPure_5489_);
v_toSeq_5490_ = lean_ctor_get(v_inst_5486_, 2);
lean_inc_n(v_toSeq_5490_, 2);
lean_dec_ref(v_inst_5486_);
v_binderType_5491_ = lean_ctor_get(v_x_5488_, 1);
v_body_5492_ = lean_ctor_get(v_x_5488_, 2);
lean_inc_ref(v_body_5492_);
lean_inc(v_f_5487_);
v___f_5493_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5493_, 0, v_f_5487_);
lean_closure_set(v___f_5493_, 1, v_body_5492_);
lean_inc_ref(v_binderType_5491_);
v___f_5494_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5494_, 0, v_f_5487_);
lean_closure_set(v___f_5494_, 1, v_binderType_5491_);
v___x_5495_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5495_, 0, v_x_5488_);
v___x_5496_ = lean_apply_2(v_toPure_5489_, lean_box(0), v___x_5495_);
v___x_5497_ = lean_apply_4(v_toSeq_5490_, lean_box(0), lean_box(0), v___x_5496_, v___f_5494_);
v___x_5498_ = lean_apply_4(v_toSeq_5490_, lean_box(0), lean_box(0), v___x_5497_, v___f_5493_);
return v___x_5498_;
}
case 6:
{
lean_object* v_toPure_5499_; lean_object* v_toSeq_5500_; lean_object* v_binderType_5501_; lean_object* v_body_5502_; lean_object* v___f_5503_; lean_object* v___f_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; 
v_toPure_5499_ = lean_ctor_get(v_inst_5486_, 1);
lean_inc(v_toPure_5499_);
v_toSeq_5500_ = lean_ctor_get(v_inst_5486_, 2);
lean_inc_n(v_toSeq_5500_, 2);
lean_dec_ref(v_inst_5486_);
v_binderType_5501_ = lean_ctor_get(v_x_5488_, 1);
v_body_5502_ = lean_ctor_get(v_x_5488_, 2);
lean_inc_ref(v_body_5502_);
lean_inc(v_f_5487_);
v___f_5503_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5503_, 0, v_f_5487_);
lean_closure_set(v___f_5503_, 1, v_body_5502_);
lean_inc_ref(v_binderType_5501_);
v___f_5504_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5504_, 0, v_f_5487_);
lean_closure_set(v___f_5504_, 1, v_binderType_5501_);
v___x_5505_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5505_, 0, v_x_5488_);
v___x_5506_ = lean_apply_2(v_toPure_5499_, lean_box(0), v___x_5505_);
v___x_5507_ = lean_apply_4(v_toSeq_5500_, lean_box(0), lean_box(0), v___x_5506_, v___f_5504_);
v___x_5508_ = lean_apply_4(v_toSeq_5500_, lean_box(0), lean_box(0), v___x_5507_, v___f_5503_);
return v___x_5508_;
}
case 10:
{
lean_object* v_toFunctor_5509_; lean_object* v_expr_5510_; lean_object* v_map_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; 
v_toFunctor_5509_ = lean_ctor_get(v_inst_5486_, 0);
lean_inc_ref(v_toFunctor_5509_);
lean_dec_ref(v_inst_5486_);
v_expr_5510_ = lean_ctor_get(v_x_5488_, 1);
lean_inc_ref(v_expr_5510_);
v_map_5511_ = lean_ctor_get(v_toFunctor_5509_, 0);
lean_inc(v_map_5511_);
lean_dec_ref(v_toFunctor_5509_);
v___x_5512_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5512_, 0, v_x_5488_);
v___x_5513_ = lean_apply_1(v_f_5487_, v_expr_5510_);
v___x_5514_ = lean_apply_4(v_map_5511_, lean_box(0), lean_box(0), v___x_5512_, v___x_5513_);
return v___x_5514_;
}
case 8:
{
lean_object* v_toPure_5515_; lean_object* v_toSeq_5516_; lean_object* v_type_5517_; lean_object* v_value_5518_; lean_object* v_body_5519_; lean_object* v___f_5520_; lean_object* v___f_5521_; lean_object* v___f_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; 
v_toPure_5515_ = lean_ctor_get(v_inst_5486_, 1);
lean_inc(v_toPure_5515_);
v_toSeq_5516_ = lean_ctor_get(v_inst_5486_, 2);
lean_inc_n(v_toSeq_5516_, 3);
lean_dec_ref(v_inst_5486_);
v_type_5517_ = lean_ctor_get(v_x_5488_, 1);
v_value_5518_ = lean_ctor_get(v_x_5488_, 2);
v_body_5519_ = lean_ctor_get(v_x_5488_, 3);
lean_inc_ref(v_body_5519_);
lean_inc_n(v_f_5487_, 2);
v___f_5520_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5520_, 0, v_f_5487_);
lean_closure_set(v___f_5520_, 1, v_body_5519_);
lean_inc_ref(v_value_5518_);
v___f_5521_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5521_, 0, v_f_5487_);
lean_closure_set(v___f_5521_, 1, v_value_5518_);
lean_inc_ref(v_type_5517_);
v___f_5522_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5522_, 0, v_f_5487_);
lean_closure_set(v___f_5522_, 1, v_type_5517_);
v___x_5523_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5523_, 0, v_x_5488_);
v___x_5524_ = lean_apply_2(v_toPure_5515_, lean_box(0), v___x_5523_);
v___x_5525_ = lean_apply_4(v_toSeq_5516_, lean_box(0), lean_box(0), v___x_5524_, v___f_5522_);
v___x_5526_ = lean_apply_4(v_toSeq_5516_, lean_box(0), lean_box(0), v___x_5525_, v___f_5521_);
v___x_5527_ = lean_apply_4(v_toSeq_5516_, lean_box(0), lean_box(0), v___x_5526_, v___f_5520_);
return v___x_5527_;
}
case 5:
{
lean_object* v_toPure_5528_; lean_object* v_toSeq_5529_; lean_object* v_fn_5530_; lean_object* v_arg_5531_; lean_object* v___f_5532_; lean_object* v___f_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; 
v_toPure_5528_ = lean_ctor_get(v_inst_5486_, 1);
lean_inc(v_toPure_5528_);
v_toSeq_5529_ = lean_ctor_get(v_inst_5486_, 2);
lean_inc_n(v_toSeq_5529_, 2);
lean_dec_ref(v_inst_5486_);
v_fn_5530_ = lean_ctor_get(v_x_5488_, 0);
v_arg_5531_ = lean_ctor_get(v_x_5488_, 1);
lean_inc_ref(v_arg_5531_);
lean_inc(v_f_5487_);
v___f_5532_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5532_, 0, v_f_5487_);
lean_closure_set(v___f_5532_, 1, v_arg_5531_);
lean_inc_ref(v_fn_5530_);
v___f_5533_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5533_, 0, v_f_5487_);
lean_closure_set(v___f_5533_, 1, v_fn_5530_);
v___x_5534_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5534_, 0, v_x_5488_);
v___x_5535_ = lean_apply_2(v_toPure_5528_, lean_box(0), v___x_5534_);
v___x_5536_ = lean_apply_4(v_toSeq_5529_, lean_box(0), lean_box(0), v___x_5535_, v___f_5533_);
v___x_5537_ = lean_apply_4(v_toSeq_5529_, lean_box(0), lean_box(0), v___x_5536_, v___f_5532_);
return v___x_5537_;
}
case 11:
{
lean_object* v_toFunctor_5538_; lean_object* v_struct_5539_; lean_object* v_map_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; 
v_toFunctor_5538_ = lean_ctor_get(v_inst_5486_, 0);
lean_inc_ref(v_toFunctor_5538_);
lean_dec_ref(v_inst_5486_);
v_struct_5539_ = lean_ctor_get(v_x_5488_, 2);
lean_inc_ref(v_struct_5539_);
v_map_5540_ = lean_ctor_get(v_toFunctor_5538_, 0);
lean_inc(v_map_5540_);
lean_dec_ref(v_toFunctor_5538_);
v___x_5541_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5541_, 0, v_x_5488_);
v___x_5542_ = lean_apply_1(v_f_5487_, v_struct_5539_);
v___x_5543_ = lean_apply_4(v_map_5540_, lean_box(0), lean_box(0), v___x_5541_, v___x_5542_);
return v___x_5543_;
}
default: 
{
lean_object* v_toPure_5544_; lean_object* v___x_5545_; 
lean_dec(v_f_5487_);
v_toPure_5544_ = lean_ctor_get(v_inst_5486_, 1);
lean_inc(v_toPure_5544_);
lean_dec_ref(v_inst_5486_);
v___x_5545_ = lean_apply_2(v_toPure_5544_, lean_box(0), v_x_5488_);
return v___x_5545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5546_, lean_object* v_inst_5547_, lean_object* v_f_5548_, lean_object* v_x_5549_){
_start:
{
lean_object* v___x_5550_; 
v___x_5550_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5547_, v_f_5548_, v_x_5549_);
return v___x_5550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5551_){
_start:
{
lean_object* v_snd_5552_; 
v_snd_5552_ = lean_ctor_get(v_self_5551_, 1);
lean_inc(v_snd_5552_);
return v_snd_5552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5553_){
_start:
{
lean_object* v_res_5554_; 
v_res_5554_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5553_);
lean_dec_ref(v_self_5553_);
return v_res_5554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5555_, lean_object* v_snd_5556_){
_start:
{
lean_object* v___x_5557_; 
v___x_5557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5557_, 0, v_e_x27_5555_);
lean_ctor_set(v___x_5557_, 1, v_snd_5556_);
return v___x_5557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5558_, lean_object* v_map_5559_, lean_object* v_e_x27_5560_, lean_object* v_a_5561_){
_start:
{
lean_object* v___f_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; 
lean_inc_ref(v_e_x27_5560_);
v___f_5562_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5562_, 0, v_e_x27_5560_);
v___x_5563_ = lean_apply_2(v_f_5558_, v_a_5561_, v_e_x27_5560_);
v___x_5564_ = lean_apply_4(v_map_5559_, lean_box(0), lean_box(0), v___f_5562_, v___x_5563_);
return v___x_5564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5566_, lean_object* v_f_5567_, lean_object* v_init_5568_, lean_object* v_e_5569_){
_start:
{
lean_object* v_toApplicative_5570_; lean_object* v_toFunctor_5571_; lean_object* v___x_5573_; uint8_t v_isShared_5574_; uint8_t v_isSharedCheck_5598_; 
v_toApplicative_5570_ = lean_ctor_get(v_inst_5566_, 0);
lean_inc_ref(v_toApplicative_5570_);
v_toFunctor_5571_ = lean_ctor_get(v_toApplicative_5570_, 0);
v_isSharedCheck_5598_ = !lean_is_exclusive(v_toApplicative_5570_);
if (v_isSharedCheck_5598_ == 0)
{
lean_object* v_unused_5599_; lean_object* v_unused_5600_; lean_object* v_unused_5601_; lean_object* v_unused_5602_; 
v_unused_5599_ = lean_ctor_get(v_toApplicative_5570_, 4);
lean_dec(v_unused_5599_);
v_unused_5600_ = lean_ctor_get(v_toApplicative_5570_, 3);
lean_dec(v_unused_5600_);
v_unused_5601_ = lean_ctor_get(v_toApplicative_5570_, 2);
lean_dec(v_unused_5601_);
v_unused_5602_ = lean_ctor_get(v_toApplicative_5570_, 1);
lean_dec(v_unused_5602_);
v___x_5573_ = v_toApplicative_5570_;
v_isShared_5574_ = v_isSharedCheck_5598_;
goto v_resetjp_5572_;
}
else
{
lean_inc(v_toFunctor_5571_);
lean_dec(v_toApplicative_5570_);
v___x_5573_ = lean_box(0);
v_isShared_5574_ = v_isSharedCheck_5598_;
goto v_resetjp_5572_;
}
v_resetjp_5572_:
{
lean_object* v_map_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5596_; 
v_map_5575_ = lean_ctor_get(v_toFunctor_5571_, 0);
v_isSharedCheck_5596_ = !lean_is_exclusive(v_toFunctor_5571_);
if (v_isSharedCheck_5596_ == 0)
{
lean_object* v_unused_5597_; 
v_unused_5597_ = lean_ctor_get(v_toFunctor_5571_, 1);
lean_dec(v_unused_5597_);
v___x_5577_ = v_toFunctor_5571_;
v_isShared_5578_ = v_isSharedCheck_5596_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_map_5575_);
lean_dec(v_toFunctor_5571_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5596_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v___f_5579_; lean_object* v___f_5580_; lean_object* v___f_5581_; lean_object* v___f_5582_; lean_object* v___f_5583_; lean_object* v___f_5584_; lean_object* v___x_5585_; lean_object* v___x_5587_; 
v___f_5579_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5575_);
v___f_5580_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5580_, 0, v_f_5567_);
lean_closure_set(v___f_5580_, 1, v_map_5575_);
lean_inc_ref_n(v_inst_5566_, 5);
v___f_5581_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5581_, 0, v_inst_5566_);
v___f_5582_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5582_, 0, v_inst_5566_);
v___f_5583_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5583_, 0, v_inst_5566_);
v___f_5584_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5584_, 0, v_inst_5566_);
v___x_5585_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5585_, 0, lean_box(0));
lean_closure_set(v___x_5585_, 1, lean_box(0));
lean_closure_set(v___x_5585_, 2, v_inst_5566_);
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 1, v___f_5581_);
lean_ctor_set(v___x_5577_, 0, v___x_5585_);
v___x_5587_ = v___x_5577_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v___x_5585_);
lean_ctor_set(v_reuseFailAlloc_5595_, 1, v___f_5581_);
v___x_5587_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
lean_object* v___x_5588_; lean_object* v___x_5590_; 
v___x_5588_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5588_, 0, lean_box(0));
lean_closure_set(v___x_5588_, 1, lean_box(0));
lean_closure_set(v___x_5588_, 2, v_inst_5566_);
if (v_isShared_5574_ == 0)
{
lean_ctor_set(v___x_5573_, 4, v___f_5584_);
lean_ctor_set(v___x_5573_, 3, v___f_5583_);
lean_ctor_set(v___x_5573_, 2, v___f_5582_);
lean_ctor_set(v___x_5573_, 1, v___x_5588_);
lean_ctor_set(v___x_5573_, 0, v___x_5587_);
v___x_5590_ = v___x_5573_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v___x_5587_);
lean_ctor_set(v_reuseFailAlloc_5594_, 1, v___x_5588_);
lean_ctor_set(v_reuseFailAlloc_5594_, 2, v___f_5582_);
lean_ctor_set(v_reuseFailAlloc_5594_, 3, v___f_5583_);
lean_ctor_set(v_reuseFailAlloc_5594_, 4, v___f_5584_);
v___x_5590_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
lean_object* v___x_18__overap_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; 
v___x_18__overap_5591_ = l_Lean_Expr_traverseChildren___redArg(v___x_5590_, v___f_5580_, v_e_5569_);
v___x_5592_ = lean_apply_1(v___x_18__overap_5591_, v_init_5568_);
v___x_5593_ = lean_apply_4(v_map_5575_, lean_box(0), lean_box(0), v___f_5579_, v___x_5592_);
return v___x_5593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5603_, lean_object* v_m_5604_, lean_object* v_inst_5605_, lean_object* v_f_5606_, lean_object* v_init_5607_, lean_object* v_e_5608_){
_start:
{
lean_object* v___x_5609_; 
v___x_5609_ = l_Lean_Expr_foldlM___redArg(v_inst_5605_, v_f_5606_, v_init_5607_, v_e_5608_);
return v___x_5609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5610_){
_start:
{
lean_object* v_d_5612_; lean_object* v_b_5613_; 
switch(lean_obj_tag(v_x_5610_))
{
case 5:
{
lean_object* v_fn_5619_; lean_object* v_arg_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; 
v_fn_5619_ = lean_ctor_get(v_x_5610_, 0);
v_arg_5620_ = lean_ctor_get(v_x_5610_, 1);
v___x_5621_ = lean_unsigned_to_nat(1u);
v___x_5622_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5619_);
v___x_5623_ = lean_nat_add(v___x_5621_, v___x_5622_);
lean_dec(v___x_5622_);
v___x_5624_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5620_);
v___x_5625_ = lean_nat_add(v___x_5623_, v___x_5624_);
lean_dec(v___x_5624_);
lean_dec(v___x_5623_);
return v___x_5625_;
}
case 6:
{
lean_object* v_binderType_5626_; lean_object* v_body_5627_; 
v_binderType_5626_ = lean_ctor_get(v_x_5610_, 1);
v_body_5627_ = lean_ctor_get(v_x_5610_, 2);
v_d_5612_ = v_binderType_5626_;
v_b_5613_ = v_body_5627_;
goto v___jp_5611_;
}
case 7:
{
lean_object* v_binderType_5628_; lean_object* v_body_5629_; 
v_binderType_5628_ = lean_ctor_get(v_x_5610_, 1);
v_body_5629_ = lean_ctor_get(v_x_5610_, 2);
v_d_5612_ = v_binderType_5628_;
v_b_5613_ = v_body_5629_;
goto v___jp_5611_;
}
case 8:
{
lean_object* v_type_5630_; lean_object* v_value_5631_; lean_object* v_body_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; 
v_type_5630_ = lean_ctor_get(v_x_5610_, 1);
v_value_5631_ = lean_ctor_get(v_x_5610_, 2);
v_body_5632_ = lean_ctor_get(v_x_5610_, 3);
v___x_5633_ = lean_unsigned_to_nat(1u);
v___x_5634_ = l_Lean_Expr_sizeWithoutSharing(v_type_5630_);
v___x_5635_ = lean_nat_add(v___x_5633_, v___x_5634_);
lean_dec(v___x_5634_);
v___x_5636_ = l_Lean_Expr_sizeWithoutSharing(v_value_5631_);
v___x_5637_ = lean_nat_add(v___x_5635_, v___x_5636_);
lean_dec(v___x_5636_);
lean_dec(v___x_5635_);
v___x_5638_ = l_Lean_Expr_sizeWithoutSharing(v_body_5632_);
v___x_5639_ = lean_nat_add(v___x_5637_, v___x_5638_);
lean_dec(v___x_5638_);
lean_dec(v___x_5637_);
return v___x_5639_;
}
case 10:
{
lean_object* v_expr_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; 
v_expr_5640_ = lean_ctor_get(v_x_5610_, 1);
v___x_5641_ = lean_unsigned_to_nat(1u);
v___x_5642_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5640_);
v___x_5643_ = lean_nat_add(v___x_5641_, v___x_5642_);
lean_dec(v___x_5642_);
return v___x_5643_;
}
case 11:
{
lean_object* v_struct_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; 
v_struct_5644_ = lean_ctor_get(v_x_5610_, 2);
v___x_5645_ = lean_unsigned_to_nat(1u);
v___x_5646_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5644_);
v___x_5647_ = lean_nat_add(v___x_5645_, v___x_5646_);
lean_dec(v___x_5646_);
return v___x_5647_;
}
default: 
{
lean_object* v___x_5648_; 
v___x_5648_ = lean_unsigned_to_nat(1u);
return v___x_5648_;
}
}
v___jp_5611_:
{
lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; 
v___x_5614_ = lean_unsigned_to_nat(1u);
v___x_5615_ = l_Lean_Expr_sizeWithoutSharing(v_d_5612_);
v___x_5616_ = lean_nat_add(v___x_5614_, v___x_5615_);
lean_dec(v___x_5615_);
v___x_5617_ = l_Lean_Expr_sizeWithoutSharing(v_b_5613_);
v___x_5618_ = lean_nat_add(v___x_5616_, v___x_5617_);
lean_dec(v___x_5617_);
lean_dec(v___x_5616_);
return v___x_5618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5649_){
_start:
{
lean_object* v_res_5650_; 
v_res_5650_ = l_Lean_Expr_sizeWithoutSharing(v_x_5649_);
lean_dec_ref(v_x_5649_);
return v_res_5650_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5653_, lean_object* v_e_5654_){
_start:
{
lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; 
v___x_5655_ = l_Lean_KVMap_empty;
v___x_5656_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5657_ = l_Lean_KVMap_insert(v___x_5655_, v_kind_5653_, v___x_5656_);
v___x_5658_ = l_Lean_Expr_mdata___override(v___x_5657_, v_e_5654_);
return v___x_5658_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5659_, lean_object* v_e_5660_){
_start:
{
if (lean_obj_tag(v_e_5660_) == 10)
{
lean_object* v_data_5661_; lean_object* v_expr_5662_; uint8_t v___y_5664_; lean_object* v___x_5667_; lean_object* v___x_5668_; uint8_t v___x_5669_; 
v_data_5661_ = lean_ctor_get(v_e_5660_, 0);
v_expr_5662_ = lean_ctor_get(v_e_5660_, 1);
v___x_5667_ = l_Lean_KVMap_size(v_data_5661_);
v___x_5668_ = lean_unsigned_to_nat(1u);
v___x_5669_ = lean_nat_dec_eq(v___x_5667_, v___x_5668_);
lean_dec(v___x_5667_);
if (v___x_5669_ == 0)
{
v___y_5664_ = v___x_5669_;
goto v___jp_5663_;
}
else
{
uint8_t v___x_5670_; uint8_t v___x_5671_; 
v___x_5670_ = 0;
v___x_5671_ = l_Lean_KVMap_getBool(v_data_5661_, v_kind_5659_, v___x_5670_);
v___y_5664_ = v___x_5671_;
goto v___jp_5663_;
}
v___jp_5663_:
{
if (v___y_5664_ == 0)
{
lean_object* v___x_5665_; 
v___x_5665_ = lean_box(0);
return v___x_5665_;
}
else
{
lean_object* v___x_5666_; 
lean_inc_ref(v_expr_5662_);
v___x_5666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5666_, 0, v_expr_5662_);
return v___x_5666_;
}
}
}
else
{
lean_object* v___x_5672_; 
v___x_5672_ = lean_box(0);
return v___x_5672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* v_kind_5673_, lean_object* v_e_5674_){
_start:
{
lean_object* v_res_5675_; 
v_res_5675_ = l_Lean_annotation_x3f(v_kind_5673_, v_e_5674_);
lean_dec_ref(v_e_5674_);
lean_dec(v_kind_5673_);
return v_res_5675_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* v_e_5679_){
_start:
{
lean_object* v___x_5680_; lean_object* v___x_5681_; 
v___x_5680_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5681_ = l_Lean_mkAnnotation(v___x_5680_, v_e_5679_);
return v___x_5681_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* v_e_5682_){
_start:
{
lean_object* v___x_5683_; lean_object* v___x_5684_; 
v___x_5683_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5684_ = l_Lean_annotation_x3f(v___x_5683_, v_e_5682_);
return v___x_5684_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* v_e_5685_){
_start:
{
lean_object* v_res_5686_; 
v_res_5686_ = l_Lean_inaccessible_x3f(v_e_5685_);
lean_dec_ref(v_e_5685_);
return v_res_5686_;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* v_p_5691_){
_start:
{
if (lean_obj_tag(v_p_5691_) == 10)
{
lean_object* v_data_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; 
v_data_5692_ = lean_ctor_get(v_p_5691_, 0);
v___x_5693_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5694_ = l_Lean_KVMap_find(v_data_5692_, v___x_5693_);
if (lean_obj_tag(v___x_5694_) == 1)
{
lean_object* v_val_5695_; lean_object* v___x_5697_; uint8_t v_isShared_5698_; uint8_t v_isSharedCheck_5706_; 
v_val_5695_ = lean_ctor_get(v___x_5694_, 0);
v_isSharedCheck_5706_ = !lean_is_exclusive(v___x_5694_);
if (v_isSharedCheck_5706_ == 0)
{
v___x_5697_ = v___x_5694_;
v_isShared_5698_ = v_isSharedCheck_5706_;
goto v_resetjp_5696_;
}
else
{
lean_inc(v_val_5695_);
lean_dec(v___x_5694_);
v___x_5697_ = lean_box(0);
v_isShared_5698_ = v_isSharedCheck_5706_;
goto v_resetjp_5696_;
}
v_resetjp_5696_:
{
if (lean_obj_tag(v_val_5695_) == 5)
{
lean_object* v_v_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5703_; 
v_v_5699_ = lean_ctor_get(v_val_5695_, 0);
lean_inc(v_v_5699_);
lean_dec_ref_known(v_val_5695_, 1);
v___x_5700_ = l_Lean_Expr_mdataExpr_x21(v_p_5691_);
v___x_5701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5701_, 0, v_v_5699_);
lean_ctor_set(v___x_5701_, 1, v___x_5700_);
if (v_isShared_5698_ == 0)
{
lean_ctor_set(v___x_5697_, 0, v___x_5701_);
v___x_5703_ = v___x_5697_;
goto v_reusejp_5702_;
}
else
{
lean_object* v_reuseFailAlloc_5704_; 
v_reuseFailAlloc_5704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5704_, 0, v___x_5701_);
v___x_5703_ = v_reuseFailAlloc_5704_;
goto v_reusejp_5702_;
}
v_reusejp_5702_:
{
return v___x_5703_;
}
}
else
{
lean_object* v___x_5705_; 
lean_del_object(v___x_5697_);
lean_dec(v_val_5695_);
v___x_5705_ = lean_box(0);
return v___x_5705_;
}
}
}
else
{
lean_object* v___x_5707_; 
lean_dec(v___x_5694_);
v___x_5707_ = lean_box(0);
return v___x_5707_;
}
}
else
{
lean_object* v___x_5708_; 
v___x_5708_ = lean_box(0);
return v___x_5708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* v_p_5709_){
_start:
{
lean_object* v_res_5710_; 
v_res_5710_ = l_Lean_patternWithRef_x3f(v_p_5709_);
lean_dec_ref(v_p_5709_);
return v_res_5710_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object* v_p_5711_){
_start:
{
lean_object* v___x_5712_; 
v___x_5712_ = l_Lean_patternWithRef_x3f(v_p_5711_);
if (lean_obj_tag(v___x_5712_) == 0)
{
uint8_t v___x_5713_; 
v___x_5713_ = 0;
return v___x_5713_;
}
else
{
uint8_t v___x_5714_; 
lean_dec_ref_known(v___x_5712_, 1);
v___x_5714_ = 1;
return v___x_5714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* v_p_5715_){
_start:
{
uint8_t v_res_5716_; lean_object* v_r_5717_; 
v_res_5716_ = l_Lean_isPatternWithRef(v_p_5715_);
lean_dec_ref(v_p_5715_);
v_r_5717_ = lean_box(v_res_5716_);
return v_r_5717_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* v_p_5718_, lean_object* v_stx_5719_){
_start:
{
lean_object* v___x_5720_; 
v___x_5720_ = l_Lean_patternWithRef_x3f(v_p_5718_);
if (lean_obj_tag(v___x_5720_) == 0)
{
lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; 
v___x_5721_ = l_Lean_KVMap_empty;
v___x_5722_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5723_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_5723_, 0, v_stx_5719_);
v___x_5724_ = l_Lean_KVMap_insert(v___x_5721_, v___x_5722_, v___x_5723_);
v___x_5725_ = l_Lean_Expr_mdata___override(v___x_5724_, v_p_5718_);
return v___x_5725_;
}
else
{
lean_dec_ref_known(v___x_5720_, 1);
lean_dec(v_stx_5719_);
return v_p_5718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* v_e_5726_){
_start:
{
lean_object* v___x_5727_; 
v___x_5727_ = l_Lean_inaccessible_x3f(v_e_5726_);
if (lean_obj_tag(v___x_5727_) == 1)
{
return v___x_5727_;
}
else
{
lean_object* v___x_5728_; 
lean_dec(v___x_5727_);
v___x_5728_ = l_Lean_patternWithRef_x3f(v_e_5726_);
if (lean_obj_tag(v___x_5728_) == 1)
{
lean_object* v_val_5729_; lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5737_; 
v_val_5729_ = lean_ctor_get(v___x_5728_, 0);
v_isSharedCheck_5737_ = !lean_is_exclusive(v___x_5728_);
if (v_isSharedCheck_5737_ == 0)
{
v___x_5731_ = v___x_5728_;
v_isShared_5732_ = v_isSharedCheck_5737_;
goto v_resetjp_5730_;
}
else
{
lean_inc(v_val_5729_);
lean_dec(v___x_5728_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5737_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
lean_object* v_snd_5733_; lean_object* v___x_5735_; 
v_snd_5733_ = lean_ctor_get(v_val_5729_, 1);
lean_inc(v_snd_5733_);
lean_dec(v_val_5729_);
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 0, v_snd_5733_);
v___x_5735_ = v___x_5731_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5736_; 
v_reuseFailAlloc_5736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5736_, 0, v_snd_5733_);
v___x_5735_ = v_reuseFailAlloc_5736_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
return v___x_5735_;
}
}
}
else
{
lean_object* v___x_5738_; 
lean_dec(v___x_5728_);
v___x_5738_ = lean_box(0);
return v___x_5738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* v_e_5739_){
_start:
{
lean_object* v_res_5740_; 
v_res_5740_ = l_Lean_patternAnnotation_x3f(v_e_5739_);
lean_dec_ref(v_e_5739_);
return v_res_5740_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* v_e_5744_){
_start:
{
lean_object* v___x_5745_; lean_object* v___x_5746_; 
v___x_5745_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5746_ = l_Lean_mkAnnotation(v___x_5745_, v_e_5744_);
return v___x_5746_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* v_e_5750_){
_start:
{
lean_object* v___x_5751_; lean_object* v___x_5752_; 
v___x_5751_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5752_ = l_Lean_annotation_x3f(v___x_5751_, v_e_5750_);
if (lean_obj_tag(v___x_5752_) == 0)
{
return v___x_5752_;
}
else
{
lean_object* v_val_5753_; lean_object* v___x_5755_; uint8_t v_isShared_5756_; uint8_t v_isSharedCheck_5766_; 
v_val_5753_ = lean_ctor_get(v___x_5752_, 0);
v_isSharedCheck_5766_ = !lean_is_exclusive(v___x_5752_);
if (v_isSharedCheck_5766_ == 0)
{
v___x_5755_ = v___x_5752_;
v_isShared_5756_ = v_isSharedCheck_5766_;
goto v_resetjp_5754_;
}
else
{
lean_inc(v_val_5753_);
lean_dec(v___x_5752_);
v___x_5755_ = lean_box(0);
v_isShared_5756_ = v_isSharedCheck_5766_;
goto v_resetjp_5754_;
}
v_resetjp_5754_:
{
lean_object* v___x_5757_; lean_object* v___x_5758_; uint8_t v___x_5759_; 
v___x_5757_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5758_ = lean_unsigned_to_nat(3u);
v___x_5759_ = l_Lean_Expr_isAppOfArity(v_val_5753_, v___x_5757_, v___x_5758_);
if (v___x_5759_ == 0)
{
lean_object* v___x_5760_; 
lean_del_object(v___x_5755_);
lean_dec(v_val_5753_);
v___x_5760_ = lean_box(0);
return v___x_5760_;
}
else
{
lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5764_; 
v___x_5761_ = l_Lean_Expr_appFn_x21(v_val_5753_);
lean_dec(v_val_5753_);
v___x_5762_ = l_Lean_Expr_appArg_x21(v___x_5761_);
lean_dec_ref(v___x_5761_);
if (v_isShared_5756_ == 0)
{
lean_ctor_set(v___x_5755_, 0, v___x_5762_);
v___x_5764_ = v___x_5755_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5765_; 
v_reuseFailAlloc_5765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5765_, 0, v___x_5762_);
v___x_5764_ = v_reuseFailAlloc_5765_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
return v___x_5764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* v_e_5767_){
_start:
{
lean_object* v_res_5768_; 
v_res_5768_ = l_Lean_isLHSGoal_x3f(v_e_5767_);
lean_dec_ref(v_e_5767_);
return v_res_5768_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* v_toPure_5769_, lean_object* v_____do__lift_5770_){
_start:
{
lean_object* v___x_5771_; 
v___x_5771_ = lean_apply_2(v_toPure_5769_, lean_box(0), v_____do__lift_5770_);
return v___x_5771_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* v_inst_5772_, lean_object* v_inst_5773_){
_start:
{
lean_object* v_toApplicative_5774_; lean_object* v_toBind_5775_; lean_object* v_toPure_5776_; lean_object* v___x_5777_; lean_object* v___f_5778_; lean_object* v___x_5779_; 
v_toApplicative_5774_ = lean_ctor_get(v_inst_5772_, 0);
v_toBind_5775_ = lean_ctor_get(v_inst_5772_, 1);
lean_inc(v_toBind_5775_);
v_toPure_5776_ = lean_ctor_get(v_toApplicative_5774_, 1);
lean_inc(v_toPure_5776_);
v___x_5777_ = l_Lean_mkFreshId___redArg(v_inst_5772_, v_inst_5773_);
v___f_5778_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5778_, 0, v_toPure_5776_);
v___x_5779_ = lean_apply_4(v_toBind_5775_, lean_box(0), lean_box(0), v___x_5777_, v___f_5778_);
return v___x_5779_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* v_m_5780_, lean_object* v_inst_5781_, lean_object* v_inst_5782_){
_start:
{
lean_object* v___x_5783_; 
v___x_5783_ = l_Lean_mkFreshFVarId___redArg(v_inst_5781_, v_inst_5782_);
return v___x_5783_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* v_inst_5784_, lean_object* v_inst_5785_){
_start:
{
lean_object* v_toApplicative_5786_; lean_object* v_toBind_5787_; lean_object* v_toPure_5788_; lean_object* v___x_5789_; lean_object* v___f_5790_; lean_object* v___x_5791_; 
v_toApplicative_5786_ = lean_ctor_get(v_inst_5784_, 0);
v_toBind_5787_ = lean_ctor_get(v_inst_5784_, 1);
lean_inc(v_toBind_5787_);
v_toPure_5788_ = lean_ctor_get(v_toApplicative_5786_, 1);
lean_inc(v_toPure_5788_);
v___x_5789_ = l_Lean_mkFreshId___redArg(v_inst_5784_, v_inst_5785_);
v___f_5790_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5790_, 0, v_toPure_5788_);
v___x_5791_ = lean_apply_4(v_toBind_5787_, lean_box(0), lean_box(0), v___x_5789_, v___f_5790_);
return v___x_5791_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* v_m_5792_, lean_object* v_inst_5793_, lean_object* v_inst_5794_){
_start:
{
lean_object* v___x_5795_; 
v___x_5795_ = l_Lean_mkFreshMVarId___redArg(v_inst_5793_, v_inst_5794_);
return v___x_5795_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* v_inst_5796_, lean_object* v_inst_5797_){
_start:
{
lean_object* v_toApplicative_5798_; lean_object* v_toBind_5799_; lean_object* v_toPure_5800_; lean_object* v___x_5801_; lean_object* v___f_5802_; lean_object* v___x_5803_; 
v_toApplicative_5798_ = lean_ctor_get(v_inst_5796_, 0);
v_toBind_5799_ = lean_ctor_get(v_inst_5796_, 1);
lean_inc(v_toBind_5799_);
v_toPure_5800_ = lean_ctor_get(v_toApplicative_5798_, 1);
lean_inc(v_toPure_5800_);
v___x_5801_ = l_Lean_mkFreshId___redArg(v_inst_5796_, v_inst_5797_);
v___f_5802_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5802_, 0, v_toPure_5800_);
v___x_5803_ = lean_apply_4(v_toBind_5799_, lean_box(0), lean_box(0), v___x_5801_, v___f_5802_);
return v___x_5803_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* v_m_5804_, lean_object* v_inst_5805_, lean_object* v_inst_5806_){
_start:
{
lean_object* v___x_5807_; 
v___x_5807_ = l_Lean_mkFreshLMVarId___redArg(v_inst_5805_, v_inst_5806_);
return v___x_5807_;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2(void){
_start:
{
lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; 
v___x_5811_ = lean_box(0);
v___x_5812_ = ((lean_object*)(l_Lean_mkNot___closed__1));
v___x_5813_ = l_Lean_Expr_const___override(v___x_5812_, v___x_5811_);
return v___x_5813_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* v_p_5814_){
_start:
{
lean_object* v___x_5815_; lean_object* v___x_5816_; 
v___x_5815_ = lean_obj_once(&l_Lean_mkNot___closed__2, &l_Lean_mkNot___closed__2_once, _init_l_Lean_mkNot___closed__2);
v___x_5816_ = l_Lean_Expr_app___override(v___x_5815_, v_p_5814_);
return v___x_5816_;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2(void){
_start:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5820_ = lean_box(0);
v___x_5821_ = ((lean_object*)(l_Lean_mkOr___closed__1));
v___x_5822_ = l_Lean_Expr_const___override(v___x_5821_, v___x_5820_);
return v___x_5822_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* v_p_5823_, lean_object* v_q_5824_){
_start:
{
lean_object* v___x_5825_; lean_object* v___x_5826_; 
v___x_5825_ = lean_obj_once(&l_Lean_mkOr___closed__2, &l_Lean_mkOr___closed__2_once, _init_l_Lean_mkOr___closed__2);
v___x_5826_ = l_Lean_mkAppB(v___x_5825_, v_p_5823_, v_q_5824_);
return v___x_5826_;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2(void){
_start:
{
lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; 
v___x_5830_ = lean_box(0);
v___x_5831_ = ((lean_object*)(l_Lean_mkAnd___closed__1));
v___x_5832_ = l_Lean_Expr_const___override(v___x_5831_, v___x_5830_);
return v___x_5832_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* v_p_5833_, lean_object* v_q_5834_){
_start:
{
lean_object* v___x_5835_; lean_object* v___x_5836_; 
v___x_5835_ = lean_obj_once(&l_Lean_mkAnd___closed__2, &l_Lean_mkAnd___closed__2_once, _init_l_Lean_mkAnd___closed__2);
v___x_5836_ = l_Lean_mkAppB(v___x_5835_, v_p_5833_, v_q_5834_);
return v___x_5836_;
}
}
static lean_object* _init_l_Lean_mkAndN___closed__0(void){
_start:
{
lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; 
v___x_5837_ = lean_box(0);
v___x_5838_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_5839_ = l_Lean_Expr_const___override(v___x_5838_, v___x_5837_);
return v___x_5839_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* v_x_5840_){
_start:
{
if (lean_obj_tag(v_x_5840_) == 0)
{
lean_object* v___x_5841_; 
v___x_5841_ = lean_obj_once(&l_Lean_mkAndN___closed__0, &l_Lean_mkAndN___closed__0_once, _init_l_Lean_mkAndN___closed__0);
return v___x_5841_;
}
else
{
lean_object* v_tail_5842_; 
v_tail_5842_ = lean_ctor_get(v_x_5840_, 1);
if (lean_obj_tag(v_tail_5842_) == 0)
{
lean_object* v_head_5843_; 
v_head_5843_ = lean_ctor_get(v_x_5840_, 0);
lean_inc(v_head_5843_);
lean_dec_ref_known(v_x_5840_, 2);
return v_head_5843_;
}
else
{
lean_object* v_head_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; 
lean_inc(v_tail_5842_);
v_head_5844_ = lean_ctor_get(v_x_5840_, 0);
lean_inc(v_head_5844_);
lean_dec_ref_known(v_x_5840_, 2);
v___x_5845_ = l_Lean_mkAndN(v_tail_5842_);
v___x_5846_ = l_Lean_mkAnd(v_head_5844_, v___x_5845_);
return v___x_5846_;
}
}
}
}
static lean_object* _init_l_Lean_mkEM___closed__3(void){
_start:
{
lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5852_ = lean_box(0);
v___x_5853_ = ((lean_object*)(l_Lean_mkEM___closed__2));
v___x_5854_ = l_Lean_Expr_const___override(v___x_5853_, v___x_5852_);
return v___x_5854_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* v_p_5855_){
_start:
{
lean_object* v___x_5856_; lean_object* v___x_5857_; 
v___x_5856_ = lean_obj_once(&l_Lean_mkEM___closed__3, &l_Lean_mkEM___closed__3_once, _init_l_Lean_mkEM___closed__3);
v___x_5857_ = l_Lean_Expr_app___override(v___x_5856_, v_p_5855_);
return v___x_5857_;
}
}
static lean_object* _init_l_Lean_mkIff___closed__2(void){
_start:
{
lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; 
v___x_5861_ = lean_box(0);
v___x_5862_ = ((lean_object*)(l_Lean_mkIff___closed__1));
v___x_5863_ = l_Lean_Expr_const___override(v___x_5862_, v___x_5861_);
return v___x_5863_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* v_p_5864_, lean_object* v_q_5865_){
_start:
{
lean_object* v___x_5866_; lean_object* v___x_5867_; 
v___x_5866_ = lean_obj_once(&l_Lean_mkIff___closed__2, &l_Lean_mkIff___closed__2_once, _init_l_Lean_mkIff___closed__2);
v___x_5867_ = l_Lean_mkAppB(v___x_5866_, v_p_5864_, v_q_5865_);
return v___x_5867_;
}
}
static lean_object* _init_l_Lean_Nat_mkType(void){
_start:
{
lean_object* v___x_5868_; 
v___x_5868_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_5868_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; 
v___x_5872_ = lean_box(0);
v___x_5873_ = ((lean_object*)(l_Lean_Nat_mkInstAdd___closed__1));
v___x_5874_ = l_Lean_Expr_const___override(v___x_5873_, v___x_5872_);
return v___x_5874_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd(void){
_start:
{
lean_object* v___x_5875_; 
v___x_5875_ = lean_obj_once(&l_Lean_Nat_mkInstAdd___closed__2, &l_Lean_Nat_mkInstAdd___closed__2_once, _init_l_Lean_Nat_mkInstAdd___closed__2);
return v___x_5875_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__2(void){
_start:
{
lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; 
v___x_5879_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5880_ = ((lean_object*)(l_Lean_Nat_mkInstHAdd___closed__1));
v___x_5881_ = l_Lean_Expr_const___override(v___x_5880_, v___x_5879_);
return v___x_5881_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__3(void){
_start:
{
lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; 
v___x_5882_ = l_Lean_Nat_mkInstAdd;
v___x_5883_ = l_Lean_Nat_mkType;
v___x_5884_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_5885_ = l_Lean_mkAppB(v___x_5884_, v___x_5883_, v___x_5882_);
return v___x_5885_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd(void){
_start:
{
lean_object* v___x_5886_; 
v___x_5886_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__3, &l_Lean_Nat_mkInstHAdd___closed__3_once, _init_l_Lean_Nat_mkInstHAdd___closed__3);
return v___x_5886_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; 
v___x_5890_ = lean_box(0);
v___x_5891_ = ((lean_object*)(l_Lean_Nat_mkInstSub___closed__1));
v___x_5892_ = l_Lean_Expr_const___override(v___x_5891_, v___x_5890_);
return v___x_5892_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub(void){
_start:
{
lean_object* v___x_5893_; 
v___x_5893_ = lean_obj_once(&l_Lean_Nat_mkInstSub___closed__2, &l_Lean_Nat_mkInstSub___closed__2_once, _init_l_Lean_Nat_mkInstSub___closed__2);
return v___x_5893_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__2(void){
_start:
{
lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; 
v___x_5897_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5898_ = ((lean_object*)(l_Lean_Nat_mkInstHSub___closed__1));
v___x_5899_ = l_Lean_Expr_const___override(v___x_5898_, v___x_5897_);
return v___x_5899_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__3(void){
_start:
{
lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; 
v___x_5900_ = l_Lean_Nat_mkInstSub;
v___x_5901_ = l_Lean_Nat_mkType;
v___x_5902_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_5903_ = l_Lean_mkAppB(v___x_5902_, v___x_5901_, v___x_5900_);
return v___x_5903_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub(void){
_start:
{
lean_object* v___x_5904_; 
v___x_5904_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__3, &l_Lean_Nat_mkInstHSub___closed__3_once, _init_l_Lean_Nat_mkInstHSub___closed__3);
return v___x_5904_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; 
v___x_5908_ = lean_box(0);
v___x_5909_ = ((lean_object*)(l_Lean_Nat_mkInstMul___closed__1));
v___x_5910_ = l_Lean_Expr_const___override(v___x_5909_, v___x_5908_);
return v___x_5910_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul(void){
_start:
{
lean_object* v___x_5911_; 
v___x_5911_ = lean_obj_once(&l_Lean_Nat_mkInstMul___closed__2, &l_Lean_Nat_mkInstMul___closed__2_once, _init_l_Lean_Nat_mkInstMul___closed__2);
return v___x_5911_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__2(void){
_start:
{
lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; 
v___x_5915_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5916_ = ((lean_object*)(l_Lean_Nat_mkInstHMul___closed__1));
v___x_5917_ = l_Lean_Expr_const___override(v___x_5916_, v___x_5915_);
return v___x_5917_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; 
v___x_5918_ = l_Lean_Nat_mkInstMul;
v___x_5919_ = l_Lean_Nat_mkType;
v___x_5920_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_5921_ = l_Lean_mkAppB(v___x_5920_, v___x_5919_, v___x_5918_);
return v___x_5921_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul(void){
_start:
{
lean_object* v___x_5922_; 
v___x_5922_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__3, &l_Lean_Nat_mkInstHMul___closed__3_once, _init_l_Lean_Nat_mkInstHMul___closed__3);
return v___x_5922_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv___closed__2(void){
_start:
{
lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; 
v___x_5927_ = lean_box(0);
v___x_5928_ = ((lean_object*)(l_Lean_Nat_mkInstDiv___closed__1));
v___x_5929_ = l_Lean_Expr_const___override(v___x_5928_, v___x_5927_);
return v___x_5929_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv(void){
_start:
{
lean_object* v___x_5930_; 
v___x_5930_ = lean_obj_once(&l_Lean_Nat_mkInstDiv___closed__2, &l_Lean_Nat_mkInstDiv___closed__2_once, _init_l_Lean_Nat_mkInstDiv___closed__2);
return v___x_5930_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__2(void){
_start:
{
lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; 
v___x_5934_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5935_ = ((lean_object*)(l_Lean_Nat_mkInstHDiv___closed__1));
v___x_5936_ = l_Lean_Expr_const___override(v___x_5935_, v___x_5934_);
return v___x_5936_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__3(void){
_start:
{
lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; 
v___x_5937_ = l_Lean_Nat_mkInstDiv;
v___x_5938_ = l_Lean_Nat_mkType;
v___x_5939_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_5940_ = l_Lean_mkAppB(v___x_5939_, v___x_5938_, v___x_5937_);
return v___x_5940_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv(void){
_start:
{
lean_object* v___x_5941_; 
v___x_5941_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__3, &l_Lean_Nat_mkInstHDiv___closed__3_once, _init_l_Lean_Nat_mkInstHDiv___closed__3);
return v___x_5941_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod___closed__2(void){
_start:
{
lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; 
v___x_5946_ = lean_box(0);
v___x_5947_ = ((lean_object*)(l_Lean_Nat_mkInstMod___closed__1));
v___x_5948_ = l_Lean_Expr_const___override(v___x_5947_, v___x_5946_);
return v___x_5948_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod(void){
_start:
{
lean_object* v___x_5949_; 
v___x_5949_ = lean_obj_once(&l_Lean_Nat_mkInstMod___closed__2, &l_Lean_Nat_mkInstMod___closed__2_once, _init_l_Lean_Nat_mkInstMod___closed__2);
return v___x_5949_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__2(void){
_start:
{
lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; 
v___x_5953_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5954_ = ((lean_object*)(l_Lean_Nat_mkInstHMod___closed__1));
v___x_5955_ = l_Lean_Expr_const___override(v___x_5954_, v___x_5953_);
return v___x_5955_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__3(void){
_start:
{
lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; 
v___x_5956_ = l_Lean_Nat_mkInstMod;
v___x_5957_ = l_Lean_Nat_mkType;
v___x_5958_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_5959_ = l_Lean_mkAppB(v___x_5958_, v___x_5957_, v___x_5956_);
return v___x_5959_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod(void){
_start:
{
lean_object* v___x_5960_; 
v___x_5960_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__3, &l_Lean_Nat_mkInstHMod___closed__3_once, _init_l_Lean_Nat_mkInstHMod___closed__3);
return v___x_5960_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow___closed__2(void){
_start:
{
lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; 
v___x_5964_ = lean_box(0);
v___x_5965_ = ((lean_object*)(l_Lean_Nat_mkInstNatPow___closed__1));
v___x_5966_ = l_Lean_Expr_const___override(v___x_5965_, v___x_5964_);
return v___x_5966_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow(void){
_start:
{
lean_object* v___x_5967_; 
v___x_5967_ = lean_obj_once(&l_Lean_Nat_mkInstNatPow___closed__2, &l_Lean_Nat_mkInstNatPow___closed__2_once, _init_l_Lean_Nat_mkInstNatPow___closed__2);
return v___x_5967_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; 
v___x_5971_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5972_ = ((lean_object*)(l_Lean_Nat_mkInstPow___closed__1));
v___x_5973_ = l_Lean_Expr_const___override(v___x_5972_, v___x_5971_);
return v___x_5973_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__3(void){
_start:
{
lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; 
v___x_5974_ = l_Lean_Nat_mkInstNatPow;
v___x_5975_ = l_Lean_Nat_mkType;
v___x_5976_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_5977_ = l_Lean_mkAppB(v___x_5976_, v___x_5975_, v___x_5974_);
return v___x_5977_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow(void){
_start:
{
lean_object* v___x_5978_; 
v___x_5978_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__3, &l_Lean_Nat_mkInstPow___closed__3_once, _init_l_Lean_Nat_mkInstPow___closed__3);
return v___x_5978_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__3(void){
_start:
{
lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; 
v___x_5985_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__2));
v___x_5986_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__1));
v___x_5987_ = l_Lean_Expr_const___override(v___x_5986_, v___x_5985_);
return v___x_5987_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__4(void){
_start:
{
lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; 
v___x_5988_ = l_Lean_Nat_mkInstPow;
v___x_5989_ = l_Lean_Nat_mkType;
v___x_5990_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_5991_ = l_Lean_mkApp3(v___x_5990_, v___x_5989_, v___x_5989_, v___x_5988_);
return v___x_5991_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow(void){
_start:
{
lean_object* v___x_5992_; 
v___x_5992_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__4, &l_Lean_Nat_mkInstHPow___closed__4_once, _init_l_Lean_Nat_mkInstHPow___closed__4);
return v___x_5992_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; 
v___x_5996_ = lean_box(0);
v___x_5997_ = ((lean_object*)(l_Lean_Nat_mkInstLT___closed__1));
v___x_5998_ = l_Lean_Expr_const___override(v___x_5997_, v___x_5996_);
return v___x_5998_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT(void){
_start:
{
lean_object* v___x_5999_; 
v___x_5999_ = lean_obj_once(&l_Lean_Nat_mkInstLT___closed__2, &l_Lean_Nat_mkInstLT___closed__2_once, _init_l_Lean_Nat_mkInstLT___closed__2);
return v___x_5999_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; 
v___x_6003_ = lean_box(0);
v___x_6004_ = ((lean_object*)(l_Lean_Nat_mkInstLE___closed__1));
v___x_6005_ = l_Lean_Expr_const___override(v___x_6004_, v___x_6003_);
return v___x_6005_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE(void){
_start:
{
lean_object* v___x_6006_; 
v___x_6006_ = lean_obj_once(&l_Lean_Nat_mkInstLE___closed__2, &l_Lean_Nat_mkInstLE___closed__2_once, _init_l_Lean_Nat_mkInstLE___closed__2);
return v___x_6006_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3(void){
_start:
{
lean_object* v___x_6012_; lean_object* v___x_6013_; 
v___x_6012_ = lean_unsigned_to_nat(0u);
v___x_6013_ = l_Lean_Level_ofNat(v___x_6012_);
return v___x_6013_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4(void){
_start:
{
lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; 
v___x_6014_ = lean_box(0);
v___x_6015_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6015_);
lean_ctor_set(v___x_6016_, 1, v___x_6014_);
return v___x_6016_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5(void){
_start:
{
lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; 
v___x_6017_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6018_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6019_, 0, v___x_6018_);
lean_ctor_set(v___x_6019_, 1, v___x_6017_);
return v___x_6019_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6(void){
_start:
{
lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; 
v___x_6020_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__5, &l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5);
v___x_6021_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6021_);
lean_ctor_set(v___x_6022_, 1, v___x_6020_);
return v___x_6022_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7(void){
_start:
{
lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; 
v___x_6023_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6024_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natAddFn___closed__2));
v___x_6025_ = l_Lean_Expr_const___override(v___x_6024_, v___x_6023_);
return v___x_6025_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8(void){
_start:
{
lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; 
v___x_6026_ = l_Lean_Nat_mkInstHAdd;
v___x_6027_ = l_Lean_Nat_mkType;
v___x_6028_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6029_ = l_Lean_mkApp4(v___x_6028_, v___x_6027_, v___x_6027_, v___x_6027_, v___x_6026_);
return v___x_6029_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn(void){
_start:
{
lean_object* v___x_6030_; 
v___x_6030_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__8, &l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8);
return v___x_6030_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3(void){
_start:
{
lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; 
v___x_6036_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6037_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natSubFn___closed__2));
v___x_6038_ = l_Lean_Expr_const___override(v___x_6037_, v___x_6036_);
return v___x_6038_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4(void){
_start:
{
lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; 
v___x_6039_ = l_Lean_Nat_mkInstHSub;
v___x_6040_ = l_Lean_Nat_mkType;
v___x_6041_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6042_ = l_Lean_mkApp4(v___x_6041_, v___x_6040_, v___x_6040_, v___x_6040_, v___x_6039_);
return v___x_6042_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn(void){
_start:
{
lean_object* v___x_6043_; 
v___x_6043_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__4, &l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4);
return v___x_6043_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3(void){
_start:
{
lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; 
v___x_6049_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6050_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natMulFn___closed__2));
v___x_6051_ = l_Lean_Expr_const___override(v___x_6050_, v___x_6049_);
return v___x_6051_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4(void){
_start:
{
lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; 
v___x_6052_ = l_Lean_Nat_mkInstHMul;
v___x_6053_ = l_Lean_Nat_mkType;
v___x_6054_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6055_ = l_Lean_mkApp4(v___x_6054_, v___x_6053_, v___x_6053_, v___x_6053_, v___x_6052_);
return v___x_6055_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn(void){
_start:
{
lean_object* v___x_6056_; 
v___x_6056_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__4, &l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4);
return v___x_6056_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3(void){
_start:
{
lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; 
v___x_6062_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6063_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natPowFn___closed__2));
v___x_6064_ = l_Lean_Expr_const___override(v___x_6063_, v___x_6062_);
return v___x_6064_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4(void){
_start:
{
lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; 
v___x_6065_ = l_Lean_Nat_mkInstHPow;
v___x_6066_ = l_Lean_Nat_mkType;
v___x_6067_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6068_ = l_Lean_mkApp4(v___x_6067_, v___x_6066_, v___x_6066_, v___x_6066_, v___x_6065_);
return v___x_6068_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn(void){
_start:
{
lean_object* v___x_6069_; 
v___x_6069_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__4, &l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4);
return v___x_6069_;
}
}
static lean_object* _init_l_Lean_mkNatSucc___closed__2(void){
_start:
{
lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; 
v___x_6074_ = lean_box(0);
v___x_6075_ = ((lean_object*)(l_Lean_mkNatSucc___closed__1));
v___x_6076_ = l_Lean_Expr_const___override(v___x_6075_, v___x_6074_);
return v___x_6076_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* v_a_6077_){
_start:
{
lean_object* v___x_6078_; lean_object* v___x_6079_; 
v___x_6078_ = lean_obj_once(&l_Lean_mkNatSucc___closed__2, &l_Lean_mkNatSucc___closed__2_once, _init_l_Lean_mkNatSucc___closed__2);
v___x_6079_ = l_Lean_Expr_app___override(v___x_6078_, v_a_6077_);
return v___x_6079_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* v_a_6080_, lean_object* v_b_6081_){
_start:
{
lean_object* v___x_6082_; lean_object* v___x_6083_; 
v___x_6082_ = l___private_Lean_Expr_0__Lean_natAddFn;
v___x_6083_ = l_Lean_mkAppB(v___x_6082_, v_a_6080_, v_b_6081_);
return v___x_6083_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* v_a_6084_, lean_object* v_b_6085_){
_start:
{
lean_object* v___x_6086_; lean_object* v___x_6087_; 
v___x_6086_ = l___private_Lean_Expr_0__Lean_natSubFn;
v___x_6087_ = l_Lean_mkAppB(v___x_6086_, v_a_6084_, v_b_6085_);
return v___x_6087_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* v_a_6088_, lean_object* v_b_6089_){
_start:
{
lean_object* v___x_6090_; lean_object* v___x_6091_; 
v___x_6090_ = l___private_Lean_Expr_0__Lean_natMulFn;
v___x_6091_ = l_Lean_mkAppB(v___x_6090_, v_a_6088_, v_b_6089_);
return v___x_6091_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object* v_a_6092_, lean_object* v_b_6093_){
_start:
{
lean_object* v___x_6094_; lean_object* v___x_6095_; 
v___x_6094_ = l___private_Lean_Expr_0__Lean_natPowFn;
v___x_6095_ = l_Lean_mkAppB(v___x_6094_, v_a_6092_, v_b_6093_);
return v___x_6095_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3(void){
_start:
{
lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; 
v___x_6101_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6102_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natLEPred___closed__2));
v___x_6103_ = l_Lean_Expr_const___override(v___x_6102_, v___x_6101_);
return v___x_6103_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4(void){
_start:
{
lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; 
v___x_6104_ = l_Lean_Nat_mkInstLE;
v___x_6105_ = l_Lean_Nat_mkType;
v___x_6106_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6107_ = l_Lean_mkAppB(v___x_6106_, v___x_6105_, v___x_6104_);
return v___x_6107_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred(void){
_start:
{
lean_object* v___x_6108_; 
v___x_6108_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__4, &l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4);
return v___x_6108_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* v_a_6109_, lean_object* v_b_6110_){
_start:
{
lean_object* v___x_6111_; lean_object* v___x_6112_; 
v___x_6111_ = l___private_Lean_Expr_0__Lean_natLEPred;
v___x_6112_ = l_Lean_mkAppB(v___x_6111_, v_a_6109_, v_b_6110_);
return v___x_6112_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0(void){
_start:
{
lean_object* v___x_6113_; lean_object* v___x_6114_; 
v___x_6113_ = lean_unsigned_to_nat(1u);
v___x_6114_ = l_Lean_Level_ofNat(v___x_6113_);
return v___x_6114_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1(void){
_start:
{
lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; 
v___x_6115_ = lean_box(0);
v___x_6116_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__0, &l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0);
v___x_6117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6116_);
lean_ctor_set(v___x_6117_, 1, v___x_6115_);
return v___x_6117_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2(void){
_start:
{
lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; 
v___x_6118_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__1, &l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1);
v___x_6119_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_6120_ = l_Lean_Expr_const___override(v___x_6119_, v___x_6118_);
return v___x_6120_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3(void){
_start:
{
lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; 
v___x_6121_ = l_Lean_Nat_mkType;
v___x_6122_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6123_ = l_Lean_Expr_app___override(v___x_6122_, v___x_6121_);
return v___x_6123_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred(void){
_start:
{
lean_object* v___x_6124_; 
v___x_6124_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__3, &l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3);
return v___x_6124_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* v_a_6125_, lean_object* v_b_6126_){
_start:
{
lean_object* v___x_6127_; lean_object* v___x_6128_; 
v___x_6127_ = l___private_Lean_Expr_0__Lean_natEqPred;
v___x_6128_ = l_Lean_mkAppB(v___x_6127_, v_a_6125_, v_b_6126_);
return v___x_6128_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__0(void){
_start:
{
lean_object* v___x_6129_; lean_object* v___x_6130_; 
v___x_6129_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6130_ = l_Lean_Expr_sort___override(v___x_6129_);
return v___x_6130_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__1(void){
_start:
{
lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; 
v___x_6131_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__0, &l___private_Lean_Expr_0__Lean_propEq___closed__0_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__0);
v___x_6132_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6133_ = l_Lean_Expr_app___override(v___x_6132_, v___x_6131_);
return v___x_6133_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq(void){
_start:
{
lean_object* v___x_6134_; 
v___x_6134_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__1, &l___private_Lean_Expr_0__Lean_propEq___closed__1_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__1);
return v___x_6134_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* v_a_6135_, lean_object* v_b_6136_){
_start:
{
lean_object* v___x_6137_; lean_object* v___x_6138_; 
v___x_6137_ = l___private_Lean_Expr_0__Lean_propEq;
v___x_6138_ = l_Lean_mkAppB(v___x_6137_, v_a_6135_, v_b_6136_);
return v___x_6138_;
}
}
static lean_object* _init_l_Lean_Int_mkType___closed__2(void){
_start:
{
lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; 
v___x_6142_ = lean_box(0);
v___x_6143_ = ((lean_object*)(l_Lean_Int_mkType___closed__1));
v___x_6144_ = l_Lean_Expr_const___override(v___x_6143_, v___x_6142_);
return v___x_6144_;
}
}
static lean_object* _init_l_Lean_Int_mkType(void){
_start:
{
lean_object* v___x_6145_; 
v___x_6145_ = lean_obj_once(&l_Lean_Int_mkType___closed__2, &l_Lean_Int_mkType___closed__2_once, _init_l_Lean_Int_mkType___closed__2);
return v___x_6145_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg___closed__2(void){
_start:
{
lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; 
v___x_6150_ = lean_box(0);
v___x_6151_ = ((lean_object*)(l_Lean_Int_mkInstNeg___closed__1));
v___x_6152_ = l_Lean_Expr_const___override(v___x_6151_, v___x_6150_);
return v___x_6152_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg(void){
_start:
{
lean_object* v___x_6153_; 
v___x_6153_ = lean_obj_once(&l_Lean_Int_mkInstNeg___closed__2, &l_Lean_Int_mkInstNeg___closed__2_once, _init_l_Lean_Int_mkInstNeg___closed__2);
return v___x_6153_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; 
v___x_6158_ = lean_box(0);
v___x_6159_ = ((lean_object*)(l_Lean_Int_mkInstAdd___closed__1));
v___x_6160_ = l_Lean_Expr_const___override(v___x_6159_, v___x_6158_);
return v___x_6160_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd(void){
_start:
{
lean_object* v___x_6161_; 
v___x_6161_ = lean_obj_once(&l_Lean_Int_mkInstAdd___closed__2, &l_Lean_Int_mkInstAdd___closed__2_once, _init_l_Lean_Int_mkInstAdd___closed__2);
return v___x_6161_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd___closed__0(void){
_start:
{
lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; 
v___x_6162_ = l_Lean_Int_mkInstAdd;
v___x_6163_ = l_Lean_Int_mkType;
v___x_6164_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6165_ = l_Lean_mkAppB(v___x_6164_, v___x_6163_, v___x_6162_);
return v___x_6165_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd(void){
_start:
{
lean_object* v___x_6166_; 
v___x_6166_ = lean_obj_once(&l_Lean_Int_mkInstHAdd___closed__0, &l_Lean_Int_mkInstHAdd___closed__0_once, _init_l_Lean_Int_mkInstHAdd___closed__0);
return v___x_6166_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; 
v___x_6171_ = lean_box(0);
v___x_6172_ = ((lean_object*)(l_Lean_Int_mkInstSub___closed__1));
v___x_6173_ = l_Lean_Expr_const___override(v___x_6172_, v___x_6171_);
return v___x_6173_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub(void){
_start:
{
lean_object* v___x_6174_; 
v___x_6174_ = lean_obj_once(&l_Lean_Int_mkInstSub___closed__2, &l_Lean_Int_mkInstSub___closed__2_once, _init_l_Lean_Int_mkInstSub___closed__2);
return v___x_6174_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub___closed__0(void){
_start:
{
lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; 
v___x_6175_ = l_Lean_Int_mkInstSub;
v___x_6176_ = l_Lean_Int_mkType;
v___x_6177_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6178_ = l_Lean_mkAppB(v___x_6177_, v___x_6176_, v___x_6175_);
return v___x_6178_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub(void){
_start:
{
lean_object* v___x_6179_; 
v___x_6179_ = lean_obj_once(&l_Lean_Int_mkInstHSub___closed__0, &l_Lean_Int_mkInstHSub___closed__0_once, _init_l_Lean_Int_mkInstHSub___closed__0);
return v___x_6179_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; 
v___x_6184_ = lean_box(0);
v___x_6185_ = ((lean_object*)(l_Lean_Int_mkInstMul___closed__1));
v___x_6186_ = l_Lean_Expr_const___override(v___x_6185_, v___x_6184_);
return v___x_6186_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul(void){
_start:
{
lean_object* v___x_6187_; 
v___x_6187_ = lean_obj_once(&l_Lean_Int_mkInstMul___closed__2, &l_Lean_Int_mkInstMul___closed__2_once, _init_l_Lean_Int_mkInstMul___closed__2);
return v___x_6187_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul___closed__0(void){
_start:
{
lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; 
v___x_6188_ = l_Lean_Int_mkInstMul;
v___x_6189_ = l_Lean_Int_mkType;
v___x_6190_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6191_ = l_Lean_mkAppB(v___x_6190_, v___x_6189_, v___x_6188_);
return v___x_6191_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul(void){
_start:
{
lean_object* v___x_6192_; 
v___x_6192_ = lean_obj_once(&l_Lean_Int_mkInstHMul___closed__0, &l_Lean_Int_mkInstHMul___closed__0_once, _init_l_Lean_Int_mkInstHMul___closed__0);
return v___x_6192_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv___closed__1(void){
_start:
{
lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; 
v___x_6196_ = lean_box(0);
v___x_6197_ = ((lean_object*)(l_Lean_Int_mkInstDiv___closed__0));
v___x_6198_ = l_Lean_Expr_const___override(v___x_6197_, v___x_6196_);
return v___x_6198_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv(void){
_start:
{
lean_object* v___x_6199_; 
v___x_6199_ = lean_obj_once(&l_Lean_Int_mkInstDiv___closed__1, &l_Lean_Int_mkInstDiv___closed__1_once, _init_l_Lean_Int_mkInstDiv___closed__1);
return v___x_6199_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv___closed__0(void){
_start:
{
lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; 
v___x_6200_ = l_Lean_Int_mkInstDiv;
v___x_6201_ = l_Lean_Int_mkType;
v___x_6202_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6203_ = l_Lean_mkAppB(v___x_6202_, v___x_6201_, v___x_6200_);
return v___x_6203_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv(void){
_start:
{
lean_object* v___x_6204_; 
v___x_6204_ = lean_obj_once(&l_Lean_Int_mkInstHDiv___closed__0, &l_Lean_Int_mkInstHDiv___closed__0_once, _init_l_Lean_Int_mkInstHDiv___closed__0);
return v___x_6204_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod___closed__1(void){
_start:
{
lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; 
v___x_6208_ = lean_box(0);
v___x_6209_ = ((lean_object*)(l_Lean_Int_mkInstMod___closed__0));
v___x_6210_ = l_Lean_Expr_const___override(v___x_6209_, v___x_6208_);
return v___x_6210_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod(void){
_start:
{
lean_object* v___x_6211_; 
v___x_6211_ = lean_obj_once(&l_Lean_Int_mkInstMod___closed__1, &l_Lean_Int_mkInstMod___closed__1_once, _init_l_Lean_Int_mkInstMod___closed__1);
return v___x_6211_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod___closed__0(void){
_start:
{
lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; 
v___x_6212_ = l_Lean_Int_mkInstMod;
v___x_6213_ = l_Lean_Int_mkType;
v___x_6214_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6215_ = l_Lean_mkAppB(v___x_6214_, v___x_6213_, v___x_6212_);
return v___x_6215_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod(void){
_start:
{
lean_object* v___x_6216_; 
v___x_6216_ = lean_obj_once(&l_Lean_Int_mkInstHMod___closed__0, &l_Lean_Int_mkInstHMod___closed__0_once, _init_l_Lean_Int_mkInstHMod___closed__0);
return v___x_6216_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; 
v___x_6221_ = lean_box(0);
v___x_6222_ = ((lean_object*)(l_Lean_Int_mkInstPow___closed__1));
v___x_6223_ = l_Lean_Expr_const___override(v___x_6222_, v___x_6221_);
return v___x_6223_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow(void){
_start:
{
lean_object* v___x_6224_; 
v___x_6224_ = lean_obj_once(&l_Lean_Int_mkInstPow___closed__2, &l_Lean_Int_mkInstPow___closed__2_once, _init_l_Lean_Int_mkInstPow___closed__2);
return v___x_6224_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat___closed__0(void){
_start:
{
lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; 
v___x_6225_ = l_Lean_Int_mkInstPow;
v___x_6226_ = l_Lean_Int_mkType;
v___x_6227_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6228_ = l_Lean_mkAppB(v___x_6227_, v___x_6226_, v___x_6225_);
return v___x_6228_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat(void){
_start:
{
lean_object* v___x_6229_; 
v___x_6229_ = lean_obj_once(&l_Lean_Int_mkInstPowNat___closed__0, &l_Lean_Int_mkInstPowNat___closed__0_once, _init_l_Lean_Int_mkInstPowNat___closed__0);
return v___x_6229_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow___closed__0(void){
_start:
{
lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; 
v___x_6230_ = l_Lean_Int_mkInstPowNat;
v___x_6231_ = l_Lean_Nat_mkType;
v___x_6232_ = l_Lean_Int_mkType;
v___x_6233_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6234_ = l_Lean_mkApp3(v___x_6233_, v___x_6232_, v___x_6231_, v___x_6230_);
return v___x_6234_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow(void){
_start:
{
lean_object* v___x_6235_; 
v___x_6235_ = lean_obj_once(&l_Lean_Int_mkInstHPow___closed__0, &l_Lean_Int_mkInstHPow___closed__0_once, _init_l_Lean_Int_mkInstHPow___closed__0);
return v___x_6235_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6240_; lean_object* v___x_6241_; lean_object* v___x_6242_; 
v___x_6240_ = lean_box(0);
v___x_6241_ = ((lean_object*)(l_Lean_Int_mkInstLT___closed__1));
v___x_6242_ = l_Lean_Expr_const___override(v___x_6241_, v___x_6240_);
return v___x_6242_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT(void){
_start:
{
lean_object* v___x_6243_; 
v___x_6243_ = lean_obj_once(&l_Lean_Int_mkInstLT___closed__2, &l_Lean_Int_mkInstLT___closed__2_once, _init_l_Lean_Int_mkInstLT___closed__2);
return v___x_6243_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6248_; lean_object* v___x_6249_; lean_object* v___x_6250_; 
v___x_6248_ = lean_box(0);
v___x_6249_ = ((lean_object*)(l_Lean_Int_mkInstLE___closed__1));
v___x_6250_ = l_Lean_Expr_const___override(v___x_6249_, v___x_6248_);
return v___x_6250_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE(void){
_start:
{
lean_object* v___x_6251_; 
v___x_6251_ = lean_obj_once(&l_Lean_Int_mkInstLE___closed__2, &l_Lean_Int_mkInstLE___closed__2_once, _init_l_Lean_Int_mkInstLE___closed__2);
return v___x_6251_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast___closed__2(void){
_start:
{
lean_object* v___x_6255_; lean_object* v___x_6256_; lean_object* v___x_6257_; 
v___x_6255_ = lean_box(0);
v___x_6256_ = ((lean_object*)(l_Lean_Int_mkInstNatCast___closed__1));
v___x_6257_ = l_Lean_Expr_const___override(v___x_6256_, v___x_6255_);
return v___x_6257_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast(void){
_start:
{
lean_object* v___x_6258_; 
v___x_6258_ = lean_obj_once(&l_Lean_Int_mkInstNatCast___closed__2, &l_Lean_Int_mkInstNatCast___closed__2_once, _init_l_Lean_Int_mkInstNatCast___closed__2);
return v___x_6258_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0(void){
_start:
{
lean_object* v___x_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; 
v___x_6259_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6260_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_6261_ = l_Lean_Expr_const___override(v___x_6260_, v___x_6259_);
return v___x_6261_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1(void){
_start:
{
lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; 
v___x_6262_ = l_Lean_Int_mkInstNeg;
v___x_6263_ = l_Lean_Int_mkType;
v___x_6264_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__0, &l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0);
v___x_6265_ = l_Lean_mkAppB(v___x_6264_, v___x_6263_, v___x_6262_);
return v___x_6265_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn(void){
_start:
{
lean_object* v___x_6266_; 
v___x_6266_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__1, &l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1);
return v___x_6266_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0(void){
_start:
{
lean_object* v___x_6267_; lean_object* v___x_6268_; lean_object* v___x_6269_; lean_object* v___x_6270_; 
v___x_6267_ = l_Lean_Int_mkInstHAdd;
v___x_6268_ = l_Lean_Int_mkType;
v___x_6269_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6270_ = l_Lean_mkApp4(v___x_6269_, v___x_6268_, v___x_6268_, v___x_6268_, v___x_6267_);
return v___x_6270_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn(void){
_start:
{
lean_object* v___x_6271_; 
v___x_6271_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intAddFn___closed__0, &l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0);
return v___x_6271_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0(void){
_start:
{
lean_object* v___x_6272_; lean_object* v___x_6273_; lean_object* v___x_6274_; lean_object* v___x_6275_; 
v___x_6272_ = l_Lean_Int_mkInstHSub;
v___x_6273_ = l_Lean_Int_mkType;
v___x_6274_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6275_ = l_Lean_mkApp4(v___x_6274_, v___x_6273_, v___x_6273_, v___x_6273_, v___x_6272_);
return v___x_6275_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn(void){
_start:
{
lean_object* v___x_6276_; 
v___x_6276_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intSubFn___closed__0, &l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0);
return v___x_6276_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0(void){
_start:
{
lean_object* v___x_6277_; lean_object* v___x_6278_; lean_object* v___x_6279_; lean_object* v___x_6280_; 
v___x_6277_ = l_Lean_Int_mkInstHMul;
v___x_6278_ = l_Lean_Int_mkType;
v___x_6279_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6280_ = l_Lean_mkApp4(v___x_6279_, v___x_6278_, v___x_6278_, v___x_6278_, v___x_6277_);
return v___x_6280_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn(void){
_start:
{
lean_object* v___x_6281_; 
v___x_6281_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intMulFn___closed__0, &l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0);
return v___x_6281_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3(void){
_start:
{
lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; 
v___x_6287_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6288_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intDivFn___closed__2));
v___x_6289_ = l_Lean_Expr_const___override(v___x_6288_, v___x_6287_);
return v___x_6289_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4(void){
_start:
{
lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v___x_6293_; 
v___x_6290_ = l_Lean_Int_mkInstHDiv;
v___x_6291_ = l_Lean_Int_mkType;
v___x_6292_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__3, &l___private_Lean_Expr_0__Lean_intDivFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3);
v___x_6293_ = l_Lean_mkApp4(v___x_6292_, v___x_6291_, v___x_6291_, v___x_6291_, v___x_6290_);
return v___x_6293_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn(void){
_start:
{
lean_object* v___x_6294_; 
v___x_6294_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__4, &l___private_Lean_Expr_0__Lean_intDivFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4);
return v___x_6294_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3(void){
_start:
{
lean_object* v___x_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; 
v___x_6300_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6301_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intModFn___closed__2));
v___x_6302_ = l_Lean_Expr_const___override(v___x_6301_, v___x_6300_);
return v___x_6302_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4(void){
_start:
{
lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; 
v___x_6303_ = l_Lean_Int_mkInstHMod;
v___x_6304_ = l_Lean_Int_mkType;
v___x_6305_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__3, &l___private_Lean_Expr_0__Lean_intModFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3);
v___x_6306_ = l_Lean_mkApp4(v___x_6305_, v___x_6304_, v___x_6304_, v___x_6304_, v___x_6303_);
return v___x_6306_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn(void){
_start:
{
lean_object* v___x_6307_; 
v___x_6307_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__4, &l___private_Lean_Expr_0__Lean_intModFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4);
return v___x_6307_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0(void){
_start:
{
lean_object* v___x_6308_; lean_object* v___x_6309_; lean_object* v___x_6310_; lean_object* v___x_6311_; lean_object* v___x_6312_; 
v___x_6308_ = l_Lean_Int_mkInstHPow;
v___x_6309_ = l_Lean_Nat_mkType;
v___x_6310_ = l_Lean_Int_mkType;
v___x_6311_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6312_ = l_Lean_mkApp4(v___x_6311_, v___x_6310_, v___x_6309_, v___x_6310_, v___x_6308_);
return v___x_6312_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn(void){
_start:
{
lean_object* v___x_6313_; 
v___x_6313_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0, &l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0);
return v___x_6313_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3(void){
_start:
{
lean_object* v___x_6319_; lean_object* v___x_6320_; lean_object* v___x_6321_; 
v___x_6319_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6320_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2));
v___x_6321_ = l_Lean_Expr_const___override(v___x_6320_, v___x_6319_);
return v___x_6321_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4(void){
_start:
{
lean_object* v___x_6322_; lean_object* v___x_6323_; lean_object* v___x_6324_; lean_object* v___x_6325_; 
v___x_6322_ = l_Lean_Int_mkInstNatCast;
v___x_6323_ = l_Lean_Int_mkType;
v___x_6324_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3);
v___x_6325_ = l_Lean_mkAppB(v___x_6324_, v___x_6323_, v___x_6322_);
return v___x_6325_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn(void){
_start:
{
lean_object* v___x_6326_; 
v___x_6326_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4);
return v___x_6326_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* v_a_6327_){
_start:
{
lean_object* v___x_6328_; lean_object* v___x_6329_; 
v___x_6328_ = l___private_Lean_Expr_0__Lean_intNegFn;
v___x_6329_ = l_Lean_Expr_app___override(v___x_6328_, v_a_6327_);
return v___x_6329_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* v_a_6330_, lean_object* v_b_6331_){
_start:
{
lean_object* v___x_6332_; lean_object* v___x_6333_; 
v___x_6332_ = l___private_Lean_Expr_0__Lean_intAddFn;
v___x_6333_ = l_Lean_mkAppB(v___x_6332_, v_a_6330_, v_b_6331_);
return v___x_6333_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* v_a_6334_, lean_object* v_b_6335_){
_start:
{
lean_object* v___x_6336_; lean_object* v___x_6337_; 
v___x_6336_ = l___private_Lean_Expr_0__Lean_intSubFn;
v___x_6337_ = l_Lean_mkAppB(v___x_6336_, v_a_6334_, v_b_6335_);
return v___x_6337_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* v_a_6338_, lean_object* v_b_6339_){
_start:
{
lean_object* v___x_6340_; lean_object* v___x_6341_; 
v___x_6340_ = l___private_Lean_Expr_0__Lean_intMulFn;
v___x_6341_ = l_Lean_mkAppB(v___x_6340_, v_a_6338_, v_b_6339_);
return v___x_6341_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* v_a_6342_, lean_object* v_b_6343_){
_start:
{
lean_object* v___x_6344_; lean_object* v___x_6345_; 
v___x_6344_ = l___private_Lean_Expr_0__Lean_intDivFn;
v___x_6345_ = l_Lean_mkAppB(v___x_6344_, v_a_6342_, v_b_6343_);
return v___x_6345_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* v_a_6346_, lean_object* v_b_6347_){
_start:
{
lean_object* v___x_6348_; lean_object* v___x_6349_; 
v___x_6348_ = l___private_Lean_Expr_0__Lean_intModFn;
v___x_6349_ = l_Lean_mkAppB(v___x_6348_, v_a_6346_, v_b_6347_);
return v___x_6349_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* v_a_6350_){
_start:
{
lean_object* v___x_6351_; lean_object* v___x_6352_; 
v___x_6351_ = l___private_Lean_Expr_0__Lean_intNatCastFn;
v___x_6352_ = l_Lean_Expr_app___override(v___x_6351_, v_a_6350_);
return v___x_6352_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object* v_a_6353_, lean_object* v_b_6354_){
_start:
{
lean_object* v___x_6355_; lean_object* v___x_6356_; 
v___x_6355_ = l___private_Lean_Expr_0__Lean_intPowNatFn;
v___x_6356_ = l_Lean_mkAppB(v___x_6355_, v_a_6353_, v_b_6354_);
return v___x_6356_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0(void){
_start:
{
lean_object* v___x_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; lean_object* v___x_6360_; 
v___x_6357_ = l_Lean_Int_mkInstLE;
v___x_6358_ = l_Lean_Int_mkType;
v___x_6359_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6360_ = l_Lean_mkAppB(v___x_6359_, v___x_6358_, v___x_6357_);
return v___x_6360_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred(void){
_start:
{
lean_object* v___x_6361_; 
v___x_6361_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLEPred___closed__0, &l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0);
return v___x_6361_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* v_a_6362_, lean_object* v_b_6363_){
_start:
{
lean_object* v___x_6364_; lean_object* v___x_6365_; 
v___x_6364_ = l___private_Lean_Expr_0__Lean_intLEPred;
v___x_6365_ = l_Lean_mkAppB(v___x_6364_, v_a_6362_, v_b_6363_);
return v___x_6365_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3(void){
_start:
{
lean_object* v___x_6371_; lean_object* v___x_6372_; lean_object* v___x_6373_; 
v___x_6371_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6372_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intLTPred___closed__2));
v___x_6373_ = l_Lean_Expr_const___override(v___x_6372_, v___x_6371_);
return v___x_6373_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4(void){
_start:
{
lean_object* v___x_6374_; lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v___x_6377_; 
v___x_6374_ = l_Lean_Int_mkInstLT;
v___x_6375_ = l_Lean_Int_mkType;
v___x_6376_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__3, &l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3);
v___x_6377_ = l_Lean_mkAppB(v___x_6376_, v___x_6375_, v___x_6374_);
return v___x_6377_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred(void){
_start:
{
lean_object* v___x_6378_; 
v___x_6378_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__4, &l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4);
return v___x_6378_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object* v_a_6379_, lean_object* v_b_6380_){
_start:
{
lean_object* v___x_6381_; lean_object* v___x_6382_; 
v___x_6381_ = l___private_Lean_Expr_0__Lean_intLTPred;
v___x_6382_ = l_Lean_mkAppB(v___x_6381_, v_a_6379_, v_b_6380_);
return v___x_6382_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0(void){
_start:
{
lean_object* v___x_6383_; lean_object* v___x_6384_; lean_object* v___x_6385_; 
v___x_6383_ = l_Lean_Int_mkType;
v___x_6384_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6385_ = l_Lean_Expr_app___override(v___x_6384_, v___x_6383_);
return v___x_6385_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred(void){
_start:
{
lean_object* v___x_6386_; 
v___x_6386_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intEqPred___closed__0, &l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0);
return v___x_6386_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* v_a_6387_, lean_object* v_b_6388_){
_start:
{
lean_object* v___x_6389_; lean_object* v___x_6390_; 
v___x_6389_ = l___private_Lean_Expr_0__Lean_intEqPred;
v___x_6390_ = l_Lean_mkAppB(v___x_6389_, v_a_6387_, v_b_6388_);
return v___x_6390_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__3(void){
_start:
{
lean_object* v___x_6396_; lean_object* v___x_6397_; lean_object* v___x_6398_; 
v___x_6396_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6397_ = ((lean_object*)(l_Lean_mkIntDvd___closed__2));
v___x_6398_ = l_Lean_Expr_const___override(v___x_6397_, v___x_6396_);
return v___x_6398_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__6(void){
_start:
{
lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; 
v___x_6403_ = lean_box(0);
v___x_6404_ = ((lean_object*)(l_Lean_mkIntDvd___closed__5));
v___x_6405_ = l_Lean_Expr_const___override(v___x_6404_, v___x_6403_);
return v___x_6405_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* v_a_6406_, lean_object* v_b_6407_){
_start:
{
lean_object* v___x_6408_; lean_object* v___x_6409_; lean_object* v___x_6410_; lean_object* v___x_6411_; 
v___x_6408_ = lean_obj_once(&l_Lean_mkIntDvd___closed__3, &l_Lean_mkIntDvd___closed__3_once, _init_l_Lean_mkIntDvd___closed__3);
v___x_6409_ = l_Lean_Int_mkType;
v___x_6410_ = lean_obj_once(&l_Lean_mkIntDvd___closed__6, &l_Lean_mkIntDvd___closed__6_once, _init_l_Lean_mkIntDvd___closed__6);
v___x_6411_ = l_Lean_mkApp4(v___x_6408_, v___x_6409_, v___x_6410_, v_a_6406_, v_b_6407_);
return v___x_6411_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__2(void){
_start:
{
lean_object* v___x_6415_; lean_object* v___x_6416_; lean_object* v___x_6417_; 
v___x_6415_ = lean_box(0);
v___x_6416_ = ((lean_object*)(l_Lean_mkIntLit___closed__1));
v___x_6417_ = l_Lean_Expr_const___override(v___x_6416_, v___x_6415_);
return v___x_6417_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__3(void){
_start:
{
lean_object* v___x_6418_; lean_object* v___x_6419_; 
v___x_6418_ = lean_unsigned_to_nat(0u);
v___x_6419_ = lean_nat_to_int(v___x_6418_);
return v___x_6419_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* v_n_6420_){
_start:
{
lean_object* v___x_6421_; lean_object* v_r_6422_; lean_object* v___x_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; lean_object* v_r_6427_; lean_object* v___x_6428_; uint8_t v___x_6429_; 
v___x_6421_ = lean_nat_abs(v_n_6420_);
v_r_6422_ = l_Lean_mkRawNatLit(v___x_6421_);
v___x_6423_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_6424_ = l_Lean_Int_mkType;
v___x_6425_ = lean_obj_once(&l_Lean_mkIntLit___closed__2, &l_Lean_mkIntLit___closed__2_once, _init_l_Lean_mkIntLit___closed__2);
lean_inc_ref(v_r_6422_);
v___x_6426_ = l_Lean_Expr_app___override(v___x_6425_, v_r_6422_);
v_r_6427_ = l_Lean_mkApp3(v___x_6423_, v___x_6424_, v_r_6422_, v___x_6426_);
v___x_6428_ = lean_obj_once(&l_Lean_mkIntLit___closed__3, &l_Lean_mkIntLit___closed__3_once, _init_l_Lean_mkIntLit___closed__3);
v___x_6429_ = lean_int_dec_lt(v_n_6420_, v___x_6428_);
if (v___x_6429_ == 0)
{
return v_r_6427_;
}
else
{
lean_object* v___x_6430_; 
v___x_6430_ = l_Lean_mkIntNeg(v_r_6427_);
return v___x_6430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* v_n_6431_){
_start:
{
lean_object* v_res_6432_; 
v_res_6432_ = l_Lean_mkIntLit(v_n_6431_);
lean_dec(v_n_6431_);
return v_res_6432_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6437_; lean_object* v___x_6438_; 
v___x_6437_ = lean_box(0);
v___x_6438_ = l_Lean_Level_succ___override(v___x_6437_);
return v___x_6438_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6439_; lean_object* v___x_6440_; lean_object* v___x_6441_; 
v___x_6439_ = lean_box(0);
v___x_6440_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__2, &l_Lean_reflBoolTrue___closed__2_once, _init_l_Lean_reflBoolTrue___closed__2);
v___x_6441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6441_, 0, v___x_6440_);
lean_ctor_set(v___x_6441_, 1, v___x_6439_);
return v___x_6441_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6442_; lean_object* v___x_6443_; lean_object* v___x_6444_; 
v___x_6442_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__3, &l_Lean_reflBoolTrue___closed__3_once, _init_l_Lean_reflBoolTrue___closed__3);
v___x_6443_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__1));
v___x_6444_ = l_Lean_Expr_const___override(v___x_6443_, v___x_6442_);
return v___x_6444_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__6(void){
_start:
{
lean_object* v___x_6447_; lean_object* v___x_6448_; lean_object* v___x_6449_; 
v___x_6447_ = lean_box(0);
v___x_6448_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__5));
v___x_6449_ = l_Lean_Expr_const___override(v___x_6448_, v___x_6447_);
return v___x_6449_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__7(void){
_start:
{
lean_object* v___x_6450_; lean_object* v___x_6451_; lean_object* v___x_6452_; 
v___x_6450_ = lean_box(0);
v___x_6451_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_6452_ = l_Lean_Expr_const___override(v___x_6451_, v___x_6450_);
return v___x_6452_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__8(void){
_start:
{
lean_object* v___x_6453_; lean_object* v___x_6454_; lean_object* v___x_6455_; lean_object* v___x_6456_; 
v___x_6453_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6454_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6455_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6456_ = l_Lean_mkAppB(v___x_6455_, v___x_6454_, v___x_6453_);
return v___x_6456_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue(void){
_start:
{
lean_object* v___x_6457_; 
v___x_6457_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__8, &l_Lean_reflBoolTrue___closed__8_once, _init_l_Lean_reflBoolTrue___closed__8);
return v___x_6457_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6458_; lean_object* v___x_6459_; lean_object* v___x_6460_; 
v___x_6458_ = lean_box(0);
v___x_6459_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_6460_ = l_Lean_Expr_const___override(v___x_6459_, v___x_6458_);
return v___x_6460_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; lean_object* v___x_6464_; 
v___x_6461_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6462_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6463_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6464_ = l_Lean_mkAppB(v___x_6463_, v___x_6462_, v___x_6461_);
return v___x_6464_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse(void){
_start:
{
lean_object* v___x_6465_; 
v___x_6465_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
return v___x_6465_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6469_; lean_object* v___x_6470_; lean_object* v___x_6471_; 
v___x_6469_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6470_ = ((lean_object*)(l_Lean_eagerReflBoolTrue___closed__1));
v___x_6471_ = l_Lean_Expr_const___override(v___x_6470_, v___x_6469_);
return v___x_6471_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; lean_object* v___x_6475_; 
v___x_6472_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6473_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6474_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6475_ = l_Lean_mkApp3(v___x_6474_, v___x_6473_, v___x_6472_, v___x_6472_);
return v___x_6475_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; 
v___x_6476_ = l_Lean_reflBoolTrue;
v___x_6477_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__3, &l_Lean_eagerReflBoolTrue___closed__3_once, _init_l_Lean_eagerReflBoolTrue___closed__3);
v___x_6478_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6479_ = l_Lean_mkAppB(v___x_6478_, v___x_6477_, v___x_6476_);
return v___x_6479_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue(void){
_start:
{
lean_object* v___x_6480_; 
v___x_6480_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__4, &l_Lean_eagerReflBoolTrue___closed__4_once, _init_l_Lean_eagerReflBoolTrue___closed__4);
return v___x_6480_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; 
v___x_6481_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6482_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6483_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6484_ = l_Lean_mkApp3(v___x_6483_, v___x_6482_, v___x_6481_, v___x_6481_);
return v___x_6484_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; 
v___x_6485_ = l_Lean_reflBoolFalse;
v___x_6486_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__0, &l_Lean_eagerReflBoolFalse___closed__0_once, _init_l_Lean_eagerReflBoolFalse___closed__0);
v___x_6487_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6488_ = l_Lean_mkAppB(v___x_6487_, v___x_6486_, v___x_6485_);
return v___x_6488_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse(void){
_start:
{
lean_object* v___x_6489_; 
v___x_6489_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__1, &l_Lean_eagerReflBoolFalse___closed__1_once, _init_l_Lean_eagerReflBoolFalse___closed__1);
return v___x_6489_;
}
}
static lean_object* _init_l_Lean_Expr_replaceFn___closed__2(void){
_start:
{
lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; lean_object* v___x_6496_; lean_object* v___x_6497_; 
v___x_6492_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__1));
v___x_6493_ = lean_unsigned_to_nat(9u);
v___x_6494_ = lean_unsigned_to_nat(2441u);
v___x_6495_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__0));
v___x_6496_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_6497_ = l_mkPanicMessageWithDecl(v___x_6496_, v___x_6495_, v___x_6494_, v___x_6493_, v___x_6492_);
return v___x_6497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object* v_e_6498_, lean_object* v_declName_6499_){
_start:
{
switch(lean_obj_tag(v_e_6498_))
{
case 5:
{
lean_object* v_fn_6500_; lean_object* v_arg_6501_; lean_object* v___x_6502_; lean_object* v___x_6503_; 
v_fn_6500_ = lean_ctor_get(v_e_6498_, 0);
lean_inc_ref(v_fn_6500_);
v_arg_6501_ = lean_ctor_get(v_e_6498_, 1);
lean_inc_ref(v_arg_6501_);
lean_dec_ref_known(v_e_6498_, 2);
v___x_6502_ = l_Lean_Expr_replaceFn(v_fn_6500_, v_declName_6499_);
v___x_6503_ = l_Lean_Expr_app___override(v___x_6502_, v_arg_6501_);
return v___x_6503_;
}
case 4:
{
lean_object* v_us_6504_; lean_object* v___x_6505_; 
v_us_6504_ = lean_ctor_get(v_e_6498_, 1);
lean_inc(v_us_6504_);
lean_dec_ref_known(v_e_6498_, 2);
v___x_6505_ = l_Lean_Expr_const___override(v_declName_6499_, v_us_6504_);
return v___x_6505_;
}
default: 
{
lean_object* v___x_6506_; lean_object* v___x_6507_; 
lean_dec(v_declName_6499_);
lean_dec_ref(v_e_6498_);
v___x_6506_ = lean_obj_once(&l_Lean_Expr_replaceFn___closed__2, &l_Lean_Expr_replaceFn___closed__2_once, _init_l_Lean_Expr_replaceFn___closed__2);
v___x_6507_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_6506_);
return v___x_6507_;
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
