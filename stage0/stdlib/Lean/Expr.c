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
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx(uint8_t v_x_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_BinderInfo_ctorIdx(v_x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx___boxed(lean_object* v_x_167_){
_start:
{
uint8_t v_x_4__boxed_168_; lean_object* v_res_169_; 
v_x_4__boxed_168_ = lean_unbox(v_x_167_);
v_res_169_ = l_Lean_BinderInfo_toCtorIdx(v_x_4__boxed_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg(lean_object* v_k_170_){
_start:
{
lean_inc(v_k_170_);
return v_k_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg___boxed(lean_object* v_k_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_BinderInfo_ctorElim___redArg(v_k_171_);
lean_dec(v_k_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim(lean_object* v_motive_173_, lean_object* v_ctorIdx_174_, uint8_t v_t_175_, lean_object* v_h_176_, lean_object* v_k_177_){
_start:
{
lean_inc(v_k_177_);
return v_k_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___boxed(lean_object* v_motive_178_, lean_object* v_ctorIdx_179_, lean_object* v_t_180_, lean_object* v_h_181_, lean_object* v_k_182_){
_start:
{
uint8_t v_t_boxed_183_; lean_object* v_res_184_; 
v_t_boxed_183_ = lean_unbox(v_t_180_);
v_res_184_ = l_Lean_BinderInfo_ctorElim(v_motive_178_, v_ctorIdx_179_, v_t_boxed_183_, v_h_181_, v_k_182_);
lean_dec(v_k_182_);
lean_dec(v_ctorIdx_179_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg(lean_object* v_default_185_){
_start:
{
lean_inc(v_default_185_);
return v_default_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg___boxed(lean_object* v_default_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_BinderInfo_default_elim___redArg(v_default_186_);
lean_dec(v_default_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim(lean_object* v_motive_188_, uint8_t v_t_189_, lean_object* v_h_190_, lean_object* v_default_191_){
_start:
{
lean_inc(v_default_191_);
return v_default_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___boxed(lean_object* v_motive_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_default_195_){
_start:
{
uint8_t v_t_boxed_196_; lean_object* v_res_197_; 
v_t_boxed_196_ = lean_unbox(v_t_193_);
v_res_197_ = l_Lean_BinderInfo_default_elim(v_motive_192_, v_t_boxed_196_, v_h_194_, v_default_195_);
lean_dec(v_default_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg(lean_object* v_implicit_198_){
_start:
{
lean_inc(v_implicit_198_);
return v_implicit_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg___boxed(lean_object* v_implicit_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_BinderInfo_implicit_elim___redArg(v_implicit_199_);
lean_dec(v_implicit_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim(lean_object* v_motive_201_, uint8_t v_t_202_, lean_object* v_h_203_, lean_object* v_implicit_204_){
_start:
{
lean_inc(v_implicit_204_);
return v_implicit_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___boxed(lean_object* v_motive_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_implicit_208_){
_start:
{
uint8_t v_t_boxed_209_; lean_object* v_res_210_; 
v_t_boxed_209_ = lean_unbox(v_t_206_);
v_res_210_ = l_Lean_BinderInfo_implicit_elim(v_motive_205_, v_t_boxed_209_, v_h_207_, v_implicit_208_);
lean_dec(v_implicit_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___redArg(lean_object* v_strictImplicit_211_){
_start:
{
lean_inc(v_strictImplicit_211_);
return v_strictImplicit_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___redArg___boxed(lean_object* v_strictImplicit_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_BinderInfo_strictImplicit_elim___redArg(v_strictImplicit_212_);
lean_dec(v_strictImplicit_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim(lean_object* v_motive_214_, uint8_t v_t_215_, lean_object* v_h_216_, lean_object* v_strictImplicit_217_){
_start:
{
lean_inc(v_strictImplicit_217_);
return v_strictImplicit_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___boxed(lean_object* v_motive_218_, lean_object* v_t_219_, lean_object* v_h_220_, lean_object* v_strictImplicit_221_){
_start:
{
uint8_t v_t_boxed_222_; lean_object* v_res_223_; 
v_t_boxed_222_ = lean_unbox(v_t_219_);
v_res_223_ = l_Lean_BinderInfo_strictImplicit_elim(v_motive_218_, v_t_boxed_222_, v_h_220_, v_strictImplicit_221_);
lean_dec(v_strictImplicit_221_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg(lean_object* v_instImplicit_224_){
_start:
{
lean_inc(v_instImplicit_224_);
return v_instImplicit_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg___boxed(lean_object* v_instImplicit_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_BinderInfo_instImplicit_elim___redArg(v_instImplicit_225_);
lean_dec(v_instImplicit_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim(lean_object* v_motive_227_, uint8_t v_t_228_, lean_object* v_h_229_, lean_object* v_instImplicit_230_){
_start:
{
lean_inc(v_instImplicit_230_);
return v_instImplicit_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___boxed(lean_object* v_motive_231_, lean_object* v_t_232_, lean_object* v_h_233_, lean_object* v_instImplicit_234_){
_start:
{
uint8_t v_t_boxed_235_; lean_object* v_res_236_; 
v_t_boxed_235_ = lean_unbox(v_t_232_);
v_res_236_ = l_Lean_BinderInfo_instImplicit_elim(v_motive_231_, v_t_boxed_235_, v_h_233_, v_instImplicit_234_);
lean_dec(v_instImplicit_234_);
return v_res_236_;
}
}
static uint8_t _init_l_Lean_instInhabitedBinderInfo_default(void){
_start:
{
uint8_t v___x_237_; 
v___x_237_ = 0;
return v___x_237_;
}
}
static uint8_t _init_l_Lean_instInhabitedBinderInfo(void){
_start:
{
uint8_t v___x_238_; 
v___x_238_ = 0;
return v___x_238_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t v_x_239_, uint8_t v_y_240_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_241_ = l_Lean_BinderInfo_ctorIdx(v_x_239_);
v___x_242_ = l_Lean_BinderInfo_ctorIdx(v_y_240_);
v___x_243_ = lean_nat_dec_eq(v___x_241_, v___x_242_);
lean_dec(v___x_242_);
lean_dec(v___x_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqBinderInfo_beq___boxed(lean_object* v_x_244_, lean_object* v_y_245_){
_start:
{
uint8_t v_x_17__boxed_246_; uint8_t v_y_18__boxed_247_; uint8_t v_res_248_; lean_object* v_r_249_; 
v_x_17__boxed_246_ = lean_unbox(v_x_244_);
v_y_18__boxed_247_ = lean_unbox(v_y_245_);
v_res_248_ = l_Lean_instBEqBinderInfo_beq(v_x_17__boxed_246_, v_y_18__boxed_247_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr(uint8_t v_x_264_, lean_object* v_prec_265_){
_start:
{
lean_object* v___y_267_; lean_object* v___y_274_; lean_object* v___y_281_; lean_object* v___y_288_; 
switch(v_x_264_)
{
case 0:
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(1024u);
v___x_295_ = lean_nat_dec_le(v___x_294_, v_prec_265_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_267_ = v___x_296_;
goto v___jp_266_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_267_ = v___x_297_;
goto v___jp_266_;
}
}
case 1:
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(1024u);
v___x_299_ = lean_nat_dec_le(v___x_298_, v_prec_265_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
v___x_300_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_274_ = v___x_300_;
goto v___jp_273_;
}
else
{
lean_object* v___x_301_; 
v___x_301_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_274_ = v___x_301_;
goto v___jp_273_;
}
}
case 2:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(1024u);
v___x_303_ = lean_nat_dec_le(v___x_302_, v_prec_265_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
v___x_304_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_281_ = v___x_304_;
goto v___jp_280_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_281_ = v___x_305_;
goto v___jp_280_;
}
}
default: 
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = lean_unsigned_to_nat(1024u);
v___x_307_ = lean_nat_dec_le(v___x_306_, v_prec_265_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
v___x_308_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_288_ = v___x_308_;
goto v___jp_287_;
}
else
{
lean_object* v___x_309_; 
v___x_309_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_288_ = v___x_309_;
goto v___jp_287_;
}
}
}
v___jp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_268_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__1));
lean_inc(v___y_267_);
v___x_269_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_269_, 0, v___y_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = 0;
v___x_271_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*1, v___x_270_);
v___x_272_ = l_Repr_addAppParen(v___x_271_, v_prec_265_);
return v___x_272_;
}
v___jp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_275_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__3));
lean_inc(v___y_274_);
v___x_276_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_276_, 0, v___y_274_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = 0;
v___x_278_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set_uint8(v___x_278_, sizeof(void*)*1, v___x_277_);
v___x_279_ = l_Repr_addAppParen(v___x_278_, v_prec_265_);
return v___x_279_;
}
v___jp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_282_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__5));
lean_inc(v___y_281_);
v___x_283_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_283_, 0, v___y_281_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = 0;
v___x_285_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*1, v___x_284_);
v___x_286_ = l_Repr_addAppParen(v___x_285_, v_prec_265_);
return v___x_286_;
}
v___jp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_289_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__7));
lean_inc(v___y_288_);
v___x_290_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_290_, 0, v___y_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = 0;
v___x_292_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*1, v___x_291_);
v___x_293_ = l_Repr_addAppParen(v___x_292_, v_prec_265_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr___boxed(lean_object* v_x_310_, lean_object* v_prec_311_){
_start:
{
uint8_t v_x_229__boxed_312_; lean_object* v_res_313_; 
v_x_229__boxed_312_ = lean_unbox(v_x_310_);
v_res_313_ = l_Lean_instReprBinderInfo_repr(v_x_229__boxed_312_, v_prec_311_);
lean_dec(v_prec_311_);
return v_res_313_;
}
}
LEAN_EXPORT uint64_t l_Lean_BinderInfo_hash(uint8_t v_x_316_){
_start:
{
switch(v_x_316_)
{
case 0:
{
uint64_t v___x_317_; 
v___x_317_ = 947ULL;
return v___x_317_;
}
case 1:
{
uint64_t v___x_318_; 
v___x_318_ = 1019ULL;
return v___x_318_;
}
case 2:
{
uint64_t v___x_319_; 
v___x_319_ = 1087ULL;
return v___x_319_;
}
default: 
{
uint64_t v___x_320_; 
v___x_320_ = 1153ULL;
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_hash___boxed(lean_object* v_x_321_){
_start:
{
uint8_t v_x_52__boxed_322_; uint64_t v_res_323_; lean_object* v_r_324_; 
v_x_52__boxed_322_ = lean_unbox(v_x_321_);
v_res_323_ = l_Lean_BinderInfo_hash(v_x_52__boxed_322_);
v_r_324_ = lean_box_uint64(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isExplicit(uint8_t v_x_325_){
_start:
{
switch(v_x_325_)
{
case 1:
{
uint8_t v___x_326_; 
v___x_326_ = 0;
return v___x_326_;
}
case 2:
{
uint8_t v___x_327_; 
v___x_327_ = 0;
return v___x_327_;
}
case 3:
{
uint8_t v___x_328_; 
v___x_328_ = 0;
return v___x_328_;
}
default: 
{
uint8_t v___x_329_; 
v___x_329_ = 1;
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object* v_x_330_){
_start:
{
uint8_t v_x_31__boxed_331_; uint8_t v_res_332_; lean_object* v_r_333_; 
v_x_31__boxed_331_ = lean_unbox(v_x_330_);
v_res_332_ = l_Lean_BinderInfo_isExplicit(v_x_31__boxed_331_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t v_x_336_){
_start:
{
if (v_x_336_ == 3)
{
uint8_t v___x_337_; 
v___x_337_ = 1;
return v___x_337_;
}
else
{
uint8_t v___x_338_; 
v___x_338_ = 0;
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object* v_x_339_){
_start:
{
uint8_t v_x_21__boxed_340_; uint8_t v_res_341_; lean_object* v_r_342_; 
v_x_21__boxed_340_ = lean_unbox(v_x_339_);
v_res_341_ = l_Lean_BinderInfo_isInstImplicit(v_x_21__boxed_340_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isImplicit(uint8_t v_x_343_){
_start:
{
if (v_x_343_ == 1)
{
uint8_t v___x_344_; 
v___x_344_ = 1;
return v___x_344_;
}
else
{
uint8_t v___x_345_; 
v___x_345_ = 0;
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isImplicit___boxed(lean_object* v_x_346_){
_start:
{
uint8_t v_x_21__boxed_347_; uint8_t v_res_348_; lean_object* v_r_349_; 
v_x_21__boxed_347_ = lean_unbox(v_x_346_);
v_res_348_ = l_Lean_BinderInfo_isImplicit(v_x_21__boxed_347_);
v_r_349_ = lean_box(v_res_348_);
return v_r_349_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isStrictImplicit(uint8_t v_x_350_){
_start:
{
if (v_x_350_ == 2)
{
uint8_t v___x_351_; 
v___x_351_ = 1;
return v___x_351_;
}
else
{
uint8_t v___x_352_; 
v___x_352_ = 0;
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isStrictImplicit___boxed(lean_object* v_x_353_){
_start:
{
uint8_t v_x_21__boxed_354_; uint8_t v_res_355_; lean_object* v_r_356_; 
v_x_21__boxed_354_ = lean_unbox(v_x_353_);
v_res_355_ = l_Lean_BinderInfo_isStrictImplicit(v_x_21__boxed_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
static lean_object* _init_l_Lean_MData_empty(void){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lean_box(0);
return v___x_357_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1___aux__1___closed__0(void){
_start:
{
lean_object* v___x_358_; uint64_t v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_uint64_of_nat(v___x_358_);
return v___x_359_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1___aux__1(void){
_start:
{
uint64_t v___x_360_; 
v___x_360_ = lean_uint64_once(&l_Lean_instInhabitedData__1___aux__1___closed__0, &l_Lean_instInhabitedData__1___aux__1___closed__0_once, _init_l_Lean_instInhabitedData__1___aux__1___closed__0);
return v___x_360_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1(void){
_start:
{
uint64_t v___x_361_; 
v___x_361_ = lean_uint64_once(&l_Lean_instInhabitedData__1___aux__1___closed__0, &l_Lean_instInhabitedData__1___aux__1___closed__0_once, _init_l_Lean_instInhabitedData__1___aux__1___closed__0);
return v___x_361_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_Data_hash(uint64_t v_c_362_){
_start:
{
uint32_t v___x_363_; uint64_t v___x_364_; 
v___x_363_ = lean_uint64_to_uint32(v_c_362_);
v___x_364_ = lean_uint32_to_uint64(v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object* v_c_365_){
_start:
{
uint64_t v_c_boxed_366_; uint64_t v_res_367_; lean_object* v_r_368_; 
v_c_boxed_366_ = lean_unbox_uint64(v_c_365_);
lean_dec_ref(v_c_365_);
v_res_367_ = l_Lean_Expr_Data_hash(v_c_boxed_366_);
v_r_368_ = lean_box_uint64(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t v_c_371_){
_start:
{
uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v___x_374_; uint64_t v___x_375_; uint8_t v___x_376_; 
v___x_372_ = 32ULL;
v___x_373_ = lean_uint64_shift_right(v_c_371_, v___x_372_);
v___x_374_ = 255ULL;
v___x_375_ = lean_uint64_land(v___x_373_, v___x_374_);
v___x_376_ = lean_uint64_to_uint8(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object* v_c_377_){
_start:
{
uint64_t v_c_boxed_378_; uint8_t v_res_379_; lean_object* v_r_380_; 
v_c_boxed_378_ = lean_unbox_uint64(v_c_377_);
lean_dec_ref(v_c_377_);
v_res_379_ = l_Lean_Expr_Data_approxDepth(v_c_boxed_378_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t v_c_381_){
_start:
{
uint64_t v___x_382_; uint64_t v___x_383_; uint32_t v___x_384_; 
v___x_382_ = 44ULL;
v___x_383_ = lean_uint64_shift_right(v_c_381_, v___x_382_);
v___x_384_ = lean_uint64_to_uint32(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object* v_c_385_){
_start:
{
uint64_t v_c_boxed_386_; uint32_t v_res_387_; lean_object* v_r_388_; 
v_c_boxed_386_ = lean_unbox_uint64(v_c_385_);
lean_dec_ref(v_c_385_);
v_res_387_ = l_Lean_Expr_Data_looseBVarRange(v_c_boxed_386_);
v_r_388_ = lean_box_uint32(v_res_387_);
return v_r_388_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t v_c_389_){
_start:
{
uint64_t v___x_390_; uint64_t v___x_391_; uint64_t v___x_392_; uint64_t v___x_393_; uint8_t v___x_394_; 
v___x_390_ = 40ULL;
v___x_391_ = lean_uint64_shift_right(v_c_389_, v___x_390_);
v___x_392_ = 1ULL;
v___x_393_ = lean_uint64_land(v___x_391_, v___x_392_);
v___x_394_ = lean_uint64_dec_eq(v___x_393_, v___x_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object* v_c_395_){
_start:
{
uint64_t v_c_boxed_396_; uint8_t v_res_397_; lean_object* v_r_398_; 
v_c_boxed_396_ = lean_unbox_uint64(v_c_395_);
lean_dec_ref(v_c_395_);
v_res_397_ = l_Lean_Expr_Data_hasFVar(v_c_boxed_396_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t v_c_399_){
_start:
{
uint64_t v___x_400_; uint64_t v___x_401_; uint64_t v___x_402_; uint64_t v___x_403_; uint8_t v___x_404_; 
v___x_400_ = 41ULL;
v___x_401_ = lean_uint64_shift_right(v_c_399_, v___x_400_);
v___x_402_ = 1ULL;
v___x_403_ = lean_uint64_land(v___x_401_, v___x_402_);
v___x_404_ = lean_uint64_dec_eq(v___x_403_, v___x_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object* v_c_405_){
_start:
{
uint64_t v_c_boxed_406_; uint8_t v_res_407_; lean_object* v_r_408_; 
v_c_boxed_406_ = lean_unbox_uint64(v_c_405_);
lean_dec_ref(v_c_405_);
v_res_407_ = l_Lean_Expr_Data_hasExprMVar(v_c_boxed_406_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t v_c_409_){
_start:
{
uint64_t v___x_410_; uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; uint8_t v___x_414_; 
v___x_410_ = 42ULL;
v___x_411_ = lean_uint64_shift_right(v_c_409_, v___x_410_);
v___x_412_ = 1ULL;
v___x_413_ = lean_uint64_land(v___x_411_, v___x_412_);
v___x_414_ = lean_uint64_dec_eq(v___x_413_, v___x_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object* v_c_415_){
_start:
{
uint64_t v_c_boxed_416_; uint8_t v_res_417_; lean_object* v_r_418_; 
v_c_boxed_416_ = lean_unbox_uint64(v_c_415_);
lean_dec_ref(v_c_415_);
v_res_417_ = l_Lean_Expr_Data_hasLevelMVar(v_c_boxed_416_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t v_c_419_){
_start:
{
uint64_t v___x_420_; uint64_t v___x_421_; uint64_t v___x_422_; uint64_t v___x_423_; uint8_t v___x_424_; 
v___x_420_ = 43ULL;
v___x_421_ = lean_uint64_shift_right(v_c_419_, v___x_420_);
v___x_422_ = 1ULL;
v___x_423_ = lean_uint64_land(v___x_421_, v___x_422_);
v___x_424_ = lean_uint64_dec_eq(v___x_423_, v___x_422_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object* v_c_425_){
_start:
{
uint64_t v_c_boxed_426_; uint8_t v_res_427_; lean_object* v_r_428_; 
v_c_boxed_426_ = lean_unbox_uint64(v_c_425_);
lean_dec_ref(v_c_425_);
v_res_427_ = l_Lean_Expr_Data_hasLevelParam(v_c_boxed_426_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_430_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_431_; uint64_t v_res_432_; lean_object* v_r_433_; 
v_a_00___x40___internal___hyg_1__boxed_431_ = lean_unbox(v_a_00___x40___internal___hyg_430_);
v_res_432_ = lean_uint8_to_uint64(v_a_00___x40___internal___hyg_1__boxed_431_);
v_r_433_ = lean_box_uint64(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object* v_h_441_, lean_object* v_looseBVarRange_442_, lean_object* v_approxDepth_443_, lean_object* v_hasFVar_444_, lean_object* v_hasExprMVar_445_, lean_object* v_hasLevelMVar_446_, lean_object* v_hasLevelParam_447_){
_start:
{
uint64_t v_h_boxed_448_; uint32_t v_approxDepth_boxed_449_; uint8_t v_hasFVar_boxed_450_; uint8_t v_hasExprMVar_boxed_451_; uint8_t v_hasLevelMVar_boxed_452_; uint8_t v_hasLevelParam_boxed_453_; uint64_t v_res_454_; lean_object* v_r_455_; 
v_h_boxed_448_ = lean_unbox_uint64(v_h_441_);
lean_dec_ref(v_h_441_);
v_approxDepth_boxed_449_ = lean_unbox_uint32(v_approxDepth_443_);
lean_dec(v_approxDepth_443_);
v_hasFVar_boxed_450_ = lean_unbox(v_hasFVar_444_);
v_hasExprMVar_boxed_451_ = lean_unbox(v_hasExprMVar_445_);
v_hasLevelMVar_boxed_452_ = lean_unbox(v_hasLevelMVar_446_);
v_hasLevelParam_boxed_453_ = lean_unbox(v_hasLevelParam_447_);
v_res_454_ = lean_expr_mk_data(v_h_boxed_448_, v_looseBVarRange_442_, v_approxDepth_boxed_449_, v_hasFVar_boxed_450_, v_hasExprMVar_boxed_451_, v_hasLevelMVar_boxed_452_, v_hasLevelParam_boxed_453_);
v_r_455_ = lean_box_uint64(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object* v_fData_458_, lean_object* v_aData_459_){
_start:
{
uint64_t v_fData_boxed_460_; uint64_t v_aData_boxed_461_; uint64_t v_res_462_; lean_object* v_r_463_; 
v_fData_boxed_460_ = lean_unbox_uint64(v_fData_458_);
lean_dec_ref(v_fData_458_);
v_aData_boxed_461_ = lean_unbox_uint64(v_aData_459_);
lean_dec_ref(v_aData_459_);
v_res_462_ = lean_expr_mk_app_data(v_fData_boxed_460_, v_aData_boxed_461_);
v_r_463_ = lean_box_uint64(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint64_t v_h_464_, lean_object* v_looseBVarRange_465_, uint32_t v_approxDepth_466_, uint8_t v_hasFVar_467_, uint8_t v_hasExprMVar_468_, uint8_t v_hasLevelMVar_469_, uint8_t v_hasLevelParam_470_){
_start:
{
uint64_t v___x_471_; 
v___x_471_ = lean_expr_mk_data(v_h_464_, v_looseBVarRange_465_, v_approxDepth_466_, v_hasFVar_467_, v_hasExprMVar_468_, v_hasLevelMVar_469_, v_hasLevelParam_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object* v_h_472_, lean_object* v_looseBVarRange_473_, lean_object* v_approxDepth_474_, lean_object* v_hasFVar_475_, lean_object* v_hasExprMVar_476_, lean_object* v_hasLevelMVar_477_, lean_object* v_hasLevelParam_478_){
_start:
{
uint64_t v_h_boxed_479_; uint32_t v_approxDepth_boxed_480_; uint8_t v_hasFVar_boxed_481_; uint8_t v_hasExprMVar_boxed_482_; uint8_t v_hasLevelMVar_boxed_483_; uint8_t v_hasLevelParam_boxed_484_; uint64_t v_res_485_; lean_object* v_r_486_; 
v_h_boxed_479_ = lean_unbox_uint64(v_h_472_);
lean_dec_ref(v_h_472_);
v_approxDepth_boxed_480_ = lean_unbox_uint32(v_approxDepth_474_);
lean_dec(v_approxDepth_474_);
v_hasFVar_boxed_481_ = lean_unbox(v_hasFVar_475_);
v_hasExprMVar_boxed_482_ = lean_unbox(v_hasExprMVar_476_);
v_hasLevelMVar_boxed_483_ = lean_unbox(v_hasLevelMVar_477_);
v_hasLevelParam_boxed_484_ = lean_unbox(v_hasLevelParam_478_);
v_res_485_ = l_Lean_Expr_mkDataForBinder(v_h_boxed_479_, v_looseBVarRange_473_, v_approxDepth_boxed_480_, v_hasFVar_boxed_481_, v_hasExprMVar_boxed_482_, v_hasLevelMVar_boxed_483_, v_hasLevelParam_boxed_484_);
v_r_486_ = lean_box_uint64(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint64_t v_h_487_, lean_object* v_looseBVarRange_488_, uint32_t v_approxDepth_489_, uint8_t v_hasFVar_490_, uint8_t v_hasExprMVar_491_, uint8_t v_hasLevelMVar_492_, uint8_t v_hasLevelParam_493_){
_start:
{
uint64_t v___x_494_; 
v___x_494_ = lean_expr_mk_data(v_h_487_, v_looseBVarRange_488_, v_approxDepth_489_, v_hasFVar_490_, v_hasExprMVar_491_, v_hasLevelMVar_492_, v_hasLevelParam_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object* v_h_495_, lean_object* v_looseBVarRange_496_, lean_object* v_approxDepth_497_, lean_object* v_hasFVar_498_, lean_object* v_hasExprMVar_499_, lean_object* v_hasLevelMVar_500_, lean_object* v_hasLevelParam_501_){
_start:
{
uint64_t v_h_boxed_502_; uint32_t v_approxDepth_boxed_503_; uint8_t v_hasFVar_boxed_504_; uint8_t v_hasExprMVar_boxed_505_; uint8_t v_hasLevelMVar_boxed_506_; uint8_t v_hasLevelParam_boxed_507_; uint64_t v_res_508_; lean_object* v_r_509_; 
v_h_boxed_502_ = lean_unbox_uint64(v_h_495_);
lean_dec_ref(v_h_495_);
v_approxDepth_boxed_503_ = lean_unbox_uint32(v_approxDepth_497_);
lean_dec(v_approxDepth_497_);
v_hasFVar_boxed_504_ = lean_unbox(v_hasFVar_498_);
v_hasExprMVar_boxed_505_ = lean_unbox(v_hasExprMVar_499_);
v_hasLevelMVar_boxed_506_ = lean_unbox(v_hasLevelMVar_500_);
v_hasLevelParam_boxed_507_ = lean_unbox(v_hasLevelParam_501_);
v_res_508_ = l_Lean_Expr_mkDataForLet(v_h_boxed_502_, v_looseBVarRange_496_, v_approxDepth_boxed_503_, v_hasFVar_boxed_504_, v_hasExprMVar_boxed_505_, v_hasLevelMVar_boxed_506_, v_hasLevelParam_boxed_507_);
v_r_509_ = lean_box_uint64(v_res_508_);
return v_r_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0(uint64_t v_v_519_, lean_object* v_prec_520_){
_start:
{
lean_object* v_r_522_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v_r_532_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v_r_545_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v_r_558_; lean_object* v_r_565_; lean_object* v___x_577_; uint64_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_r_581_; uint32_t v___x_582_; uint32_t v___x_583_; uint8_t v___x_584_; uint8_t v___x_585_; 
v___x_577_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__7));
v___x_578_ = l_Lean_Expr_Data_hash(v_v_519_);
v___x_579_ = lean_uint64_to_nat(v___x_578_);
v___x_580_ = l_Nat_reprFast(v___x_579_);
v_r_581_ = lean_string_append(v___x_577_, v___x_580_);
lean_dec_ref(v___x_580_);
v___x_582_ = l_Lean_Expr_Data_looseBVarRange(v_v_519_);
v___x_583_ = 0;
v___x_584_ = lean_uint32_dec_eq(v___x_582_, v___x_583_);
v___x_585_ = lean_bool_not(v___x_584_);
if (v___x_585_ == 0)
{
v_r_565_ = v_r_581_;
goto v___jp_564_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_r_592_; 
v___x_586_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__8));
v___x_587_ = lean_string_append(v_r_581_, v___x_586_);
v___x_588_ = lean_uint32_to_nat(v___x_582_);
v___x_589_ = l_Nat_reprFast(v___x_588_);
v___x_590_ = lean_string_append(v___x_587_, v___x_589_);
lean_dec_ref(v___x_589_);
v___x_591_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_592_ = lean_string_append(v___x_590_, v___x_591_);
v_r_565_ = v_r_592_;
goto v___jp_564_;
}
v___jp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_523_, 0, v_r_522_);
v___x_524_ = l_Repr_addAppParen(v___x_523_, v_prec_520_);
return v___x_524_;
}
v___jp_525_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v_r_530_; 
v___x_528_ = lean_string_append(v___y_526_, v___y_527_);
v___x_529_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_530_ = lean_string_append(v___x_528_, v___x_529_);
v_r_522_ = v_r_530_;
goto v___jp_521_;
}
v___jp_531_:
{
uint8_t v___x_533_; 
v___x_533_ = l_Lean_Expr_Data_hasLevelMVar(v_v_519_);
if (v___x_533_ == 0)
{
v_r_522_ = v_r_532_;
goto v___jp_521_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
v___x_535_ = lean_string_append(v_r_532_, v___x_534_);
if (v___x_533_ == 0)
{
lean_object* v___x_536_; 
v___x_536_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_526_ = v___x_535_;
v___y_527_ = v___x_536_;
goto v___jp_525_;
}
else
{
lean_object* v___x_537_; 
v___x_537_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_526_ = v___x_535_;
v___y_527_ = v___x_537_;
goto v___jp_525_;
}
}
}
v___jp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_r_543_; 
v___x_541_ = lean_string_append(v___y_539_, v___y_540_);
v___x_542_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_543_ = lean_string_append(v___x_541_, v___x_542_);
v_r_532_ = v_r_543_;
goto v___jp_531_;
}
v___jp_544_:
{
uint8_t v___x_546_; 
v___x_546_ = l_Lean_Expr_Data_hasExprMVar(v_v_519_);
if (v___x_546_ == 0)
{
v_r_532_ = v_r_545_;
goto v___jp_531_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__4));
v___x_548_ = lean_string_append(v_r_545_, v___x_547_);
if (v___x_546_ == 0)
{
lean_object* v___x_549_; 
v___x_549_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_539_ = v___x_548_;
v___y_540_ = v___x_549_;
goto v___jp_538_;
}
else
{
lean_object* v___x_550_; 
v___x_550_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_539_ = v___x_548_;
v___y_540_ = v___x_550_;
goto v___jp_538_;
}
}
}
v___jp_551_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v_r_556_; 
v___x_554_ = lean_string_append(v___y_552_, v___y_553_);
v___x_555_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_556_ = lean_string_append(v___x_554_, v___x_555_);
v_r_545_ = v_r_556_;
goto v___jp_544_;
}
v___jp_557_:
{
uint8_t v___x_559_; 
v___x_559_ = l_Lean_Expr_Data_hasFVar(v_v_519_);
if (v___x_559_ == 0)
{
v_r_545_ = v_r_558_;
goto v___jp_544_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__5));
v___x_561_ = lean_string_append(v_r_558_, v___x_560_);
if (v___x_559_ == 0)
{
lean_object* v___x_562_; 
v___x_562_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_552_ = v___x_561_;
v___y_553_ = v___x_562_;
goto v___jp_551_;
}
else
{
lean_object* v___x_563_; 
v___x_563_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_552_ = v___x_561_;
v___y_553_ = v___x_563_;
goto v___jp_551_;
}
}
}
v___jp_564_:
{
uint8_t v___x_566_; uint8_t v___x_567_; uint8_t v___x_568_; uint8_t v___x_569_; 
v___x_566_ = l_Lean_Expr_Data_approxDepth(v_v_519_);
v___x_567_ = 0;
v___x_568_ = lean_uint8_dec_eq(v___x_566_, v___x_567_);
v___x_569_ = lean_bool_not(v___x_568_);
if (v___x_569_ == 0)
{
v_r_558_ = v_r_565_;
goto v___jp_557_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_r_576_; 
v___x_570_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__6));
v___x_571_ = lean_string_append(v_r_565_, v___x_570_);
v___x_572_ = lean_uint8_to_nat(v___x_566_);
v___x_573_ = l_Nat_reprFast(v___x_572_);
v___x_574_ = lean_string_append(v___x_571_, v___x_573_);
lean_dec_ref(v___x_573_);
v___x_575_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_576_ = lean_string_append(v___x_574_, v___x_575_);
v_r_558_ = v_r_576_;
goto v___jp_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0___boxed(lean_object* v_v_593_, lean_object* v_prec_594_){
_start:
{
uint64_t v_v_boxed_595_; lean_object* v_res_596_; 
v_v_boxed_595_ = lean_unbox_uint64(v_v_593_);
lean_dec_ref(v_v_593_);
v_res_596_ = l_Lean_instReprData__1___lam__0(v_v_boxed_595_, v_prec_594_);
lean_dec(v_prec_594_);
return v_res_596_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId_default(void){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_box(0);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId(void){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = lean_box(0);
return v___x_600_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqFVarId_beq(lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
uint8_t v___x_603_; 
v___x_603_ = lean_name_eq(v_x_601_, v_x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
uint8_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Lean_instBEqFVarId_beq(v_x_604_, v_x_605_);
lean_dec(v_x_605_);
lean_dec(v_x_604_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
static uint64_t _init_l_Lean_instHashableFVarId_hash___closed__0(void){
_start:
{
lean_object* v___x_610_; uint64_t v___x_611_; 
v___x_610_ = lean_unsigned_to_nat(1723u);
v___x_611_ = lean_uint64_of_nat(v___x_610_);
return v___x_611_;
}
}
static uint64_t _init_l_Lean_instHashableFVarId_hash___closed__1(void){
_start:
{
uint64_t v___x_612_; uint64_t v___x_613_; uint64_t v___x_614_; 
v___x_612_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
v___x_613_ = 0ULL;
v___x_614_ = lean_uint64_mix_hash(v___x_613_, v___x_612_);
return v___x_614_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableFVarId_hash(lean_object* v_x_615_){
_start:
{
uint64_t v___x_616_; 
v___x_616_ = 0ULL;
if (lean_obj_tag(v_x_615_) == 0)
{
uint64_t v___x_617_; 
v___x_617_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__1, &l_Lean_instHashableFVarId_hash___closed__1_once, _init_l_Lean_instHashableFVarId_hash___closed__1);
return v___x_617_;
}
else
{
uint64_t v_hash_618_; uint64_t v___x_619_; 
v_hash_618_ = lean_ctor_get_uint64(v_x_615_, sizeof(void*)*2);
v___x_619_ = lean_uint64_mix_hash(v___x_616_, v_hash_618_);
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object* v_x_620_){
_start:
{
uint64_t v_res_621_; lean_object* v_r_622_; 
v_res_621_ = l_Lean_instHashableFVarId_hash(v_x_620_);
lean_dec(v_x_620_);
v_r_622_ = lean_box_uint64(v_res_621_);
return v_r_622_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = lean_box(1);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet(void){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_box(1);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = lean_box(1);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet(void){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_box(1);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___aux__1(lean_object* v_e_632_){
_start:
{
lean_object* v___f_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___f_633_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_634_ = lean_box(1);
lean_inc(v_e_632_);
v___x_635_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___f_633_, v_e_632_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_box(0);
v___x_637_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_633_, v_e_632_, v___x_636_, v___x_634_);
return v___x_637_;
}
else
{
lean_dec(v_e_632_);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object* v_k_638_, lean_object* v_v_639_, lean_object* v_t_640_){
_start:
{
if (lean_obj_tag(v_t_640_) == 0)
{
lean_object* v_size_641_; lean_object* v_k_642_; lean_object* v_v_643_; lean_object* v_l_644_; lean_object* v_r_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_925_; 
v_size_641_ = lean_ctor_get(v_t_640_, 0);
v_k_642_ = lean_ctor_get(v_t_640_, 1);
v_v_643_ = lean_ctor_get(v_t_640_, 2);
v_l_644_ = lean_ctor_get(v_t_640_, 3);
v_r_645_ = lean_ctor_get(v_t_640_, 4);
v_isSharedCheck_925_ = !lean_is_exclusive(v_t_640_);
if (v_isSharedCheck_925_ == 0)
{
v___x_647_ = v_t_640_;
v_isShared_648_ = v_isSharedCheck_925_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_r_645_);
lean_inc(v_l_644_);
lean_inc(v_v_643_);
lean_inc(v_k_642_);
lean_inc(v_size_641_);
lean_dec(v_t_640_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_925_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
uint8_t v___x_649_; 
v___x_649_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_638_, v_k_642_);
switch(v___x_649_)
{
case 0:
{
lean_object* v_impl_650_; lean_object* v___x_651_; 
lean_dec(v_size_641_);
v_impl_650_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_638_, v_v_639_, v_l_644_);
v___x_651_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_645_) == 0)
{
lean_object* v_size_652_; lean_object* v_size_653_; lean_object* v_k_654_; lean_object* v_v_655_; lean_object* v_l_656_; lean_object* v_r_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v_size_652_ = lean_ctor_get(v_r_645_, 0);
v_size_653_ = lean_ctor_get(v_impl_650_, 0);
lean_inc(v_size_653_);
v_k_654_ = lean_ctor_get(v_impl_650_, 1);
lean_inc(v_k_654_);
v_v_655_ = lean_ctor_get(v_impl_650_, 2);
lean_inc(v_v_655_);
v_l_656_ = lean_ctor_get(v_impl_650_, 3);
lean_inc(v_l_656_);
v_r_657_ = lean_ctor_get(v_impl_650_, 4);
lean_inc(v_r_657_);
v___x_658_ = lean_unsigned_to_nat(3u);
v___x_659_ = lean_nat_mul(v___x_658_, v_size_652_);
v___x_660_ = lean_nat_dec_lt(v___x_659_, v_size_653_);
lean_dec(v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
lean_dec(v_r_657_);
lean_dec(v_l_656_);
lean_dec(v_v_655_);
lean_dec(v_k_654_);
v___x_661_ = lean_nat_add(v___x_651_, v_size_653_);
lean_dec(v_size_653_);
v___x_662_ = lean_nat_add(v___x_661_, v_size_652_);
lean_dec(v___x_661_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 3, v_impl_650_);
lean_ctor_set(v___x_647_, 0, v___x_662_);
v___x_664_ = v___x_647_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_665_, 3, v_impl_650_);
lean_ctor_set(v_reuseFailAlloc_665_, 4, v_r_645_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
else
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_731_; 
v_isSharedCheck_731_ = !lean_is_exclusive(v_impl_650_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; lean_object* v_unused_733_; lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; 
v_unused_732_ = lean_ctor_get(v_impl_650_, 4);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_impl_650_, 3);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_impl_650_, 2);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_impl_650_, 1);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_impl_650_, 0);
lean_dec(v_unused_736_);
v___x_667_ = v_impl_650_;
v_isShared_668_ = v_isSharedCheck_731_;
goto v_resetjp_666_;
}
else
{
lean_dec(v_impl_650_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_731_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_size_669_; lean_object* v_size_670_; lean_object* v_k_671_; lean_object* v_v_672_; lean_object* v_l_673_; lean_object* v_r_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_size_669_ = lean_ctor_get(v_l_656_, 0);
v_size_670_ = lean_ctor_get(v_r_657_, 0);
v_k_671_ = lean_ctor_get(v_r_657_, 1);
v_v_672_ = lean_ctor_get(v_r_657_, 2);
v_l_673_ = lean_ctor_get(v_r_657_, 3);
v_r_674_ = lean_ctor_get(v_r_657_, 4);
v___x_675_ = lean_unsigned_to_nat(2u);
v___x_676_ = lean_nat_mul(v___x_675_, v_size_669_);
v___x_677_ = lean_nat_dec_lt(v_size_670_, v___x_676_);
lean_dec(v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_706_; 
lean_inc(v_r_674_);
lean_inc(v_l_673_);
lean_inc(v_v_672_);
lean_inc(v_k_671_);
v_isSharedCheck_706_ = !lean_is_exclusive(v_r_657_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; lean_object* v_unused_711_; 
v_unused_707_ = lean_ctor_get(v_r_657_, 4);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_r_657_, 3);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_r_657_, 2);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_r_657_, 1);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_r_657_, 0);
lean_dec(v_unused_711_);
v___x_679_ = v_r_657_;
v_isShared_680_ = v_isSharedCheck_706_;
goto v_resetjp_678_;
}
else
{
lean_dec(v_r_657_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_706_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___x_694_; lean_object* v___y_696_; 
v___x_681_ = lean_nat_add(v___x_651_, v_size_653_);
lean_dec(v_size_653_);
v___x_682_ = lean_nat_add(v___x_681_, v_size_652_);
lean_dec(v___x_681_);
v___x_694_ = lean_nat_add(v___x_651_, v_size_669_);
if (lean_obj_tag(v_l_673_) == 0)
{
lean_object* v_size_704_; 
v_size_704_ = lean_ctor_get(v_l_673_, 0);
lean_inc(v_size_704_);
v___y_696_ = v_size_704_;
goto v___jp_695_;
}
else
{
lean_object* v___x_705_; 
v___x_705_ = lean_unsigned_to_nat(0u);
v___y_696_ = v___x_705_;
goto v___jp_695_;
}
v___jp_683_:
{
lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_687_ = lean_nat_add(v___y_684_, v___y_686_);
lean_dec(v___y_686_);
lean_dec(v___y_684_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 4, v_r_645_);
lean_ctor_set(v___x_679_, 3, v_r_674_);
lean_ctor_set(v___x_679_, 2, v_v_643_);
lean_ctor_set(v___x_679_, 1, v_k_642_);
lean_ctor_set(v___x_679_, 0, v___x_687_);
v___x_689_ = v___x_679_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v_r_674_);
lean_ctor_set(v_reuseFailAlloc_693_, 4, v_r_645_);
v___x_689_ = v_reuseFailAlloc_693_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_691_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 4, v___x_689_);
lean_ctor_set(v___x_667_, 3, v___y_685_);
lean_ctor_set(v___x_667_, 2, v_v_672_);
lean_ctor_set(v___x_667_, 1, v_k_671_);
lean_ctor_set(v___x_667_, 0, v___x_682_);
v___x_691_ = v___x_667_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_k_671_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_v_672_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v___y_685_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
v___jp_695_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_nat_add(v___x_694_, v___y_696_);
lean_dec(v___y_696_);
lean_dec(v___x_694_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 4, v_l_673_);
lean_ctor_set(v___x_647_, 3, v_l_656_);
lean_ctor_set(v___x_647_, 2, v_v_655_);
lean_ctor_set(v___x_647_, 1, v_k_654_);
lean_ctor_set(v___x_647_, 0, v___x_697_);
v___x_699_ = v___x_647_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_k_654_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_v_655_);
lean_ctor_set(v_reuseFailAlloc_703_, 3, v_l_656_);
lean_ctor_set(v_reuseFailAlloc_703_, 4, v_l_673_);
v___x_699_ = v_reuseFailAlloc_703_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; 
v___x_700_ = lean_nat_add(v___x_651_, v_size_652_);
if (lean_obj_tag(v_r_674_) == 0)
{
lean_object* v_size_701_; 
v_size_701_ = lean_ctor_get(v_r_674_, 0);
lean_inc(v_size_701_);
v___y_684_ = v___x_700_;
v___y_685_ = v___x_699_;
v___y_686_ = v_size_701_;
goto v___jp_683_;
}
else
{
lean_object* v___x_702_; 
v___x_702_ = lean_unsigned_to_nat(0u);
v___y_684_ = v___x_700_;
v___y_685_ = v___x_699_;
v___y_686_ = v___x_702_;
goto v___jp_683_;
}
}
}
}
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
lean_del_object(v___x_647_);
v___x_712_ = lean_nat_add(v___x_651_, v_size_653_);
lean_dec(v_size_653_);
v___x_713_ = lean_nat_add(v___x_712_, v_size_652_);
lean_dec(v___x_712_);
v___x_714_ = lean_nat_add(v___x_651_, v_size_652_);
v___x_715_ = lean_nat_add(v___x_714_, v_size_670_);
lean_dec(v___x_714_);
lean_inc_ref(v_r_645_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 4, v_r_645_);
lean_ctor_set(v___x_667_, 3, v_r_657_);
lean_ctor_set(v___x_667_, 2, v_v_643_);
lean_ctor_set(v___x_667_, 1, v_k_642_);
lean_ctor_set(v___x_667_, 0, v___x_715_);
v___x_717_ = v___x_667_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_r_657_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v_r_645_);
v___x_717_ = v_reuseFailAlloc_730_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
v_isSharedCheck_724_ = !lean_is_exclusive(v_r_645_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; lean_object* v_unused_726_; lean_object* v_unused_727_; lean_object* v_unused_728_; lean_object* v_unused_729_; 
v_unused_725_ = lean_ctor_get(v_r_645_, 4);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_r_645_, 3);
lean_dec(v_unused_726_);
v_unused_727_ = lean_ctor_get(v_r_645_, 2);
lean_dec(v_unused_727_);
v_unused_728_ = lean_ctor_get(v_r_645_, 1);
lean_dec(v_unused_728_);
v_unused_729_ = lean_ctor_get(v_r_645_, 0);
lean_dec(v_unused_729_);
v___x_719_ = v_r_645_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_dec(v_r_645_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 4, v___x_717_);
lean_ctor_set(v___x_719_, 3, v_l_656_);
lean_ctor_set(v___x_719_, 2, v_v_655_);
lean_ctor_set(v___x_719_, 1, v_k_654_);
lean_ctor_set(v___x_719_, 0, v___x_713_);
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_k_654_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_v_655_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_l_656_);
lean_ctor_set(v_reuseFailAlloc_723_, 4, v___x_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_737_; 
v_l_737_ = lean_ctor_get(v_impl_650_, 3);
lean_inc(v_l_737_);
if (lean_obj_tag(v_l_737_) == 0)
{
lean_object* v_r_738_; lean_object* v_k_739_; lean_object* v_v_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_751_; 
v_r_738_ = lean_ctor_get(v_impl_650_, 4);
v_k_739_ = lean_ctor_get(v_impl_650_, 1);
v_v_740_ = lean_ctor_get(v_impl_650_, 2);
v_isSharedCheck_751_ = !lean_is_exclusive(v_impl_650_);
if (v_isSharedCheck_751_ == 0)
{
lean_object* v_unused_752_; lean_object* v_unused_753_; 
v_unused_752_ = lean_ctor_get(v_impl_650_, 3);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_impl_650_, 0);
lean_dec(v_unused_753_);
v___x_742_ = v_impl_650_;
v_isShared_743_ = v_isSharedCheck_751_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_r_738_);
lean_inc(v_v_740_);
lean_inc(v_k_739_);
lean_dec(v_impl_650_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_751_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_744_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_738_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 3, v_r_738_);
lean_ctor_set(v___x_742_, 2, v_v_643_);
lean_ctor_set(v___x_742_, 1, v_k_642_);
lean_ctor_set(v___x_742_, 0, v___x_651_);
v___x_746_ = v___x_742_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_750_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_750_, 3, v_r_738_);
lean_ctor_set(v_reuseFailAlloc_750_, 4, v_r_738_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_748_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 4, v___x_746_);
lean_ctor_set(v___x_647_, 3, v_l_737_);
lean_ctor_set(v___x_647_, 2, v_v_740_);
lean_ctor_set(v___x_647_, 1, v_k_739_);
lean_ctor_set(v___x_647_, 0, v___x_744_);
v___x_748_ = v___x_647_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_k_739_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_v_740_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_l_737_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_r_754_; 
v_r_754_ = lean_ctor_get(v_impl_650_, 4);
lean_inc(v_r_754_);
if (lean_obj_tag(v_r_754_) == 0)
{
lean_object* v_k_755_; lean_object* v_v_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_779_; 
v_k_755_ = lean_ctor_get(v_impl_650_, 1);
v_v_756_ = lean_ctor_get(v_impl_650_, 2);
v_isSharedCheck_779_ = !lean_is_exclusive(v_impl_650_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; lean_object* v_unused_781_; lean_object* v_unused_782_; 
v_unused_780_ = lean_ctor_get(v_impl_650_, 4);
lean_dec(v_unused_780_);
v_unused_781_ = lean_ctor_get(v_impl_650_, 3);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_impl_650_, 0);
lean_dec(v_unused_782_);
v___x_758_ = v_impl_650_;
v_isShared_759_ = v_isSharedCheck_779_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_v_756_);
lean_inc(v_k_755_);
lean_dec(v_impl_650_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_779_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v_k_760_; lean_object* v_v_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_775_; 
v_k_760_ = lean_ctor_get(v_r_754_, 1);
v_v_761_ = lean_ctor_get(v_r_754_, 2);
v_isSharedCheck_775_ = !lean_is_exclusive(v_r_754_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; lean_object* v_unused_777_; lean_object* v_unused_778_; 
v_unused_776_ = lean_ctor_get(v_r_754_, 4);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_r_754_, 3);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_r_754_, 0);
lean_dec(v_unused_778_);
v___x_763_ = v_r_754_;
v_isShared_764_ = v_isSharedCheck_775_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_v_761_);
lean_inc(v_k_760_);
lean_dec(v_r_754_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_775_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = lean_unsigned_to_nat(3u);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 4, v_l_737_);
lean_ctor_set(v___x_763_, 3, v_l_737_);
lean_ctor_set(v___x_763_, 2, v_v_756_);
lean_ctor_set(v___x_763_, 1, v_k_755_);
lean_ctor_set(v___x_763_, 0, v___x_651_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_l_737_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_l_737_);
v___x_767_ = v_reuseFailAlloc_774_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 4, v_l_737_);
lean_ctor_set(v___x_758_, 2, v_v_643_);
lean_ctor_set(v___x_758_, 1, v_k_642_);
lean_ctor_set(v___x_758_, 0, v___x_651_);
v___x_769_ = v___x_758_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v_l_737_);
lean_ctor_set(v_reuseFailAlloc_773_, 4, v_l_737_);
v___x_769_ = v_reuseFailAlloc_773_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_771_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 4, v___x_769_);
lean_ctor_set(v___x_647_, 3, v___x_767_);
lean_ctor_set(v___x_647_, 2, v_v_761_);
lean_ctor_set(v___x_647_, 1, v_k_760_);
lean_ctor_set(v___x_647_, 0, v___x_765_);
v___x_771_ = v___x_647_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_k_760_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_v_761_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
else
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = lean_unsigned_to_nat(2u);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 4, v_r_754_);
lean_ctor_set(v___x_647_, 3, v_impl_650_);
lean_ctor_set(v___x_647_, 0, v___x_783_);
v___x_785_ = v___x_647_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v_impl_650_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v_r_754_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
case 1:
{
lean_object* v___x_788_; 
lean_dec(v_v_643_);
lean_dec(v_k_642_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 2, v_v_639_);
lean_ctor_set(v___x_647_, 1, v_k_638_);
v___x_788_ = v___x_647_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_size_641_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_k_638_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_v_639_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v_l_644_);
lean_ctor_set(v_reuseFailAlloc_789_, 4, v_r_645_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
default: 
{
lean_object* v_impl_790_; lean_object* v___x_791_; 
lean_dec(v_size_641_);
v_impl_790_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_638_, v_v_639_, v_r_645_);
v___x_791_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_644_) == 0)
{
lean_object* v_size_792_; lean_object* v_size_793_; lean_object* v_k_794_; lean_object* v_v_795_; lean_object* v_l_796_; lean_object* v_r_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v_size_792_ = lean_ctor_get(v_l_644_, 0);
v_size_793_ = lean_ctor_get(v_impl_790_, 0);
lean_inc(v_size_793_);
v_k_794_ = lean_ctor_get(v_impl_790_, 1);
lean_inc(v_k_794_);
v_v_795_ = lean_ctor_get(v_impl_790_, 2);
lean_inc(v_v_795_);
v_l_796_ = lean_ctor_get(v_impl_790_, 3);
lean_inc(v_l_796_);
v_r_797_ = lean_ctor_get(v_impl_790_, 4);
lean_inc(v_r_797_);
v___x_798_ = lean_unsigned_to_nat(3u);
v___x_799_ = lean_nat_mul(v___x_798_, v_size_792_);
v___x_800_ = lean_nat_dec_lt(v___x_799_, v_size_793_);
lean_dec(v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
lean_dec(v_r_797_);
lean_dec(v_l_796_);
lean_dec(v_v_795_);
lean_dec(v_k_794_);
v___x_801_ = lean_nat_add(v___x_791_, v_size_792_);
v___x_802_ = lean_nat_add(v___x_801_, v_size_793_);
lean_dec(v_size_793_);
lean_dec(v___x_801_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 4, v_impl_790_);
lean_ctor_set(v___x_647_, 0, v___x_802_);
v___x_804_ = v___x_647_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v_l_644_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v_impl_790_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
else
{
lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_869_; 
v_isSharedCheck_869_ = !lean_is_exclusive(v_impl_790_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; lean_object* v_unused_871_; lean_object* v_unused_872_; lean_object* v_unused_873_; lean_object* v_unused_874_; 
v_unused_870_ = lean_ctor_get(v_impl_790_, 4);
lean_dec(v_unused_870_);
v_unused_871_ = lean_ctor_get(v_impl_790_, 3);
lean_dec(v_unused_871_);
v_unused_872_ = lean_ctor_get(v_impl_790_, 2);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_impl_790_, 1);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_impl_790_, 0);
lean_dec(v_unused_874_);
v___x_807_ = v_impl_790_;
v_isShared_808_ = v_isSharedCheck_869_;
goto v_resetjp_806_;
}
else
{
lean_dec(v_impl_790_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_869_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v_size_809_; lean_object* v_k_810_; lean_object* v_v_811_; lean_object* v_l_812_; lean_object* v_r_813_; lean_object* v_size_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_size_809_ = lean_ctor_get(v_l_796_, 0);
v_k_810_ = lean_ctor_get(v_l_796_, 1);
v_v_811_ = lean_ctor_get(v_l_796_, 2);
v_l_812_ = lean_ctor_get(v_l_796_, 3);
v_r_813_ = lean_ctor_get(v_l_796_, 4);
v_size_814_ = lean_ctor_get(v_r_797_, 0);
v___x_815_ = lean_unsigned_to_nat(2u);
v___x_816_ = lean_nat_mul(v___x_815_, v_size_814_);
v___x_817_ = lean_nat_dec_lt(v_size_809_, v___x_816_);
lean_dec(v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_845_; 
lean_inc(v_r_813_);
lean_inc(v_l_812_);
lean_inc(v_v_811_);
lean_inc(v_k_810_);
v_isSharedCheck_845_ = !lean_is_exclusive(v_l_796_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; lean_object* v_unused_847_; lean_object* v_unused_848_; lean_object* v_unused_849_; lean_object* v_unused_850_; 
v_unused_846_ = lean_ctor_get(v_l_796_, 4);
lean_dec(v_unused_846_);
v_unused_847_ = lean_ctor_get(v_l_796_, 3);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_l_796_, 2);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_l_796_, 1);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v_l_796_, 0);
lean_dec(v_unused_850_);
v___x_819_ = v_l_796_;
v_isShared_820_ = v_isSharedCheck_845_;
goto v_resetjp_818_;
}
else
{
lean_dec(v_l_796_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_845_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_835_; 
v___x_821_ = lean_nat_add(v___x_791_, v_size_792_);
v___x_822_ = lean_nat_add(v___x_821_, v_size_793_);
lean_dec(v_size_793_);
if (lean_obj_tag(v_l_812_) == 0)
{
lean_object* v_size_843_; 
v_size_843_ = lean_ctor_get(v_l_812_, 0);
lean_inc(v_size_843_);
v___y_835_ = v_size_843_;
goto v___jp_834_;
}
else
{
lean_object* v___x_844_; 
v___x_844_ = lean_unsigned_to_nat(0u);
v___y_835_ = v___x_844_;
goto v___jp_834_;
}
v___jp_823_:
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = lean_nat_add(v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec(v___y_825_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 4, v_r_797_);
lean_ctor_set(v___x_819_, 3, v_r_813_);
lean_ctor_set(v___x_819_, 2, v_v_795_);
lean_ctor_set(v___x_819_, 1, v_k_794_);
lean_ctor_set(v___x_819_, 0, v___x_827_);
v___x_829_ = v___x_819_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_833_, 3, v_r_813_);
lean_ctor_set(v_reuseFailAlloc_833_, 4, v_r_797_);
v___x_829_ = v_reuseFailAlloc_833_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_831_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v___x_829_);
lean_ctor_set(v___x_807_, 3, v___y_824_);
lean_ctor_set(v___x_807_, 2, v_v_811_);
lean_ctor_set(v___x_807_, 1, v_k_810_);
lean_ctor_set(v___x_807_, 0, v___x_822_);
v___x_831_ = v___x_807_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_k_810_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_v_811_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v___y_824_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
v___jp_834_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_nat_add(v___x_821_, v___y_835_);
lean_dec(v___y_835_);
lean_dec(v___x_821_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 4, v_l_812_);
lean_ctor_set(v___x_647_, 0, v___x_836_);
v___x_838_ = v___x_647_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_l_644_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_l_812_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; 
v___x_839_ = lean_nat_add(v___x_791_, v_size_814_);
if (lean_obj_tag(v_r_813_) == 0)
{
lean_object* v_size_840_; 
v_size_840_ = lean_ctor_get(v_r_813_, 0);
lean_inc(v_size_840_);
v___y_824_ = v___x_838_;
v___y_825_ = v___x_839_;
v___y_826_ = v_size_840_;
goto v___jp_823_;
}
else
{
lean_object* v___x_841_; 
v___x_841_ = lean_unsigned_to_nat(0u);
v___y_824_ = v___x_838_;
v___y_825_ = v___x_839_;
v___y_826_ = v___x_841_;
goto v___jp_823_;
}
}
}
}
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
lean_del_object(v___x_647_);
v___x_851_ = lean_nat_add(v___x_791_, v_size_792_);
v___x_852_ = lean_nat_add(v___x_851_, v_size_793_);
lean_dec(v_size_793_);
v___x_853_ = lean_nat_add(v___x_851_, v_size_809_);
lean_dec(v___x_851_);
lean_inc_ref(v_l_644_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v_l_796_);
lean_ctor_set(v___x_807_, 3, v_l_644_);
lean_ctor_set(v___x_807_, 2, v_v_643_);
lean_ctor_set(v___x_807_, 1, v_k_642_);
lean_ctor_set(v___x_807_, 0, v___x_853_);
v___x_855_ = v___x_807_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_868_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_868_, 3, v_l_644_);
lean_ctor_set(v_reuseFailAlloc_868_, 4, v_l_796_);
v___x_855_ = v_reuseFailAlloc_868_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_isSharedCheck_862_ = !lean_is_exclusive(v_l_644_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; lean_object* v_unused_864_; lean_object* v_unused_865_; lean_object* v_unused_866_; lean_object* v_unused_867_; 
v_unused_863_ = lean_ctor_get(v_l_644_, 4);
lean_dec(v_unused_863_);
v_unused_864_ = lean_ctor_get(v_l_644_, 3);
lean_dec(v_unused_864_);
v_unused_865_ = lean_ctor_get(v_l_644_, 2);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_l_644_, 1);
lean_dec(v_unused_866_);
v_unused_867_ = lean_ctor_get(v_l_644_, 0);
lean_dec(v_unused_867_);
v___x_857_ = v_l_644_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_dec(v_l_644_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 4, v_r_797_);
lean_ctor_set(v___x_857_, 3, v___x_855_);
lean_ctor_set(v___x_857_, 2, v_v_795_);
lean_ctor_set(v___x_857_, 1, v_k_794_);
lean_ctor_set(v___x_857_, 0, v___x_852_);
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v_r_797_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_875_; 
v_l_875_ = lean_ctor_get(v_impl_790_, 3);
lean_inc(v_l_875_);
if (lean_obj_tag(v_l_875_) == 0)
{
lean_object* v_r_876_; lean_object* v_k_877_; lean_object* v_v_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_901_; 
v_r_876_ = lean_ctor_get(v_impl_790_, 4);
v_k_877_ = lean_ctor_get(v_impl_790_, 1);
v_v_878_ = lean_ctor_get(v_impl_790_, 2);
v_isSharedCheck_901_ = !lean_is_exclusive(v_impl_790_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; lean_object* v_unused_903_; 
v_unused_902_ = lean_ctor_get(v_impl_790_, 3);
lean_dec(v_unused_902_);
v_unused_903_ = lean_ctor_get(v_impl_790_, 0);
lean_dec(v_unused_903_);
v___x_880_ = v_impl_790_;
v_isShared_881_ = v_isSharedCheck_901_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_r_876_);
lean_inc(v_v_878_);
lean_inc(v_k_877_);
lean_dec(v_impl_790_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_901_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_k_882_; lean_object* v_v_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_897_; 
v_k_882_ = lean_ctor_get(v_l_875_, 1);
v_v_883_ = lean_ctor_get(v_l_875_, 2);
v_isSharedCheck_897_ = !lean_is_exclusive(v_l_875_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; lean_object* v_unused_899_; lean_object* v_unused_900_; 
v_unused_898_ = lean_ctor_get(v_l_875_, 4);
lean_dec(v_unused_898_);
v_unused_899_ = lean_ctor_get(v_l_875_, 3);
lean_dec(v_unused_899_);
v_unused_900_ = lean_ctor_get(v_l_875_, 0);
lean_dec(v_unused_900_);
v___x_885_ = v_l_875_;
v_isShared_886_ = v_isSharedCheck_897_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_v_883_);
lean_inc(v_k_882_);
lean_dec(v_l_875_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_897_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_876_, 2);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 4, v_r_876_);
lean_ctor_set(v___x_885_, 3, v_r_876_);
lean_ctor_set(v___x_885_, 2, v_v_643_);
lean_ctor_set(v___x_885_, 1, v_k_642_);
lean_ctor_set(v___x_885_, 0, v___x_791_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_896_, 3, v_r_876_);
lean_ctor_set(v_reuseFailAlloc_896_, 4, v_r_876_);
v___x_889_ = v_reuseFailAlloc_896_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_891_; 
lean_inc(v_r_876_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 3, v_r_876_);
lean_ctor_set(v___x_880_, 0, v___x_791_);
v___x_891_ = v___x_880_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_r_876_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v_r_876_);
v___x_891_ = v_reuseFailAlloc_895_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_893_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 4, v___x_891_);
lean_ctor_set(v___x_647_, 3, v___x_889_);
lean_ctor_set(v___x_647_, 2, v_v_883_);
lean_ctor_set(v___x_647_, 1, v_k_882_);
lean_ctor_set(v___x_647_, 0, v___x_887_);
v___x_893_ = v___x_647_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
}
else
{
lean_object* v_r_904_; 
v_r_904_ = lean_ctor_get(v_impl_790_, 4);
lean_inc(v_r_904_);
if (lean_obj_tag(v_r_904_) == 0)
{
lean_object* v_k_905_; lean_object* v_v_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_917_; 
v_k_905_ = lean_ctor_get(v_impl_790_, 1);
v_v_906_ = lean_ctor_get(v_impl_790_, 2);
v_isSharedCheck_917_ = !lean_is_exclusive(v_impl_790_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; lean_object* v_unused_919_; lean_object* v_unused_920_; 
v_unused_918_ = lean_ctor_get(v_impl_790_, 4);
lean_dec(v_unused_918_);
v_unused_919_ = lean_ctor_get(v_impl_790_, 3);
lean_dec(v_unused_919_);
v_unused_920_ = lean_ctor_get(v_impl_790_, 0);
lean_dec(v_unused_920_);
v___x_908_ = v_impl_790_;
v_isShared_909_ = v_isSharedCheck_917_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_v_906_);
lean_inc(v_k_905_);
lean_dec(v_impl_790_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_917_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = lean_unsigned_to_nat(3u);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 4, v_l_875_);
lean_ctor_set(v___x_908_, 2, v_v_643_);
lean_ctor_set(v___x_908_, 1, v_k_642_);
lean_ctor_set(v___x_908_, 0, v___x_791_);
v___x_912_ = v___x_908_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v_l_875_);
lean_ctor_set(v_reuseFailAlloc_916_, 4, v_l_875_);
v___x_912_ = v_reuseFailAlloc_916_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_914_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 4, v_r_904_);
lean_ctor_set(v___x_647_, 3, v___x_912_);
lean_ctor_set(v___x_647_, 2, v_v_906_);
lean_ctor_set(v___x_647_, 1, v_k_905_);
lean_ctor_set(v___x_647_, 0, v___x_910_);
v___x_914_ = v___x_647_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_k_905_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_v_906_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_915_, 4, v_r_904_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_921_ = lean_unsigned_to_nat(2u);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 4, v_impl_790_);
lean_ctor_set(v___x_647_, 3, v_r_904_);
lean_ctor_set(v___x_647_, 0, v___x_921_);
v___x_923_ = v___x_647_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_924_, 3, v_r_904_);
lean_ctor_set(v_reuseFailAlloc_924_, 4, v_impl_790_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
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
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_unsigned_to_nat(1u);
v___x_927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v_k_638_);
lean_ctor_set(v___x_927_, 2, v_v_639_);
lean_ctor_set(v___x_927_, 3, v_t_640_);
lean_ctor_set(v___x_927_, 4, v_t_640_);
return v___x_927_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(lean_object* v_k_928_, lean_object* v_t_929_){
_start:
{
if (lean_obj_tag(v_t_929_) == 0)
{
lean_object* v_k_930_; lean_object* v_l_931_; lean_object* v_r_932_; uint8_t v___x_933_; 
v_k_930_ = lean_ctor_get(v_t_929_, 1);
v_l_931_ = lean_ctor_get(v_t_929_, 3);
v_r_932_ = lean_ctor_get(v_t_929_, 4);
v___x_933_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_928_, v_k_930_);
switch(v___x_933_)
{
case 0:
{
v_t_929_ = v_l_931_;
goto _start;
}
case 1:
{
uint8_t v___x_935_; 
v___x_935_ = 1;
return v___x_935_;
}
default: 
{
v_t_929_ = v_r_932_;
goto _start;
}
}
}
else
{
uint8_t v___x_937_; 
v___x_937_ = 0;
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg___boxed(lean_object* v_k_938_, lean_object* v_t_939_){
_start:
{
uint8_t v_res_940_; lean_object* v_r_941_; 
v_res_940_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_938_, v_t_939_);
lean_dec(v_t_939_);
lean_dec(v_k_938_);
v_r_941_ = lean_box(v_res_940_);
return v_r_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object* v___y_942_){
_start:
{
lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_943_ = lean_box(1);
v___x_944_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v___y_942_, v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_box(0);
v___x_946_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___y_942_, v___x_945_, v___x_943_);
return v___x_946_;
}
else
{
lean_dec(v___y_942_);
return v___x_943_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(lean_object* v_00_u03b2_949_, lean_object* v_k_950_, lean_object* v_t_951_){
_start:
{
uint8_t v___x_952_; 
v___x_952_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_950_, v_t_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___boxed(lean_object* v_00_u03b2_953_, lean_object* v_k_954_, lean_object* v_t_955_){
_start:
{
uint8_t v_res_956_; lean_object* v_r_957_; 
v_res_956_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(v_00_u03b2_953_, v_k_954_, v_t_955_);
lean_dec(v_t_955_);
lean_dec(v_k_954_);
v_r_957_ = lean_box(v_res_956_);
return v_r_957_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1(lean_object* v_00_u03b2_958_, lean_object* v_k_959_, lean_object* v_v_960_, lean_object* v_t_961_, lean_object* v_hl_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_959_, v_v_960_, v_t_961_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_964_, lean_object* v_a_965_, lean_object* v_b_966_, lean_object* v_c_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = lean_apply_2(v_f_964_, v_a_965_, v_c_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_969_, lean_object* v_____do__lift_970_){
_start:
{
lean_object* v_a_971_; lean_object* v___x_972_; 
v_a_971_ = lean_ctor_get(v_____do__lift_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref(v_____do__lift_970_);
v___x_972_ = lean_apply_2(v_toPure_969_, lean_box(0), v_a_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg(lean_object* v_inst_973_, lean_object* v_m_974_, lean_object* v_init_975_, lean_object* v_f_976_){
_start:
{
lean_object* v_toApplicative_977_; lean_object* v_toBind_978_; lean_object* v_toPure_979_; lean_object* v___f_980_; lean_object* v___x_981_; lean_object* v___f_982_; lean_object* v___x_983_; 
v_toApplicative_977_ = lean_ctor_get(v_inst_973_, 0);
v_toBind_978_ = lean_ctor_get(v_inst_973_, 1);
lean_inc(v_toBind_978_);
v_toPure_979_ = lean_ctor_get(v_toApplicative_977_, 1);
lean_inc(v_toPure_979_);
v___f_980_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_980_, 0, v_f_976_);
v___x_981_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_973_, v___f_980_, v_init_975_, v_m_974_);
v___f_982_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_982_, 0, v_toPure_979_);
v___x_983_ = lean_apply_4(v_toBind_978_, lean_box(0), lean_box(0), v___x_981_, v___f_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1(lean_object* v_m_984_, lean_object* v_inst_985_, lean_object* v_00_u03b2_986_, lean_object* v_m_987_, lean_object* v_init_988_, lean_object* v_f_989_){
_start:
{
lean_object* v_toApplicative_990_; lean_object* v_toBind_991_; lean_object* v_toPure_992_; lean_object* v___f_993_; lean_object* v___x_994_; lean_object* v___f_995_; lean_object* v___x_996_; 
v_toApplicative_990_ = lean_ctor_get(v_inst_985_, 0);
v_toBind_991_ = lean_ctor_get(v_inst_985_, 1);
lean_inc(v_toBind_991_);
v_toPure_992_ = lean_ctor_get(v_toApplicative_990_, 1);
lean_inc(v_toPure_992_);
v___f_993_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_993_, 0, v_f_989_);
v___x_994_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_985_, v___f_993_, v_init_988_, v_m_987_);
v___f_995_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_995_, 0, v_toPure_992_);
v___x_996_ = lean_apply_4(v_toBind_991_, lean_box(0), lean_box(0), v___x_994_, v___f_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___redArg(lean_object* v_inst_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_998_, 0, lean_box(0));
lean_closure_set(v___x_998_, 1, v_inst_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad(lean_object* v_m_999_, lean_object* v_inst_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1001_, 0, lean_box(0));
lean_closure_set(v___x_1001_, 1, v_inst_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object* v_s_1002_, lean_object* v_fvarId_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_fvarId_1003_, v_s_1002_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_box(0);
v___x_1006_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1003_, v___x_1005_, v_s_1002_);
return v___x_1006_;
}
else
{
lean_dec(v_fvarId_1003_);
return v_s_1002_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(lean_object* v_init_1007_, lean_object* v_x_1008_){
_start:
{
if (lean_obj_tag(v_x_1008_) == 0)
{
lean_object* v_k_1009_; lean_object* v_l_1010_; lean_object* v_r_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_k_1009_ = lean_ctor_get(v_x_1008_, 1);
lean_inc(v_k_1009_);
v_l_1010_ = lean_ctor_get(v_x_1008_, 3);
lean_inc(v_l_1010_);
v_r_1011_ = lean_ctor_get(v_x_1008_, 4);
lean_inc(v_r_1011_);
lean_dec_ref_known(v_x_1008_, 5);
v___x_1012_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_1007_, v_l_1010_);
v___x_1013_ = l_Lean_FVarIdSet_insert(v___x_1012_, v_k_1009_);
v_init_1007_ = v___x_1013_;
v_x_1008_ = v_r_1011_;
goto _start;
}
else
{
return v_init_1007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_union(lean_object* v_vs_u2081_1015_, lean_object* v_vs_u2082_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_vs_u2082_1016_, v_vs_u2081_1015_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0(lean_object* v_init_1018_, lean_object* v_t_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_1018_, v_t_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList(lean_object* v_l_1021_){
_start:
{
lean_object* v___f_1022_; lean_object* v___x_1023_; 
v___f_1022_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1023_ = l_Std_TreeSet_ofList___redArg(v_l_1021_, v___f_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList___boxed(lean_object* v_l_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_FVarIdSet_ofList(v_l_1024_);
lean_dec(v_l_1024_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object* v_l_1026_){
_start:
{
lean_object* v___f_1027_; lean_object* v___x_1028_; 
v___f_1027_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1028_ = l_Std_TreeSet_ofArray___redArg(v_l_1026_, v___f_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object* v_l_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_FVarIdSet_ofArray(v_l_1029_);
lean_dec_ref(v_l_1029_);
return v_res_1030_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_unsigned_to_nat(16u);
v___x_1033_ = lean_mk_array(v___x_1032_, v___x_1031_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0);
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v___x_1034_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1037_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet(void){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet(void){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object* v_s_1041_, lean_object* v_fvarId_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1042_, v_a_1043_, v_s_1041_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object* v_00_u03b1_1045_, lean_object* v_s_1046_, lean_object* v_fvarId_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1047_, v_a_1048_, v_s_1046_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1(lean_object* v_00_u03b1_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_box(1);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* v_00_u03b1_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_box(1);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* v_00_u03b1_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_box(1);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId_default(void){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_box(0);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId(void){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_box(0);
return v___x_1057_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMVarId_beq(lean_object* v_x_1058_, lean_object* v_x_1059_){
_start:
{
uint8_t v___x_1060_; 
v___x_1060_ = lean_name_eq(v_x_1058_, v_x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
uint8_t v_res_1063_; lean_object* v_r_1064_; 
v_res_1063_ = l_Lean_instBEqMVarId_beq(v_x_1061_, v_x_1062_);
lean_dec(v_x_1062_);
lean_dec(v_x_1061_);
v_r_1064_ = lean_box(v_res_1063_);
return v_r_1064_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableMVarId_hash(lean_object* v_x_1067_){
_start:
{
uint64_t v___x_1068_; 
v___x_1068_ = 0ULL;
if (lean_obj_tag(v_x_1067_) == 0)
{
uint64_t v___x_1069_; 
v___x_1069_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__1, &l_Lean_instHashableFVarId_hash___closed__1_once, _init_l_Lean_instHashableFVarId_hash___closed__1);
return v___x_1069_;
}
else
{
uint64_t v_hash_1070_; uint64_t v___x_1071_; 
v_hash_1070_ = lean_ctor_get_uint64(v_x_1067_, sizeof(void*)*2);
v___x_1071_ = lean_uint64_mix_hash(v___x_1068_, v_hash_1070_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object* v_x_1072_){
_start:
{
uint64_t v_res_1073_; lean_object* v_r_1074_; 
v_res_1073_ = l_Lean_instHashableMVarId_hash(v_x_1072_);
lean_dec(v_x_1072_);
v_r_1074_ = lean_box_uint64(v_res_1073_);
return v_r_1074_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_box(1);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet(void){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_box(1);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_box(1);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet(void){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_box(1);
return v___x_1081_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object* v_k_1082_, lean_object* v_t_1083_){
_start:
{
if (lean_obj_tag(v_t_1083_) == 0)
{
lean_object* v_k_1084_; lean_object* v_l_1085_; lean_object* v_r_1086_; uint8_t v___x_1087_; 
v_k_1084_ = lean_ctor_get(v_t_1083_, 1);
v_l_1085_ = lean_ctor_get(v_t_1083_, 3);
v_r_1086_ = lean_ctor_get(v_t_1083_, 4);
v___x_1087_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1082_, v_k_1084_);
switch(v___x_1087_)
{
case 0:
{
v_t_1083_ = v_l_1085_;
goto _start;
}
case 1:
{
uint8_t v___x_1089_; 
v___x_1089_ = 1;
return v___x_1089_;
}
default: 
{
v_t_1083_ = v_r_1086_;
goto _start;
}
}
}
else
{
uint8_t v___x_1091_; 
v___x_1091_ = 0;
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object* v_k_1092_, lean_object* v_t_1093_){
_start:
{
uint8_t v_res_1094_; lean_object* v_r_1095_; 
v_res_1094_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1092_, v_t_1093_);
lean_dec(v_t_1093_);
lean_dec(v_k_1092_);
v_r_1095_ = lean_box(v_res_1094_);
return v_r_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object* v_k_1096_, lean_object* v_v_1097_, lean_object* v_t_1098_){
_start:
{
if (lean_obj_tag(v_t_1098_) == 0)
{
lean_object* v_size_1099_; lean_object* v_k_1100_; lean_object* v_v_1101_; lean_object* v_l_1102_; lean_object* v_r_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1383_; 
v_size_1099_ = lean_ctor_get(v_t_1098_, 0);
v_k_1100_ = lean_ctor_get(v_t_1098_, 1);
v_v_1101_ = lean_ctor_get(v_t_1098_, 2);
v_l_1102_ = lean_ctor_get(v_t_1098_, 3);
v_r_1103_ = lean_ctor_get(v_t_1098_, 4);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_t_1098_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1105_ = v_t_1098_;
v_isShared_1106_ = v_isSharedCheck_1383_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_r_1103_);
lean_inc(v_l_1102_);
lean_inc(v_v_1101_);
lean_inc(v_k_1100_);
lean_inc(v_size_1099_);
lean_dec(v_t_1098_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1383_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
uint8_t v___x_1107_; 
v___x_1107_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1096_, v_k_1100_);
switch(v___x_1107_)
{
case 0:
{
lean_object* v_impl_1108_; lean_object* v___x_1109_; 
lean_dec(v_size_1099_);
v_impl_1108_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1096_, v_v_1097_, v_l_1102_);
v___x_1109_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1103_) == 0)
{
lean_object* v_size_1110_; lean_object* v_size_1111_; lean_object* v_k_1112_; lean_object* v_v_1113_; lean_object* v_l_1114_; lean_object* v_r_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v_size_1110_ = lean_ctor_get(v_r_1103_, 0);
v_size_1111_ = lean_ctor_get(v_impl_1108_, 0);
lean_inc(v_size_1111_);
v_k_1112_ = lean_ctor_get(v_impl_1108_, 1);
lean_inc(v_k_1112_);
v_v_1113_ = lean_ctor_get(v_impl_1108_, 2);
lean_inc(v_v_1113_);
v_l_1114_ = lean_ctor_get(v_impl_1108_, 3);
lean_inc(v_l_1114_);
v_r_1115_ = lean_ctor_get(v_impl_1108_, 4);
lean_inc(v_r_1115_);
v___x_1116_ = lean_unsigned_to_nat(3u);
v___x_1117_ = lean_nat_mul(v___x_1116_, v_size_1110_);
v___x_1118_ = lean_nat_dec_lt(v___x_1117_, v_size_1111_);
lean_dec(v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
lean_dec(v_r_1115_);
lean_dec(v_l_1114_);
lean_dec(v_v_1113_);
lean_dec(v_k_1112_);
v___x_1119_ = lean_nat_add(v___x_1109_, v_size_1111_);
lean_dec(v_size_1111_);
v___x_1120_ = lean_nat_add(v___x_1119_, v_size_1110_);
lean_dec(v___x_1119_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 3, v_impl_1108_);
lean_ctor_set(v___x_1105_, 0, v___x_1120_);
v___x_1122_ = v___x_1105_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1123_, 3, v_impl_1108_);
lean_ctor_set(v_reuseFailAlloc_1123_, 4, v_r_1103_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
else
{
lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1189_; 
v_isSharedCheck_1189_ = !lean_is_exclusive(v_impl_1108_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; lean_object* v_unused_1191_; lean_object* v_unused_1192_; lean_object* v_unused_1193_; lean_object* v_unused_1194_; 
v_unused_1190_ = lean_ctor_get(v_impl_1108_, 4);
lean_dec(v_unused_1190_);
v_unused_1191_ = lean_ctor_get(v_impl_1108_, 3);
lean_dec(v_unused_1191_);
v_unused_1192_ = lean_ctor_get(v_impl_1108_, 2);
lean_dec(v_unused_1192_);
v_unused_1193_ = lean_ctor_get(v_impl_1108_, 1);
lean_dec(v_unused_1193_);
v_unused_1194_ = lean_ctor_get(v_impl_1108_, 0);
lean_dec(v_unused_1194_);
v___x_1125_ = v_impl_1108_;
v_isShared_1126_ = v_isSharedCheck_1189_;
goto v_resetjp_1124_;
}
else
{
lean_dec(v_impl_1108_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1189_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_size_1127_; lean_object* v_size_1128_; lean_object* v_k_1129_; lean_object* v_v_1130_; lean_object* v_l_1131_; lean_object* v_r_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_size_1127_ = lean_ctor_get(v_l_1114_, 0);
v_size_1128_ = lean_ctor_get(v_r_1115_, 0);
v_k_1129_ = lean_ctor_get(v_r_1115_, 1);
v_v_1130_ = lean_ctor_get(v_r_1115_, 2);
v_l_1131_ = lean_ctor_get(v_r_1115_, 3);
v_r_1132_ = lean_ctor_get(v_r_1115_, 4);
v___x_1133_ = lean_unsigned_to_nat(2u);
v___x_1134_ = lean_nat_mul(v___x_1133_, v_size_1127_);
v___x_1135_ = lean_nat_dec_lt(v_size_1128_, v___x_1134_);
lean_dec(v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1164_; 
lean_inc(v_r_1132_);
lean_inc(v_l_1131_);
lean_inc(v_v_1130_);
lean_inc(v_k_1129_);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_r_1115_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; lean_object* v_unused_1166_; lean_object* v_unused_1167_; lean_object* v_unused_1168_; lean_object* v_unused_1169_; 
v_unused_1165_ = lean_ctor_get(v_r_1115_, 4);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_r_1115_, 3);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v_r_1115_, 2);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_r_1115_, 1);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_r_1115_, 0);
lean_dec(v_unused_1169_);
v___x_1137_ = v_r_1115_;
v_isShared_1138_ = v_isSharedCheck_1164_;
goto v_resetjp_1136_;
}
else
{
lean_dec(v_r_1115_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1164_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___x_1152_; lean_object* v___y_1154_; 
v___x_1139_ = lean_nat_add(v___x_1109_, v_size_1111_);
lean_dec(v_size_1111_);
v___x_1140_ = lean_nat_add(v___x_1139_, v_size_1110_);
lean_dec(v___x_1139_);
v___x_1152_ = lean_nat_add(v___x_1109_, v_size_1127_);
if (lean_obj_tag(v_l_1131_) == 0)
{
lean_object* v_size_1162_; 
v_size_1162_ = lean_ctor_get(v_l_1131_, 0);
lean_inc(v_size_1162_);
v___y_1154_ = v_size_1162_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_unsigned_to_nat(0u);
v___y_1154_ = v___x_1163_;
goto v___jp_1153_;
}
v___jp_1141_:
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = lean_nat_add(v___y_1142_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec(v___y_1142_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 4, v_r_1103_);
lean_ctor_set(v___x_1137_, 3, v_r_1132_);
lean_ctor_set(v___x_1137_, 2, v_v_1101_);
lean_ctor_set(v___x_1137_, 1, v_k_1100_);
lean_ctor_set(v___x_1137_, 0, v___x_1145_);
v___x_1147_ = v___x_1137_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_r_1132_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_r_1103_);
v___x_1147_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1149_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 4, v___x_1147_);
lean_ctor_set(v___x_1125_, 3, v___y_1143_);
lean_ctor_set(v___x_1125_, 2, v_v_1130_);
lean_ctor_set(v___x_1125_, 1, v_k_1129_);
lean_ctor_set(v___x_1125_, 0, v___x_1140_);
v___x_1149_ = v___x_1125_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_k_1129_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v_v_1130_);
lean_ctor_set(v_reuseFailAlloc_1150_, 3, v___y_1143_);
lean_ctor_set(v_reuseFailAlloc_1150_, 4, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
v___jp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_nat_add(v___x_1152_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec(v___x_1152_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 4, v_l_1131_);
lean_ctor_set(v___x_1105_, 3, v_l_1114_);
lean_ctor_set(v___x_1105_, 2, v_v_1113_);
lean_ctor_set(v___x_1105_, 1, v_k_1112_);
lean_ctor_set(v___x_1105_, 0, v___x_1155_);
v___x_1157_ = v___x_1105_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_k_1112_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_v_1113_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_l_1114_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_l_1131_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_nat_add(v___x_1109_, v_size_1110_);
if (lean_obj_tag(v_r_1132_) == 0)
{
lean_object* v_size_1159_; 
v_size_1159_ = lean_ctor_get(v_r_1132_, 0);
lean_inc(v_size_1159_);
v___y_1142_ = v___x_1158_;
v___y_1143_ = v___x_1157_;
v___y_1144_ = v_size_1159_;
goto v___jp_1141_;
}
else
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_unsigned_to_nat(0u);
v___y_1142_ = v___x_1158_;
v___y_1143_ = v___x_1157_;
v___y_1144_ = v___x_1160_;
goto v___jp_1141_;
}
}
}
}
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
lean_del_object(v___x_1105_);
v___x_1170_ = lean_nat_add(v___x_1109_, v_size_1111_);
lean_dec(v_size_1111_);
v___x_1171_ = lean_nat_add(v___x_1170_, v_size_1110_);
lean_dec(v___x_1170_);
v___x_1172_ = lean_nat_add(v___x_1109_, v_size_1110_);
v___x_1173_ = lean_nat_add(v___x_1172_, v_size_1128_);
lean_dec(v___x_1172_);
lean_inc_ref(v_r_1103_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 4, v_r_1103_);
lean_ctor_set(v___x_1125_, 3, v_r_1115_);
lean_ctor_set(v___x_1125_, 2, v_v_1101_);
lean_ctor_set(v___x_1125_, 1, v_k_1100_);
lean_ctor_set(v___x_1125_, 0, v___x_1173_);
v___x_1175_ = v___x_1125_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1188_, 3, v_r_1115_);
lean_ctor_set(v_reuseFailAlloc_1188_, 4, v_r_1103_);
v___x_1175_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
v_isSharedCheck_1182_ = !lean_is_exclusive(v_r_1103_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; lean_object* v_unused_1184_; lean_object* v_unused_1185_; lean_object* v_unused_1186_; lean_object* v_unused_1187_; 
v_unused_1183_ = lean_ctor_get(v_r_1103_, 4);
lean_dec(v_unused_1183_);
v_unused_1184_ = lean_ctor_get(v_r_1103_, 3);
lean_dec(v_unused_1184_);
v_unused_1185_ = lean_ctor_get(v_r_1103_, 2);
lean_dec(v_unused_1185_);
v_unused_1186_ = lean_ctor_get(v_r_1103_, 1);
lean_dec(v_unused_1186_);
v_unused_1187_ = lean_ctor_get(v_r_1103_, 0);
lean_dec(v_unused_1187_);
v___x_1177_ = v_r_1103_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_dec(v_r_1103_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 4, v___x_1175_);
lean_ctor_set(v___x_1177_, 3, v_l_1114_);
lean_ctor_set(v___x_1177_, 2, v_v_1113_);
lean_ctor_set(v___x_1177_, 1, v_k_1112_);
lean_ctor_set(v___x_1177_, 0, v___x_1171_);
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_k_1112_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_v_1113_);
lean_ctor_set(v_reuseFailAlloc_1181_, 3, v_l_1114_);
lean_ctor_set(v_reuseFailAlloc_1181_, 4, v___x_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1195_; 
v_l_1195_ = lean_ctor_get(v_impl_1108_, 3);
lean_inc(v_l_1195_);
if (lean_obj_tag(v_l_1195_) == 0)
{
lean_object* v_r_1196_; lean_object* v_k_1197_; lean_object* v_v_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1209_; 
v_r_1196_ = lean_ctor_get(v_impl_1108_, 4);
v_k_1197_ = lean_ctor_get(v_impl_1108_, 1);
v_v_1198_ = lean_ctor_get(v_impl_1108_, 2);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_impl_1108_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; lean_object* v_unused_1211_; 
v_unused_1210_ = lean_ctor_get(v_impl_1108_, 3);
lean_dec(v_unused_1210_);
v_unused_1211_ = lean_ctor_get(v_impl_1108_, 0);
lean_dec(v_unused_1211_);
v___x_1200_ = v_impl_1108_;
v_isShared_1201_ = v_isSharedCheck_1209_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_r_1196_);
lean_inc(v_v_1198_);
lean_inc(v_k_1197_);
lean_dec(v_impl_1108_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1209_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1202_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1196_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 3, v_r_1196_);
lean_ctor_set(v___x_1200_, 2, v_v_1101_);
lean_ctor_set(v___x_1200_, 1, v_k_1100_);
lean_ctor_set(v___x_1200_, 0, v___x_1109_);
v___x_1204_ = v___x_1200_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_r_1196_);
lean_ctor_set(v_reuseFailAlloc_1208_, 4, v_r_1196_);
v___x_1204_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 4, v___x_1204_);
lean_ctor_set(v___x_1105_, 3, v_l_1195_);
lean_ctor_set(v___x_1105_, 2, v_v_1198_);
lean_ctor_set(v___x_1105_, 1, v_k_1197_);
lean_ctor_set(v___x_1105_, 0, v___x_1202_);
v___x_1206_ = v___x_1105_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_k_1197_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_v_1198_);
lean_ctor_set(v_reuseFailAlloc_1207_, 3, v_l_1195_);
lean_ctor_set(v_reuseFailAlloc_1207_, 4, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_r_1212_; 
v_r_1212_ = lean_ctor_get(v_impl_1108_, 4);
lean_inc(v_r_1212_);
if (lean_obj_tag(v_r_1212_) == 0)
{
lean_object* v_k_1213_; lean_object* v_v_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1237_; 
v_k_1213_ = lean_ctor_get(v_impl_1108_, 1);
v_v_1214_ = lean_ctor_get(v_impl_1108_, 2);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_impl_1108_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; lean_object* v_unused_1239_; lean_object* v_unused_1240_; 
v_unused_1238_ = lean_ctor_get(v_impl_1108_, 4);
lean_dec(v_unused_1238_);
v_unused_1239_ = lean_ctor_get(v_impl_1108_, 3);
lean_dec(v_unused_1239_);
v_unused_1240_ = lean_ctor_get(v_impl_1108_, 0);
lean_dec(v_unused_1240_);
v___x_1216_ = v_impl_1108_;
v_isShared_1217_ = v_isSharedCheck_1237_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_v_1214_);
lean_inc(v_k_1213_);
lean_dec(v_impl_1108_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1237_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_k_1218_; lean_object* v_v_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1233_; 
v_k_1218_ = lean_ctor_get(v_r_1212_, 1);
v_v_1219_ = lean_ctor_get(v_r_1212_, 2);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_r_1212_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; lean_object* v_unused_1235_; lean_object* v_unused_1236_; 
v_unused_1234_ = lean_ctor_get(v_r_1212_, 4);
lean_dec(v_unused_1234_);
v_unused_1235_ = lean_ctor_get(v_r_1212_, 3);
lean_dec(v_unused_1235_);
v_unused_1236_ = lean_ctor_get(v_r_1212_, 0);
lean_dec(v_unused_1236_);
v___x_1221_ = v_r_1212_;
v_isShared_1222_ = v_isSharedCheck_1233_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_v_1219_);
lean_inc(v_k_1218_);
lean_dec(v_r_1212_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1233_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = lean_unsigned_to_nat(3u);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v_l_1195_);
lean_ctor_set(v___x_1221_, 3, v_l_1195_);
lean_ctor_set(v___x_1221_, 2, v_v_1214_);
lean_ctor_set(v___x_1221_, 1, v_k_1213_);
lean_ctor_set(v___x_1221_, 0, v___x_1109_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_k_1213_);
lean_ctor_set(v_reuseFailAlloc_1232_, 2, v_v_1214_);
lean_ctor_set(v_reuseFailAlloc_1232_, 3, v_l_1195_);
lean_ctor_set(v_reuseFailAlloc_1232_, 4, v_l_1195_);
v___x_1225_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 4, v_l_1195_);
lean_ctor_set(v___x_1216_, 2, v_v_1101_);
lean_ctor_set(v___x_1216_, 1, v_k_1100_);
lean_ctor_set(v___x_1216_, 0, v___x_1109_);
v___x_1227_ = v___x_1216_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1231_, 3, v_l_1195_);
lean_ctor_set(v_reuseFailAlloc_1231_, 4, v_l_1195_);
v___x_1227_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1229_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 4, v___x_1227_);
lean_ctor_set(v___x_1105_, 3, v___x_1225_);
lean_ctor_set(v___x_1105_, 2, v_v_1219_);
lean_ctor_set(v___x_1105_, 1, v_k_1218_);
lean_ctor_set(v___x_1105_, 0, v___x_1223_);
v___x_1229_ = v___x_1105_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_k_1218_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_v_1219_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = lean_unsigned_to_nat(2u);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 4, v_r_1212_);
lean_ctor_set(v___x_1105_, 3, v_impl_1108_);
lean_ctor_set(v___x_1105_, 0, v___x_1241_);
v___x_1243_ = v___x_1105_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v_impl_1108_);
lean_ctor_set(v_reuseFailAlloc_1244_, 4, v_r_1212_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1246_; 
lean_dec(v_v_1101_);
lean_dec(v_k_1100_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 2, v_v_1097_);
lean_ctor_set(v___x_1105_, 1, v_k_1096_);
v___x_1246_ = v___x_1105_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_size_1099_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v_l_1102_);
lean_ctor_set(v_reuseFailAlloc_1247_, 4, v_r_1103_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
default: 
{
lean_object* v_impl_1248_; lean_object* v___x_1249_; 
lean_dec(v_size_1099_);
v_impl_1248_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1096_, v_v_1097_, v_r_1103_);
v___x_1249_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1102_) == 0)
{
lean_object* v_size_1250_; lean_object* v_size_1251_; lean_object* v_k_1252_; lean_object* v_v_1253_; lean_object* v_l_1254_; lean_object* v_r_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_size_1250_ = lean_ctor_get(v_l_1102_, 0);
v_size_1251_ = lean_ctor_get(v_impl_1248_, 0);
lean_inc(v_size_1251_);
v_k_1252_ = lean_ctor_get(v_impl_1248_, 1);
lean_inc(v_k_1252_);
v_v_1253_ = lean_ctor_get(v_impl_1248_, 2);
lean_inc(v_v_1253_);
v_l_1254_ = lean_ctor_get(v_impl_1248_, 3);
lean_inc(v_l_1254_);
v_r_1255_ = lean_ctor_get(v_impl_1248_, 4);
lean_inc(v_r_1255_);
v___x_1256_ = lean_unsigned_to_nat(3u);
v___x_1257_ = lean_nat_mul(v___x_1256_, v_size_1250_);
v___x_1258_ = lean_nat_dec_lt(v___x_1257_, v_size_1251_);
lean_dec(v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
lean_dec(v_r_1255_);
lean_dec(v_l_1254_);
lean_dec(v_v_1253_);
lean_dec(v_k_1252_);
v___x_1259_ = lean_nat_add(v___x_1249_, v_size_1250_);
v___x_1260_ = lean_nat_add(v___x_1259_, v_size_1251_);
lean_dec(v_size_1251_);
lean_dec(v___x_1259_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 4, v_impl_1248_);
lean_ctor_set(v___x_1105_, 0, v___x_1260_);
v___x_1262_ = v___x_1105_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v_l_1102_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v_impl_1248_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
else
{
lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1327_; 
v_isSharedCheck_1327_ = !lean_is_exclusive(v_impl_1248_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; lean_object* v_unused_1329_; lean_object* v_unused_1330_; lean_object* v_unused_1331_; lean_object* v_unused_1332_; 
v_unused_1328_ = lean_ctor_get(v_impl_1248_, 4);
lean_dec(v_unused_1328_);
v_unused_1329_ = lean_ctor_get(v_impl_1248_, 3);
lean_dec(v_unused_1329_);
v_unused_1330_ = lean_ctor_get(v_impl_1248_, 2);
lean_dec(v_unused_1330_);
v_unused_1331_ = lean_ctor_get(v_impl_1248_, 1);
lean_dec(v_unused_1331_);
v_unused_1332_ = lean_ctor_get(v_impl_1248_, 0);
lean_dec(v_unused_1332_);
v___x_1265_ = v_impl_1248_;
v_isShared_1266_ = v_isSharedCheck_1327_;
goto v_resetjp_1264_;
}
else
{
lean_dec(v_impl_1248_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1327_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v_size_1267_; lean_object* v_k_1268_; lean_object* v_v_1269_; lean_object* v_l_1270_; lean_object* v_r_1271_; lean_object* v_size_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v_size_1267_ = lean_ctor_get(v_l_1254_, 0);
v_k_1268_ = lean_ctor_get(v_l_1254_, 1);
v_v_1269_ = lean_ctor_get(v_l_1254_, 2);
v_l_1270_ = lean_ctor_get(v_l_1254_, 3);
v_r_1271_ = lean_ctor_get(v_l_1254_, 4);
v_size_1272_ = lean_ctor_get(v_r_1255_, 0);
v___x_1273_ = lean_unsigned_to_nat(2u);
v___x_1274_ = lean_nat_mul(v___x_1273_, v_size_1272_);
v___x_1275_ = lean_nat_dec_lt(v_size_1267_, v___x_1274_);
lean_dec(v___x_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1303_; 
lean_inc(v_r_1271_);
lean_inc(v_l_1270_);
lean_inc(v_v_1269_);
lean_inc(v_k_1268_);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_l_1254_);
if (v_isSharedCheck_1303_ == 0)
{
lean_object* v_unused_1304_; lean_object* v_unused_1305_; lean_object* v_unused_1306_; lean_object* v_unused_1307_; lean_object* v_unused_1308_; 
v_unused_1304_ = lean_ctor_get(v_l_1254_, 4);
lean_dec(v_unused_1304_);
v_unused_1305_ = lean_ctor_get(v_l_1254_, 3);
lean_dec(v_unused_1305_);
v_unused_1306_ = lean_ctor_get(v_l_1254_, 2);
lean_dec(v_unused_1306_);
v_unused_1307_ = lean_ctor_get(v_l_1254_, 1);
lean_dec(v_unused_1307_);
v_unused_1308_ = lean_ctor_get(v_l_1254_, 0);
lean_dec(v_unused_1308_);
v___x_1277_ = v_l_1254_;
v_isShared_1278_ = v_isSharedCheck_1303_;
goto v_resetjp_1276_;
}
else
{
lean_dec(v_l_1254_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1303_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1293_; 
v___x_1279_ = lean_nat_add(v___x_1249_, v_size_1250_);
v___x_1280_ = lean_nat_add(v___x_1279_, v_size_1251_);
lean_dec(v_size_1251_);
if (lean_obj_tag(v_l_1270_) == 0)
{
lean_object* v_size_1301_; 
v_size_1301_ = lean_ctor_get(v_l_1270_, 0);
lean_inc(v_size_1301_);
v___y_1293_ = v_size_1301_;
goto v___jp_1292_;
}
else
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_unsigned_to_nat(0u);
v___y_1293_ = v___x_1302_;
goto v___jp_1292_;
}
v___jp_1281_:
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = lean_nat_add(v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec(v___y_1283_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 4, v_r_1255_);
lean_ctor_set(v___x_1277_, 3, v_r_1271_);
lean_ctor_set(v___x_1277_, 2, v_v_1253_);
lean_ctor_set(v___x_1277_, 1, v_k_1252_);
lean_ctor_set(v___x_1277_, 0, v___x_1285_);
v___x_1287_ = v___x_1277_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_k_1252_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_v_1253_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v_r_1271_);
lean_ctor_set(v_reuseFailAlloc_1291_, 4, v_r_1255_);
v___x_1287_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1289_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 4, v___x_1287_);
lean_ctor_set(v___x_1265_, 3, v___y_1282_);
lean_ctor_set(v___x_1265_, 2, v_v_1269_);
lean_ctor_set(v___x_1265_, 1, v_k_1268_);
lean_ctor_set(v___x_1265_, 0, v___x_1280_);
v___x_1289_ = v___x_1265_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1280_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_k_1268_);
lean_ctor_set(v_reuseFailAlloc_1290_, 2, v_v_1269_);
lean_ctor_set(v_reuseFailAlloc_1290_, 3, v___y_1282_);
lean_ctor_set(v_reuseFailAlloc_1290_, 4, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
v___jp_1292_:
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1294_ = lean_nat_add(v___x_1279_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec(v___x_1279_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 4, v_l_1270_);
lean_ctor_set(v___x_1105_, 0, v___x_1294_);
v___x_1296_ = v___x_1105_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1300_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1300_, 3, v_l_1102_);
lean_ctor_set(v_reuseFailAlloc_1300_, 4, v_l_1270_);
v___x_1296_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_nat_add(v___x_1249_, v_size_1272_);
if (lean_obj_tag(v_r_1271_) == 0)
{
lean_object* v_size_1298_; 
v_size_1298_ = lean_ctor_get(v_r_1271_, 0);
lean_inc(v_size_1298_);
v___y_1282_ = v___x_1296_;
v___y_1283_ = v___x_1297_;
v___y_1284_ = v_size_1298_;
goto v___jp_1281_;
}
else
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_unsigned_to_nat(0u);
v___y_1282_ = v___x_1296_;
v___y_1283_ = v___x_1297_;
v___y_1284_ = v___x_1299_;
goto v___jp_1281_;
}
}
}
}
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
lean_del_object(v___x_1105_);
v___x_1309_ = lean_nat_add(v___x_1249_, v_size_1250_);
v___x_1310_ = lean_nat_add(v___x_1309_, v_size_1251_);
lean_dec(v_size_1251_);
v___x_1311_ = lean_nat_add(v___x_1309_, v_size_1267_);
lean_dec(v___x_1309_);
lean_inc_ref(v_l_1102_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 4, v_l_1254_);
lean_ctor_set(v___x_1265_, 3, v_l_1102_);
lean_ctor_set(v___x_1265_, 2, v_v_1101_);
lean_ctor_set(v___x_1265_, 1, v_k_1100_);
lean_ctor_set(v___x_1265_, 0, v___x_1311_);
v___x_1313_ = v___x_1265_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1326_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1326_, 3, v_l_1102_);
lean_ctor_set(v_reuseFailAlloc_1326_, 4, v_l_1254_);
v___x_1313_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
v_isSharedCheck_1320_ = !lean_is_exclusive(v_l_1102_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; lean_object* v_unused_1322_; lean_object* v_unused_1323_; lean_object* v_unused_1324_; lean_object* v_unused_1325_; 
v_unused_1321_ = lean_ctor_get(v_l_1102_, 4);
lean_dec(v_unused_1321_);
v_unused_1322_ = lean_ctor_get(v_l_1102_, 3);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v_l_1102_, 2);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v_l_1102_, 1);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v_l_1102_, 0);
lean_dec(v_unused_1325_);
v___x_1315_ = v_l_1102_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_dec(v_l_1102_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 4, v_r_1255_);
lean_ctor_set(v___x_1315_, 3, v___x_1313_);
lean_ctor_set(v___x_1315_, 2, v_v_1253_);
lean_ctor_set(v___x_1315_, 1, v_k_1252_);
lean_ctor_set(v___x_1315_, 0, v___x_1310_);
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_k_1252_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_v_1253_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_r_1255_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1333_; 
v_l_1333_ = lean_ctor_get(v_impl_1248_, 3);
lean_inc(v_l_1333_);
if (lean_obj_tag(v_l_1333_) == 0)
{
lean_object* v_r_1334_; lean_object* v_k_1335_; lean_object* v_v_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1359_; 
v_r_1334_ = lean_ctor_get(v_impl_1248_, 4);
v_k_1335_ = lean_ctor_get(v_impl_1248_, 1);
v_v_1336_ = lean_ctor_get(v_impl_1248_, 2);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_impl_1248_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; lean_object* v_unused_1361_; 
v_unused_1360_ = lean_ctor_get(v_impl_1248_, 3);
lean_dec(v_unused_1360_);
v_unused_1361_ = lean_ctor_get(v_impl_1248_, 0);
lean_dec(v_unused_1361_);
v___x_1338_ = v_impl_1248_;
v_isShared_1339_ = v_isSharedCheck_1359_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_r_1334_);
lean_inc(v_v_1336_);
lean_inc(v_k_1335_);
lean_dec(v_impl_1248_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1359_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v_k_1340_; lean_object* v_v_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1355_; 
v_k_1340_ = lean_ctor_get(v_l_1333_, 1);
v_v_1341_ = lean_ctor_get(v_l_1333_, 2);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_l_1333_);
if (v_isSharedCheck_1355_ == 0)
{
lean_object* v_unused_1356_; lean_object* v_unused_1357_; lean_object* v_unused_1358_; 
v_unused_1356_ = lean_ctor_get(v_l_1333_, 4);
lean_dec(v_unused_1356_);
v_unused_1357_ = lean_ctor_get(v_l_1333_, 3);
lean_dec(v_unused_1357_);
v_unused_1358_ = lean_ctor_get(v_l_1333_, 0);
lean_dec(v_unused_1358_);
v___x_1343_ = v_l_1333_;
v_isShared_1344_ = v_isSharedCheck_1355_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_v_1341_);
lean_inc(v_k_1340_);
lean_dec(v_l_1333_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1355_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1345_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1334_, 2);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v_r_1334_);
lean_ctor_set(v___x_1343_, 3, v_r_1334_);
lean_ctor_set(v___x_1343_, 2, v_v_1101_);
lean_ctor_set(v___x_1343_, 1, v_k_1100_);
lean_ctor_set(v___x_1343_, 0, v___x_1249_);
v___x_1347_ = v___x_1343_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1354_, 3, v_r_1334_);
lean_ctor_set(v_reuseFailAlloc_1354_, 4, v_r_1334_);
v___x_1347_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1349_; 
lean_inc(v_r_1334_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 3, v_r_1334_);
lean_ctor_set(v___x_1338_, 0, v___x_1249_);
v___x_1349_ = v___x_1338_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_k_1335_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v_v_1336_);
lean_ctor_set(v_reuseFailAlloc_1353_, 3, v_r_1334_);
lean_ctor_set(v_reuseFailAlloc_1353_, 4, v_r_1334_);
v___x_1349_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1351_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 4, v___x_1349_);
lean_ctor_set(v___x_1105_, 3, v___x_1347_);
lean_ctor_set(v___x_1105_, 2, v_v_1341_);
lean_ctor_set(v___x_1105_, 1, v_k_1340_);
lean_ctor_set(v___x_1105_, 0, v___x_1345_);
v___x_1351_ = v___x_1105_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_k_1340_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_v_1341_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1352_, 4, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
}
else
{
lean_object* v_r_1362_; 
v_r_1362_ = lean_ctor_get(v_impl_1248_, 4);
lean_inc(v_r_1362_);
if (lean_obj_tag(v_r_1362_) == 0)
{
lean_object* v_k_1363_; lean_object* v_v_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1375_; 
v_k_1363_ = lean_ctor_get(v_impl_1248_, 1);
v_v_1364_ = lean_ctor_get(v_impl_1248_, 2);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_impl_1248_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; lean_object* v_unused_1377_; lean_object* v_unused_1378_; 
v_unused_1376_ = lean_ctor_get(v_impl_1248_, 4);
lean_dec(v_unused_1376_);
v_unused_1377_ = lean_ctor_get(v_impl_1248_, 3);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_impl_1248_, 0);
lean_dec(v_unused_1378_);
v___x_1366_ = v_impl_1248_;
v_isShared_1367_ = v_isSharedCheck_1375_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_v_1364_);
lean_inc(v_k_1363_);
lean_dec(v_impl_1248_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1375_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1368_ = lean_unsigned_to_nat(3u);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v_l_1333_);
lean_ctor_set(v___x_1366_, 2, v_v_1101_);
lean_ctor_set(v___x_1366_, 1, v_k_1100_);
lean_ctor_set(v___x_1366_, 0, v___x_1249_);
v___x_1370_ = v___x_1366_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_l_1333_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v_l_1333_);
v___x_1370_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1372_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 4, v_r_1362_);
lean_ctor_set(v___x_1105_, 3, v___x_1370_);
lean_ctor_set(v___x_1105_, 2, v_v_1364_);
lean_ctor_set(v___x_1105_, 1, v_k_1363_);
lean_ctor_set(v___x_1105_, 0, v___x_1368_);
v___x_1372_ = v___x_1105_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1363_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1364_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_r_1362_);
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
else
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1379_ = lean_unsigned_to_nat(2u);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 4, v_impl_1248_);
lean_ctor_set(v___x_1105_, 3, v_r_1362_);
lean_ctor_set(v___x_1105_, 0, v___x_1379_);
v___x_1381_ = v___x_1105_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1382_, 3, v_r_1362_);
lean_ctor_set(v_reuseFailAlloc_1382_, 4, v_impl_1248_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
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
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
lean_ctor_set(v___x_1385_, 1, v_k_1096_);
lean_ctor_set(v___x_1385_, 2, v_v_1097_);
lean_ctor_set(v___x_1385_, 3, v_t_1098_);
lean_ctor_set(v___x_1385_, 4, v_t_1098_);
return v___x_1385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object* v_s_1386_, lean_object* v_mvarId_1387_){
_start:
{
uint8_t v___x_1388_; 
v___x_1388_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_mvarId_1387_, v_s_1386_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1387_, v___x_1389_, v_s_1386_);
return v___x_1390_;
}
else
{
lean_dec(v_mvarId_1387_);
return v_s_1386_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object* v_00_u03b2_1391_, lean_object* v_k_1392_, lean_object* v_t_1393_){
_start:
{
uint8_t v___x_1394_; 
v___x_1394_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1392_, v_t_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object* v_00_u03b2_1395_, lean_object* v_k_1396_, lean_object* v_t_1397_){
_start:
{
uint8_t v_res_1398_; lean_object* v_r_1399_; 
v_res_1398_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(v_00_u03b2_1395_, v_k_1396_, v_t_1397_);
lean_dec(v_t_1397_);
lean_dec(v_k_1396_);
v_r_1399_ = lean_box(v_res_1398_);
return v_r_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object* v_00_u03b2_1400_, lean_object* v_k_1401_, lean_object* v_v_1402_, lean_object* v_t_1403_, lean_object* v_hl_1404_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1401_, v_v_1402_, v_t_1403_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object* v_l_1406_){
_start:
{
lean_object* v___f_1407_; lean_object* v___x_1408_; 
v___f_1407_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1408_ = l_Std_TreeSet_ofList___redArg(v_l_1406_, v___f_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList___boxed(lean_object* v_l_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_MVarIdSet_ofList(v_l_1409_);
lean_dec(v_l_1409_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object* v_l_1411_){
_start:
{
lean_object* v___f_1412_; lean_object* v___x_1413_; 
v___f_1412_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1413_ = l_Std_TreeSet_ofArray___redArg(v_l_1411_, v___f_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object* v_l_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_MVarIdSet_ofArray(v_l_1414_);
lean_dec_ref(v_l_1414_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1416_, lean_object* v_m_1417_, lean_object* v_init_1418_, lean_object* v_f_1419_){
_start:
{
lean_object* v_toApplicative_1420_; lean_object* v_toBind_1421_; lean_object* v_toPure_1422_; lean_object* v___f_1423_; lean_object* v___x_1424_; lean_object* v___f_1425_; lean_object* v___x_1426_; 
v_toApplicative_1420_ = lean_ctor_get(v_inst_1416_, 0);
v_toBind_1421_ = lean_ctor_get(v_inst_1416_, 1);
lean_inc(v_toBind_1421_);
v_toPure_1422_ = lean_ctor_get(v_toApplicative_1420_, 1);
lean_inc(v_toPure_1422_);
v___f_1423_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1423_, 0, v_f_1419_);
v___x_1424_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1416_, v___f_1423_, v_init_1418_, v_m_1417_);
v___f_1425_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1425_, 0, v_toPure_1422_);
v___x_1426_ = lean_apply_4(v_toBind_1421_, lean_box(0), lean_box(0), v___x_1424_, v___f_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1(lean_object* v_m_1427_, lean_object* v_inst_1428_, lean_object* v_00_u03b2_1429_, lean_object* v_m_1430_, lean_object* v_init_1431_, lean_object* v_f_1432_){
_start:
{
lean_object* v_toApplicative_1433_; lean_object* v_toBind_1434_; lean_object* v_toPure_1435_; lean_object* v___f_1436_; lean_object* v___x_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; 
v_toApplicative_1433_ = lean_ctor_get(v_inst_1428_, 0);
v_toBind_1434_ = lean_ctor_get(v_inst_1428_, 1);
lean_inc(v_toBind_1434_);
v_toPure_1435_ = lean_ctor_get(v_toApplicative_1433_, 1);
lean_inc(v_toPure_1435_);
v___f_1436_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1436_, 0, v_f_1432_);
v___x_1437_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1428_, v___f_1436_, v_init_1431_, v_m_1430_);
v___f_1438_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1438_, 0, v_toPure_1435_);
v___x_1439_ = lean_apply_4(v_toBind_1434_, lean_box(0), lean_box(0), v___x_1437_, v___f_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object* v_inst_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1441_, 0, lean_box(0));
lean_closure_set(v___x_1441_, 1, v_inst_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object* v_m_1442_, lean_object* v_inst_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1444_, 0, lean_box(0));
lean_closure_set(v___x_1444_, 1, v_inst_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object* v_s_1445_, lean_object* v_mvarId_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1446_, v_a_1447_, v_s_1445_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object* v_00_u03b1_1449_, lean_object* v_s_1450_, lean_object* v_mvarId_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1451_, v_a_1452_, v_s_1450_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object* v_00_u03b1_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_box(1);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* v_00_u03b1_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_box(1);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_1458_, lean_object* v_a_1459_, lean_object* v_b_1460_, lean_object* v_c_1461_){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_a_1459_);
lean_ctor_set(v___x_1462_, 1, v_b_1460_);
v___x_1463_ = lean_apply_2(v_f_1458_, v___x_1462_, v_c_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1464_, lean_object* v_m_1465_, lean_object* v_init_1466_, lean_object* v_f_1467_){
_start:
{
lean_object* v_toApplicative_1468_; lean_object* v_toBind_1469_; lean_object* v_toPure_1470_; lean_object* v___f_1471_; lean_object* v___x_1472_; lean_object* v___f_1473_; lean_object* v___x_1474_; 
v_toApplicative_1468_ = lean_ctor_get(v_inst_1464_, 0);
v_toBind_1469_ = lean_ctor_get(v_inst_1464_, 1);
lean_inc(v_toBind_1469_);
v_toPure_1470_ = lean_ctor_get(v_toApplicative_1468_, 1);
lean_inc(v_toPure_1470_);
v___f_1471_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1471_, 0, v_f_1467_);
v___x_1472_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1464_, v___f_1471_, v_init_1466_, v_m_1465_);
v___f_1473_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1473_, 0, v_toPure_1470_);
v___x_1474_ = lean_apply_4(v_toBind_1469_, lean_box(0), lean_box(0), v___x_1472_, v___f_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object* v_m_1475_, lean_object* v_00_u03b1_1476_, lean_object* v_inst_1477_, lean_object* v_00_u03b2_1478_, lean_object* v_m_1479_, lean_object* v_init_1480_, lean_object* v_f_1481_){
_start:
{
lean_object* v_toApplicative_1482_; lean_object* v_toBind_1483_; lean_object* v_toPure_1484_; lean_object* v___f_1485_; lean_object* v___x_1486_; lean_object* v___f_1487_; lean_object* v___x_1488_; 
v_toApplicative_1482_ = lean_ctor_get(v_inst_1477_, 0);
v_toBind_1483_ = lean_ctor_get(v_inst_1477_, 1);
lean_inc(v_toBind_1483_);
v_toPure_1484_ = lean_ctor_get(v_toApplicative_1482_, 1);
lean_inc(v_toPure_1484_);
v___f_1485_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1485_, 0, v_f_1481_);
v___x_1486_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1477_, v___f_1485_, v_init_1480_, v_m_1479_);
v___f_1487_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1487_, 0, v_toPure_1484_);
v___x_1488_ = lean_apply_4(v_toBind_1483_, lean_box(0), lean_box(0), v___x_1486_, v___f_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object* v_inst_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1490_, 0, lean_box(0));
lean_closure_set(v___x_1490_, 1, lean_box(0));
lean_closure_set(v___x_1490_, 2, v_inst_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object* v_m_1491_, lean_object* v_00_u03b1_1492_, lean_object* v_inst_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1494_, 0, lean_box(0));
lean_closure_set(v___x_1494_, 1, lean_box(0));
lean_closure_set(v___x_1494_, 2, v_inst_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* v_00_u03b1_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_box(1);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx(lean_object* v_x_1497_){
_start:
{
switch(lean_obj_tag(v_x_1497_))
{
case 0:
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_unsigned_to_nat(0u);
return v___x_1498_;
}
case 1:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_unsigned_to_nat(1u);
return v___x_1499_;
}
case 2:
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_unsigned_to_nat(2u);
return v___x_1500_;
}
case 3:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_unsigned_to_nat(3u);
return v___x_1501_;
}
case 4:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_unsigned_to_nat(4u);
return v___x_1502_;
}
case 5:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_unsigned_to_nat(5u);
return v___x_1503_;
}
case 6:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_unsigned_to_nat(6u);
return v___x_1504_;
}
case 7:
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_unsigned_to_nat(7u);
return v___x_1505_;
}
case 8:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_unsigned_to_nat(8u);
return v___x_1506_;
}
case 9:
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_unsigned_to_nat(9u);
return v___x_1507_;
}
case 10:
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_unsigned_to_nat(10u);
return v___x_1508_;
}
default: 
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_unsigned_to_nat(11u);
return v___x_1509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___boxed(lean_object* v_x_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_Expr_ctorIdx(v_x_1510_);
lean_dec_ref(v_x_1510_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object* v_t_1512_, lean_object* v_k_1513_){
_start:
{
switch(lean_obj_tag(v_t_1512_))
{
case 4:
{
lean_object* v_declName_1514_; lean_object* v_us_1515_; lean_object* v___x_1516_; 
v_declName_1514_ = lean_ctor_get(v_t_1512_, 0);
lean_inc(v_declName_1514_);
v_us_1515_ = lean_ctor_get(v_t_1512_, 1);
lean_inc(v_us_1515_);
lean_dec_ref_known(v_t_1512_, 2);
v___x_1516_ = lean_apply_2(v_k_1513_, v_declName_1514_, v_us_1515_);
return v___x_1516_;
}
case 5:
{
lean_object* v_fn_1517_; lean_object* v_arg_1518_; lean_object* v___x_1519_; 
v_fn_1517_ = lean_ctor_get(v_t_1512_, 0);
lean_inc_ref(v_fn_1517_);
v_arg_1518_ = lean_ctor_get(v_t_1512_, 1);
lean_inc_ref(v_arg_1518_);
lean_dec_ref_known(v_t_1512_, 2);
v___x_1519_ = lean_apply_2(v_k_1513_, v_fn_1517_, v_arg_1518_);
return v___x_1519_;
}
case 6:
{
lean_object* v_binderName_1520_; lean_object* v_binderType_1521_; lean_object* v_body_1522_; uint8_t v_binderInfo_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_binderName_1520_ = lean_ctor_get(v_t_1512_, 0);
lean_inc(v_binderName_1520_);
v_binderType_1521_ = lean_ctor_get(v_t_1512_, 1);
lean_inc_ref(v_binderType_1521_);
v_body_1522_ = lean_ctor_get(v_t_1512_, 2);
lean_inc_ref(v_body_1522_);
v_binderInfo_1523_ = lean_ctor_get_uint8(v_t_1512_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1512_, 3);
v___x_1524_ = lean_box(v_binderInfo_1523_);
v___x_1525_ = lean_apply_4(v_k_1513_, v_binderName_1520_, v_binderType_1521_, v_body_1522_, v___x_1524_);
return v___x_1525_;
}
case 7:
{
lean_object* v_binderName_1526_; lean_object* v_binderType_1527_; lean_object* v_body_1528_; uint8_t v_binderInfo_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v_binderName_1526_ = lean_ctor_get(v_t_1512_, 0);
lean_inc(v_binderName_1526_);
v_binderType_1527_ = lean_ctor_get(v_t_1512_, 1);
lean_inc_ref(v_binderType_1527_);
v_body_1528_ = lean_ctor_get(v_t_1512_, 2);
lean_inc_ref(v_body_1528_);
v_binderInfo_1529_ = lean_ctor_get_uint8(v_t_1512_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1512_, 3);
v___x_1530_ = lean_box(v_binderInfo_1529_);
v___x_1531_ = lean_apply_4(v_k_1513_, v_binderName_1526_, v_binderType_1527_, v_body_1528_, v___x_1530_);
return v___x_1531_;
}
case 8:
{
lean_object* v_declName_1532_; lean_object* v_type_1533_; lean_object* v_value_1534_; lean_object* v_body_1535_; uint8_t v_nondep_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_declName_1532_ = lean_ctor_get(v_t_1512_, 0);
lean_inc(v_declName_1532_);
v_type_1533_ = lean_ctor_get(v_t_1512_, 1);
lean_inc_ref(v_type_1533_);
v_value_1534_ = lean_ctor_get(v_t_1512_, 2);
lean_inc_ref(v_value_1534_);
v_body_1535_ = lean_ctor_get(v_t_1512_, 3);
lean_inc_ref(v_body_1535_);
v_nondep_1536_ = lean_ctor_get_uint8(v_t_1512_, sizeof(void*)*4);
lean_dec_ref_known(v_t_1512_, 4);
v___x_1537_ = lean_box(v_nondep_1536_);
v___x_1538_ = lean_apply_5(v_k_1513_, v_declName_1532_, v_type_1533_, v_value_1534_, v_body_1535_, v___x_1537_);
return v___x_1538_;
}
case 9:
{
lean_object* v_a_1539_; lean_object* v___x_1540_; 
v_a_1539_ = lean_ctor_get(v_t_1512_, 0);
lean_inc_ref(v_a_1539_);
lean_dec_ref_known(v_t_1512_, 1);
v___x_1540_ = lean_apply_1(v_k_1513_, v_a_1539_);
return v___x_1540_;
}
case 10:
{
lean_object* v_data_1541_; lean_object* v_expr_1542_; lean_object* v___x_1543_; 
v_data_1541_ = lean_ctor_get(v_t_1512_, 0);
lean_inc(v_data_1541_);
v_expr_1542_ = lean_ctor_get(v_t_1512_, 1);
lean_inc_ref(v_expr_1542_);
lean_dec_ref_known(v_t_1512_, 2);
v___x_1543_ = lean_apply_2(v_k_1513_, v_data_1541_, v_expr_1542_);
return v___x_1543_;
}
case 11:
{
lean_object* v_typeName_1544_; lean_object* v_idx_1545_; lean_object* v_struct_1546_; lean_object* v___x_1547_; 
v_typeName_1544_ = lean_ctor_get(v_t_1512_, 0);
lean_inc(v_typeName_1544_);
v_idx_1545_ = lean_ctor_get(v_t_1512_, 1);
lean_inc(v_idx_1545_);
v_struct_1546_ = lean_ctor_get(v_t_1512_, 2);
lean_inc_ref(v_struct_1546_);
lean_dec_ref_known(v_t_1512_, 3);
v___x_1547_ = lean_apply_3(v_k_1513_, v_typeName_1544_, v_idx_1545_, v_struct_1546_);
return v___x_1547_;
}
default: 
{
lean_object* v_deBruijnIndex_1548_; lean_object* v___x_1549_; 
v_deBruijnIndex_1548_ = lean_ctor_get(v_t_1512_, 0);
lean_inc(v_deBruijnIndex_1548_);
lean_dec_ref(v_t_1512_);
v___x_1549_ = lean_apply_1(v_k_1513_, v_deBruijnIndex_1548_);
return v___x_1549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object* v_motive_1550_, lean_object* v_ctorIdx_1551_, lean_object* v_t_1552_, lean_object* v_h_1553_, lean_object* v_k_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Expr_ctorElim___redArg(v_t_1552_, v_k_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object* v_motive_1556_, lean_object* v_ctorIdx_1557_, lean_object* v_t_1558_, lean_object* v_h_1559_, lean_object* v_k_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_Expr_ctorElim(v_motive_1556_, v_ctorIdx_1557_, v_t_1558_, v_h_1559_, v_k_1560_);
lean_dec(v_ctorIdx_1557_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object* v_t_1562_, lean_object* v_bvar_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Expr_ctorElim___redArg(v_t_1562_, v_bvar_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object* v_motive_1565_, lean_object* v_t_1566_, lean_object* v_h_1567_, lean_object* v_bvar_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_Expr_ctorElim___redArg(v_t_1566_, v_bvar_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object* v_t_1570_, lean_object* v_fvar_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_Expr_ctorElim___redArg(v_t_1570_, v_fvar_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object* v_motive_1573_, lean_object* v_t_1574_, lean_object* v_h_1575_, lean_object* v_fvar_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_Expr_ctorElim___redArg(v_t_1574_, v_fvar_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object* v_t_1578_, lean_object* v_mvar_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_Expr_ctorElim___redArg(v_t_1578_, v_mvar_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object* v_motive_1581_, lean_object* v_t_1582_, lean_object* v_h_1583_, lean_object* v_mvar_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Expr_ctorElim___redArg(v_t_1582_, v_mvar_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object* v_t_1586_, lean_object* v_sort_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_Expr_ctorElim___redArg(v_t_1586_, v_sort_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object* v_motive_1589_, lean_object* v_t_1590_, lean_object* v_h_1591_, lean_object* v_sort_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_Expr_ctorElim___redArg(v_t_1590_, v_sort_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object* v_t_1594_, lean_object* v_const_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_Expr_ctorElim___redArg(v_t_1594_, v_const_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object* v_motive_1597_, lean_object* v_t_1598_, lean_object* v_h_1599_, lean_object* v_const_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Expr_ctorElim___redArg(v_t_1598_, v_const_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object* v_t_1602_, lean_object* v_app_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Expr_ctorElim___redArg(v_t_1602_, v_app_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object* v_motive_1605_, lean_object* v_t_1606_, lean_object* v_h_1607_, lean_object* v_app_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Expr_ctorElim___redArg(v_t_1606_, v_app_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object* v_t_1610_, lean_object* v_lam_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Expr_ctorElim___redArg(v_t_1610_, v_lam_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object* v_motive_1613_, lean_object* v_t_1614_, lean_object* v_h_1615_, lean_object* v_lam_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Expr_ctorElim___redArg(v_t_1614_, v_lam_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object* v_t_1618_, lean_object* v_forallE_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Expr_ctorElim___redArg(v_t_1618_, v_forallE_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object* v_motive_1621_, lean_object* v_t_1622_, lean_object* v_h_1623_, lean_object* v_forallE_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_Expr_ctorElim___redArg(v_t_1622_, v_forallE_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object* v_t_1626_, lean_object* v_letE_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Expr_ctorElim___redArg(v_t_1626_, v_letE_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object* v_motive_1629_, lean_object* v_t_1630_, lean_object* v_h_1631_, lean_object* v_letE_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Expr_ctorElim___redArg(v_t_1630_, v_letE_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object* v_t_1634_, lean_object* v_lit_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Expr_ctorElim___redArg(v_t_1634_, v_lit_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object* v_motive_1637_, lean_object* v_t_1638_, lean_object* v_h_1639_, lean_object* v_lit_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Expr_ctorElim___redArg(v_t_1638_, v_lit_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object* v_t_1642_, lean_object* v_mdata_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Expr_ctorElim___redArg(v_t_1642_, v_mdata_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object* v_motive_1645_, lean_object* v_t_1646_, lean_object* v_h_1647_, lean_object* v_mdata_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_Expr_ctorElim___redArg(v_t_1646_, v_mdata_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object* v_t_1650_, lean_object* v_proj_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_Expr_ctorElim___redArg(v_t_1650_, v_proj_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object* v_motive_1653_, lean_object* v_t_1654_, lean_object* v_h_1655_, lean_object* v_proj_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Expr_ctorElim___redArg(v_t_1654_, v_proj_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* v_a_00___x40___internal___hyg_1659_){
_start:
{
uint64_t v_res_1660_; lean_object* v_r_1661_; 
v_res_1660_ = lean_expr_data(v_a_00___x40___internal___hyg_1659_);
lean_dec_ref(v_a_00___x40___internal___hyg_1659_);
v_r_1661_ = lean_box_uint64(v_res_1660_);
return v_r_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object* v_t_1662_, lean_object* v_bvar_1663_, lean_object* v_fvar_1664_, lean_object* v_mvar_1665_, lean_object* v_sort_1666_, lean_object* v_const_1667_, lean_object* v_app_1668_, lean_object* v_lam_1669_, lean_object* v_forallE_1670_, lean_object* v_letE_1671_, lean_object* v_lit_1672_, lean_object* v_mdata_1673_, lean_object* v_proj_1674_){
_start:
{
switch(lean_obj_tag(v_t_1662_))
{
case 0:
{
lean_object* v_deBruijnIndex_1675_; lean_object* v___x_1676_; 
lean_dec(v_proj_1674_);
lean_dec(v_mdata_1673_);
lean_dec(v_lit_1672_);
lean_dec(v_letE_1671_);
lean_dec(v_forallE_1670_);
lean_dec(v_lam_1669_);
lean_dec(v_app_1668_);
lean_dec(v_const_1667_);
lean_dec(v_sort_1666_);
lean_dec(v_mvar_1665_);
lean_dec(v_fvar_1664_);
v_deBruijnIndex_1675_ = lean_ctor_get(v_t_1662_, 0);
lean_inc(v_deBruijnIndex_1675_);
lean_dec_ref_known(v_t_1662_, 1);
v___x_1676_ = lean_apply_1(v_bvar_1663_, v_deBruijnIndex_1675_);
return v___x_1676_;
}
case 1:
{
lean_object* v_fvarId_1677_; lean_object* v___x_1678_; 
lean_dec(v_proj_1674_);
lean_dec(v_mdata_1673_);
lean_dec(v_lit_1672_);
lean_dec(v_letE_1671_);
lean_dec(v_forallE_1670_);
lean_dec(v_lam_1669_);
lean_dec(v_app_1668_);
lean_dec(v_const_1667_);
lean_dec(v_sort_1666_);
lean_dec(v_mvar_1665_);
lean_dec(v_bvar_1663_);
v_fvarId_1677_ = lean_ctor_get(v_t_1662_, 0);
lean_inc(v_fvarId_1677_);
lean_dec_ref_known(v_t_1662_, 1);
v___x_1678_ = lean_apply_1(v_fvar_1664_, v_fvarId_1677_);
return v___x_1678_;
}
case 2:
{
lean_object* v_mvarId_1679_; lean_object* v___x_1680_; 
lean_dec(v_proj_1674_);
lean_dec(v_mdata_1673_);
lean_dec(v_lit_1672_);
lean_dec(v_letE_1671_);
lean_dec(v_forallE_1670_);
lean_dec(v_lam_1669_);
lean_dec(v_app_1668_);
lean_dec(v_const_1667_);
lean_dec(v_sort_1666_);
lean_dec(v_fvar_1664_);
lean_dec(v_bvar_1663_);
v_mvarId_1679_ = lean_ctor_get(v_t_1662_, 0);
lean_inc(v_mvarId_1679_);
lean_dec_ref_known(v_t_1662_, 1);
v___x_1680_ = lean_apply_1(v_mvar_1665_, v_mvarId_1679_);
return v___x_1680_;
}
case 3:
{
lean_object* v_u_1681_; lean_object* v___x_1682_; 
lean_dec(v_proj_1674_);
lean_dec(v_mdata_1673_);
lean_dec(v_lit_1672_);
lean_dec(v_letE_1671_);
lean_dec(v_forallE_1670_);
lean_dec(v_lam_1669_);
lean_dec(v_app_1668_);
lean_dec(v_const_1667_);
lean_dec(v_mvar_1665_);
lean_dec(v_fvar_1664_);
lean_dec(v_bvar_1663_);
v_u_1681_ = lean_ctor_get(v_t_1662_, 0);
lean_inc(v_u_1681_);
lean_dec_ref_known(v_t_1662_, 1);
v___x_1682_ = lean_apply_1(v_sort_1666_, v_u_1681_);
return v___x_1682_;
}
case 4:
{
lean_object* v_declName_1683_; lean_object* v_us_1684_; lean_object* v___x_1685_; 
lean_dec(v_proj_1674_);
lean_dec(v_mdata_1673_);
lean_dec(v_lit_1672_);
lean_dec(v_letE_1671_);
lean_dec(v_forallE_1670_);
lean_dec(v_lam_1669_);
lean_dec(v_app_1668_);
lean_dec(v_sort_1666_);
lean_dec(v_mvar_1665_);
lean_dec(v_fvar_1664_);
lean_dec(v_bvar_1663_);
v_declName_1683_ = lean_ctor_get(v_t_1662_, 0);
lean_inc(v_declName_1683_);
v_us_1684_ = lean_ctor_get(v_t_1662_, 1);
lean_inc(v_us_1684_);
lean_dec_ref_known(v_t_1662_, 2);
v___x_1685_ = lean_apply_2(v_const_1667_, v_declName_1683_, v_us_1684_);
return v___x_1685_;
}
case 5:
{
lean_object* v_fn_1686_; lean_object* v_arg_1687_; lean_object* v___x_1688_; 
lean_dec(v_proj_1674_);
lean_dec(v_mdata_1673_);
lean_dec(v_lit_1672_);
lean_dec(v_letE_1671_);
lean_dec(v_forallE_1670_);
lean_dec(v_lam_1669_);
lean_dec(v_const_1667_);
lean_dec(v_sort_1666_);
lean_dec(v_mvar_1665_);
lean_dec(v_fvar_1664_);
lean_dec(v_bvar_1663_);
v_fn_1686_ = lean_ctor_get(v_t_1662_, 0);
lean_inc_ref(v_fn_1686_);
v_arg_1687_ = lean_ctor_get(v_t_1662_, 1);
lean_inc_ref(v_arg_1687_);
lean_dec_ref_known(v_t_1662_, 2);
v___x_1688_ = lean_apply_2(v_app_1668_, v_fn_1686_, v_arg_1687_);
return v___x_1688_;
}
case 6:
{
lean_object* v_binderName_1689_; lean_object* v_binderType_1690_; lean_object* v_body_1691_; uint8_t v_binderInfo_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_dec(v_proj_1674_);
lean_dec(v_mdata_1673_);
lean_dec(v_lit_1672_);
lean_dec(v_letE_1671_);
lean_dec(v_forallE_1670_);
lean_dec(v_app_1668_);
lean_dec(v_const_1667_);
lean_dec(v_sort_1666_);
lean_dec(v_mvar_1665_);
lean_dec(v_fvar_1664_);
lean_dec(v_bvar_1663_);
v_binderName_1689_ = lean_ctor_get(v_t_1662_, 0);
lean_inc(v_binderName_1689_);
v_binderType_1690_ = lean_ctor_get(v_t_1662_, 1);
lean_inc_ref(v_binderType_1690_);
v_body_1691_ = lean_ctor_get(v_t_1662_, 2);
lean_inc_ref(v_body_1691_);
v_binderInfo_1692_ = lean_ctor_get_uint8(v_t_1662_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1662_, 3);
v___x_1693_ = lean_box(v_binderInfo_1692_);
v___x_1694_ = lean_apply_4(v_lam_1669_, v_binderName_1689_, v_binderType_1690_, v_body_1691_, v___x_1693_);
return v___x_1694_;
}
case 7:
{
lean_object* v_binderName_1695_; lean_object* v_binderType_1696_; lean_object* v_body_1697_; uint8_t v_binderInfo_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_dec(v_proj_1674_);
lean_dec(v_mdata_1673_);
lean_dec(v_lit_1672_);
lean_dec(v_letE_1671_);
lean_dec(v_lam_1669_);
lean_dec(v_app_1668_);
lean_dec(v_const_1667_);
lean_dec(v_sort_1666_);
lean_dec(v_mvar_1665_);
lean_dec(v_fvar_1664_);
lean_dec(v_bvar_1663_);
v_binderName_1695_ = lean_ctor_get(v_t_1662_, 0);
lean_inc(v_binderName_1695_);
v_binderType_1696_ = lean_ctor_get(v_t_1662_, 1);
lean_inc_ref(v_binderType_1696_);
v_body_1697_ = lean_ctor_get(v_t_1662_, 2);
lean_inc_ref(v_body_1697_);
v_binderInfo_1698_ = lean_ctor_get_uint8(v_t_1662_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1662_, 3);
v___x_1699_ = lean_box(v_binderInfo_1698_);
v___x_1700_ = lean_apply_4(v_forallE_1670_, v_binderName_1695_, v_binderType_1696_, v_body_1697_, v___x_1699_);
return v___x_1700_;
}
case 8:
{
lean_object* v_declName_1701_; lean_object* v_type_1702_; lean_object* v_value_1703_; lean_object* v_body_1704_; uint8_t v_nondep_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec(v_proj_1674_);
lean_dec(v_mdata_1673_);
lean_dec(v_lit_1672_);
lean_dec(v_forallE_1670_);
lean_dec(v_lam_1669_);
lean_dec(v_app_1668_);
lean_dec(v_const_1667_);
lean_dec(v_sort_1666_);
lean_dec(v_mvar_1665_);
lean_dec(v_fvar_1664_);
lean_dec(v_bvar_1663_);
v_declName_1701_ = lean_ctor_get(v_t_1662_, 0);
lean_inc(v_declName_1701_);
v_type_1702_ = lean_ctor_get(v_t_1662_, 1);
lean_inc_ref(v_type_1702_);
v_value_1703_ = lean_ctor_get(v_t_1662_, 2);
lean_inc_ref(v_value_1703_);
v_body_1704_ = lean_ctor_get(v_t_1662_, 3);
lean_inc_ref(v_body_1704_);
v_nondep_1705_ = lean_ctor_get_uint8(v_t_1662_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1662_, 4);
v___x_1706_ = lean_box(v_nondep_1705_);
v___x_1707_ = lean_apply_5(v_letE_1671_, v_declName_1701_, v_type_1702_, v_value_1703_, v_body_1704_, v___x_1706_);
return v___x_1707_;
}
case 9:
{
lean_object* v_a_1708_; lean_object* v___x_1709_; 
lean_dec(v_proj_1674_);
lean_dec(v_mdata_1673_);
lean_dec(v_letE_1671_);
lean_dec(v_forallE_1670_);
lean_dec(v_lam_1669_);
lean_dec(v_app_1668_);
lean_dec(v_const_1667_);
lean_dec(v_sort_1666_);
lean_dec(v_mvar_1665_);
lean_dec(v_fvar_1664_);
lean_dec(v_bvar_1663_);
v_a_1708_ = lean_ctor_get(v_t_1662_, 0);
lean_inc_ref(v_a_1708_);
lean_dec_ref_known(v_t_1662_, 1);
v___x_1709_ = lean_apply_1(v_lit_1672_, v_a_1708_);
return v___x_1709_;
}
case 10:
{
lean_object* v_data_1710_; lean_object* v_expr_1711_; lean_object* v___x_1712_; 
lean_dec(v_proj_1674_);
lean_dec(v_lit_1672_);
lean_dec(v_letE_1671_);
lean_dec(v_forallE_1670_);
lean_dec(v_lam_1669_);
lean_dec(v_app_1668_);
lean_dec(v_const_1667_);
lean_dec(v_sort_1666_);
lean_dec(v_mvar_1665_);
lean_dec(v_fvar_1664_);
lean_dec(v_bvar_1663_);
v_data_1710_ = lean_ctor_get(v_t_1662_, 0);
lean_inc(v_data_1710_);
v_expr_1711_ = lean_ctor_get(v_t_1662_, 1);
lean_inc_ref(v_expr_1711_);
lean_dec_ref_known(v_t_1662_, 2);
v___x_1712_ = lean_apply_2(v_mdata_1673_, v_data_1710_, v_expr_1711_);
return v___x_1712_;
}
default: 
{
lean_object* v_typeName_1713_; lean_object* v_idx_1714_; lean_object* v_struct_1715_; lean_object* v___x_1716_; 
lean_dec(v_mdata_1673_);
lean_dec(v_lit_1672_);
lean_dec(v_letE_1671_);
lean_dec(v_forallE_1670_);
lean_dec(v_lam_1669_);
lean_dec(v_app_1668_);
lean_dec(v_const_1667_);
lean_dec(v_sort_1666_);
lean_dec(v_mvar_1665_);
lean_dec(v_fvar_1664_);
lean_dec(v_bvar_1663_);
v_typeName_1713_ = lean_ctor_get(v_t_1662_, 0);
lean_inc(v_typeName_1713_);
v_idx_1714_ = lean_ctor_get(v_t_1662_, 1);
lean_inc(v_idx_1714_);
v_struct_1715_ = lean_ctor_get(v_t_1662_, 2);
lean_inc_ref(v_struct_1715_);
lean_dec_ref_known(v_t_1662_, 3);
v___x_1716_ = lean_apply_3(v_proj_1674_, v_typeName_1713_, v_idx_1714_, v_struct_1715_);
return v___x_1716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* v_motive_1717_, lean_object* v_t_1718_, lean_object* v_bvar_1719_, lean_object* v_fvar_1720_, lean_object* v_mvar_1721_, lean_object* v_sort_1722_, lean_object* v_const_1723_, lean_object* v_app_1724_, lean_object* v_lam_1725_, lean_object* v_forallE_1726_, lean_object* v_letE_1727_, lean_object* v_lit_1728_, lean_object* v_mdata_1729_, lean_object* v_proj_1730_){
_start:
{
switch(lean_obj_tag(v_t_1718_))
{
case 0:
{
lean_object* v_deBruijnIndex_1731_; lean_object* v___x_1732_; 
lean_dec(v_proj_1730_);
lean_dec(v_mdata_1729_);
lean_dec(v_lit_1728_);
lean_dec(v_letE_1727_);
lean_dec(v_forallE_1726_);
lean_dec(v_lam_1725_);
lean_dec(v_app_1724_);
lean_dec(v_const_1723_);
lean_dec(v_sort_1722_);
lean_dec(v_mvar_1721_);
lean_dec(v_fvar_1720_);
v_deBruijnIndex_1731_ = lean_ctor_get(v_t_1718_, 0);
lean_inc(v_deBruijnIndex_1731_);
lean_dec_ref_known(v_t_1718_, 1);
v___x_1732_ = lean_apply_1(v_bvar_1719_, v_deBruijnIndex_1731_);
return v___x_1732_;
}
case 1:
{
lean_object* v_fvarId_1733_; lean_object* v___x_1734_; 
lean_dec(v_proj_1730_);
lean_dec(v_mdata_1729_);
lean_dec(v_lit_1728_);
lean_dec(v_letE_1727_);
lean_dec(v_forallE_1726_);
lean_dec(v_lam_1725_);
lean_dec(v_app_1724_);
lean_dec(v_const_1723_);
lean_dec(v_sort_1722_);
lean_dec(v_mvar_1721_);
lean_dec(v_bvar_1719_);
v_fvarId_1733_ = lean_ctor_get(v_t_1718_, 0);
lean_inc(v_fvarId_1733_);
lean_dec_ref_known(v_t_1718_, 1);
v___x_1734_ = lean_apply_1(v_fvar_1720_, v_fvarId_1733_);
return v___x_1734_;
}
case 2:
{
lean_object* v_mvarId_1735_; lean_object* v___x_1736_; 
lean_dec(v_proj_1730_);
lean_dec(v_mdata_1729_);
lean_dec(v_lit_1728_);
lean_dec(v_letE_1727_);
lean_dec(v_forallE_1726_);
lean_dec(v_lam_1725_);
lean_dec(v_app_1724_);
lean_dec(v_const_1723_);
lean_dec(v_sort_1722_);
lean_dec(v_fvar_1720_);
lean_dec(v_bvar_1719_);
v_mvarId_1735_ = lean_ctor_get(v_t_1718_, 0);
lean_inc(v_mvarId_1735_);
lean_dec_ref_known(v_t_1718_, 1);
v___x_1736_ = lean_apply_1(v_mvar_1721_, v_mvarId_1735_);
return v___x_1736_;
}
case 3:
{
lean_object* v_u_1737_; lean_object* v___x_1738_; 
lean_dec(v_proj_1730_);
lean_dec(v_mdata_1729_);
lean_dec(v_lit_1728_);
lean_dec(v_letE_1727_);
lean_dec(v_forallE_1726_);
lean_dec(v_lam_1725_);
lean_dec(v_app_1724_);
lean_dec(v_const_1723_);
lean_dec(v_mvar_1721_);
lean_dec(v_fvar_1720_);
lean_dec(v_bvar_1719_);
v_u_1737_ = lean_ctor_get(v_t_1718_, 0);
lean_inc(v_u_1737_);
lean_dec_ref_known(v_t_1718_, 1);
v___x_1738_ = lean_apply_1(v_sort_1722_, v_u_1737_);
return v___x_1738_;
}
case 4:
{
lean_object* v_declName_1739_; lean_object* v_us_1740_; lean_object* v___x_1741_; 
lean_dec(v_proj_1730_);
lean_dec(v_mdata_1729_);
lean_dec(v_lit_1728_);
lean_dec(v_letE_1727_);
lean_dec(v_forallE_1726_);
lean_dec(v_lam_1725_);
lean_dec(v_app_1724_);
lean_dec(v_sort_1722_);
lean_dec(v_mvar_1721_);
lean_dec(v_fvar_1720_);
lean_dec(v_bvar_1719_);
v_declName_1739_ = lean_ctor_get(v_t_1718_, 0);
lean_inc(v_declName_1739_);
v_us_1740_ = lean_ctor_get(v_t_1718_, 1);
lean_inc(v_us_1740_);
lean_dec_ref_known(v_t_1718_, 2);
v___x_1741_ = lean_apply_2(v_const_1723_, v_declName_1739_, v_us_1740_);
return v___x_1741_;
}
case 5:
{
lean_object* v_fn_1742_; lean_object* v_arg_1743_; lean_object* v___x_1744_; 
lean_dec(v_proj_1730_);
lean_dec(v_mdata_1729_);
lean_dec(v_lit_1728_);
lean_dec(v_letE_1727_);
lean_dec(v_forallE_1726_);
lean_dec(v_lam_1725_);
lean_dec(v_const_1723_);
lean_dec(v_sort_1722_);
lean_dec(v_mvar_1721_);
lean_dec(v_fvar_1720_);
lean_dec(v_bvar_1719_);
v_fn_1742_ = lean_ctor_get(v_t_1718_, 0);
lean_inc_ref(v_fn_1742_);
v_arg_1743_ = lean_ctor_get(v_t_1718_, 1);
lean_inc_ref(v_arg_1743_);
lean_dec_ref_known(v_t_1718_, 2);
v___x_1744_ = lean_apply_2(v_app_1724_, v_fn_1742_, v_arg_1743_);
return v___x_1744_;
}
case 6:
{
lean_object* v_binderName_1745_; lean_object* v_binderType_1746_; lean_object* v_body_1747_; uint8_t v_binderInfo_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec(v_proj_1730_);
lean_dec(v_mdata_1729_);
lean_dec(v_lit_1728_);
lean_dec(v_letE_1727_);
lean_dec(v_forallE_1726_);
lean_dec(v_app_1724_);
lean_dec(v_const_1723_);
lean_dec(v_sort_1722_);
lean_dec(v_mvar_1721_);
lean_dec(v_fvar_1720_);
lean_dec(v_bvar_1719_);
v_binderName_1745_ = lean_ctor_get(v_t_1718_, 0);
lean_inc(v_binderName_1745_);
v_binderType_1746_ = lean_ctor_get(v_t_1718_, 1);
lean_inc_ref(v_binderType_1746_);
v_body_1747_ = lean_ctor_get(v_t_1718_, 2);
lean_inc_ref(v_body_1747_);
v_binderInfo_1748_ = lean_ctor_get_uint8(v_t_1718_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1718_, 3);
v___x_1749_ = lean_box(v_binderInfo_1748_);
v___x_1750_ = lean_apply_4(v_lam_1725_, v_binderName_1745_, v_binderType_1746_, v_body_1747_, v___x_1749_);
return v___x_1750_;
}
case 7:
{
lean_object* v_binderName_1751_; lean_object* v_binderType_1752_; lean_object* v_body_1753_; uint8_t v_binderInfo_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v_proj_1730_);
lean_dec(v_mdata_1729_);
lean_dec(v_lit_1728_);
lean_dec(v_letE_1727_);
lean_dec(v_lam_1725_);
lean_dec(v_app_1724_);
lean_dec(v_const_1723_);
lean_dec(v_sort_1722_);
lean_dec(v_mvar_1721_);
lean_dec(v_fvar_1720_);
lean_dec(v_bvar_1719_);
v_binderName_1751_ = lean_ctor_get(v_t_1718_, 0);
lean_inc(v_binderName_1751_);
v_binderType_1752_ = lean_ctor_get(v_t_1718_, 1);
lean_inc_ref(v_binderType_1752_);
v_body_1753_ = lean_ctor_get(v_t_1718_, 2);
lean_inc_ref(v_body_1753_);
v_binderInfo_1754_ = lean_ctor_get_uint8(v_t_1718_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1718_, 3);
v___x_1755_ = lean_box(v_binderInfo_1754_);
v___x_1756_ = lean_apply_4(v_forallE_1726_, v_binderName_1751_, v_binderType_1752_, v_body_1753_, v___x_1755_);
return v___x_1756_;
}
case 8:
{
lean_object* v_declName_1757_; lean_object* v_type_1758_; lean_object* v_value_1759_; lean_object* v_body_1760_; uint8_t v_nondep_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec(v_proj_1730_);
lean_dec(v_mdata_1729_);
lean_dec(v_lit_1728_);
lean_dec(v_forallE_1726_);
lean_dec(v_lam_1725_);
lean_dec(v_app_1724_);
lean_dec(v_const_1723_);
lean_dec(v_sort_1722_);
lean_dec(v_mvar_1721_);
lean_dec(v_fvar_1720_);
lean_dec(v_bvar_1719_);
v_declName_1757_ = lean_ctor_get(v_t_1718_, 0);
lean_inc(v_declName_1757_);
v_type_1758_ = lean_ctor_get(v_t_1718_, 1);
lean_inc_ref(v_type_1758_);
v_value_1759_ = lean_ctor_get(v_t_1718_, 2);
lean_inc_ref(v_value_1759_);
v_body_1760_ = lean_ctor_get(v_t_1718_, 3);
lean_inc_ref(v_body_1760_);
v_nondep_1761_ = lean_ctor_get_uint8(v_t_1718_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1718_, 4);
v___x_1762_ = lean_box(v_nondep_1761_);
v___x_1763_ = lean_apply_5(v_letE_1727_, v_declName_1757_, v_type_1758_, v_value_1759_, v_body_1760_, v___x_1762_);
return v___x_1763_;
}
case 9:
{
lean_object* v_a_1764_; lean_object* v___x_1765_; 
lean_dec(v_proj_1730_);
lean_dec(v_mdata_1729_);
lean_dec(v_letE_1727_);
lean_dec(v_forallE_1726_);
lean_dec(v_lam_1725_);
lean_dec(v_app_1724_);
lean_dec(v_const_1723_);
lean_dec(v_sort_1722_);
lean_dec(v_mvar_1721_);
lean_dec(v_fvar_1720_);
lean_dec(v_bvar_1719_);
v_a_1764_ = lean_ctor_get(v_t_1718_, 0);
lean_inc_ref(v_a_1764_);
lean_dec_ref_known(v_t_1718_, 1);
v___x_1765_ = lean_apply_1(v_lit_1728_, v_a_1764_);
return v___x_1765_;
}
case 10:
{
lean_object* v_data_1766_; lean_object* v_expr_1767_; lean_object* v___x_1768_; 
lean_dec(v_proj_1730_);
lean_dec(v_lit_1728_);
lean_dec(v_letE_1727_);
lean_dec(v_forallE_1726_);
lean_dec(v_lam_1725_);
lean_dec(v_app_1724_);
lean_dec(v_const_1723_);
lean_dec(v_sort_1722_);
lean_dec(v_mvar_1721_);
lean_dec(v_fvar_1720_);
lean_dec(v_bvar_1719_);
v_data_1766_ = lean_ctor_get(v_t_1718_, 0);
lean_inc(v_data_1766_);
v_expr_1767_ = lean_ctor_get(v_t_1718_, 1);
lean_inc_ref(v_expr_1767_);
lean_dec_ref_known(v_t_1718_, 2);
v___x_1768_ = lean_apply_2(v_mdata_1729_, v_data_1766_, v_expr_1767_);
return v___x_1768_;
}
default: 
{
lean_object* v_typeName_1769_; lean_object* v_idx_1770_; lean_object* v_struct_1771_; lean_object* v___x_1772_; 
lean_dec(v_mdata_1729_);
lean_dec(v_lit_1728_);
lean_dec(v_letE_1727_);
lean_dec(v_forallE_1726_);
lean_dec(v_lam_1725_);
lean_dec(v_app_1724_);
lean_dec(v_const_1723_);
lean_dec(v_sort_1722_);
lean_dec(v_mvar_1721_);
lean_dec(v_fvar_1720_);
lean_dec(v_bvar_1719_);
v_typeName_1769_ = lean_ctor_get(v_t_1718_, 0);
lean_inc(v_typeName_1769_);
v_idx_1770_ = lean_ctor_get(v_t_1718_, 1);
lean_inc(v_idx_1770_);
v_struct_1771_ = lean_ctor_get(v_t_1718_, 2);
lean_inc_ref(v_struct_1771_);
lean_dec_ref_known(v_t_1718_, 3);
v___x_1772_ = lean_apply_3(v_proj_1730_, v_typeName_1769_, v_idx_1770_, v_struct_1771_);
return v___x_1772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* v_deBruijnIndex_1773_){
_start:
{
uint64_t v___x_1774_; uint64_t v___x_1775_; uint64_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; uint32_t v___x_1779_; uint8_t v___x_1780_; uint64_t v___x_1781_; lean_object* v___x_1782_; 
v___x_1774_ = 7ULL;
v___x_1775_ = lean_uint64_of_nat(v_deBruijnIndex_1773_);
v___x_1776_ = lean_uint64_mix_hash(v___x_1774_, v___x_1775_);
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = lean_nat_add(v_deBruijnIndex_1773_, v___x_1777_);
v___x_1779_ = 0;
v___x_1780_ = 0;
v___x_1781_ = lean_expr_mk_data(v___x_1776_, v___x_1778_, v___x_1779_, v___x_1780_, v___x_1780_, v___x_1780_, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1782_, 0, v_deBruijnIndex_1773_);
lean_ctor_set_uint64(v___x_1782_, sizeof(void*)*1, v___x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* v_fvarId_1783_){
_start:
{
uint64_t v___x_1784_; uint64_t v___x_1785_; uint64_t v___x_1786_; lean_object* v___x_1787_; uint32_t v___x_1788_; uint8_t v___x_1789_; uint8_t v___x_1790_; uint64_t v___x_1791_; lean_object* v___x_1792_; 
v___x_1784_ = 13ULL;
v___x_1785_ = l_Lean_instHashableFVarId_hash(v_fvarId_1783_);
v___x_1786_ = lean_uint64_mix_hash(v___x_1784_, v___x_1785_);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = 0;
v___x_1789_ = 1;
v___x_1790_ = 0;
v___x_1791_ = lean_expr_mk_data(v___x_1786_, v___x_1787_, v___x_1788_, v___x_1789_, v___x_1790_, v___x_1790_, v___x_1790_);
v___x_1792_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_1792_, 0, v_fvarId_1783_);
lean_ctor_set_uint64(v___x_1792_, sizeof(void*)*1, v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* v_mvarId_1793_){
_start:
{
uint64_t v___x_1794_; uint64_t v___x_1795_; uint64_t v___x_1796_; lean_object* v___x_1797_; uint32_t v___x_1798_; uint8_t v___x_1799_; uint8_t v___x_1800_; uint64_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1794_ = 17ULL;
v___x_1795_ = l_Lean_instHashableMVarId_hash(v_mvarId_1793_);
v___x_1796_ = lean_uint64_mix_hash(v___x_1794_, v___x_1795_);
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = 0;
v___x_1799_ = 0;
v___x_1800_ = 1;
v___x_1801_ = lean_expr_mk_data(v___x_1796_, v___x_1797_, v___x_1798_, v___x_1799_, v___x_1800_, v___x_1799_, v___x_1799_);
v___x_1802_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_1802_, 0, v_mvarId_1793_);
lean_ctor_set_uint64(v___x_1802_, sizeof(void*)*1, v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* v_u_1803_){
_start:
{
uint64_t v___x_1804_; uint64_t v___x_1805_; uint64_t v___x_1806_; lean_object* v___x_1807_; uint32_t v___x_1808_; uint8_t v___x_1809_; uint8_t v___x_1810_; uint8_t v___x_1811_; uint64_t v___x_1812_; lean_object* v___x_1813_; 
v___x_1804_ = 11ULL;
v___x_1805_ = l_Lean_Level_hash(v_u_1803_);
v___x_1806_ = lean_uint64_mix_hash(v___x_1804_, v___x_1805_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = 0;
v___x_1809_ = 0;
v___x_1810_ = l_Lean_Level_hasMVar(v_u_1803_);
v___x_1811_ = l_Lean_Level_hasParam(v_u_1803_);
v___x_1812_ = lean_expr_mk_data(v___x_1806_, v___x_1807_, v___x_1808_, v___x_1809_, v___x_1809_, v___x_1810_, v___x_1811_);
v___x_1813_ = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(v___x_1813_, 0, v_u_1803_);
lean_ctor_set_uint64(v___x_1813_, sizeof(void*)*1, v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* v_fn_1814_, lean_object* v_arg_1815_){
_start:
{
uint64_t v___x_1816_; uint64_t v___x_1817_; uint64_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1816_ = lean_expr_data(v_fn_1814_);
v___x_1817_ = lean_expr_data(v_arg_1815_);
v___x_1818_ = lean_expr_mk_app_data(v___x_1816_, v___x_1817_);
v___x_1819_ = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(v___x_1819_, 0, v_fn_1814_);
lean_ctor_set(v___x_1819_, 1, v_arg_1815_);
lean_ctor_set_uint64(v___x_1819_, sizeof(void*)*2, v___x_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object* v_binderName_1820_, lean_object* v_binderType_1821_, lean_object* v_body_1822_, uint8_t v_binderInfo_1823_){
_start:
{
uint32_t v___y_1825_; uint8_t v___y_1826_; uint8_t v___y_1827_; uint64_t v___y_1828_; uint8_t v___y_1829_; lean_object* v___y_1830_; uint8_t v___y_1831_; uint64_t v___x_1834_; uint8_t v___x_1835_; uint32_t v___x_1836_; uint64_t v___x_1837_; uint32_t v___y_1839_; uint8_t v___y_1840_; uint8_t v___y_1841_; uint64_t v___y_1842_; lean_object* v___y_1843_; uint8_t v___y_1844_; uint32_t v___y_1848_; uint8_t v___y_1849_; uint64_t v___y_1850_; lean_object* v___y_1851_; uint8_t v___y_1852_; uint32_t v___y_1856_; uint64_t v___y_1857_; lean_object* v___y_1858_; uint8_t v___y_1859_; uint32_t v___y_1863_; uint64_t v___y_1864_; lean_object* v___y_1865_; uint32_t v___y_1869_; uint8_t v___x_1884_; uint32_t v___x_1885_; uint8_t v___x_1886_; 
v___x_1834_ = lean_expr_data(v_binderType_1821_);
v___x_1835_ = l_Lean_Expr_Data_approxDepth(v___x_1834_);
v___x_1836_ = lean_uint8_to_uint32(v___x_1835_);
v___x_1837_ = lean_expr_data(v_body_1822_);
v___x_1884_ = l_Lean_Expr_Data_approxDepth(v___x_1837_);
v___x_1885_ = lean_uint8_to_uint32(v___x_1884_);
v___x_1886_ = lean_uint32_dec_le(v___x_1836_, v___x_1885_);
if (v___x_1886_ == 0)
{
v___y_1869_ = v___x_1836_;
goto v___jp_1868_;
}
else
{
v___y_1869_ = v___x_1885_;
goto v___jp_1868_;
}
v___jp_1824_:
{
uint64_t v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = lean_expr_mk_data(v___y_1828_, v___y_1830_, v___y_1825_, v___y_1827_, v___y_1826_, v___y_1829_, v___y_1831_);
v___x_1833_ = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(v___x_1833_, 0, v_binderName_1820_);
lean_ctor_set(v___x_1833_, 1, v_binderType_1821_);
lean_ctor_set(v___x_1833_, 2, v_body_1822_);
lean_ctor_set_uint64(v___x_1833_, sizeof(void*)*3, v___x_1832_);
lean_ctor_set_uint8(v___x_1833_, sizeof(void*)*3 + 8, v_binderInfo_1823_);
return v___x_1833_;
}
v___jp_1838_:
{
uint8_t v___x_1845_; 
v___x_1845_ = l_Lean_Expr_Data_hasLevelParam(v___x_1834_);
if (v___x_1845_ == 0)
{
uint8_t v___x_1846_; 
v___x_1846_ = l_Lean_Expr_Data_hasLevelParam(v___x_1837_);
v___y_1825_ = v___y_1839_;
v___y_1826_ = v___y_1840_;
v___y_1827_ = v___y_1841_;
v___y_1828_ = v___y_1842_;
v___y_1829_ = v___y_1844_;
v___y_1830_ = v___y_1843_;
v___y_1831_ = v___x_1846_;
goto v___jp_1824_;
}
else
{
v___y_1825_ = v___y_1839_;
v___y_1826_ = v___y_1840_;
v___y_1827_ = v___y_1841_;
v___y_1828_ = v___y_1842_;
v___y_1829_ = v___y_1844_;
v___y_1830_ = v___y_1843_;
v___y_1831_ = v___x_1845_;
goto v___jp_1824_;
}
}
v___jp_1847_:
{
uint8_t v___x_1853_; 
v___x_1853_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1834_);
if (v___x_1853_ == 0)
{
uint8_t v___x_1854_; 
v___x_1854_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1837_);
v___y_1839_ = v___y_1848_;
v___y_1840_ = v___y_1852_;
v___y_1841_ = v___y_1849_;
v___y_1842_ = v___y_1850_;
v___y_1843_ = v___y_1851_;
v___y_1844_ = v___x_1854_;
goto v___jp_1838_;
}
else
{
v___y_1839_ = v___y_1848_;
v___y_1840_ = v___y_1852_;
v___y_1841_ = v___y_1849_;
v___y_1842_ = v___y_1850_;
v___y_1843_ = v___y_1851_;
v___y_1844_ = v___x_1853_;
goto v___jp_1838_;
}
}
v___jp_1855_:
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Lean_Expr_Data_hasExprMVar(v___x_1834_);
if (v___x_1860_ == 0)
{
uint8_t v___x_1861_; 
v___x_1861_ = l_Lean_Expr_Data_hasExprMVar(v___x_1837_);
v___y_1848_ = v___y_1856_;
v___y_1849_ = v___y_1859_;
v___y_1850_ = v___y_1857_;
v___y_1851_ = v___y_1858_;
v___y_1852_ = v___x_1861_;
goto v___jp_1847_;
}
else
{
v___y_1848_ = v___y_1856_;
v___y_1849_ = v___y_1859_;
v___y_1850_ = v___y_1857_;
v___y_1851_ = v___y_1858_;
v___y_1852_ = v___x_1860_;
goto v___jp_1847_;
}
}
v___jp_1862_:
{
uint8_t v___x_1866_; 
v___x_1866_ = l_Lean_Expr_Data_hasFVar(v___x_1834_);
if (v___x_1866_ == 0)
{
uint8_t v___x_1867_; 
v___x_1867_ = l_Lean_Expr_Data_hasFVar(v___x_1837_);
v___y_1856_ = v___y_1863_;
v___y_1857_ = v___y_1864_;
v___y_1858_ = v___y_1865_;
v___y_1859_ = v___x_1867_;
goto v___jp_1855_;
}
else
{
v___y_1856_ = v___y_1863_;
v___y_1857_ = v___y_1864_;
v___y_1858_ = v___y_1865_;
v___y_1859_ = v___x_1866_;
goto v___jp_1855_;
}
}
v___jp_1868_:
{
lean_object* v___x_1870_; uint32_t v___x_1871_; uint32_t v___x_1872_; uint64_t v___x_1873_; uint64_t v___x_1874_; uint64_t v___x_1875_; uint64_t v___x_1876_; uint64_t v___x_1877_; uint32_t v___x_1878_; lean_object* v___x_1879_; uint32_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1870_ = lean_unsigned_to_nat(1u);
v___x_1871_ = 1;
v___x_1872_ = lean_uint32_add(v___y_1869_, v___x_1871_);
v___x_1873_ = lean_uint32_to_uint64(v___x_1872_);
v___x_1874_ = l_Lean_Expr_Data_hash(v___x_1834_);
v___x_1875_ = l_Lean_Expr_Data_hash(v___x_1837_);
v___x_1876_ = lean_uint64_mix_hash(v___x_1874_, v___x_1875_);
v___x_1877_ = lean_uint64_mix_hash(v___x_1873_, v___x_1876_);
v___x_1878_ = l_Lean_Expr_Data_looseBVarRange(v___x_1834_);
v___x_1879_ = lean_uint32_to_nat(v___x_1878_);
v___x_1880_ = l_Lean_Expr_Data_looseBVarRange(v___x_1837_);
v___x_1881_ = lean_uint32_to_nat(v___x_1880_);
v___x_1882_ = lean_nat_sub(v___x_1881_, v___x_1870_);
lean_dec(v___x_1881_);
v___x_1883_ = lean_nat_dec_le(v___x_1879_, v___x_1882_);
if (v___x_1883_ == 0)
{
lean_dec(v___x_1882_);
v___y_1863_ = v___x_1872_;
v___y_1864_ = v___x_1877_;
v___y_1865_ = v___x_1879_;
goto v___jp_1862_;
}
else
{
lean_dec(v___x_1879_);
v___y_1863_ = v___x_1872_;
v___y_1864_ = v___x_1877_;
v___y_1865_ = v___x_1882_;
goto v___jp_1862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* v_binderName_1887_, lean_object* v_binderType_1888_, lean_object* v_body_1889_, lean_object* v_binderInfo_1890_){
_start:
{
uint8_t v_binderInfo_boxed_1891_; lean_object* v_res_1892_; 
v_binderInfo_boxed_1891_ = lean_unbox(v_binderInfo_1890_);
v_res_1892_ = l_Lean_Expr_lam___override(v_binderName_1887_, v_binderType_1888_, v_body_1889_, v_binderInfo_boxed_1891_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object* v_binderName_1893_, lean_object* v_binderType_1894_, lean_object* v_body_1895_, uint8_t v_binderInfo_1896_){
_start:
{
uint8_t v___y_1898_; uint32_t v___y_1899_; uint8_t v___y_1900_; uint64_t v___y_1901_; lean_object* v___y_1902_; uint8_t v___y_1903_; uint8_t v___y_1904_; uint64_t v___x_1907_; uint8_t v___x_1908_; uint32_t v___x_1909_; uint64_t v___x_1910_; uint8_t v___y_1912_; uint32_t v___y_1913_; uint8_t v___y_1914_; uint64_t v___y_1915_; lean_object* v___y_1916_; uint8_t v___y_1917_; uint32_t v___y_1921_; uint8_t v___y_1922_; uint64_t v___y_1923_; lean_object* v___y_1924_; uint8_t v___y_1925_; uint32_t v___y_1929_; uint64_t v___y_1930_; lean_object* v___y_1931_; uint8_t v___y_1932_; uint32_t v___y_1936_; uint64_t v___y_1937_; lean_object* v___y_1938_; uint32_t v___y_1942_; uint8_t v___x_1957_; uint32_t v___x_1958_; uint8_t v___x_1959_; 
v___x_1907_ = lean_expr_data(v_binderType_1894_);
v___x_1908_ = l_Lean_Expr_Data_approxDepth(v___x_1907_);
v___x_1909_ = lean_uint8_to_uint32(v___x_1908_);
v___x_1910_ = lean_expr_data(v_body_1895_);
v___x_1957_ = l_Lean_Expr_Data_approxDepth(v___x_1910_);
v___x_1958_ = lean_uint8_to_uint32(v___x_1957_);
v___x_1959_ = lean_uint32_dec_le(v___x_1909_, v___x_1958_);
if (v___x_1959_ == 0)
{
v___y_1942_ = v___x_1909_;
goto v___jp_1941_;
}
else
{
v___y_1942_ = v___x_1958_;
goto v___jp_1941_;
}
v___jp_1897_:
{
uint64_t v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_expr_mk_data(v___y_1901_, v___y_1902_, v___y_1899_, v___y_1900_, v___y_1898_, v___y_1903_, v___y_1904_);
v___x_1906_ = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(v___x_1906_, 0, v_binderName_1893_);
lean_ctor_set(v___x_1906_, 1, v_binderType_1894_);
lean_ctor_set(v___x_1906_, 2, v_body_1895_);
lean_ctor_set_uint64(v___x_1906_, sizeof(void*)*3, v___x_1905_);
lean_ctor_set_uint8(v___x_1906_, sizeof(void*)*3 + 8, v_binderInfo_1896_);
return v___x_1906_;
}
v___jp_1911_:
{
uint8_t v___x_1918_; 
v___x_1918_ = l_Lean_Expr_Data_hasLevelParam(v___x_1907_);
if (v___x_1918_ == 0)
{
uint8_t v___x_1919_; 
v___x_1919_ = l_Lean_Expr_Data_hasLevelParam(v___x_1910_);
v___y_1898_ = v___y_1912_;
v___y_1899_ = v___y_1913_;
v___y_1900_ = v___y_1914_;
v___y_1901_ = v___y_1915_;
v___y_1902_ = v___y_1916_;
v___y_1903_ = v___y_1917_;
v___y_1904_ = v___x_1919_;
goto v___jp_1897_;
}
else
{
v___y_1898_ = v___y_1912_;
v___y_1899_ = v___y_1913_;
v___y_1900_ = v___y_1914_;
v___y_1901_ = v___y_1915_;
v___y_1902_ = v___y_1916_;
v___y_1903_ = v___y_1917_;
v___y_1904_ = v___x_1918_;
goto v___jp_1897_;
}
}
v___jp_1920_:
{
uint8_t v___x_1926_; 
v___x_1926_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1907_);
if (v___x_1926_ == 0)
{
uint8_t v___x_1927_; 
v___x_1927_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1910_);
v___y_1912_ = v___y_1925_;
v___y_1913_ = v___y_1921_;
v___y_1914_ = v___y_1922_;
v___y_1915_ = v___y_1923_;
v___y_1916_ = v___y_1924_;
v___y_1917_ = v___x_1927_;
goto v___jp_1911_;
}
else
{
v___y_1912_ = v___y_1925_;
v___y_1913_ = v___y_1921_;
v___y_1914_ = v___y_1922_;
v___y_1915_ = v___y_1923_;
v___y_1916_ = v___y_1924_;
v___y_1917_ = v___x_1926_;
goto v___jp_1911_;
}
}
v___jp_1928_:
{
uint8_t v___x_1933_; 
v___x_1933_ = l_Lean_Expr_Data_hasExprMVar(v___x_1907_);
if (v___x_1933_ == 0)
{
uint8_t v___x_1934_; 
v___x_1934_ = l_Lean_Expr_Data_hasExprMVar(v___x_1910_);
v___y_1921_ = v___y_1929_;
v___y_1922_ = v___y_1932_;
v___y_1923_ = v___y_1930_;
v___y_1924_ = v___y_1931_;
v___y_1925_ = v___x_1934_;
goto v___jp_1920_;
}
else
{
v___y_1921_ = v___y_1929_;
v___y_1922_ = v___y_1932_;
v___y_1923_ = v___y_1930_;
v___y_1924_ = v___y_1931_;
v___y_1925_ = v___x_1933_;
goto v___jp_1920_;
}
}
v___jp_1935_:
{
uint8_t v___x_1939_; 
v___x_1939_ = l_Lean_Expr_Data_hasFVar(v___x_1907_);
if (v___x_1939_ == 0)
{
uint8_t v___x_1940_; 
v___x_1940_ = l_Lean_Expr_Data_hasFVar(v___x_1910_);
v___y_1929_ = v___y_1936_;
v___y_1930_ = v___y_1937_;
v___y_1931_ = v___y_1938_;
v___y_1932_ = v___x_1940_;
goto v___jp_1928_;
}
else
{
v___y_1929_ = v___y_1936_;
v___y_1930_ = v___y_1937_;
v___y_1931_ = v___y_1938_;
v___y_1932_ = v___x_1939_;
goto v___jp_1928_;
}
}
v___jp_1941_:
{
lean_object* v___x_1943_; uint32_t v___x_1944_; uint32_t v___x_1945_; uint64_t v___x_1946_; uint64_t v___x_1947_; uint64_t v___x_1948_; uint64_t v___x_1949_; uint64_t v___x_1950_; uint32_t v___x_1951_; lean_object* v___x_1952_; uint32_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1943_ = lean_unsigned_to_nat(1u);
v___x_1944_ = 1;
v___x_1945_ = lean_uint32_add(v___y_1942_, v___x_1944_);
v___x_1946_ = lean_uint32_to_uint64(v___x_1945_);
v___x_1947_ = l_Lean_Expr_Data_hash(v___x_1907_);
v___x_1948_ = l_Lean_Expr_Data_hash(v___x_1910_);
v___x_1949_ = lean_uint64_mix_hash(v___x_1947_, v___x_1948_);
v___x_1950_ = lean_uint64_mix_hash(v___x_1946_, v___x_1949_);
v___x_1951_ = l_Lean_Expr_Data_looseBVarRange(v___x_1907_);
v___x_1952_ = lean_uint32_to_nat(v___x_1951_);
v___x_1953_ = l_Lean_Expr_Data_looseBVarRange(v___x_1910_);
v___x_1954_ = lean_uint32_to_nat(v___x_1953_);
v___x_1955_ = lean_nat_sub(v___x_1954_, v___x_1943_);
lean_dec(v___x_1954_);
v___x_1956_ = lean_nat_dec_le(v___x_1952_, v___x_1955_);
if (v___x_1956_ == 0)
{
lean_dec(v___x_1955_);
v___y_1936_ = v___x_1945_;
v___y_1937_ = v___x_1950_;
v___y_1938_ = v___x_1952_;
goto v___jp_1935_;
}
else
{
lean_dec(v___x_1952_);
v___y_1936_ = v___x_1945_;
v___y_1937_ = v___x_1950_;
v___y_1938_ = v___x_1955_;
goto v___jp_1935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* v_binderName_1960_, lean_object* v_binderType_1961_, lean_object* v_body_1962_, lean_object* v_binderInfo_1963_){
_start:
{
uint8_t v_binderInfo_boxed_1964_; lean_object* v_res_1965_; 
v_binderInfo_boxed_1964_ = lean_unbox(v_binderInfo_1963_);
v_res_1965_ = l_Lean_Expr_forallE___override(v_binderName_1960_, v_binderType_1961_, v_body_1962_, v_binderInfo_boxed_1964_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object* v_declName_1966_, lean_object* v_type_1967_, lean_object* v_value_1968_, lean_object* v_body_1969_, uint8_t v_nondep_1970_){
_start:
{
lean_object* v___y_1972_; uint8_t v___y_1973_; uint8_t v___y_1974_; uint8_t v___y_1975_; uint32_t v___y_1976_; uint64_t v___y_1977_; uint8_t v___y_1978_; lean_object* v___y_1982_; uint8_t v___y_1983_; uint8_t v___y_1984_; uint8_t v___y_1985_; uint64_t v___y_1986_; uint64_t v___y_1987_; uint32_t v___y_1988_; uint8_t v___y_1989_; uint64_t v___x_1991_; uint8_t v___x_1992_; uint32_t v___x_1993_; uint64_t v___x_1994_; lean_object* v___y_1996_; uint8_t v___y_1997_; uint8_t v___y_1998_; uint64_t v___y_1999_; uint64_t v___y_2000_; uint32_t v___y_2001_; uint8_t v___y_2002_; lean_object* v___y_2006_; uint8_t v___y_2007_; uint8_t v___y_2008_; uint64_t v___y_2009_; uint32_t v___y_2010_; uint64_t v___y_2011_; uint8_t v___y_2012_; lean_object* v___y_2015_; uint8_t v___y_2016_; uint64_t v___y_2017_; uint32_t v___y_2018_; uint64_t v___y_2019_; uint8_t v___y_2020_; lean_object* v___y_2024_; uint8_t v___y_2025_; uint64_t v___y_2026_; uint64_t v___y_2027_; uint32_t v___y_2028_; uint8_t v___y_2029_; lean_object* v___y_2032_; uint64_t v___y_2033_; uint64_t v___y_2034_; uint32_t v___y_2035_; uint8_t v___y_2036_; lean_object* v___y_2040_; uint64_t v___y_2041_; uint32_t v___y_2042_; uint64_t v___y_2043_; uint8_t v___y_2044_; uint64_t v___y_2047_; uint32_t v___y_2048_; uint64_t v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2054_; uint64_t v___y_2055_; uint64_t v___y_2056_; uint32_t v___y_2057_; lean_object* v___y_2058_; uint64_t v___y_2064_; uint32_t v___y_2065_; uint32_t v___y_2082_; uint8_t v___x_2087_; uint32_t v___x_2088_; uint8_t v___x_2089_; 
v___x_1991_ = lean_expr_data(v_type_1967_);
v___x_1992_ = l_Lean_Expr_Data_approxDepth(v___x_1991_);
v___x_1993_ = lean_uint8_to_uint32(v___x_1992_);
v___x_1994_ = lean_expr_data(v_value_1968_);
v___x_2087_ = l_Lean_Expr_Data_approxDepth(v___x_1994_);
v___x_2088_ = lean_uint8_to_uint32(v___x_2087_);
v___x_2089_ = lean_uint32_dec_le(v___x_1993_, v___x_2088_);
if (v___x_2089_ == 0)
{
v___y_2082_ = v___x_1993_;
goto v___jp_2081_;
}
else
{
v___y_2082_ = v___x_2088_;
goto v___jp_2081_;
}
v___jp_1971_:
{
uint64_t v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_expr_mk_data(v___y_1977_, v___y_1972_, v___y_1976_, v___y_1974_, v___y_1975_, v___y_1973_, v___y_1978_);
v___x_1980_ = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(v___x_1980_, 0, v_declName_1966_);
lean_ctor_set(v___x_1980_, 1, v_type_1967_);
lean_ctor_set(v___x_1980_, 2, v_value_1968_);
lean_ctor_set(v___x_1980_, 3, v_body_1969_);
lean_ctor_set_uint64(v___x_1980_, sizeof(void*)*4, v___x_1979_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*4 + 8, v_nondep_1970_);
return v___x_1980_;
}
v___jp_1981_:
{
if (v___y_1989_ == 0)
{
uint8_t v___x_1990_; 
v___x_1990_ = l_Lean_Expr_Data_hasLevelParam(v___y_1986_);
v___y_1972_ = v___y_1982_;
v___y_1973_ = v___y_1983_;
v___y_1974_ = v___y_1984_;
v___y_1975_ = v___y_1985_;
v___y_1976_ = v___y_1988_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___x_1990_;
goto v___jp_1971_;
}
else
{
v___y_1972_ = v___y_1982_;
v___y_1973_ = v___y_1983_;
v___y_1974_ = v___y_1984_;
v___y_1975_ = v___y_1985_;
v___y_1976_ = v___y_1988_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1989_;
goto v___jp_1971_;
}
}
v___jp_1995_:
{
uint8_t v___x_2003_; 
v___x_2003_ = l_Lean_Expr_Data_hasLevelParam(v___x_1991_);
if (v___x_2003_ == 0)
{
uint8_t v___x_2004_; 
v___x_2004_ = l_Lean_Expr_Data_hasLevelParam(v___x_1994_);
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_2002_;
v___y_1984_ = v___y_1997_;
v___y_1985_ = v___y_1998_;
v___y_1986_ = v___y_1999_;
v___y_1987_ = v___y_2000_;
v___y_1988_ = v___y_2001_;
v___y_1989_ = v___x_2004_;
goto v___jp_1981_;
}
else
{
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_2002_;
v___y_1984_ = v___y_1997_;
v___y_1985_ = v___y_1998_;
v___y_1986_ = v___y_1999_;
v___y_1987_ = v___y_2000_;
v___y_1988_ = v___y_2001_;
v___y_1989_ = v___x_2003_;
goto v___jp_1981_;
}
}
v___jp_2005_:
{
if (v___y_2012_ == 0)
{
uint8_t v___x_2013_; 
v___x_2013_ = l_Lean_Expr_Data_hasLevelMVar(v___y_2009_);
v___y_1996_ = v___y_2006_;
v___y_1997_ = v___y_2007_;
v___y_1998_ = v___y_2008_;
v___y_1999_ = v___y_2009_;
v___y_2000_ = v___y_2011_;
v___y_2001_ = v___y_2010_;
v___y_2002_ = v___x_2013_;
goto v___jp_1995_;
}
else
{
v___y_1996_ = v___y_2006_;
v___y_1997_ = v___y_2007_;
v___y_1998_ = v___y_2008_;
v___y_1999_ = v___y_2009_;
v___y_2000_ = v___y_2011_;
v___y_2001_ = v___y_2010_;
v___y_2002_ = v___y_2012_;
goto v___jp_1995_;
}
}
v___jp_2014_:
{
uint8_t v___x_2021_; 
v___x_2021_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1991_);
if (v___x_2021_ == 0)
{
uint8_t v___x_2022_; 
v___x_2022_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1994_);
v___y_2006_ = v___y_2015_;
v___y_2007_ = v___y_2016_;
v___y_2008_ = v___y_2020_;
v___y_2009_ = v___y_2017_;
v___y_2010_ = v___y_2018_;
v___y_2011_ = v___y_2019_;
v___y_2012_ = v___x_2022_;
goto v___jp_2005_;
}
else
{
v___y_2006_ = v___y_2015_;
v___y_2007_ = v___y_2016_;
v___y_2008_ = v___y_2020_;
v___y_2009_ = v___y_2017_;
v___y_2010_ = v___y_2018_;
v___y_2011_ = v___y_2019_;
v___y_2012_ = v___x_2021_;
goto v___jp_2005_;
}
}
v___jp_2023_:
{
if (v___y_2029_ == 0)
{
uint8_t v___x_2030_; 
v___x_2030_ = l_Lean_Expr_Data_hasExprMVar(v___y_2026_);
v___y_2015_ = v___y_2024_;
v___y_2016_ = v___y_2025_;
v___y_2017_ = v___y_2026_;
v___y_2018_ = v___y_2028_;
v___y_2019_ = v___y_2027_;
v___y_2020_ = v___x_2030_;
goto v___jp_2014_;
}
else
{
v___y_2015_ = v___y_2024_;
v___y_2016_ = v___y_2025_;
v___y_2017_ = v___y_2026_;
v___y_2018_ = v___y_2028_;
v___y_2019_ = v___y_2027_;
v___y_2020_ = v___y_2029_;
goto v___jp_2014_;
}
}
v___jp_2031_:
{
uint8_t v___x_2037_; 
v___x_2037_ = l_Lean_Expr_Data_hasExprMVar(v___x_1991_);
if (v___x_2037_ == 0)
{
uint8_t v___x_2038_; 
v___x_2038_ = l_Lean_Expr_Data_hasExprMVar(v___x_1994_);
v___y_2024_ = v___y_2032_;
v___y_2025_ = v___y_2036_;
v___y_2026_ = v___y_2033_;
v___y_2027_ = v___y_2034_;
v___y_2028_ = v___y_2035_;
v___y_2029_ = v___x_2038_;
goto v___jp_2023_;
}
else
{
v___y_2024_ = v___y_2032_;
v___y_2025_ = v___y_2036_;
v___y_2026_ = v___y_2033_;
v___y_2027_ = v___y_2034_;
v___y_2028_ = v___y_2035_;
v___y_2029_ = v___x_2037_;
goto v___jp_2023_;
}
}
v___jp_2039_:
{
if (v___y_2044_ == 0)
{
uint8_t v___x_2045_; 
v___x_2045_ = l_Lean_Expr_Data_hasFVar(v___y_2041_);
v___y_2032_ = v___y_2040_;
v___y_2033_ = v___y_2041_;
v___y_2034_ = v___y_2043_;
v___y_2035_ = v___y_2042_;
v___y_2036_ = v___x_2045_;
goto v___jp_2031_;
}
else
{
v___y_2032_ = v___y_2040_;
v___y_2033_ = v___y_2041_;
v___y_2034_ = v___y_2043_;
v___y_2035_ = v___y_2042_;
v___y_2036_ = v___y_2044_;
goto v___jp_2031_;
}
}
v___jp_2046_:
{
uint8_t v___x_2051_; 
v___x_2051_ = l_Lean_Expr_Data_hasFVar(v___x_1991_);
if (v___x_2051_ == 0)
{
uint8_t v___x_2052_; 
v___x_2052_ = l_Lean_Expr_Data_hasFVar(v___x_1994_);
v___y_2040_ = v___y_2050_;
v___y_2041_ = v___y_2047_;
v___y_2042_ = v___y_2048_;
v___y_2043_ = v___y_2049_;
v___y_2044_ = v___x_2052_;
goto v___jp_2039_;
}
else
{
v___y_2040_ = v___y_2050_;
v___y_2041_ = v___y_2047_;
v___y_2042_ = v___y_2048_;
v___y_2043_ = v___y_2049_;
v___y_2044_ = v___x_2051_;
goto v___jp_2039_;
}
}
v___jp_2053_:
{
uint32_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2059_ = l_Lean_Expr_Data_looseBVarRange(v___y_2055_);
v___x_2060_ = lean_uint32_to_nat(v___x_2059_);
v___x_2061_ = lean_nat_sub(v___x_2060_, v___y_2054_);
lean_dec(v___x_2060_);
v___x_2062_ = lean_nat_dec_le(v___y_2058_, v___x_2061_);
if (v___x_2062_ == 0)
{
lean_dec(v___x_2061_);
v___y_2047_ = v___y_2055_;
v___y_2048_ = v___y_2057_;
v___y_2049_ = v___y_2056_;
v___y_2050_ = v___y_2058_;
goto v___jp_2046_;
}
else
{
lean_dec(v___y_2058_);
v___y_2047_ = v___y_2055_;
v___y_2048_ = v___y_2057_;
v___y_2049_ = v___y_2056_;
v___y_2050_ = v___x_2061_;
goto v___jp_2046_;
}
}
v___jp_2063_:
{
lean_object* v___x_2066_; uint32_t v___x_2067_; uint32_t v___x_2068_; uint64_t v___x_2069_; uint64_t v___x_2070_; uint64_t v___x_2071_; uint64_t v___x_2072_; uint64_t v___x_2073_; uint64_t v___x_2074_; uint64_t v___x_2075_; uint32_t v___x_2076_; lean_object* v___x_2077_; uint32_t v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2066_ = lean_unsigned_to_nat(1u);
v___x_2067_ = 1;
v___x_2068_ = lean_uint32_add(v___y_2065_, v___x_2067_);
v___x_2069_ = lean_uint32_to_uint64(v___x_2068_);
v___x_2070_ = l_Lean_Expr_Data_hash(v___x_1991_);
v___x_2071_ = l_Lean_Expr_Data_hash(v___x_1994_);
v___x_2072_ = l_Lean_Expr_Data_hash(v___y_2064_);
v___x_2073_ = lean_uint64_mix_hash(v___x_2071_, v___x_2072_);
v___x_2074_ = lean_uint64_mix_hash(v___x_2070_, v___x_2073_);
v___x_2075_ = lean_uint64_mix_hash(v___x_2069_, v___x_2074_);
v___x_2076_ = l_Lean_Expr_Data_looseBVarRange(v___x_1991_);
v___x_2077_ = lean_uint32_to_nat(v___x_2076_);
v___x_2078_ = l_Lean_Expr_Data_looseBVarRange(v___x_1994_);
v___x_2079_ = lean_uint32_to_nat(v___x_2078_);
v___x_2080_ = lean_nat_dec_le(v___x_2077_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_dec(v___x_2079_);
v___y_2054_ = v___x_2066_;
v___y_2055_ = v___y_2064_;
v___y_2056_ = v___x_2075_;
v___y_2057_ = v___x_2068_;
v___y_2058_ = v___x_2077_;
goto v___jp_2053_;
}
else
{
lean_dec(v___x_2077_);
v___y_2054_ = v___x_2066_;
v___y_2055_ = v___y_2064_;
v___y_2056_ = v___x_2075_;
v___y_2057_ = v___x_2068_;
v___y_2058_ = v___x_2079_;
goto v___jp_2053_;
}
}
v___jp_2081_:
{
uint64_t v___x_2083_; uint8_t v___x_2084_; uint32_t v___x_2085_; uint8_t v___x_2086_; 
v___x_2083_ = lean_expr_data(v_body_1969_);
v___x_2084_ = l_Lean_Expr_Data_approxDepth(v___x_2083_);
v___x_2085_ = lean_uint8_to_uint32(v___x_2084_);
v___x_2086_ = lean_uint32_dec_le(v___y_2082_, v___x_2085_);
if (v___x_2086_ == 0)
{
v___y_2064_ = v___x_2083_;
v___y_2065_ = v___y_2082_;
goto v___jp_2063_;
}
else
{
v___y_2064_ = v___x_2083_;
v___y_2065_ = v___x_2085_;
goto v___jp_2063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* v_declName_2090_, lean_object* v_type_2091_, lean_object* v_value_2092_, lean_object* v_body_2093_, lean_object* v_nondep_2094_){
_start:
{
uint8_t v_nondep_boxed_2095_; lean_object* v_res_2096_; 
v_nondep_boxed_2095_ = lean_unbox(v_nondep_2094_);
v_res_2096_ = l_Lean_Expr_letE___override(v_declName_2090_, v_type_2091_, v_value_2092_, v_body_2093_, v_nondep_boxed_2095_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* v_a_2097_){
_start:
{
uint64_t v___x_2098_; uint64_t v___x_2099_; uint64_t v___x_2100_; lean_object* v___x_2101_; uint32_t v___x_2102_; uint8_t v___x_2103_; uint64_t v___x_2104_; lean_object* v___x_2105_; 
v___x_2098_ = 3ULL;
v___x_2099_ = l_Lean_Literal_hash(v_a_2097_);
v___x_2100_ = lean_uint64_mix_hash(v___x_2098_, v___x_2099_);
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = 0;
v___x_2103_ = 0;
v___x_2104_ = lean_expr_mk_data(v___x_2100_, v___x_2101_, v___x_2102_, v___x_2103_, v___x_2103_, v___x_2103_, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(v___x_2105_, 0, v_a_2097_);
lean_ctor_set_uint64(v___x_2105_, sizeof(void*)*1, v___x_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* v_data_2106_, lean_object* v_expr_2107_){
_start:
{
uint64_t v___x_2108_; uint8_t v___x_2109_; uint32_t v___x_2110_; uint32_t v___x_2111_; uint32_t v___x_2112_; uint64_t v___x_2113_; uint64_t v___x_2114_; uint64_t v___x_2115_; uint32_t v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; uint8_t v___x_2119_; uint8_t v___x_2120_; uint8_t v___x_2121_; uint64_t v___x_2122_; lean_object* v___x_2123_; 
v___x_2108_ = lean_expr_data(v_expr_2107_);
v___x_2109_ = l_Lean_Expr_Data_approxDepth(v___x_2108_);
v___x_2110_ = lean_uint8_to_uint32(v___x_2109_);
v___x_2111_ = 1;
v___x_2112_ = lean_uint32_add(v___x_2110_, v___x_2111_);
v___x_2113_ = lean_uint32_to_uint64(v___x_2112_);
v___x_2114_ = l_Lean_Expr_Data_hash(v___x_2108_);
v___x_2115_ = lean_uint64_mix_hash(v___x_2113_, v___x_2114_);
v___x_2116_ = l_Lean_Expr_Data_looseBVarRange(v___x_2108_);
v___x_2117_ = lean_uint32_to_nat(v___x_2116_);
v___x_2118_ = l_Lean_Expr_Data_hasFVar(v___x_2108_);
v___x_2119_ = l_Lean_Expr_Data_hasExprMVar(v___x_2108_);
v___x_2120_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2108_);
v___x_2121_ = l_Lean_Expr_Data_hasLevelParam(v___x_2108_);
v___x_2122_ = lean_expr_mk_data(v___x_2115_, v___x_2117_, v___x_2112_, v___x_2118_, v___x_2119_, v___x_2120_, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(v___x_2123_, 0, v_data_2106_);
lean_ctor_set(v___x_2123_, 1, v_expr_2107_);
lean_ctor_set_uint64(v___x_2123_, sizeof(void*)*2, v___x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* v_typeName_2124_, lean_object* v_idx_2125_, lean_object* v_struct_2126_){
_start:
{
uint64_t v___x_2127_; uint8_t v___x_2128_; uint32_t v___x_2129_; uint32_t v___x_2130_; uint32_t v___x_2131_; uint64_t v___x_2132_; uint64_t v___y_2134_; 
v___x_2127_ = lean_expr_data(v_struct_2126_);
v___x_2128_ = l_Lean_Expr_Data_approxDepth(v___x_2127_);
v___x_2129_ = lean_uint8_to_uint32(v___x_2128_);
v___x_2130_ = 1;
v___x_2131_ = lean_uint32_add(v___x_2129_, v___x_2130_);
v___x_2132_ = lean_uint32_to_uint64(v___x_2131_);
if (lean_obj_tag(v_typeName_2124_) == 0)
{
uint64_t v___x_2148_; 
v___x_2148_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
v___y_2134_ = v___x_2148_;
goto v___jp_2133_;
}
else
{
uint64_t v_hash_2149_; 
v_hash_2149_ = lean_ctor_get_uint64(v_typeName_2124_, sizeof(void*)*2);
v___y_2134_ = v_hash_2149_;
goto v___jp_2133_;
}
v___jp_2133_:
{
uint64_t v___x_2135_; uint64_t v___x_2136_; uint64_t v___x_2137_; uint64_t v___x_2138_; uint64_t v___x_2139_; uint32_t v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; uint8_t v___x_2143_; uint8_t v___x_2144_; uint8_t v___x_2145_; uint64_t v___x_2146_; lean_object* v___x_2147_; 
v___x_2135_ = lean_uint64_of_nat(v_idx_2125_);
v___x_2136_ = l_Lean_Expr_Data_hash(v___x_2127_);
v___x_2137_ = lean_uint64_mix_hash(v___x_2135_, v___x_2136_);
v___x_2138_ = lean_uint64_mix_hash(v___y_2134_, v___x_2137_);
v___x_2139_ = lean_uint64_mix_hash(v___x_2132_, v___x_2138_);
v___x_2140_ = l_Lean_Expr_Data_looseBVarRange(v___x_2127_);
v___x_2141_ = lean_uint32_to_nat(v___x_2140_);
v___x_2142_ = l_Lean_Expr_Data_hasFVar(v___x_2127_);
v___x_2143_ = l_Lean_Expr_Data_hasExprMVar(v___x_2127_);
v___x_2144_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2127_);
v___x_2145_ = l_Lean_Expr_Data_hasLevelParam(v___x_2127_);
v___x_2146_ = lean_expr_mk_data(v___x_2139_, v___x_2141_, v___x_2131_, v___x_2142_, v___x_2143_, v___x_2144_, v___x_2145_);
v___x_2147_ = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(v___x_2147_, 0, v_typeName_2124_);
lean_ctor_set(v___x_2147_, 1, v_idx_2125_);
lean_ctor_set(v___x_2147_, 2, v_struct_2126_);
lean_ctor_set_uint64(v___x_2147_, sizeof(void*)*3, v___x_2146_);
return v___x_2147_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__5(lean_object* v_x_2150_){
_start:
{
if (lean_obj_tag(v_x_2150_) == 0)
{
uint8_t v___x_2151_; 
v___x_2151_ = 0;
return v___x_2151_;
}
else
{
lean_object* v_head_2152_; lean_object* v_tail_2153_; uint8_t v___x_2154_; 
v_head_2152_ = lean_ctor_get(v_x_2150_, 0);
v_tail_2153_ = lean_ctor_get(v_x_2150_, 1);
v___x_2154_ = l_Lean_Level_hasMVar(v_head_2152_);
if (v___x_2154_ == 0)
{
v_x_2150_ = v_tail_2153_;
goto _start;
}
else
{
return v___x_2154_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__5___boxed(lean_object* v_x_2156_){
_start:
{
uint8_t v_res_2157_; lean_object* v_r_2158_; 
v_res_2157_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_x_2156_);
lean_dec(v_x_2156_);
v_r_2158_ = lean_box(v_res_2157_);
return v_r_2158_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__6(lean_object* v_x_2159_){
_start:
{
if (lean_obj_tag(v_x_2159_) == 0)
{
uint8_t v___x_2160_; 
v___x_2160_ = 0;
return v___x_2160_;
}
else
{
lean_object* v_head_2161_; lean_object* v_tail_2162_; uint8_t v___x_2163_; 
v_head_2161_ = lean_ctor_get(v_x_2159_, 0);
v_tail_2162_ = lean_ctor_get(v_x_2159_, 1);
v___x_2163_ = l_Lean_Level_hasParam(v_head_2161_);
if (v___x_2163_ == 0)
{
v_x_2159_ = v_tail_2162_;
goto _start;
}
else
{
return v___x_2163_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__6___boxed(lean_object* v_x_2165_){
_start:
{
uint8_t v_res_2166_; lean_object* v_r_2167_; 
v_res_2166_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_x_2165_);
lean_dec(v_x_2165_);
v_r_2167_ = lean_box(v_res_2166_);
return v_r_2167_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t v_x_2168_, lean_object* v_x_2169_){
_start:
{
if (lean_obj_tag(v_x_2169_) == 0)
{
return v_x_2168_;
}
else
{
lean_object* v_head_2170_; lean_object* v_tail_2171_; uint64_t v___x_2172_; uint64_t v___x_2173_; 
v_head_2170_ = lean_ctor_get(v_x_2169_, 0);
v_tail_2171_ = lean_ctor_get(v_x_2169_, 1);
v___x_2172_ = l_Lean_Level_hash(v_head_2170_);
v___x_2173_ = lean_uint64_mix_hash(v_x_2168_, v___x_2172_);
v_x_2168_ = v___x_2173_;
v_x_2169_ = v_tail_2171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object* v_x_2175_, lean_object* v_x_2176_){
_start:
{
uint64_t v_x_1734__boxed_2177_; uint64_t v_res_2178_; lean_object* v_r_2179_; 
v_x_1734__boxed_2177_ = lean_unbox_uint64(v_x_2175_);
lean_dec_ref(v_x_2175_);
v_res_2178_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_1734__boxed_2177_, v_x_2176_);
lean_dec(v_x_2176_);
v_r_2179_ = lean_box_uint64(v_res_2178_);
return v_r_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* v_declName_2180_, lean_object* v_us_2181_){
_start:
{
uint64_t v___x_2182_; uint64_t v___y_2184_; 
v___x_2182_ = 5ULL;
if (lean_obj_tag(v_declName_2180_) == 0)
{
uint64_t v___x_2196_; 
v___x_2196_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
v___y_2184_ = v___x_2196_;
goto v___jp_2183_;
}
else
{
uint64_t v_hash_2197_; 
v_hash_2197_ = lean_ctor_get_uint64(v_declName_2180_, sizeof(void*)*2);
v___y_2184_ = v_hash_2197_;
goto v___jp_2183_;
}
v___jp_2183_:
{
uint64_t v___x_2185_; uint64_t v___x_2186_; uint64_t v___x_2187_; uint64_t v___x_2188_; lean_object* v___x_2189_; uint32_t v___x_2190_; uint8_t v___x_2191_; uint8_t v___x_2192_; uint8_t v___x_2193_; uint64_t v___x_2194_; lean_object* v___x_2195_; 
v___x_2185_ = 7ULL;
v___x_2186_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v___x_2185_, v_us_2181_);
v___x_2187_ = lean_uint64_mix_hash(v___y_2184_, v___x_2186_);
v___x_2188_ = lean_uint64_mix_hash(v___x_2182_, v___x_2187_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = 0;
v___x_2191_ = 0;
v___x_2192_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_us_2181_);
v___x_2193_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_us_2181_);
v___x_2194_ = lean_expr_mk_data(v___x_2188_, v___x_2189_, v___x_2190_, v___x_2191_, v___x_2191_, v___x_2192_, v___x_2193_);
v___x_2195_ = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(v___x_2195_, 0, v_declName_2180_);
lean_ctor_set(v___x_2195_, 1, v_us_2181_);
lean_ctor_set_uint64(v___x_2195_, sizeof(void*)*2, v___x_2194_);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = lean_unsigned_to_nat(0u);
v___x_2200_ = l_Lean_instReprLevel_repr(v___y_2198_, v___x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_){
_start:
{
if (lean_obj_tag(v_x_2203_) == 0)
{
lean_dec(v_x_2201_);
return v_x_2202_;
}
else
{
lean_object* v_head_2204_; lean_object* v_tail_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2216_; 
v_head_2204_ = lean_ctor_get(v_x_2203_, 0);
v_tail_2205_ = lean_ctor_get(v_x_2203_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_x_2203_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2207_ = v_x_2203_;
v_isShared_2208_ = v_isSharedCheck_2216_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_tail_2205_);
lean_inc(v_head_2204_);
lean_dec(v_x_2203_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2216_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
lean_inc(v_x_2201_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set_tag(v___x_2207_, 5);
lean_ctor_set(v___x_2207_, 1, v_x_2201_);
lean_ctor_set(v___x_2207_, 0, v_x_2202_);
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_x_2202_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_x_2201_);
v___x_2210_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = l_Lean_instReprLevel_repr(v_head_2204_, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2210_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v_x_2202_ = v___x_2213_;
v_x_2203_ = v_tail_2205_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object* v_x_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_){
_start:
{
if (lean_obj_tag(v_x_2219_) == 0)
{
lean_dec(v_x_2217_);
return v_x_2218_;
}
else
{
lean_object* v_head_2220_; lean_object* v_tail_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2232_; 
v_head_2220_ = lean_ctor_get(v_x_2219_, 0);
v_tail_2221_ = lean_ctor_get(v_x_2219_, 1);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_x_2219_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2223_ = v_x_2219_;
v_isShared_2224_ = v_isSharedCheck_2232_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_tail_2221_);
lean_inc(v_head_2220_);
lean_dec(v_x_2219_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2232_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
lean_inc(v_x_2217_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set_tag(v___x_2223_, 5);
lean_ctor_set(v___x_2223_, 1, v_x_2217_);
lean_ctor_set(v___x_2223_, 0, v_x_2218_);
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_x_2218_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_x_2217_);
v___x_2226_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2227_ = lean_unsigned_to_nat(0u);
v___x_2228_ = l_Lean_instReprLevel_repr(v_head_2220_, v___x_2227_);
v___x_2229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2226_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(v_x_2217_, v___x_2229_, v_tail_2221_);
return v___x_2230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
if (lean_obj_tag(v_x_2233_) == 0)
{
lean_object* v___x_2235_; 
lean_dec(v_x_2234_);
v___x_2235_ = lean_box(0);
return v___x_2235_;
}
else
{
lean_object* v_tail_2236_; 
v_tail_2236_ = lean_ctor_get(v_x_2233_, 1);
if (lean_obj_tag(v_tail_2236_) == 0)
{
lean_object* v_head_2237_; lean_object* v___x_2238_; 
lean_dec(v_x_2234_);
v_head_2237_ = lean_ctor_get(v_x_2233_, 0);
lean_inc(v_head_2237_);
lean_dec_ref_known(v_x_2233_, 2);
v___x_2238_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2237_);
return v___x_2238_;
}
else
{
lean_object* v_head_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
lean_inc(v_tail_2236_);
v_head_2239_ = lean_ctor_get(v_x_2233_, 0);
lean_inc(v_head_2239_);
lean_dec_ref_known(v_x_2233_, 2);
v___x_2240_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2239_);
v___x_2241_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(v_x_2234_, v___x_2240_, v_tail_2236_);
return v___x_2241_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2));
v___x_2254_ = lean_string_length(v___x_2253_);
return v___x_2254_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7);
v___x_2256_ = lean_nat_to_int(v___x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object* v_a_2261_){
_start:
{
if (lean_obj_tag(v_a_2261_) == 0)
{
lean_object* v___x_2262_; 
v___x_2262_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1));
return v___x_2262_;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; 
v___x_2263_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5));
v___x_2264_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(v_a_2261_, v___x_2263_);
v___x_2265_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8);
v___x_2266_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9));
v___x_2267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_ctor_set(v___x_2267_, 1, v___x_2264_);
v___x_2268_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10));
v___x_2269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2265_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = 0;
v___x_2272_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*1, v___x_2271_);
return v___x_2272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object* v_x_2345_, lean_object* v_prec_2346_){
_start:
{
switch(lean_obj_tag(v_x_2345_))
{
case 0:
{
lean_object* v_deBruijnIndex_2347_; lean_object* v___y_2349_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
v_deBruijnIndex_2347_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_deBruijnIndex_2347_);
lean_dec_ref_known(v_x_2345_, 1);
v___x_2358_ = lean_unsigned_to_nat(1024u);
v___x_2359_ = lean_nat_dec_le(v___x_2358_, v_prec_2346_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2349_ = v___x_2360_;
goto v___jp_2348_;
}
else
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2349_ = v___x_2361_;
goto v___jp_2348_;
}
v___jp_2348_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2350_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__2));
v___x_2351_ = l_Nat_reprFast(v_deBruijnIndex_2347_);
v___x_2352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
v___x_2353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2350_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
lean_inc(v___y_2349_);
v___x_2354_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___y_2349_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = 0;
v___x_2356_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*1, v___x_2355_);
v___x_2357_ = l_Repr_addAppParen(v___x_2356_, v_prec_2346_);
return v___x_2357_;
}
}
case 1:
{
lean_object* v_fvarId_2362_; lean_object* v___y_2364_; lean_object* v___x_2373_; uint8_t v___x_2374_; 
v_fvarId_2362_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_fvarId_2362_);
lean_dec_ref_known(v_x_2345_, 1);
v___x_2373_ = lean_unsigned_to_nat(1024u);
v___x_2374_ = lean_nat_dec_le(v___x_2373_, v_prec_2346_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2364_ = v___x_2375_;
goto v___jp_2363_;
}
else
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2364_ = v___x_2376_;
goto v___jp_2363_;
}
v___jp_2363_:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2365_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__5));
v___x_2366_ = lean_unsigned_to_nat(1024u);
v___x_2367_ = l_Lean_Name_reprPrec(v_fvarId_2362_, v___x_2366_);
v___x_2368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2365_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
lean_inc(v___y_2364_);
v___x_2369_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___y_2364_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = 0;
v___x_2371_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set_uint8(v___x_2371_, sizeof(void*)*1, v___x_2370_);
v___x_2372_ = l_Repr_addAppParen(v___x_2371_, v_prec_2346_);
return v___x_2372_;
}
}
case 2:
{
lean_object* v_mvarId_2377_; lean_object* v___y_2379_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v_mvarId_2377_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_mvarId_2377_);
lean_dec_ref_known(v_x_2345_, 1);
v___x_2388_ = lean_unsigned_to_nat(1024u);
v___x_2389_ = lean_nat_dec_le(v___x_2388_, v_prec_2346_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; 
v___x_2390_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2379_ = v___x_2390_;
goto v___jp_2378_;
}
else
{
lean_object* v___x_2391_; 
v___x_2391_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2379_ = v___x_2391_;
goto v___jp_2378_;
}
v___jp_2378_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2380_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__8));
v___x_2381_ = lean_unsigned_to_nat(1024u);
v___x_2382_ = l_Lean_Name_reprPrec(v_mvarId_2377_, v___x_2381_);
v___x_2383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2380_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
lean_inc(v___y_2379_);
v___x_2384_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___y_2379_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = 0;
v___x_2386_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set_uint8(v___x_2386_, sizeof(void*)*1, v___x_2385_);
v___x_2387_ = l_Repr_addAppParen(v___x_2386_, v_prec_2346_);
return v___x_2387_;
}
}
case 3:
{
lean_object* v_u_2392_; lean_object* v___y_2394_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v_u_2392_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_u_2392_);
lean_dec_ref_known(v_x_2345_, 1);
v___x_2403_ = lean_unsigned_to_nat(1024u);
v___x_2404_ = lean_nat_dec_le(v___x_2403_, v_prec_2346_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; 
v___x_2405_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2394_ = v___x_2405_;
goto v___jp_2393_;
}
else
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2394_ = v___x_2406_;
goto v___jp_2393_;
}
v___jp_2393_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2395_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__11));
v___x_2396_ = lean_unsigned_to_nat(1024u);
v___x_2397_ = l_Lean_instReprLevel_repr(v_u_2392_, v___x_2396_);
v___x_2398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2395_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
lean_inc(v___y_2394_);
v___x_2399_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___y_2394_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = 0;
v___x_2401_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set_uint8(v___x_2401_, sizeof(void*)*1, v___x_2400_);
v___x_2402_ = l_Repr_addAppParen(v___x_2401_, v_prec_2346_);
return v___x_2402_;
}
}
case 4:
{
lean_object* v_declName_2407_; lean_object* v_us_2408_; lean_object* v___y_2410_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v_declName_2407_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_declName_2407_);
v_us_2408_ = lean_ctor_get(v_x_2345_, 1);
lean_inc(v_us_2408_);
lean_dec_ref_known(v_x_2345_, 2);
v___x_2423_ = lean_unsigned_to_nat(1024u);
v___x_2424_ = lean_nat_dec_le(v___x_2423_, v_prec_2346_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2410_ = v___x_2425_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2410_ = v___x_2426_;
goto v___jp_2409_;
}
v___jp_2409_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2411_ = lean_box(1);
v___x_2412_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__14));
v___x_2413_ = lean_unsigned_to_nat(1024u);
v___x_2414_ = l_Lean_Name_reprPrec(v_declName_2407_, v___x_2413_);
v___x_2415_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2412_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
lean_ctor_set(v___x_2416_, 1, v___x_2411_);
v___x_2417_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_us_2408_);
v___x_2418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
lean_inc(v___y_2410_);
v___x_2419_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___y_2410_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
v___x_2420_ = 0;
v___x_2421_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2421_, 0, v___x_2419_);
lean_ctor_set_uint8(v___x_2421_, sizeof(void*)*1, v___x_2420_);
v___x_2422_ = l_Repr_addAppParen(v___x_2421_, v_prec_2346_);
return v___x_2422_;
}
}
case 5:
{
lean_object* v_fn_2427_; lean_object* v_arg_2428_; lean_object* v___x_2429_; lean_object* v___y_2431_; uint8_t v___x_2443_; 
v_fn_2427_ = lean_ctor_get(v_x_2345_, 0);
lean_inc_ref(v_fn_2427_);
v_arg_2428_ = lean_ctor_get(v_x_2345_, 1);
lean_inc_ref(v_arg_2428_);
lean_dec_ref_known(v_x_2345_, 2);
v___x_2429_ = lean_unsigned_to_nat(1024u);
v___x_2443_ = lean_nat_dec_le(v___x_2429_, v_prec_2346_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; 
v___x_2444_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2431_ = v___x_2444_;
goto v___jp_2430_;
}
else
{
lean_object* v___x_2445_; 
v___x_2445_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2431_ = v___x_2445_;
goto v___jp_2430_;
}
v___jp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2432_ = lean_box(1);
v___x_2433_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__17));
v___x_2434_ = l_Lean_instReprExpr_repr(v_fn_2427_, v___x_2429_);
v___x_2435_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v___x_2432_);
v___x_2437_ = l_Lean_instReprExpr_repr(v_arg_2428_, v___x_2429_);
v___x_2438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
lean_inc(v___y_2431_);
v___x_2439_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___y_2431_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = 0;
v___x_2441_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set_uint8(v___x_2441_, sizeof(void*)*1, v___x_2440_);
v___x_2442_ = l_Repr_addAppParen(v___x_2441_, v_prec_2346_);
return v___x_2442_;
}
}
case 6:
{
lean_object* v_binderName_2446_; lean_object* v_binderType_2447_; lean_object* v_body_2448_; uint8_t v_binderInfo_2449_; lean_object* v___x_2450_; lean_object* v___y_2452_; uint8_t v___x_2470_; 
v_binderName_2446_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_binderName_2446_);
v_binderType_2447_ = lean_ctor_get(v_x_2345_, 1);
lean_inc_ref(v_binderType_2447_);
v_body_2448_ = lean_ctor_get(v_x_2345_, 2);
lean_inc_ref(v_body_2448_);
v_binderInfo_2449_ = lean_ctor_get_uint8(v_x_2345_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2345_, 3);
v___x_2450_ = lean_unsigned_to_nat(1024u);
v___x_2470_ = lean_nat_dec_le(v___x_2450_, v_prec_2346_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2452_ = v___x_2471_;
goto v___jp_2451_;
}
else
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2452_ = v___x_2472_;
goto v___jp_2451_;
}
v___jp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2453_ = lean_box(1);
v___x_2454_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__20));
v___x_2455_ = l_Lean_Name_reprPrec(v_binderName_2446_, v___x_2450_);
v___x_2456_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
lean_ctor_set(v___x_2457_, 1, v___x_2453_);
v___x_2458_ = l_Lean_instReprExpr_repr(v_binderType_2447_, v___x_2450_);
v___x_2459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2457_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
lean_ctor_set(v___x_2460_, 1, v___x_2453_);
v___x_2461_ = l_Lean_instReprExpr_repr(v_body_2448_, v___x_2450_);
v___x_2462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
lean_ctor_set(v___x_2463_, 1, v___x_2453_);
v___x_2464_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2449_, v___x_2450_);
v___x_2465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
lean_inc(v___y_2452_);
v___x_2466_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___y_2452_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = 0;
v___x_2468_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2468_, 0, v___x_2466_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*1, v___x_2467_);
v___x_2469_ = l_Repr_addAppParen(v___x_2468_, v_prec_2346_);
return v___x_2469_;
}
}
case 7:
{
lean_object* v_binderName_2473_; lean_object* v_binderType_2474_; lean_object* v_body_2475_; uint8_t v_binderInfo_2476_; lean_object* v___x_2477_; lean_object* v___y_2479_; uint8_t v___x_2497_; 
v_binderName_2473_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_binderName_2473_);
v_binderType_2474_ = lean_ctor_get(v_x_2345_, 1);
lean_inc_ref(v_binderType_2474_);
v_body_2475_ = lean_ctor_get(v_x_2345_, 2);
lean_inc_ref(v_body_2475_);
v_binderInfo_2476_ = lean_ctor_get_uint8(v_x_2345_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2345_, 3);
v___x_2477_ = lean_unsigned_to_nat(1024u);
v___x_2497_ = lean_nat_dec_le(v___x_2477_, v_prec_2346_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2479_ = v___x_2498_;
goto v___jp_2478_;
}
else
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2479_ = v___x_2499_;
goto v___jp_2478_;
}
v___jp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2480_ = lean_box(1);
v___x_2481_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__23));
v___x_2482_ = l_Lean_Name_reprPrec(v_binderName_2473_, v___x_2477_);
v___x_2483_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
lean_ctor_set(v___x_2484_, 1, v___x_2480_);
v___x_2485_ = l_Lean_instReprExpr_repr(v_binderType_2474_, v___x_2477_);
v___x_2486_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
lean_ctor_set(v___x_2487_, 1, v___x_2480_);
v___x_2488_ = l_Lean_instReprExpr_repr(v_body_2475_, v___x_2477_);
v___x_2489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2487_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
lean_ctor_set(v___x_2490_, 1, v___x_2480_);
v___x_2491_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2476_, v___x_2477_);
v___x_2492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2490_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
lean_inc(v___y_2479_);
v___x_2493_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___y_2479_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = 0;
v___x_2495_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2495_, 0, v___x_2493_);
lean_ctor_set_uint8(v___x_2495_, sizeof(void*)*1, v___x_2494_);
v___x_2496_ = l_Repr_addAppParen(v___x_2495_, v_prec_2346_);
return v___x_2496_;
}
}
case 8:
{
lean_object* v_declName_2500_; lean_object* v_type_2501_; lean_object* v_value_2502_; lean_object* v_body_2503_; uint8_t v_nondep_2504_; lean_object* v___x_2505_; lean_object* v___y_2507_; uint8_t v___x_2528_; 
v_declName_2500_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_declName_2500_);
v_type_2501_ = lean_ctor_get(v_x_2345_, 1);
lean_inc_ref(v_type_2501_);
v_value_2502_ = lean_ctor_get(v_x_2345_, 2);
lean_inc_ref(v_value_2502_);
v_body_2503_ = lean_ctor_get(v_x_2345_, 3);
lean_inc_ref(v_body_2503_);
v_nondep_2504_ = lean_ctor_get_uint8(v_x_2345_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_x_2345_, 4);
v___x_2505_ = lean_unsigned_to_nat(1024u);
v___x_2528_ = lean_nat_dec_le(v___x_2505_, v_prec_2346_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2507_ = v___x_2529_;
goto v___jp_2506_;
}
else
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2507_ = v___x_2530_;
goto v___jp_2506_;
}
v___jp_2506_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2508_ = lean_box(1);
v___x_2509_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__26));
v___x_2510_ = l_Lean_Name_reprPrec(v_declName_2500_, v___x_2505_);
v___x_2511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
lean_ctor_set(v___x_2512_, 1, v___x_2508_);
v___x_2513_ = l_Lean_instReprExpr_repr(v_type_2501_, v___x_2505_);
v___x_2514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
lean_ctor_set(v___x_2515_, 1, v___x_2508_);
v___x_2516_ = l_Lean_instReprExpr_repr(v_value_2502_, v___x_2505_);
v___x_2517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
lean_ctor_set(v___x_2518_, 1, v___x_2508_);
v___x_2519_ = l_Lean_instReprExpr_repr(v_body_2503_, v___x_2505_);
v___x_2520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v___x_2508_);
v___x_2522_ = l_Bool_repr___redArg(v_nondep_2504_);
v___x_2523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2521_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
lean_inc(v___y_2507_);
v___x_2524_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___y_2507_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = 0;
v___x_2526_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2526_, 0, v___x_2524_);
lean_ctor_set_uint8(v___x_2526_, sizeof(void*)*1, v___x_2525_);
v___x_2527_ = l_Repr_addAppParen(v___x_2526_, v_prec_2346_);
return v___x_2527_;
}
}
case 9:
{
lean_object* v_a_2531_; lean_object* v___y_2533_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v_a_2531_ = lean_ctor_get(v_x_2345_, 0);
lean_inc_ref(v_a_2531_);
lean_dec_ref_known(v_x_2345_, 1);
v___x_2542_ = lean_unsigned_to_nat(1024u);
v___x_2543_ = lean_nat_dec_le(v___x_2542_, v_prec_2346_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2533_ = v___x_2544_;
goto v___jp_2532_;
}
else
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2533_ = v___x_2545_;
goto v___jp_2532_;
}
v___jp_2532_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2534_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__29));
v___x_2535_ = lean_unsigned_to_nat(1024u);
v___x_2536_ = l_Lean_instReprLiteral_repr(v_a_2531_, v___x_2535_);
v___x_2537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2534_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
lean_inc(v___y_2533_);
v___x_2538_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___y_2533_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = 0;
v___x_2540_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2540_, 0, v___x_2538_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*1, v___x_2539_);
v___x_2541_ = l_Repr_addAppParen(v___x_2540_, v_prec_2346_);
return v___x_2541_;
}
}
case 10:
{
lean_object* v_data_2546_; lean_object* v_expr_2547_; lean_object* v___x_2548_; lean_object* v___y_2550_; uint8_t v___x_2562_; 
v_data_2546_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_data_2546_);
v_expr_2547_ = lean_ctor_get(v_x_2345_, 1);
lean_inc_ref(v_expr_2547_);
lean_dec_ref_known(v_x_2345_, 2);
v___x_2548_ = lean_unsigned_to_nat(1024u);
v___x_2562_ = lean_nat_dec_le(v___x_2548_, v_prec_2346_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2550_ = v___x_2563_;
goto v___jp_2549_;
}
else
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2550_ = v___x_2564_;
goto v___jp_2549_;
}
v___jp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2551_ = lean_box(1);
v___x_2552_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__32));
v___x_2553_ = l_Lean_instReprKVMap_repr___redArg(v_data_2546_);
v___x_2554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set(v___x_2555_, 1, v___x_2551_);
v___x_2556_ = l_Lean_instReprExpr_repr(v_expr_2547_, v___x_2548_);
v___x_2557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2555_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
lean_inc(v___y_2550_);
v___x_2558_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___y_2550_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = 0;
v___x_2560_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2560_, 0, v___x_2558_);
lean_ctor_set_uint8(v___x_2560_, sizeof(void*)*1, v___x_2559_);
v___x_2561_ = l_Repr_addAppParen(v___x_2560_, v_prec_2346_);
return v___x_2561_;
}
}
default: 
{
lean_object* v_typeName_2565_; lean_object* v_idx_2566_; lean_object* v_struct_2567_; lean_object* v___x_2568_; lean_object* v___y_2570_; uint8_t v___x_2586_; 
v_typeName_2565_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_typeName_2565_);
v_idx_2566_ = lean_ctor_get(v_x_2345_, 1);
lean_inc(v_idx_2566_);
v_struct_2567_ = lean_ctor_get(v_x_2345_, 2);
lean_inc_ref(v_struct_2567_);
lean_dec_ref_known(v_x_2345_, 3);
v___x_2568_ = lean_unsigned_to_nat(1024u);
v___x_2586_ = lean_nat_dec_le(v___x_2568_, v_prec_2346_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2570_ = v___x_2587_;
goto v___jp_2569_;
}
else
{
lean_object* v___x_2588_; 
v___x_2588_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2570_ = v___x_2588_;
goto v___jp_2569_;
}
v___jp_2569_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2571_ = lean_box(1);
v___x_2572_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__35));
v___x_2573_ = l_Lean_Name_reprPrec(v_typeName_2565_, v___x_2568_);
v___x_2574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v___x_2571_);
v___x_2576_ = l_Nat_reprFast(v_idx_2566_);
v___x_2577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
v___x_2578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2575_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
lean_ctor_set(v___x_2579_, 1, v___x_2571_);
v___x_2580_ = l_Lean_instReprExpr_repr(v_struct_2567_, v___x_2568_);
v___x_2581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
lean_inc(v___y_2570_);
v___x_2582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___y_2570_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = 0;
v___x_2584_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
lean_ctor_set_uint8(v___x_2584_, sizeof(void*)*1, v___x_2583_);
v___x_2585_ = l_Repr_addAppParen(v___x_2584_, v_prec_2346_);
return v___x_2585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object* v_x_2589_, lean_object* v_prec_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_instReprExpr_repr(v_x_2589_, v_prec_2590_);
lean_dec(v_prec_2590_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object* v_a_2592_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = lean_nat_to_int(v_a_2592_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object* v_a_2594_, lean_object* v_n_2595_){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_a_2594_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object* v_a_2597_, lean_object* v_n_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0(v_a_2597_, v_n_2598_);
lean_dec(v_n_2598_);
return v_res_2599_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__2(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2605_ = lean_box(0);
v___x_2606_ = ((lean_object*)(l_Lean_instInhabitedExpr___closed__1));
v___x_2607_ = l_Lean_Expr_const___override(v___x_2606_, v___x_2605_);
return v___x_2607_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr(void){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* v_x_2621_){
_start:
{
switch(lean_obj_tag(v_x_2621_))
{
case 0:
{
lean_object* v___x_2622_; 
v___x_2622_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__0));
return v___x_2622_;
}
case 1:
{
lean_object* v___x_2623_; 
v___x_2623_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__1));
return v___x_2623_;
}
case 2:
{
lean_object* v___x_2624_; 
v___x_2624_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__2));
return v___x_2624_;
}
case 3:
{
lean_object* v___x_2625_; 
v___x_2625_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__3));
return v___x_2625_;
}
case 4:
{
lean_object* v___x_2626_; 
v___x_2626_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__4));
return v___x_2626_;
}
case 5:
{
lean_object* v___x_2627_; 
v___x_2627_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__5));
return v___x_2627_;
}
case 6:
{
lean_object* v___x_2628_; 
v___x_2628_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__6));
return v___x_2628_;
}
case 7:
{
lean_object* v___x_2629_; 
v___x_2629_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__7));
return v___x_2629_;
}
case 8:
{
lean_object* v___x_2630_; 
v___x_2630_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__8));
return v___x_2630_;
}
case 9:
{
lean_object* v___x_2631_; 
v___x_2631_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__9));
return v___x_2631_;
}
case 10:
{
lean_object* v___x_2632_; 
v___x_2632_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__10));
return v___x_2632_;
}
default: 
{
lean_object* v___x_2633_; 
v___x_2633_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__11));
return v___x_2633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* v_x_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_Expr_ctorName(v_x_2634_);
lean_dec_ref(v_x_2634_);
return v_res_2635_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object* v_e_2636_){
_start:
{
uint64_t v___x_2637_; uint64_t v___x_2638_; 
v___x_2637_ = lean_expr_data(v_e_2636_);
v___x_2638_ = l_Lean_Expr_Data_hash(v___x_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* v_e_2639_){
_start:
{
uint64_t v_res_2640_; lean_object* v_r_2641_; 
v_res_2640_ = l_Lean_Expr_hash(v_e_2639_);
lean_dec_ref(v_e_2639_);
v_r_2641_ = lean_box_uint64(v_res_2640_);
return v_r_2641_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object* v_e_2644_){
_start:
{
uint64_t v___x_2645_; uint8_t v___x_2646_; 
v___x_2645_ = lean_expr_data(v_e_2644_);
v___x_2646_ = l_Lean_Expr_Data_hasFVar(v___x_2645_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* v_e_2647_){
_start:
{
uint8_t v_res_2648_; lean_object* v_r_2649_; 
v_res_2648_ = l_Lean_Expr_hasFVar(v_e_2647_);
lean_dec_ref(v_e_2647_);
v_r_2649_ = lean_box(v_res_2648_);
return v_r_2649_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object* v_e_2650_){
_start:
{
uint64_t v___x_2651_; uint8_t v___x_2652_; 
v___x_2651_ = lean_expr_data(v_e_2650_);
v___x_2652_ = l_Lean_Expr_Data_hasExprMVar(v___x_2651_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* v_e_2653_){
_start:
{
uint8_t v_res_2654_; lean_object* v_r_2655_; 
v_res_2654_ = l_Lean_Expr_hasExprMVar(v_e_2653_);
lean_dec_ref(v_e_2653_);
v_r_2655_ = lean_box(v_res_2654_);
return v_r_2655_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object* v_e_2656_){
_start:
{
uint64_t v___x_2657_; uint8_t v___x_2658_; 
v___x_2657_ = lean_expr_data(v_e_2656_);
v___x_2658_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* v_e_2659_){
_start:
{
uint8_t v_res_2660_; lean_object* v_r_2661_; 
v_res_2660_ = l_Lean_Expr_hasLevelMVar(v_e_2659_);
lean_dec_ref(v_e_2659_);
v_r_2661_ = lean_box(v_res_2660_);
return v_r_2661_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object* v_e_2662_){
_start:
{
uint64_t v_d_2663_; uint8_t v___x_2664_; 
v_d_2663_ = lean_expr_data(v_e_2662_);
v___x_2664_ = l_Lean_Expr_Data_hasExprMVar(v_d_2663_);
if (v___x_2664_ == 0)
{
uint8_t v___x_2665_; 
v___x_2665_ = l_Lean_Expr_Data_hasLevelMVar(v_d_2663_);
return v___x_2665_;
}
else
{
return v___x_2664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* v_e_2666_){
_start:
{
uint8_t v_res_2667_; lean_object* v_r_2668_; 
v_res_2667_ = l_Lean_Expr_hasMVar(v_e_2666_);
lean_dec_ref(v_e_2666_);
v_r_2668_ = lean_box(v_res_2667_);
return v_r_2668_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object* v_e_2669_){
_start:
{
uint64_t v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = lean_expr_data(v_e_2669_);
v___x_2671_ = l_Lean_Expr_Data_hasLevelParam(v___x_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* v_e_2672_){
_start:
{
uint8_t v_res_2673_; lean_object* v_r_2674_; 
v_res_2673_ = l_Lean_Expr_hasLevelParam(v_e_2672_);
lean_dec_ref(v_e_2672_);
v_r_2674_ = lean_box(v_res_2673_);
return v_r_2674_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object* v_e_2675_){
_start:
{
uint64_t v___x_2676_; uint8_t v___x_2677_; uint32_t v___x_2678_; 
v___x_2676_ = lean_expr_data(v_e_2675_);
v___x_2677_ = l_Lean_Expr_Data_approxDepth(v___x_2676_);
v___x_2678_ = lean_uint8_to_uint32(v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* v_e_2679_){
_start:
{
uint32_t v_res_2680_; lean_object* v_r_2681_; 
v_res_2680_ = l_Lean_Expr_approxDepth(v_e_2679_);
lean_dec_ref(v_e_2679_);
v_r_2681_ = lean_box_uint32(v_res_2680_);
return v_r_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* v_e_2682_){
_start:
{
uint64_t v___x_2683_; uint32_t v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = lean_expr_data(v_e_2682_);
v___x_2684_ = l_Lean_Expr_Data_looseBVarRange(v___x_2683_);
v___x_2685_ = lean_uint32_to_nat(v___x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* v_e_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_Expr_looseBVarRange(v_e_2686_);
lean_dec_ref(v_e_2686_);
return v_res_2687_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object* v_e_2688_){
_start:
{
switch(lean_obj_tag(v_e_2688_))
{
case 7:
{
uint8_t v_binderInfo_2689_; 
v_binderInfo_2689_ = lean_ctor_get_uint8(v_e_2688_, sizeof(void*)*3 + 8);
return v_binderInfo_2689_;
}
case 6:
{
uint8_t v_binderInfo_2690_; 
v_binderInfo_2690_ = lean_ctor_get_uint8(v_e_2688_, sizeof(void*)*3 + 8);
return v_binderInfo_2690_;
}
default: 
{
uint8_t v___x_2691_; 
v___x_2691_ = 0;
return v___x_2691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* v_e_2692_){
_start:
{
uint8_t v_res_2693_; lean_object* v_r_2694_; 
v_res_2693_ = l_Lean_Expr_binderInfo(v_e_2692_);
lean_dec_ref(v_e_2692_);
v_r_2694_ = lean_box(v_res_2693_);
return v_r_2694_;
}
}
LEAN_EXPORT uint64_t lean_expr_hash(lean_object* v_a_2695_){
_start:
{
uint64_t v___x_2696_; 
v___x_2696_ = l_Lean_Expr_hash(v_a_2695_);
lean_dec_ref(v_a_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* v_a_2697_){
_start:
{
uint64_t v_res_2698_; lean_object* v_r_2699_; 
v_res_2698_ = lean_expr_hash(v_a_2697_);
v_r_2699_ = lean_box_uint64(v_res_2698_);
return v_r_2699_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object* v_e_2700_){
_start:
{
uint8_t v___x_2701_; 
v___x_2701_ = l_Lean_Expr_hasFVar(v_e_2700_);
lean_dec_ref(v_e_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* v_e_2702_){
_start:
{
uint8_t v_res_2703_; lean_object* v_r_2704_; 
v_res_2703_ = lean_expr_has_fvar(v_e_2702_);
v_r_2704_ = lean_box(v_res_2703_);
return v_r_2704_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object* v_e_2705_){
_start:
{
uint8_t v___x_2706_; 
v___x_2706_ = l_Lean_Expr_hasExprMVar(v_e_2705_);
lean_dec_ref(v_e_2705_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* v_e_2707_){
_start:
{
uint8_t v_res_2708_; lean_object* v_r_2709_; 
v_res_2708_ = lean_expr_has_expr_mvar(v_e_2707_);
v_r_2709_ = lean_box(v_res_2708_);
return v_r_2709_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object* v_e_2710_){
_start:
{
uint8_t v___x_2711_; 
v___x_2711_ = l_Lean_Expr_hasLevelMVar(v_e_2710_);
lean_dec_ref(v_e_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* v_e_2712_){
_start:
{
uint8_t v_res_2713_; lean_object* v_r_2714_; 
v_res_2713_ = lean_expr_has_level_mvar(v_e_2712_);
v_r_2714_ = lean_box(v_res_2713_);
return v_r_2714_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* v_e_2715_){
_start:
{
uint8_t v___x_2716_; 
v___x_2716_ = l_Lean_Expr_hasLevelParam(v_e_2715_);
lean_dec_ref(v_e_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* v_e_2717_){
_start:
{
uint8_t v_res_2718_; lean_object* v_r_2719_; 
v_res_2718_ = lean_expr_has_level_param(v_e_2717_);
v_r_2719_ = lean_box(v_res_2718_);
return v_r_2719_;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* v_e_2720_){
_start:
{
uint64_t v___x_2721_; uint32_t v___x_2722_; 
v___x_2721_ = lean_expr_data(v_e_2720_);
lean_dec_ref(v_e_2720_);
v___x_2722_ = l_Lean_Expr_Data_looseBVarRange(v___x_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* v_e_2723_){
_start:
{
uint32_t v_res_2724_; lean_object* v_r_2725_; 
v_res_2724_ = lean_expr_loose_bvar_range(v_e_2723_);
v_r_2725_ = lean_box_uint32(v_res_2724_);
return v_r_2725_;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* v_e_2726_){
_start:
{
uint8_t v___x_2727_; 
v___x_2727_ = l_Lean_Expr_binderInfo(v_e_2726_);
lean_dec_ref(v_e_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* v_e_2728_){
_start:
{
uint8_t v_res_2729_; lean_object* v_r_2730_; 
v_res_2729_ = lean_expr_binder_info(v_e_2728_);
v_r_2730_ = lean_box(v_res_2729_);
return v_r_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* v_declName_2731_, lean_object* v_us_2732_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_Expr_const___override(v_declName_2731_, v_us_2732_);
return v___x_2733_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2737_ = lean_box(0);
v___x_2738_ = ((lean_object*)(l_Lean_Literal_type___closed__1));
v___x_2739_ = l_Lean_Expr_const___override(v___x_2738_, v___x_2737_);
return v___x_2739_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2743_ = lean_box(0);
v___x_2744_ = ((lean_object*)(l_Lean_Literal_type___closed__4));
v___x_2745_ = l_Lean_Expr_const___override(v___x_2744_, v___x_2743_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* v_x_2746_){
_start:
{
if (lean_obj_tag(v_x_2746_) == 0)
{
lean_object* v___x_2747_; 
v___x_2747_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_2747_;
}
else
{
lean_object* v___x_2748_; 
v___x_2748_ = lean_obj_once(&l_Lean_Literal_type___closed__5, &l_Lean_Literal_type___closed__5_once, _init_l_Lean_Literal_type___closed__5);
return v___x_2748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* v_x_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_Literal_type(v_x_2749_);
lean_dec_ref(v_x_2749_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* v_a_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Lean_Literal_type(v_a_2751_);
lean_dec_ref(v_a_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* v_idx_2753_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_Expr_bvar___override(v_idx_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* v_u_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Lean_Expr_sort___override(v_u_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* v_fvarId_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_Expr_fvar___override(v_fvarId_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* v_mvarId_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_Expr_mvar___override(v_mvarId_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* v_m_2761_, lean_object* v_e_2762_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_Expr_mdata___override(v_m_2761_, v_e_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* v_structName_2764_, lean_object* v_idx_2765_, lean_object* v_struct_2766_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Lean_Expr_proj___override(v_structName_2764_, v_idx_2765_, v_struct_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* v_f_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l_Lean_Expr_app___override(v_f_2768_, v_a_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* v_x_2771_, uint8_t v_bi_2772_, lean_object* v_t_2773_, lean_object* v_b_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lean_Expr_lam___override(v_x_2771_, v_t_2773_, v_b_2774_, v_bi_2772_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* v_x_2776_, lean_object* v_bi_2777_, lean_object* v_t_2778_, lean_object* v_b_2779_){
_start:
{
uint8_t v_bi_boxed_2780_; lean_object* v_res_2781_; 
v_bi_boxed_2780_ = lean_unbox(v_bi_2777_);
v_res_2781_ = l_Lean_mkLambda(v_x_2776_, v_bi_boxed_2780_, v_t_2778_, v_b_2779_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* v_x_2782_, uint8_t v_bi_2783_, lean_object* v_t_2784_, lean_object* v_b_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Lean_Expr_forallE___override(v_x_2782_, v_t_2784_, v_b_2785_, v_bi_2783_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* v_x_2787_, lean_object* v_bi_2788_, lean_object* v_t_2789_, lean_object* v_b_2790_){
_start:
{
uint8_t v_bi_boxed_2791_; lean_object* v_res_2792_; 
v_bi_boxed_2791_ = lean_unbox(v_bi_2788_);
v_res_2792_ = l_Lean_mkForall(v_x_2787_, v_bi_boxed_2791_, v_t_2789_, v_b_2790_);
return v_res_2792_;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__4(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2799_ = lean_box(0);
v___x_2800_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__3));
v___x_2801_ = l_Lean_Expr_const___override(v___x_2800_, v___x_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* v_type_2802_){
_start:
{
lean_object* v___x_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2803_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2804_ = 0;
v___x_2805_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2806_ = l_Lean_Expr_forallE___override(v___x_2803_, v___x_2805_, v_type_2802_, v___x_2804_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* v_type_2807_){
_start:
{
lean_object* v___x_2808_; uint8_t v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2808_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2809_ = 0;
v___x_2810_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2811_ = l_Lean_Expr_lam___override(v___x_2808_, v___x_2810_, v_type_2807_, v___x_2809_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* v_x_2812_, lean_object* v_t_2813_, lean_object* v_v_2814_, lean_object* v_b_2815_, uint8_t v_nondep_2816_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_Expr_letE___override(v_x_2812_, v_t_2813_, v_v_2814_, v_b_2815_, v_nondep_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* v_x_2818_, lean_object* v_t_2819_, lean_object* v_v_2820_, lean_object* v_b_2821_, lean_object* v_nondep_2822_){
_start:
{
uint8_t v_nondep_boxed_2823_; lean_object* v_res_2824_; 
v_nondep_boxed_2823_ = lean_unbox(v_nondep_2822_);
v_res_2824_ = l_Lean_mkLet(v_x_2818_, v_t_2819_, v_v_2820_, v_b_2821_, v_nondep_boxed_2823_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object* v_x_2825_, lean_object* v_t_2826_, lean_object* v_v_2827_, lean_object* v_b_2828_){
_start:
{
uint8_t v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = 1;
v___x_2830_ = l_Lean_Expr_letE___override(v_x_2825_, v_t_2826_, v_v_2827_, v_b_2828_, v___x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* v_f_2831_, lean_object* v_a_2832_, lean_object* v_b_2833_){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = l_Lean_Expr_app___override(v_f_2831_, v_a_2832_);
v___x_2835_ = l_Lean_Expr_app___override(v___x_2834_, v_b_2833_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* v_f_2836_, lean_object* v_a_2837_, lean_object* v_b_2838_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_mkAppB(v_f_2836_, v_a_2837_, v_b_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* v_f_2840_, lean_object* v_a_2841_, lean_object* v_b_2842_, lean_object* v_c_2843_){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = l_Lean_mkAppB(v_f_2840_, v_a_2841_, v_b_2842_);
v___x_2845_ = l_Lean_Expr_app___override(v___x_2844_, v_c_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* v_f_2846_, lean_object* v_a_2847_, lean_object* v_b_2848_, lean_object* v_c_2849_, lean_object* v_d_2850_){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = l_Lean_mkAppB(v_f_2846_, v_a_2847_, v_b_2848_);
v___x_2852_ = l_Lean_mkAppB(v___x_2851_, v_c_2849_, v_d_2850_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* v_f_2853_, lean_object* v_a_2854_, lean_object* v_b_2855_, lean_object* v_c_2856_, lean_object* v_d_2857_, lean_object* v_e_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = l_Lean_mkApp4(v_f_2853_, v_a_2854_, v_b_2855_, v_c_2856_, v_d_2857_);
v___x_2860_ = l_Lean_Expr_app___override(v___x_2859_, v_e_2858_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* v_f_2861_, lean_object* v_a_2862_, lean_object* v_b_2863_, lean_object* v_c_2864_, lean_object* v_d_2865_, lean_object* v_e_u2081_2866_, lean_object* v_e_u2082_2867_){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = l_Lean_mkApp4(v_f_2861_, v_a_2862_, v_b_2863_, v_c_2864_, v_d_2865_);
v___x_2869_ = l_Lean_mkAppB(v___x_2868_, v_e_u2081_2866_, v_e_u2082_2867_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* v_f_2870_, lean_object* v_a_2871_, lean_object* v_b_2872_, lean_object* v_c_2873_, lean_object* v_d_2874_, lean_object* v_e_u2081_2875_, lean_object* v_e_u2082_2876_, lean_object* v_e_u2083_2877_){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = l_Lean_mkApp4(v_f_2870_, v_a_2871_, v_b_2872_, v_c_2873_, v_d_2874_);
v___x_2879_ = l_Lean_mkApp3(v___x_2878_, v_e_u2081_2875_, v_e_u2082_2876_, v_e_u2083_2877_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* v_f_2880_, lean_object* v_a_2881_, lean_object* v_b_2882_, lean_object* v_c_2883_, lean_object* v_d_2884_, lean_object* v_e_u2081_2885_, lean_object* v_e_u2082_2886_, lean_object* v_e_u2083_2887_, lean_object* v_e_u2084_2888_){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = l_Lean_mkApp4(v_f_2880_, v_a_2881_, v_b_2882_, v_c_2883_, v_d_2884_);
v___x_2890_ = l_Lean_mkApp4(v___x_2889_, v_e_u2081_2885_, v_e_u2082_2886_, v_e_u2083_2887_, v_e_u2084_2888_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* v_f_2891_, lean_object* v_a_2892_, lean_object* v_b_2893_, lean_object* v_c_2894_, lean_object* v_d_2895_, lean_object* v_e_u2081_2896_, lean_object* v_e_u2082_2897_, lean_object* v_e_u2083_2898_, lean_object* v_e_u2084_2899_, lean_object* v_e_u2085_2900_){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = l_Lean_mkApp4(v_f_2891_, v_a_2892_, v_b_2893_, v_c_2894_, v_d_2895_);
v___x_2902_ = l_Lean_mkApp5(v___x_2901_, v_e_u2081_2896_, v_e_u2082_2897_, v_e_u2083_2898_, v_e_u2084_2899_, v_e_u2085_2900_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* v_f_2903_, lean_object* v_a_2904_, lean_object* v_b_2905_, lean_object* v_c_2906_, lean_object* v_d_2907_, lean_object* v_e_u2081_2908_, lean_object* v_e_u2082_2909_, lean_object* v_e_u2083_2910_, lean_object* v_e_u2084_2911_, lean_object* v_e_u2085_2912_, lean_object* v_e_u2086_2913_){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = l_Lean_mkApp4(v_f_2903_, v_a_2904_, v_b_2905_, v_c_2906_, v_d_2907_);
v___x_2915_ = l_Lean_mkApp6(v___x_2914_, v_e_u2081_2908_, v_e_u2082_2909_, v_e_u2083_2910_, v_e_u2084_2911_, v_e_u2085_2912_, v_e_u2086_2913_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* v_l_2916_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Lean_Expr_lit___override(v_l_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* v_n_2918_){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v_n_2918_);
v___x_2920_ = l_Lean_Expr_lit___override(v___x_2919_);
return v___x_2920_;
}
}
static lean_object* _init_l_Lean_mkInstOfNatNat___closed__2(void){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2924_ = lean_box(0);
v___x_2925_ = ((lean_object*)(l_Lean_mkInstOfNatNat___closed__1));
v___x_2926_ = l_Lean_Expr_const___override(v___x_2925_, v___x_2924_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object* v_n_2927_){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = lean_obj_once(&l_Lean_mkInstOfNatNat___closed__2, &l_Lean_mkInstOfNatNat___closed__2_once, _init_l_Lean_mkInstOfNatNat___closed__2);
v___x_2929_ = l_Lean_Expr_app___override(v___x_2928_, v_n_2927_);
return v___x_2929_;
}
}
static lean_object* _init_l_Lean_mkNatLitCore___closed__4(void){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2938_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_2939_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_2940_ = l_Lean_Expr_const___override(v___x_2939_, v___x_2938_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object* v_n_2941_){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2942_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_2943_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
lean_inc_ref(v_n_2941_);
v___x_2944_ = l_Lean_mkInstOfNatNat(v_n_2941_);
v___x_2945_ = l_Lean_mkApp3(v___x_2942_, v___x_2943_, v_n_2941_, v___x_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* v_n_2946_){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = l_Lean_mkRawNatLit(v_n_2946_);
v___x_2948_ = l_Lean_mkNatLitCore(v___x_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* v_s_2949_){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2950_, 0, v_s_2949_);
v___x_2951_ = l_Lean_Expr_lit___override(v___x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* v_idx_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_Expr_bvar___override(v_idx_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* v_fvarId_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Expr_fvar___override(v_fvarId_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object* v_mvarId_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_Expr_mvar___override(v_mvarId_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_Expr_sort___override(v_u_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_2960_, lean_object* v_lvls_2961_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_Expr_const___override(v_c_2960_, v_lvls_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_Expr_app___override(v_f_2963_, v_a_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* v_n_2966_, lean_object* v_d_2967_, lean_object* v_b_2968_, uint8_t v_bi_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_Expr_lam___override(v_n_2966_, v_d_2967_, v_b_2968_, v_bi_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_2971_, lean_object* v_d_2972_, lean_object* v_b_2973_, lean_object* v_bi_2974_){
_start:
{
uint8_t v_bi_boxed_2975_; lean_object* v_res_2976_; 
v_bi_boxed_2975_ = lean_unbox(v_bi_2974_);
v_res_2976_ = lean_expr_mk_lambda(v_n_2971_, v_d_2972_, v_b_2973_, v_bi_boxed_2975_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* v_n_2977_, lean_object* v_d_2978_, lean_object* v_b_2979_, uint8_t v_bi_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_Expr_forallE___override(v_n_2977_, v_d_2978_, v_b_2979_, v_bi_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_2982_, lean_object* v_d_2983_, lean_object* v_b_2984_, lean_object* v_bi_2985_){
_start:
{
uint8_t v_bi_boxed_2986_; lean_object* v_res_2987_; 
v_bi_boxed_2986_ = lean_unbox(v_bi_2985_);
v_res_2987_ = lean_expr_mk_forall(v_n_2982_, v_d_2983_, v_b_2984_, v_bi_boxed_2986_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* v_n_2988_, lean_object* v_t_2989_, lean_object* v_v_2990_, lean_object* v_b_2991_, uint8_t v_nondep_2992_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l_Lean_Expr_letE___override(v_n_2988_, v_t_2989_, v_v_2990_, v_b_2991_, v_nondep_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_2994_, lean_object* v_t_2995_, lean_object* v_v_2996_, lean_object* v_b_2997_, lean_object* v_nondep_2998_){
_start:
{
uint8_t v_nondep_boxed_2999_; lean_object* v_res_3000_; 
v_nondep_boxed_2999_ = lean_unbox(v_nondep_2998_);
v_res_3000_ = lean_expr_mk_let(v_n_2994_, v_t_2995_, v_v_2996_, v_b_2997_, v_nondep_boxed_2999_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_3001_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = l_Lean_Expr_lit___override(v_l_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_3003_, lean_object* v_e_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_Expr_mdata___override(v_m_3003_, v_e_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_3006_, lean_object* v_idx_3007_, lean_object* v_struct_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lean_Expr_proj___override(v_structName_3006_, v_idx_3007_, v_struct_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_3010_, size_t v_i_3011_, size_t v_stop_3012_, lean_object* v_b_3013_){
_start:
{
uint8_t v___x_3014_; 
v___x_3014_ = lean_usize_dec_eq(v_i_3011_, v_stop_3012_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; lean_object* v___x_3016_; size_t v___x_3017_; size_t v___x_3018_; 
v___x_3015_ = lean_array_uget_borrowed(v_as_3010_, v_i_3011_);
lean_inc(v___x_3015_);
v___x_3016_ = l_Lean_Expr_app___override(v_b_3013_, v___x_3015_);
v___x_3017_ = ((size_t)1ULL);
v___x_3018_ = lean_usize_add(v_i_3011_, v___x_3017_);
v_i_3011_ = v___x_3018_;
v_b_3013_ = v___x_3016_;
goto _start;
}
else
{
return v_b_3013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_3020_, lean_object* v_i_3021_, lean_object* v_stop_3022_, lean_object* v_b_3023_){
_start:
{
size_t v_i_boxed_3024_; size_t v_stop_boxed_3025_; lean_object* v_res_3026_; 
v_i_boxed_3024_ = lean_unbox_usize(v_i_3021_);
lean_dec(v_i_3021_);
v_stop_boxed_3025_ = lean_unbox_usize(v_stop_3022_);
lean_dec(v_stop_3022_);
v_res_3026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_3020_, v_i_boxed_3024_, v_stop_boxed_3025_, v_b_3023_);
lean_dec_ref(v_as_3020_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_3027_, lean_object* v_args_3028_){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3029_ = lean_unsigned_to_nat(0u);
v___x_3030_ = lean_array_get_size(v_args_3028_);
v___x_3031_ = lean_nat_dec_lt(v___x_3029_, v___x_3030_);
if (v___x_3031_ == 0)
{
return v_f_3027_;
}
else
{
uint8_t v___x_3032_; 
v___x_3032_ = lean_nat_dec_le(v___x_3030_, v___x_3030_);
if (v___x_3032_ == 0)
{
if (v___x_3031_ == 0)
{
return v_f_3027_;
}
else
{
size_t v___x_3033_; size_t v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = ((size_t)0ULL);
v___x_3034_ = lean_usize_of_nat(v___x_3030_);
v___x_3035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3028_, v___x_3033_, v___x_3034_, v_f_3027_);
return v___x_3035_;
}
}
else
{
size_t v___x_3036_; size_t v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = ((size_t)0ULL);
v___x_3037_ = lean_usize_of_nat(v___x_3030_);
v___x_3038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3028_, v___x_3036_, v___x_3037_, v_f_3027_);
return v___x_3038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_3039_, lean_object* v_args_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Lean_mkAppN(v_f_3039_, v_args_3040_);
lean_dec_ref(v_args_3040_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_3042_, lean_object* v_args_3043_, lean_object* v_i_3044_, lean_object* v_e_3045_){
_start:
{
uint8_t v___x_3046_; 
v___x_3046_ = lean_nat_dec_lt(v_i_3044_, v_n_3042_);
if (v___x_3046_ == 0)
{
lean_dec(v_i_3044_);
return v_e_3045_;
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3047_ = lean_unsigned_to_nat(1u);
v___x_3048_ = lean_nat_add(v_i_3044_, v___x_3047_);
v___x_3049_ = l_Lean_instInhabitedExpr;
v___x_3050_ = lean_array_get_borrowed(v___x_3049_, v_args_3043_, v_i_3044_);
lean_dec(v_i_3044_);
lean_inc(v___x_3050_);
v___x_3051_ = l_Lean_Expr_app___override(v_e_3045_, v___x_3050_);
v_i_3044_ = v___x_3048_;
v_e_3045_ = v___x_3051_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_3053_, lean_object* v_args_3054_, lean_object* v_i_3055_, lean_object* v_e_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_3053_, v_args_3054_, v_i_3055_, v_e_3056_);
lean_dec_ref(v_args_3054_);
lean_dec(v_n_3053_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_3058_, lean_object* v_i_3059_, lean_object* v_j_3060_, lean_object* v_args_3061_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_3060_, v_args_3061_, v_i_3059_, v_f_3058_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_3063_, lean_object* v_i_3064_, lean_object* v_j_3065_, lean_object* v_args_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Lean_mkAppRange(v_f_3063_, v_i_3064_, v_j_3065_, v_args_3066_);
lean_dec_ref(v_args_3066_);
lean_dec(v_j_3065_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_3068_, size_t v_i_3069_, size_t v_stop_3070_, lean_object* v_b_3071_){
_start:
{
uint8_t v___x_3072_; 
v___x_3072_ = lean_usize_dec_eq(v_i_3069_, v_stop_3070_);
if (v___x_3072_ == 0)
{
size_t v___x_3073_; size_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3073_ = ((size_t)1ULL);
v___x_3074_ = lean_usize_sub(v_i_3069_, v___x_3073_);
v___x_3075_ = lean_array_uget_borrowed(v_as_3068_, v___x_3074_);
lean_inc(v___x_3075_);
v___x_3076_ = l_Lean_Expr_app___override(v_b_3071_, v___x_3075_);
v_i_3069_ = v___x_3074_;
v_b_3071_ = v___x_3076_;
goto _start;
}
else
{
return v_b_3071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_3078_, lean_object* v_i_3079_, lean_object* v_stop_3080_, lean_object* v_b_3081_){
_start:
{
size_t v_i_boxed_3082_; size_t v_stop_boxed_3083_; lean_object* v_res_3084_; 
v_i_boxed_3082_ = lean_unbox_usize(v_i_3079_);
lean_dec(v_i_3079_);
v_stop_boxed_3083_ = lean_unbox_usize(v_stop_3080_);
lean_dec(v_stop_3080_);
v_res_3084_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3078_, v_i_boxed_3082_, v_stop_boxed_3083_, v_b_3081_);
lean_dec_ref(v_as_3078_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_3085_, lean_object* v_revArgs_3086_){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v___x_3087_ = lean_array_get_size(v_revArgs_3086_);
v___x_3088_ = lean_unsigned_to_nat(0u);
v___x_3089_ = lean_nat_dec_lt(v___x_3088_, v___x_3087_);
if (v___x_3089_ == 0)
{
return v_fn_3085_;
}
else
{
size_t v___x_3090_; size_t v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = lean_usize_of_nat(v___x_3087_);
v___x_3091_ = ((size_t)0ULL);
v___x_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_3086_, v___x_3090_, v___x_3091_, v_fn_3085_);
return v___x_3092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_3093_, lean_object* v_revArgs_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_mkAppRev(v_fn_3093_, v_revArgs_3094_);
lean_dec_ref(v_revArgs_3094_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = lean_expr_dbg_to_string(v_e_3097_);
lean_dec_ref(v_e_3097_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_3101_, lean_object* v_b_3102_){
_start:
{
uint8_t v_res_3103_; lean_object* v_r_3104_; 
v_res_3103_ = lean_expr_quick_lt(v_a_3101_, v_b_3102_);
lean_dec_ref(v_b_3102_);
lean_dec_ref(v_a_3101_);
v_r_3104_ = lean_box(v_res_3103_);
return v_r_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_3107_, lean_object* v_b_3108_){
_start:
{
uint8_t v_res_3109_; lean_object* v_r_3110_; 
v_res_3109_ = lean_expr_lt(v_a_3107_, v_b_3108_);
lean_dec_ref(v_b_3108_);
lean_dec_ref(v_a_3107_);
v_r_3110_ = lean_box(v_res_3109_);
return v_r_3110_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* v_a_3111_, lean_object* v_b_3112_){
_start:
{
uint8_t v___x_3113_; 
v___x_3113_ = lean_expr_quick_lt(v_a_3111_, v_b_3112_);
if (v___x_3113_ == 0)
{
uint8_t v___x_3114_; 
v___x_3114_ = lean_expr_quick_lt(v_b_3112_, v_a_3111_);
if (v___x_3114_ == 0)
{
uint8_t v___x_3115_; 
v___x_3115_ = 1;
return v___x_3115_;
}
else
{
uint8_t v___x_3116_; 
v___x_3116_ = 2;
return v___x_3116_;
}
}
else
{
uint8_t v___x_3117_; 
v___x_3117_ = 0;
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_3118_, lean_object* v_b_3119_){
_start:
{
uint8_t v_res_3120_; lean_object* v_r_3121_; 
v_res_3120_ = l_Lean_Expr_quickComp(v_a_3118_, v_b_3119_);
lean_dec_ref(v_b_3119_);
lean_dec_ref(v_a_3118_);
v_r_3121_ = lean_box(v_res_3120_);
return v_r_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_3124_, lean_object* v_b_3125_){
_start:
{
uint8_t v_res_3126_; lean_object* v_r_3127_; 
v_res_3126_ = lean_expr_eqv(v_a_3124_, v_b_3125_);
lean_dec_ref(v_b_3125_);
lean_dec_ref(v_a_3124_);
v_r_3127_ = lean_box(v_res_3126_);
return v_r_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3132_, lean_object* v_b_3133_){
_start:
{
uint8_t v_res_3134_; lean_object* v_r_3135_; 
v_res_3134_ = lean_expr_equal(v_a_3132_, v_b_3133_);
lean_dec_ref(v_b_3133_);
lean_dec_ref(v_a_3132_);
v_r_3135_ = lean_box(v_res_3134_);
return v_r_3135_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* v_x_3136_){
_start:
{
if (lean_obj_tag(v_x_3136_) == 3)
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3139_){
_start:
{
uint8_t v_res_3140_; lean_object* v_r_3141_; 
v_res_3140_ = l_Lean_Expr_isSort(v_x_3139_);
lean_dec_ref(v_x_3139_);
v_r_3141_ = lean_box(v_res_3140_);
return v_r_3141_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* v_x_3142_){
_start:
{
if (lean_obj_tag(v_x_3142_) == 3)
{
lean_object* v_u_3143_; 
v_u_3143_ = lean_ctor_get(v_x_3142_, 0);
if (lean_obj_tag(v_u_3143_) == 1)
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3147_){
_start:
{
uint8_t v_res_3148_; lean_object* v_r_3149_; 
v_res_3148_ = l_Lean_Expr_isType(v_x_3147_);
lean_dec_ref(v_x_3147_);
v_r_3149_ = lean_box(v_res_3148_);
return v_r_3149_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* v_x_3150_){
_start:
{
if (lean_obj_tag(v_x_3150_) == 3)
{
lean_object* v_u_3151_; 
v_u_3151_ = lean_ctor_get(v_x_3150_, 0);
if (lean_obj_tag(v_u_3151_) == 1)
{
lean_object* v_a_3152_; 
v_a_3152_ = lean_ctor_get(v_u_3151_, 0);
if (lean_obj_tag(v_a_3152_) == 0)
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
else
{
uint8_t v___x_3156_; 
v___x_3156_ = 0;
return v___x_3156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3157_){
_start:
{
uint8_t v_res_3158_; lean_object* v_r_3159_; 
v_res_3158_ = l_Lean_Expr_isType0(v_x_3157_);
lean_dec_ref(v_x_3157_);
v_r_3159_ = lean_box(v_res_3158_);
return v_r_3159_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* v_x_3160_){
_start:
{
if (lean_obj_tag(v_x_3160_) == 3)
{
lean_object* v_u_3161_; 
v_u_3161_ = lean_ctor_get(v_x_3160_, 0);
if (lean_obj_tag(v_u_3161_) == 0)
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
else
{
uint8_t v___x_3164_; 
v___x_3164_ = 0;
return v___x_3164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3165_){
_start:
{
uint8_t v_res_3166_; lean_object* v_r_3167_; 
v_res_3166_ = l_Lean_Expr_isProp(v_x_3165_);
lean_dec_ref(v_x_3165_);
v_r_3167_ = lean_box(v_res_3166_);
return v_r_3167_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3168_){
_start:
{
if (lean_obj_tag(v_x_3168_) == 0)
{
uint8_t v___x_3169_; 
v___x_3169_ = 1;
return v___x_3169_;
}
else
{
uint8_t v___x_3170_; 
v___x_3170_ = 0;
return v___x_3170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3171_){
_start:
{
uint8_t v_res_3172_; lean_object* v_r_3173_; 
v_res_3172_ = l_Lean_Expr_isBVar(v_x_3171_);
lean_dec_ref(v_x_3171_);
v_r_3173_ = lean_box(v_res_3172_);
return v_r_3173_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3174_){
_start:
{
if (lean_obj_tag(v_x_3174_) == 2)
{
uint8_t v___x_3175_; 
v___x_3175_ = 1;
return v___x_3175_;
}
else
{
uint8_t v___x_3176_; 
v___x_3176_ = 0;
return v___x_3176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3177_){
_start:
{
uint8_t v_res_3178_; lean_object* v_r_3179_; 
v_res_3178_ = l_Lean_Expr_isMVar(v_x_3177_);
lean_dec_ref(v_x_3177_);
v_r_3179_ = lean_box(v_res_3178_);
return v_r_3179_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3180_){
_start:
{
if (lean_obj_tag(v_x_3180_) == 1)
{
uint8_t v___x_3181_; 
v___x_3181_ = 1;
return v___x_3181_;
}
else
{
uint8_t v___x_3182_; 
v___x_3182_ = 0;
return v___x_3182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3183_){
_start:
{
uint8_t v_res_3184_; lean_object* v_r_3185_; 
v_res_3184_ = l_Lean_Expr_isFVar(v_x_3183_);
lean_dec_ref(v_x_3183_);
v_r_3185_ = lean_box(v_res_3184_);
return v_r_3185_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* v_x_3186_){
_start:
{
if (lean_obj_tag(v_x_3186_) == 5)
{
uint8_t v___x_3187_; 
v___x_3187_ = 1;
return v___x_3187_;
}
else
{
uint8_t v___x_3188_; 
v___x_3188_ = 0;
return v___x_3188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3189_){
_start:
{
uint8_t v_res_3190_; lean_object* v_r_3191_; 
v_res_3190_ = l_Lean_Expr_isApp(v_x_3189_);
lean_dec_ref(v_x_3189_);
v_r_3191_ = lean_box(v_res_3190_);
return v_r_3191_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* v_x_3192_){
_start:
{
if (lean_obj_tag(v_x_3192_) == 11)
{
uint8_t v___x_3193_; 
v___x_3193_ = 1;
return v___x_3193_;
}
else
{
uint8_t v___x_3194_; 
v___x_3194_ = 0;
return v___x_3194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3195_){
_start:
{
uint8_t v_res_3196_; lean_object* v_r_3197_; 
v_res_3196_ = l_Lean_Expr_isProj(v_x_3195_);
lean_dec_ref(v_x_3195_);
v_r_3197_ = lean_box(v_res_3196_);
return v_r_3197_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* v_x_3198_){
_start:
{
if (lean_obj_tag(v_x_3198_) == 4)
{
uint8_t v___x_3199_; 
v___x_3199_ = 1;
return v___x_3199_;
}
else
{
uint8_t v___x_3200_; 
v___x_3200_ = 0;
return v___x_3200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3201_){
_start:
{
uint8_t v_res_3202_; lean_object* v_r_3203_; 
v_res_3202_ = l_Lean_Expr_isConst(v_x_3201_);
lean_dec_ref(v_x_3201_);
v_r_3203_ = lean_box(v_res_3202_);
return v_r_3203_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3204_, lean_object* v_x_3205_){
_start:
{
if (lean_obj_tag(v_x_3204_) == 4)
{
lean_object* v_declName_3206_; uint8_t v___x_3207_; 
v_declName_3206_ = lean_ctor_get(v_x_3204_, 0);
v___x_3207_ = lean_name_eq(v_declName_3206_, v_x_3205_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3209_, lean_object* v_x_3210_){
_start:
{
uint8_t v_res_3211_; lean_object* v_r_3212_; 
v_res_3211_ = l_Lean_Expr_isConstOf(v_x_3209_, v_x_3210_);
lean_dec(v_x_3210_);
lean_dec_ref(v_x_3209_);
v_r_3212_ = lean_box(v_res_3211_);
return v_r_3212_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3213_, lean_object* v_x_3214_){
_start:
{
if (lean_obj_tag(v_x_3213_) == 1)
{
lean_object* v_fvarId_3215_; uint8_t v___x_3216_; 
v_fvarId_3215_ = lean_ctor_get(v_x_3213_, 0);
v___x_3216_ = lean_name_eq(v_fvarId_3215_, v_x_3214_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3218_, lean_object* v_x_3219_){
_start:
{
uint8_t v_res_3220_; lean_object* v_r_3221_; 
v_res_3220_ = l_Lean_Expr_isFVarOf(v_x_3218_, v_x_3219_);
lean_dec(v_x_3219_);
lean_dec_ref(v_x_3218_);
v_r_3221_ = lean_box(v_res_3220_);
return v_r_3221_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* v_x_3222_){
_start:
{
if (lean_obj_tag(v_x_3222_) == 7)
{
uint8_t v___x_3223_; 
v___x_3223_ = 1;
return v___x_3223_;
}
else
{
uint8_t v___x_3224_; 
v___x_3224_ = 0;
return v___x_3224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3225_){
_start:
{
uint8_t v_res_3226_; lean_object* v_r_3227_; 
v_res_3226_ = l_Lean_Expr_isForall(v_x_3225_);
lean_dec_ref(v_x_3225_);
v_r_3227_ = lean_box(v_res_3226_);
return v_r_3227_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3228_){
_start:
{
if (lean_obj_tag(v_x_3228_) == 6)
{
uint8_t v___x_3229_; 
v___x_3229_ = 1;
return v___x_3229_;
}
else
{
uint8_t v___x_3230_; 
v___x_3230_ = 0;
return v___x_3230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3231_){
_start:
{
uint8_t v_res_3232_; lean_object* v_r_3233_; 
v_res_3232_ = l_Lean_Expr_isLambda(v_x_3231_);
lean_dec_ref(v_x_3231_);
v_r_3233_ = lean_box(v_res_3232_);
return v_r_3233_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3234_){
_start:
{
switch(lean_obj_tag(v_x_3234_))
{
case 6:
{
uint8_t v___x_3235_; 
v___x_3235_ = 1;
return v___x_3235_;
}
case 7:
{
uint8_t v___x_3236_; 
v___x_3236_ = 1;
return v___x_3236_;
}
default: 
{
uint8_t v___x_3237_; 
v___x_3237_ = 0;
return v___x_3237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3238_){
_start:
{
uint8_t v_res_3239_; lean_object* v_r_3240_; 
v_res_3239_ = l_Lean_Expr_isBinding(v_x_3238_);
lean_dec_ref(v_x_3238_);
v_r_3240_ = lean_box(v_res_3239_);
return v_r_3240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* v_x_3241_){
_start:
{
if (lean_obj_tag(v_x_3241_) == 8)
{
uint8_t v___x_3242_; 
v___x_3242_ = 1;
return v___x_3242_;
}
else
{
uint8_t v___x_3243_; 
v___x_3243_ = 0;
return v___x_3243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3244_){
_start:
{
uint8_t v_res_3245_; lean_object* v_r_3246_; 
v_res_3245_ = l_Lean_Expr_isLet(v_x_3244_);
lean_dec_ref(v_x_3244_);
v_r_3246_ = lean_box(v_res_3245_);
return v_r_3246_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object* v_x_3247_){
_start:
{
if (lean_obj_tag(v_x_3247_) == 8)
{
uint8_t v_nondep_3248_; 
v_nondep_3248_ = lean_ctor_get_uint8(v_x_3247_, sizeof(void*)*4 + 8);
return v_nondep_3248_;
}
else
{
uint8_t v___x_3249_; 
v___x_3249_ = 0;
return v___x_3249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3250_){
_start:
{
uint8_t v_res_3251_; lean_object* v_r_3252_; 
v_res_3251_ = l_Lean_Expr_isHave(v_x_3250_);
lean_dec_ref(v_x_3250_);
v_r_3252_ = lean_box(v_res_3251_);
return v_r_3252_;
}
}
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object* v_a_3253_){
_start:
{
uint8_t v___x_3254_; 
v___x_3254_ = l_Lean_Expr_isHave(v_a_3253_);
lean_dec_ref(v_a_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3255_){
_start:
{
uint8_t v_res_3256_; lean_object* v_r_3257_; 
v_res_3256_ = lean_expr_is_have(v_a_3255_);
v_r_3257_ = lean_box(v_res_3256_);
return v_r_3257_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* v_x_3258_){
_start:
{
if (lean_obj_tag(v_x_3258_) == 10)
{
uint8_t v___x_3259_; 
v___x_3259_ = 1;
return v___x_3259_;
}
else
{
uint8_t v___x_3260_; 
v___x_3260_ = 0;
return v___x_3260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3261_){
_start:
{
uint8_t v_res_3262_; lean_object* v_r_3263_; 
v_res_3262_ = l_Lean_Expr_isMData(v_x_3261_);
lean_dec_ref(v_x_3261_);
v_r_3263_ = lean_box(v_res_3262_);
return v_r_3263_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* v_x_3264_){
_start:
{
if (lean_obj_tag(v_x_3264_) == 9)
{
uint8_t v___x_3265_; 
v___x_3265_ = 1;
return v___x_3265_;
}
else
{
uint8_t v___x_3266_; 
v___x_3266_ = 0;
return v___x_3266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3267_){
_start:
{
uint8_t v_res_3268_; lean_object* v_r_3269_; 
v_res_3268_ = l_Lean_Expr_isLit(v_x_3267_);
lean_dec_ref(v_x_3267_);
v_r_3269_ = lean_box(v_res_3268_);
return v_r_3269_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3270_){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = l_Lean_instInhabitedExpr;
v___x_3272_ = lean_panic_fn_borrowed(v___x_3271_, v_msg_3270_);
return v___x_3272_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3276_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3277_ = lean_unsigned_to_nat(15u);
v___x_3278_ = lean_unsigned_to_nat(932u);
v___x_3279_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3280_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3281_ = l_mkPanicMessageWithDecl(v___x_3280_, v___x_3279_, v___x_3278_, v___x_3277_, v___x_3276_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3282_){
_start:
{
if (lean_obj_tag(v_x_3282_) == 5)
{
lean_object* v_fn_3283_; 
v_fn_3283_ = lean_ctor_get(v_x_3282_, 0);
lean_inc_ref(v_fn_3283_);
return v_fn_3283_;
}
else
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3284_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3285_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3284_);
return v___x_3285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_Expr_appFn_x21(v_x_3286_);
lean_dec_ref(v_x_3286_);
return v_res_3287_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3289_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3290_ = lean_unsigned_to_nat(15u);
v___x_3291_ = lean_unsigned_to_nat(936u);
v___x_3292_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3293_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3294_ = l_mkPanicMessageWithDecl(v___x_3293_, v___x_3292_, v___x_3291_, v___x_3290_, v___x_3289_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3295_){
_start:
{
if (lean_obj_tag(v_x_3295_) == 5)
{
lean_object* v_arg_3296_; 
v_arg_3296_ = lean_ctor_get(v_x_3295_, 1);
lean_inc_ref(v_arg_3296_);
return v_arg_3296_;
}
else
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3298_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3297_);
return v___x_3298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_Expr_appArg_x21(v_x_3299_);
lean_dec_ref(v_x_3299_);
return v_res_3300_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3302_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3303_ = lean_unsigned_to_nat(17u);
v___x_3304_ = lean_unsigned_to_nat(941u);
v___x_3305_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3306_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3307_ = l_mkPanicMessageWithDecl(v___x_3306_, v___x_3305_, v___x_3304_, v___x_3303_, v___x_3302_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3308_){
_start:
{
switch(lean_obj_tag(v_x_3308_))
{
case 10:
{
lean_object* v_expr_3309_; 
v_expr_3309_ = lean_ctor_get(v_x_3308_, 1);
v_x_3308_ = v_expr_3309_;
goto _start;
}
case 5:
{
lean_object* v_fn_3311_; 
v_fn_3311_ = lean_ctor_get(v_x_3308_, 0);
lean_inc_ref(v_fn_3311_);
return v_fn_3311_;
}
default: 
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3313_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3312_);
return v___x_3313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lean_Expr_appFn_x21_x27(v_x_3314_);
lean_dec_ref(v_x_3314_);
return v_res_3315_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3317_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3318_ = lean_unsigned_to_nat(17u);
v___x_3319_ = lean_unsigned_to_nat(946u);
v___x_3320_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3321_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3322_ = l_mkPanicMessageWithDecl(v___x_3321_, v___x_3320_, v___x_3319_, v___x_3318_, v___x_3317_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3323_){
_start:
{
switch(lean_obj_tag(v_x_3323_))
{
case 10:
{
lean_object* v_expr_3324_; 
v_expr_3324_ = lean_ctor_get(v_x_3323_, 1);
v_x_3323_ = v_expr_3324_;
goto _start;
}
case 5:
{
lean_object* v_arg_3326_; 
v_arg_3326_ = lean_ctor_get(v_x_3323_, 1);
lean_inc_ref(v_arg_3326_);
return v_arg_3326_;
}
default: 
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3328_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3327_);
return v___x_3328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Lean_Expr_appArg_x21_x27(v_x_3329_);
lean_dec_ref(v_x_3329_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3331_){
_start:
{
lean_object* v_arg_3332_; 
v_arg_3332_ = lean_ctor_get(v_e_3331_, 1);
lean_inc_ref(v_arg_3332_);
return v_arg_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l_Lean_Expr_appArg___redArg(v_e_3333_);
lean_dec_ref(v_e_3333_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3335_, lean_object* v_h_3336_){
_start:
{
lean_object* v_arg_3337_; 
v_arg_3337_ = lean_ctor_get(v_e_3335_, 1);
lean_inc_ref(v_arg_3337_);
return v_arg_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3338_, lean_object* v_h_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_Expr_appArg(v_e_3338_, v_h_3339_);
lean_dec_ref(v_e_3338_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3341_){
_start:
{
lean_object* v_fn_3342_; 
v_fn_3342_ = lean_ctor_get(v_e_3341_, 0);
lean_inc_ref(v_fn_3342_);
return v_fn_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_Expr_appFn___redArg(v_e_3343_);
lean_dec_ref(v_e_3343_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3345_, lean_object* v_h_3346_){
_start:
{
lean_object* v_fn_3347_; 
v_fn_3347_ = lean_ctor_get(v_e_3345_, 0);
lean_inc_ref(v_fn_3347_);
return v_fn_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3348_, lean_object* v_h_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_Expr_appFn(v_e_3348_, v_h_3349_);
lean_dec_ref(v_e_3348_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3351_){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = lean_box(0);
v___x_3353_ = lean_panic_fn_borrowed(v___x_3352_, v_msg_3351_);
return v___x_3353_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3356_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3357_ = lean_unsigned_to_nat(14u);
v___x_3358_ = lean_unsigned_to_nat(958u);
v___x_3359_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3360_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3361_ = l_mkPanicMessageWithDecl(v___x_3360_, v___x_3359_, v___x_3358_, v___x_3357_, v___x_3356_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3362_){
_start:
{
if (lean_obj_tag(v_x_3362_) == 3)
{
lean_object* v_u_3363_; 
v_u_3363_ = lean_ctor_get(v_x_3362_, 0);
lean_inc(v_u_3363_);
return v_u_3363_;
}
else
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3365_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3364_);
return v___x_3365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_Expr_sortLevel_x21(v_x_3366_);
lean_dec_ref(v_x_3366_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3368_){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3370_ = lean_panic_fn_borrowed(v___x_3369_, v_msg_3368_);
return v___x_3370_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3373_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3374_ = lean_unsigned_to_nat(13u);
v___x_3375_ = lean_unsigned_to_nat(962u);
v___x_3376_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3377_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3378_ = l_mkPanicMessageWithDecl(v___x_3377_, v___x_3376_, v___x_3375_, v___x_3374_, v___x_3373_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3379_){
_start:
{
if (lean_obj_tag(v_x_3379_) == 9)
{
lean_object* v_a_3380_; 
v_a_3380_ = lean_ctor_get(v_x_3379_, 0);
lean_inc_ref(v_a_3380_);
return v_a_3380_;
}
else
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3382_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3381_);
return v___x_3382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_Lean_Expr_litValue_x21(v_x_3383_);
lean_dec_ref(v_x_3383_);
return v_res_3384_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3385_){
_start:
{
if (lean_obj_tag(v_x_3385_) == 9)
{
lean_object* v_a_3386_; 
v_a_3386_ = lean_ctor_get(v_x_3385_, 0);
if (lean_obj_tag(v_a_3386_) == 0)
{
uint8_t v___x_3387_; 
v___x_3387_ = 1;
return v___x_3387_;
}
else
{
uint8_t v___x_3388_; 
v___x_3388_ = 0;
return v___x_3388_;
}
}
else
{
uint8_t v___x_3389_; 
v___x_3389_ = 0;
return v___x_3389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3390_){
_start:
{
uint8_t v_res_3391_; lean_object* v_r_3392_; 
v_res_3391_ = l_Lean_Expr_isRawNatLit(v_x_3390_);
lean_dec_ref(v_x_3390_);
v_r_3392_ = lean_box(v_res_3391_);
return v_r_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3393_){
_start:
{
if (lean_obj_tag(v_x_3393_) == 9)
{
lean_object* v_a_3394_; 
v_a_3394_ = lean_ctor_get(v_x_3393_, 0);
lean_inc_ref(v_a_3394_);
lean_dec_ref_known(v_x_3393_, 1);
if (lean_obj_tag(v_a_3394_) == 0)
{
lean_object* v_val_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
v_val_3395_ = lean_ctor_get(v_a_3394_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_a_3394_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v_a_3394_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_val_3395_);
lean_dec(v_a_3394_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
lean_ctor_set_tag(v___x_3397_, 1);
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_val_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
else
{
lean_object* v___x_3403_; 
lean_dec_ref(v_a_3394_);
v___x_3403_ = lean_box(0);
return v___x_3403_;
}
}
else
{
lean_object* v___x_3404_; 
lean_dec_ref(v_x_3393_);
v___x_3404_ = lean_box(0);
return v___x_3404_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3405_){
_start:
{
if (lean_obj_tag(v_x_3405_) == 9)
{
lean_object* v_a_3406_; 
v_a_3406_ = lean_ctor_get(v_x_3405_, 0);
if (lean_obj_tag(v_a_3406_) == 1)
{
uint8_t v___x_3407_; 
v___x_3407_ = 1;
return v___x_3407_;
}
else
{
uint8_t v___x_3408_; 
v___x_3408_ = 0;
return v___x_3408_;
}
}
else
{
uint8_t v___x_3409_; 
v___x_3409_ = 0;
return v___x_3409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3410_){
_start:
{
uint8_t v_res_3411_; lean_object* v_r_3412_; 
v_res_3411_ = l_Lean_Expr_isStringLit(v_x_3410_);
lean_dec_ref(v_x_3410_);
v_r_3412_ = lean_box(v_res_3411_);
return v_r_3412_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3417_){
_start:
{
if (lean_obj_tag(v_x_3417_) == 5)
{
lean_object* v_fn_3418_; 
v_fn_3418_ = lean_ctor_get(v_x_3417_, 0);
if (lean_obj_tag(v_fn_3418_) == 4)
{
lean_object* v_arg_3419_; lean_object* v_declName_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; 
v_arg_3419_ = lean_ctor_get(v_x_3417_, 1);
v_declName_3420_ = lean_ctor_get(v_fn_3418_, 0);
v___x_3421_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3422_ = lean_name_eq(v_declName_3420_, v___x_3421_);
if (v___x_3422_ == 0)
{
return v___x_3422_;
}
else
{
uint8_t v___x_3423_; 
v___x_3423_ = l_Lean_Expr_isRawNatLit(v_arg_3419_);
return v___x_3423_;
}
}
else
{
uint8_t v___x_3424_; 
v___x_3424_ = 0;
return v___x_3424_;
}
}
else
{
uint8_t v___x_3425_; 
v___x_3425_ = 0;
return v___x_3425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3426_){
_start:
{
uint8_t v_res_3427_; lean_object* v_r_3428_; 
v_res_3427_ = l_Lean_Expr_isCharLit(v_x_3426_);
lean_dec_ref(v_x_3426_);
v_r_3428_ = lean_box(v_res_3427_);
return v_r_3428_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3429_){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = lean_box(0);
v___x_3431_ = lean_panic_fn_borrowed(v___x_3430_, v_msg_3429_);
return v___x_3431_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3434_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3435_ = lean_unsigned_to_nat(17u);
v___x_3436_ = lean_unsigned_to_nat(986u);
v___x_3437_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3438_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3439_ = l_mkPanicMessageWithDecl(v___x_3438_, v___x_3437_, v___x_3436_, v___x_3435_, v___x_3434_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3440_){
_start:
{
if (lean_obj_tag(v_x_3440_) == 4)
{
lean_object* v_declName_3441_; 
v_declName_3441_ = lean_ctor_get(v_x_3440_, 0);
lean_inc(v_declName_3441_);
return v_declName_3441_;
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3442_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3443_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3442_);
return v___x_3443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Lean_Expr_constName_x21(v_x_3444_);
lean_dec_ref(v_x_3444_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3446_){
_start:
{
if (lean_obj_tag(v_x_3446_) == 4)
{
lean_object* v_declName_3447_; lean_object* v___x_3448_; 
v_declName_3447_ = lean_ctor_get(v_x_3446_, 0);
lean_inc(v_declName_3447_);
v___x_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3448_, 0, v_declName_3447_);
return v___x_3448_;
}
else
{
lean_object* v___x_3449_; 
v___x_3449_ = lean_box(0);
return v___x_3449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Lean_Expr_constName_x3f(v_x_3450_);
lean_dec_ref(v_x_3450_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3452_){
_start:
{
lean_object* v___x_3453_; 
v___x_3453_ = l_Lean_Expr_constName_x3f(v_e_3452_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v___x_3454_; 
v___x_3454_ = lean_box(0);
return v___x_3454_;
}
else
{
lean_object* v_val_3455_; 
v_val_3455_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_val_3455_);
lean_dec_ref_known(v___x_3453_, 1);
return v_val_3455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_Lean_Expr_constName(v_e_3456_);
lean_dec_ref(v_e_3456_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3458_){
_start:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = lean_box(0);
v___x_3460_ = lean_panic_fn_borrowed(v___x_3459_, v_msg_3458_);
return v___x_3460_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3462_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3463_ = lean_unsigned_to_nat(18u);
v___x_3464_ = lean_unsigned_to_nat(1006u);
v___x_3465_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3466_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3467_ = l_mkPanicMessageWithDecl(v___x_3466_, v___x_3465_, v___x_3464_, v___x_3463_, v___x_3462_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3468_){
_start:
{
if (lean_obj_tag(v_x_3468_) == 4)
{
lean_object* v_us_3469_; 
v_us_3469_ = lean_ctor_get(v_x_3468_, 1);
lean_inc(v_us_3469_);
return v_us_3469_;
}
else
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3470_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3471_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3470_);
return v___x_3471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l_Lean_Expr_constLevels_x21(v_x_3472_);
lean_dec_ref(v_x_3472_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3474_){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3475_ = lean_unsigned_to_nat(0u);
v___x_3476_ = lean_panic_fn_borrowed(v___x_3475_, v_msg_3474_);
return v___x_3476_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3479_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3480_ = lean_unsigned_to_nat(16u);
v___x_3481_ = lean_unsigned_to_nat(1010u);
v___x_3482_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3483_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3484_ = l_mkPanicMessageWithDecl(v___x_3483_, v___x_3482_, v___x_3481_, v___x_3480_, v___x_3479_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3485_){
_start:
{
if (lean_obj_tag(v_x_3485_) == 0)
{
lean_object* v_deBruijnIndex_3486_; 
v_deBruijnIndex_3486_ = lean_ctor_get(v_x_3485_, 0);
lean_inc(v_deBruijnIndex_3486_);
return v_deBruijnIndex_3486_;
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3488_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3487_);
return v___x_3488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_Expr_bvarIdx_x21(v_x_3489_);
lean_dec_ref(v_x_3489_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3491_){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = lean_box(0);
v___x_3493_ = lean_panic_fn_borrowed(v___x_3492_, v_msg_3491_);
return v___x_3493_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3496_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3497_ = lean_unsigned_to_nat(14u);
v___x_3498_ = lean_unsigned_to_nat(1014u);
v___x_3499_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3500_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3501_ = l_mkPanicMessageWithDecl(v___x_3500_, v___x_3499_, v___x_3498_, v___x_3497_, v___x_3496_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3502_){
_start:
{
if (lean_obj_tag(v_x_3502_) == 1)
{
lean_object* v_fvarId_3503_; 
v_fvarId_3503_ = lean_ctor_get(v_x_3502_, 0);
lean_inc(v_fvarId_3503_);
return v_fvarId_3503_;
}
else
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3505_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3504_);
return v___x_3505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_Expr_fvarId_x21(v_x_3506_);
lean_dec_ref(v_x_3506_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3508_){
_start:
{
if (lean_obj_tag(v_x_3508_) == 1)
{
lean_object* v_fvarId_3509_; lean_object* v___x_3510_; 
v_fvarId_3509_ = lean_ctor_get(v_x_3508_, 0);
lean_inc(v_fvarId_3509_);
v___x_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3510_, 0, v_fvarId_3509_);
return v___x_3510_;
}
else
{
lean_object* v___x_3511_; 
v___x_3511_ = lean_box(0);
return v___x_3511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3512_){
_start:
{
lean_object* v_res_3513_; 
v_res_3513_ = l_Lean_Expr_fvarId_x3f(v_x_3512_);
lean_dec_ref(v_x_3512_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3514_){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = lean_box(0);
v___x_3516_ = lean_panic_fn_borrowed(v___x_3515_, v_msg_3514_);
return v___x_3516_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3519_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3520_ = lean_unsigned_to_nat(14u);
v___x_3521_ = lean_unsigned_to_nat(1022u);
v___x_3522_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3523_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3524_ = l_mkPanicMessageWithDecl(v___x_3523_, v___x_3522_, v___x_3521_, v___x_3520_, v___x_3519_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3525_){
_start:
{
if (lean_obj_tag(v_x_3525_) == 2)
{
lean_object* v_mvarId_3526_; 
v_mvarId_3526_ = lean_ctor_get(v_x_3525_, 0);
lean_inc(v_mvarId_3526_);
return v_mvarId_3526_;
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3527_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3528_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3527_);
return v___x_3528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Lean_Expr_mvarId_x21(v_x_3529_);
lean_dec_ref(v_x_3529_);
return v_res_3530_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3533_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3534_ = lean_unsigned_to_nat(23u);
v___x_3535_ = lean_unsigned_to_nat(1027u);
v___x_3536_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3537_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3538_ = l_mkPanicMessageWithDecl(v___x_3537_, v___x_3536_, v___x_3535_, v___x_3534_, v___x_3533_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3539_){
_start:
{
switch(lean_obj_tag(v_x_3539_))
{
case 7:
{
lean_object* v_binderName_3540_; 
v_binderName_3540_ = lean_ctor_get(v_x_3539_, 0);
lean_inc(v_binderName_3540_);
return v_binderName_3540_;
}
case 6:
{
lean_object* v_binderName_3541_; 
v_binderName_3541_ = lean_ctor_get(v_x_3539_, 0);
lean_inc(v_binderName_3541_);
return v_binderName_3541_;
}
default: 
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3543_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3542_);
return v___x_3543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Lean_Expr_bindingName_x21(v_x_3544_);
lean_dec_ref(v_x_3544_);
return v_res_3545_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3547_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3548_ = lean_unsigned_to_nat(23u);
v___x_3549_ = lean_unsigned_to_nat(1032u);
v___x_3550_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3551_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3552_ = l_mkPanicMessageWithDecl(v___x_3551_, v___x_3550_, v___x_3549_, v___x_3548_, v___x_3547_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3553_){
_start:
{
switch(lean_obj_tag(v_x_3553_))
{
case 7:
{
lean_object* v_binderType_3554_; 
v_binderType_3554_ = lean_ctor_get(v_x_3553_, 1);
lean_inc_ref(v_binderType_3554_);
return v_binderType_3554_;
}
case 6:
{
lean_object* v_binderType_3555_; 
v_binderType_3555_ = lean_ctor_get(v_x_3553_, 1);
lean_inc_ref(v_binderType_3555_);
return v_binderType_3555_;
}
default: 
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3556_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3557_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3556_);
return v___x_3557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Lean_Expr_bindingDomain_x21(v_x_3558_);
lean_dec_ref(v_x_3558_);
return v_res_3559_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3561_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3562_ = lean_unsigned_to_nat(23u);
v___x_3563_ = lean_unsigned_to_nat(1037u);
v___x_3564_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3565_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3566_ = l_mkPanicMessageWithDecl(v___x_3565_, v___x_3564_, v___x_3563_, v___x_3562_, v___x_3561_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3567_){
_start:
{
switch(lean_obj_tag(v_x_3567_))
{
case 7:
{
lean_object* v_body_3568_; 
v_body_3568_ = lean_ctor_get(v_x_3567_, 2);
lean_inc_ref(v_body_3568_);
return v_body_3568_;
}
case 6:
{
lean_object* v_body_3569_; 
v_body_3569_ = lean_ctor_get(v_x_3567_, 2);
lean_inc_ref(v_body_3569_);
return v_body_3569_;
}
default: 
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3571_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3570_);
return v___x_3571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l_Lean_Expr_bindingBody_x21(v_x_3572_);
lean_dec_ref(v_x_3572_);
return v_res_3573_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3574_){
_start:
{
uint8_t v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3575_ = 0;
v___x_3576_ = lean_box(v___x_3575_);
v___x_3577_ = lean_panic_fn_borrowed(v___x_3576_, v_msg_3574_);
lean_dec(v___x_3576_);
v___x_3578_ = lean_unbox(v___x_3577_);
lean_dec(v___x_3577_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3579_){
_start:
{
uint8_t v_res_3580_; lean_object* v_r_3581_; 
v_res_3580_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3579_);
v_r_3581_ = lean_box(v_res_3580_);
return v_r_3581_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3583_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3584_ = lean_unsigned_to_nat(24u);
v___x_3585_ = lean_unsigned_to_nat(1042u);
v___x_3586_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3587_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3588_ = l_mkPanicMessageWithDecl(v___x_3587_, v___x_3586_, v___x_3585_, v___x_3584_, v___x_3583_);
return v___x_3588_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3589_){
_start:
{
switch(lean_obj_tag(v_x_3589_))
{
case 7:
{
uint8_t v_binderInfo_3590_; 
v_binderInfo_3590_ = lean_ctor_get_uint8(v_x_3589_, sizeof(void*)*3 + 8);
return v_binderInfo_3590_;
}
case 6:
{
uint8_t v_binderInfo_3591_; 
v_binderInfo_3591_ = lean_ctor_get_uint8(v_x_3589_, sizeof(void*)*3 + 8);
return v_binderInfo_3591_;
}
default: 
{
lean_object* v___x_3592_; uint8_t v___x_3593_; 
v___x_3592_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3593_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3592_);
return v___x_3593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3594_){
_start:
{
uint8_t v_res_3595_; lean_object* v_r_3596_; 
v_res_3595_ = l_Lean_Expr_bindingInfo_x21(v_x_3594_);
lean_dec_ref(v_x_3594_);
v_r_3596_ = lean_box(v_res_3595_);
return v_r_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3597_){
_start:
{
lean_object* v_binderName_3598_; 
v_binderName_3598_ = lean_ctor_get(v_x_3597_, 0);
lean_inc(v_binderName_3598_);
return v_binderName_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l_Lean_Expr_forallName___redArg(v_x_3599_);
lean_dec_ref(v_x_3599_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3601_, lean_object* v_x_3602_){
_start:
{
lean_object* v_binderName_3603_; 
v_binderName_3603_ = lean_ctor_get(v_x_3601_, 0);
lean_inc(v_binderName_3603_);
return v_binderName_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3604_, lean_object* v_x_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Lean_Expr_forallName(v_x_3604_, v_x_3605_);
lean_dec_ref(v_x_3604_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3607_){
_start:
{
lean_object* v_binderType_3608_; 
v_binderType_3608_ = lean_ctor_get(v_x_3607_, 1);
lean_inc_ref(v_binderType_3608_);
return v_binderType_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_Lean_Expr_forallDomain___redArg(v_x_3609_);
lean_dec_ref(v_x_3609_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3611_, lean_object* v_x_3612_){
_start:
{
lean_object* v_binderType_3613_; 
v_binderType_3613_ = lean_ctor_get(v_x_3611_, 1);
lean_inc_ref(v_binderType_3613_);
return v_binderType_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3614_, lean_object* v_x_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Lean_Expr_forallDomain(v_x_3614_, v_x_3615_);
lean_dec_ref(v_x_3614_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3617_){
_start:
{
lean_object* v_body_3618_; 
v_body_3618_ = lean_ctor_get(v_x_3617_, 2);
lean_inc_ref(v_body_3618_);
return v_body_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_Expr_forallBody___redArg(v_x_3619_);
lean_dec_ref(v_x_3619_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3621_, lean_object* v_x_3622_){
_start:
{
lean_object* v_body_3623_; 
v_body_3623_ = lean_ctor_get(v_x_3621_, 2);
lean_inc_ref(v_body_3623_);
return v_body_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3624_, lean_object* v_x_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_Lean_Expr_forallBody(v_x_3624_, v_x_3625_);
lean_dec_ref(v_x_3624_);
return v_res_3626_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3627_){
_start:
{
uint8_t v_binderInfo_3628_; 
v_binderInfo_3628_ = lean_ctor_get_uint8(v_x_3627_, sizeof(void*)*3 + 8);
return v_binderInfo_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3629_){
_start:
{
uint8_t v_res_3630_; lean_object* v_r_3631_; 
v_res_3630_ = l_Lean_Expr_forallInfo___redArg(v_x_3629_);
lean_dec_ref(v_x_3629_);
v_r_3631_ = lean_box(v_res_3630_);
return v_r_3631_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3632_, lean_object* v_x_3633_){
_start:
{
uint8_t v_binderInfo_3634_; 
v_binderInfo_3634_ = lean_ctor_get_uint8(v_x_3632_, sizeof(void*)*3 + 8);
return v_binderInfo_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3635_, lean_object* v_x_3636_){
_start:
{
uint8_t v_res_3637_; lean_object* v_r_3638_; 
v_res_3637_ = l_Lean_Expr_forallInfo(v_x_3635_, v_x_3636_);
lean_dec_ref(v_x_3635_);
v_r_3638_ = lean_box(v_res_3637_);
return v_r_3638_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3641_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3642_ = lean_unsigned_to_nat(17u);
v___x_3643_ = lean_unsigned_to_nat(1058u);
v___x_3644_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3645_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3646_ = l_mkPanicMessageWithDecl(v___x_3645_, v___x_3644_, v___x_3643_, v___x_3642_, v___x_3641_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3647_){
_start:
{
if (lean_obj_tag(v_x_3647_) == 8)
{
lean_object* v_declName_3648_; 
v_declName_3648_ = lean_ctor_get(v_x_3647_, 0);
lean_inc(v_declName_3648_);
return v_declName_3648_;
}
else
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3650_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3649_);
return v___x_3650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lean_Expr_letName_x21(v_x_3651_);
lean_dec_ref(v_x_3651_);
return v_res_3652_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3654_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3655_ = lean_unsigned_to_nat(19u);
v___x_3656_ = lean_unsigned_to_nat(1062u);
v___x_3657_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3658_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3659_ = l_mkPanicMessageWithDecl(v___x_3658_, v___x_3657_, v___x_3656_, v___x_3655_, v___x_3654_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3660_){
_start:
{
if (lean_obj_tag(v_x_3660_) == 8)
{
lean_object* v_type_3661_; 
v_type_3661_ = lean_ctor_get(v_x_3660_, 1);
lean_inc_ref(v_type_3661_);
return v_type_3661_;
}
else
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3663_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3662_);
return v___x_3663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lean_Expr_letType_x21(v_x_3664_);
lean_dec_ref(v_x_3664_);
return v_res_3665_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3667_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3668_ = lean_unsigned_to_nat(21u);
v___x_3669_ = lean_unsigned_to_nat(1066u);
v___x_3670_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3671_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3672_ = l_mkPanicMessageWithDecl(v___x_3671_, v___x_3670_, v___x_3669_, v___x_3668_, v___x_3667_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3673_){
_start:
{
if (lean_obj_tag(v_x_3673_) == 8)
{
lean_object* v_value_3674_; 
v_value_3674_ = lean_ctor_get(v_x_3673_, 2);
lean_inc_ref(v_value_3674_);
return v_value_3674_;
}
else
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3675_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3676_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3675_);
return v___x_3676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_Expr_letValue_x21(v_x_3677_);
lean_dec_ref(v_x_3677_);
return v_res_3678_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3680_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3681_ = lean_unsigned_to_nat(23u);
v___x_3682_ = lean_unsigned_to_nat(1070u);
v___x_3683_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3684_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3685_ = l_mkPanicMessageWithDecl(v___x_3684_, v___x_3683_, v___x_3682_, v___x_3681_, v___x_3680_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3686_){
_start:
{
if (lean_obj_tag(v_x_3686_) == 8)
{
lean_object* v_body_3687_; 
v_body_3687_ = lean_ctor_get(v_x_3686_, 3);
lean_inc_ref(v_body_3687_);
return v_body_3687_;
}
else
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3689_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3688_);
return v___x_3689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_Expr_letBody_x21(v_x_3690_);
lean_dec_ref(v_x_3690_);
return v_res_3691_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3692_){
_start:
{
uint8_t v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; 
v___x_3693_ = 0;
v___x_3694_ = lean_box(v___x_3693_);
v___x_3695_ = lean_panic_fn_borrowed(v___x_3694_, v_msg_3692_);
lean_dec(v___x_3694_);
v___x_3696_ = lean_unbox(v___x_3695_);
lean_dec(v___x_3695_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3697_){
_start:
{
uint8_t v_res_3698_; lean_object* v_r_3699_; 
v_res_3698_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3697_);
v_r_3699_ = lean_box(v_res_3698_);
return v_r_3699_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3701_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3702_ = lean_unsigned_to_nat(27u);
v___x_3703_ = lean_unsigned_to_nat(1074u);
v___x_3704_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3705_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3706_ = l_mkPanicMessageWithDecl(v___x_3705_, v___x_3704_, v___x_3703_, v___x_3702_, v___x_3701_);
return v___x_3706_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3707_){
_start:
{
if (lean_obj_tag(v_x_3707_) == 8)
{
uint8_t v_nondep_3708_; 
v_nondep_3708_ = lean_ctor_get_uint8(v_x_3707_, sizeof(void*)*4 + 8);
return v_nondep_3708_;
}
else
{
lean_object* v___x_3709_; uint8_t v___x_3710_; 
v___x_3709_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3710_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3709_);
return v___x_3710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3711_){
_start:
{
uint8_t v_res_3712_; lean_object* v_r_3713_; 
v_res_3712_ = l_Lean_Expr_letNondep_x21(v_x_3711_);
lean_dec_ref(v_x_3711_);
v_r_3713_ = lean_box(v_res_3712_);
return v_r_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3714_){
_start:
{
if (lean_obj_tag(v_x_3714_) == 10)
{
lean_object* v_expr_3715_; 
v_expr_3715_ = lean_ctor_get(v_x_3714_, 1);
v_x_3714_ = v_expr_3715_;
goto _start;
}
else
{
lean_inc_ref(v_x_3714_);
return v_x_3714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_Expr_consumeMData(v_x_3717_);
lean_dec_ref(v_x_3717_);
return v_res_3718_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3721_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3722_ = lean_unsigned_to_nat(17u);
v___x_3723_ = lean_unsigned_to_nat(1082u);
v___x_3724_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3725_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3726_ = l_mkPanicMessageWithDecl(v___x_3725_, v___x_3724_, v___x_3723_, v___x_3722_, v___x_3721_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3727_){
_start:
{
if (lean_obj_tag(v_x_3727_) == 10)
{
lean_object* v_expr_3728_; 
v_expr_3728_ = lean_ctor_get(v_x_3727_, 1);
lean_inc_ref(v_expr_3728_);
return v_expr_3728_;
}
else
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3729_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3730_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3729_);
return v___x_3730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Lean_Expr_mdataExpr_x21(v_x_3731_);
lean_dec_ref(v_x_3731_);
return v_res_3732_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3735_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3736_ = lean_unsigned_to_nat(18u);
v___x_3737_ = lean_unsigned_to_nat(1086u);
v___x_3738_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3739_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3740_ = l_mkPanicMessageWithDecl(v___x_3739_, v___x_3738_, v___x_3737_, v___x_3736_, v___x_3735_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3741_){
_start:
{
if (lean_obj_tag(v_x_3741_) == 11)
{
lean_object* v_struct_3742_; 
v_struct_3742_ = lean_ctor_get(v_x_3741_, 2);
lean_inc_ref(v_struct_3742_);
return v_struct_3742_;
}
else
{
lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3743_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3744_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3743_);
return v___x_3744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l_Lean_Expr_projExpr_x21(v_x_3745_);
lean_dec_ref(v_x_3745_);
return v_res_3746_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3748_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3749_ = lean_unsigned_to_nat(18u);
v___x_3750_ = lean_unsigned_to_nat(1090u);
v___x_3751_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3752_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3753_ = l_mkPanicMessageWithDecl(v___x_3752_, v___x_3751_, v___x_3750_, v___x_3749_, v___x_3748_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3754_){
_start:
{
if (lean_obj_tag(v_x_3754_) == 11)
{
lean_object* v_idx_3755_; 
v_idx_3755_ = lean_ctor_get(v_x_3754_, 1);
lean_inc(v_idx_3755_);
return v_idx_3755_;
}
else
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3756_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3757_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3756_);
return v___x_3757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l_Lean_Expr_projIdx_x21(v_x_3758_);
lean_dec_ref(v_x_3758_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3760_){
_start:
{
if (lean_obj_tag(v_x_3760_) == 7)
{
lean_object* v_body_3761_; 
v_body_3761_ = lean_ctor_get(v_x_3760_, 2);
v_x_3760_ = v_body_3761_;
goto _start;
}
else
{
lean_inc_ref(v_x_3760_);
return v_x_3760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Lean_Expr_getForallBody(v_x_3763_);
lean_dec_ref(v_x_3763_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3765_, lean_object* v_x_3766_){
_start:
{
lean_object* v_zero_3767_; uint8_t v_isZero_3768_; 
v_zero_3767_ = lean_unsigned_to_nat(0u);
v_isZero_3768_ = lean_nat_dec_eq(v_x_3765_, v_zero_3767_);
if (v_isZero_3768_ == 1)
{
lean_dec(v_x_3765_);
lean_inc_ref(v_x_3766_);
return v_x_3766_;
}
else
{
if (lean_obj_tag(v_x_3766_) == 7)
{
lean_object* v_body_3769_; lean_object* v_one_3770_; lean_object* v_n_3771_; 
v_body_3769_ = lean_ctor_get(v_x_3766_, 2);
v_one_3770_ = lean_unsigned_to_nat(1u);
v_n_3771_ = lean_nat_sub(v_x_3765_, v_one_3770_);
lean_dec(v_x_3765_);
v_x_3765_ = v_n_3771_;
v_x_3766_ = v_body_3769_;
goto _start;
}
else
{
lean_dec(v_x_3765_);
lean_inc_ref(v_x_3766_);
return v_x_3766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3773_, lean_object* v_x_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3773_, v_x_3774_);
lean_dec_ref(v_x_3774_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3776_){
_start:
{
if (lean_obj_tag(v_x_3776_) == 7)
{
lean_object* v_binderName_3777_; lean_object* v_body_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v_binderName_3777_ = lean_ctor_get(v_x_3776_, 0);
v_body_3778_ = lean_ctor_get(v_x_3776_, 2);
v___x_3779_ = l_Lean_Expr_getForallBinderNames(v_body_3778_);
lean_inc(v_binderName_3777_);
v___x_3780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3780_, 0, v_binderName_3777_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
return v___x_3780_;
}
else
{
lean_object* v___x_3781_; 
v___x_3781_ = lean_box(0);
return v___x_3781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Expr_getForallBinderNames(v_x_3782_);
lean_dec_ref(v_x_3782_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3784_){
_start:
{
switch(lean_obj_tag(v_x_3784_))
{
case 10:
{
lean_object* v_expr_3785_; 
v_expr_3785_ = lean_ctor_get(v_x_3784_, 1);
v_x_3784_ = v_expr_3785_;
goto _start;
}
case 7:
{
lean_object* v_body_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v_body_3787_ = lean_ctor_get(v_x_3784_, 2);
v___x_3788_ = l_Lean_Expr_getNumHeadForalls(v_body_3787_);
v___x_3789_ = lean_unsigned_to_nat(1u);
v___x_3790_ = lean_nat_add(v___x_3788_, v___x_3789_);
lean_dec(v___x_3788_);
return v___x_3790_;
}
default: 
{
lean_object* v___x_3791_; 
v___x_3791_ = lean_unsigned_to_nat(0u);
return v___x_3791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_Expr_getNumHeadForalls(v_x_3792_);
lean_dec_ref(v_x_3792_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3794_){
_start:
{
if (lean_obj_tag(v_x_3794_) == 5)
{
lean_object* v_fn_3795_; 
v_fn_3795_ = lean_ctor_get(v_x_3794_, 0);
v_x_3794_ = v_fn_3795_;
goto _start;
}
else
{
lean_inc_ref(v_x_3794_);
return v_x_3794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l_Lean_Expr_getAppFn(v_x_3797_);
lean_dec_ref(v_x_3797_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3799_){
_start:
{
switch(lean_obj_tag(v_x_3799_))
{
case 5:
{
lean_object* v_fn_3800_; 
v_fn_3800_ = lean_ctor_get(v_x_3799_, 0);
v_x_3799_ = v_fn_3800_;
goto _start;
}
case 10:
{
lean_object* v_expr_3802_; 
v_expr_3802_ = lean_ctor_get(v_x_3799_, 1);
v_x_3799_ = v_expr_3802_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3799_);
return v_x_3799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Lean_Expr_getAppFn_x27(v_x_3804_);
lean_dec_ref(v_x_3804_);
return v_res_3805_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3806_, lean_object* v_n_3807_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lean_Expr_getAppFn(v_e_3806_);
if (lean_obj_tag(v___x_3808_) == 4)
{
lean_object* v_declName_3809_; uint8_t v___x_3810_; 
v_declName_3809_ = lean_ctor_get(v___x_3808_, 0);
lean_inc(v_declName_3809_);
lean_dec_ref_known(v___x_3808_, 2);
v___x_3810_ = lean_name_eq(v_declName_3809_, v_n_3807_);
lean_dec(v_declName_3809_);
return v___x_3810_;
}
else
{
uint8_t v___x_3811_; 
lean_dec_ref(v___x_3808_);
v___x_3811_ = 0;
return v___x_3811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3812_, lean_object* v_n_3813_){
_start:
{
uint8_t v_res_3814_; lean_object* v_r_3815_; 
v_res_3814_ = l_Lean_Expr_isAppOf(v_e_3812_, v_n_3813_);
lean_dec(v_n_3813_);
lean_dec_ref(v_e_3812_);
v_r_3815_ = lean_box(v_res_3814_);
return v_r_3815_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3816_, lean_object* v_x_3817_, lean_object* v_x_3818_){
_start:
{
switch(lean_obj_tag(v_x_3816_))
{
case 4:
{
lean_object* v_declName_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; 
v_declName_3819_ = lean_ctor_get(v_x_3816_, 0);
v___x_3820_ = lean_unsigned_to_nat(0u);
v___x_3821_ = lean_nat_dec_eq(v_x_3818_, v___x_3820_);
lean_dec(v_x_3818_);
if (v___x_3821_ == 0)
{
return v___x_3821_;
}
else
{
uint8_t v___x_3822_; 
v___x_3822_ = lean_name_eq(v_declName_3819_, v_x_3817_);
return v___x_3822_;
}
}
case 5:
{
lean_object* v_fn_3823_; lean_object* v_zero_3824_; uint8_t v_isZero_3825_; 
v_fn_3823_ = lean_ctor_get(v_x_3816_, 0);
v_zero_3824_ = lean_unsigned_to_nat(0u);
v_isZero_3825_ = lean_nat_dec_eq(v_x_3818_, v_zero_3824_);
if (v_isZero_3825_ == 0)
{
lean_object* v_one_3826_; lean_object* v_n_3827_; 
v_one_3826_ = lean_unsigned_to_nat(1u);
v_n_3827_ = lean_nat_sub(v_x_3818_, v_one_3826_);
lean_dec(v_x_3818_);
v_x_3816_ = v_fn_3823_;
v_x_3818_ = v_n_3827_;
goto _start;
}
else
{
uint8_t v___x_3829_; 
lean_dec(v_x_3818_);
v___x_3829_ = 0;
return v___x_3829_;
}
}
default: 
{
uint8_t v___x_3830_; 
lean_dec(v_x_3818_);
v___x_3830_ = 0;
return v___x_3830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3831_, lean_object* v_x_3832_, lean_object* v_x_3833_){
_start:
{
uint8_t v_res_3834_; lean_object* v_r_3835_; 
v_res_3834_ = l_Lean_Expr_isAppOfArity(v_x_3831_, v_x_3832_, v_x_3833_);
lean_dec(v_x_3832_);
lean_dec_ref(v_x_3831_);
v_r_3835_ = lean_box(v_res_3834_);
return v_r_3835_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3836_, lean_object* v_x_3837_, lean_object* v_x_3838_){
_start:
{
switch(lean_obj_tag(v_x_3836_))
{
case 10:
{
lean_object* v_expr_3839_; 
v_expr_3839_ = lean_ctor_get(v_x_3836_, 1);
v_x_3836_ = v_expr_3839_;
goto _start;
}
case 4:
{
lean_object* v_declName_3841_; lean_object* v___x_3842_; uint8_t v___x_3843_; 
v_declName_3841_ = lean_ctor_get(v_x_3836_, 0);
v___x_3842_ = lean_unsigned_to_nat(0u);
v___x_3843_ = lean_nat_dec_eq(v_x_3838_, v___x_3842_);
lean_dec(v_x_3838_);
if (v___x_3843_ == 0)
{
return v___x_3843_;
}
else
{
uint8_t v___x_3844_; 
v___x_3844_ = lean_name_eq(v_declName_3841_, v_x_3837_);
return v___x_3844_;
}
}
case 5:
{
lean_object* v_fn_3845_; lean_object* v_zero_3846_; uint8_t v_isZero_3847_; 
v_fn_3845_ = lean_ctor_get(v_x_3836_, 0);
v_zero_3846_ = lean_unsigned_to_nat(0u);
v_isZero_3847_ = lean_nat_dec_eq(v_x_3838_, v_zero_3846_);
if (v_isZero_3847_ == 0)
{
lean_object* v_one_3848_; lean_object* v_n_3849_; 
v_one_3848_ = lean_unsigned_to_nat(1u);
v_n_3849_ = lean_nat_sub(v_x_3838_, v_one_3848_);
lean_dec(v_x_3838_);
v_x_3836_ = v_fn_3845_;
v_x_3838_ = v_n_3849_;
goto _start;
}
else
{
uint8_t v___x_3851_; 
lean_dec(v_x_3838_);
v___x_3851_ = 0;
return v___x_3851_;
}
}
default: 
{
uint8_t v___x_3852_; 
lean_dec(v_x_3838_);
v___x_3852_ = 0;
return v___x_3852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3853_, lean_object* v_x_3854_, lean_object* v_x_3855_){
_start:
{
uint8_t v_res_3856_; lean_object* v_r_3857_; 
v_res_3856_ = l_Lean_Expr_isAppOfArity_x27(v_x_3853_, v_x_3854_, v_x_3855_);
lean_dec(v_x_3854_);
lean_dec_ref(v_x_3853_);
v_r_3857_ = lean_box(v_res_3856_);
return v_r_3857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3858_, lean_object* v_x_3859_){
_start:
{
if (lean_obj_tag(v_x_3858_) == 5)
{
lean_object* v_fn_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v_fn_3860_ = lean_ctor_get(v_x_3858_, 0);
v___x_3861_ = lean_unsigned_to_nat(1u);
v___x_3862_ = lean_nat_add(v_x_3859_, v___x_3861_);
lean_dec(v_x_3859_);
v_x_3858_ = v_fn_3860_;
v_x_3859_ = v___x_3862_;
goto _start;
}
else
{
return v_x_3859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3864_, lean_object* v_x_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3864_, v_x_3865_);
lean_dec_ref(v_x_3864_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3867_){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = lean_unsigned_to_nat(0u);
v___x_3869_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3867_, v___x_3868_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Lean_Expr_getAppNumArgs(v_e_3870_);
lean_dec_ref(v_e_3870_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3872_, lean_object* v_a_3873_){
_start:
{
switch(lean_obj_tag(v_a_3872_))
{
case 10:
{
lean_object* v_expr_3874_; 
v_expr_3874_ = lean_ctor_get(v_a_3872_, 1);
v_a_3872_ = v_expr_3874_;
goto _start;
}
case 5:
{
lean_object* v_fn_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v_fn_3876_ = lean_ctor_get(v_a_3872_, 0);
v___x_3877_ = lean_unsigned_to_nat(1u);
v___x_3878_ = lean_nat_add(v_a_3873_, v___x_3877_);
lean_dec(v_a_3873_);
v_a_3872_ = v_fn_3876_;
v_a_3873_ = v___x_3878_;
goto _start;
}
default: 
{
return v_a_3873_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3880_, lean_object* v_a_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3880_, v_a_3881_);
lean_dec_ref(v_a_3880_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3883_){
_start:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = lean_unsigned_to_nat(0u);
v___x_3885_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3883_, v___x_3884_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3886_);
lean_dec_ref(v_e_3886_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3888_, lean_object* v_x_3889_){
_start:
{
lean_object* v_zero_3890_; uint8_t v_isZero_3891_; 
v_zero_3890_ = lean_unsigned_to_nat(0u);
v_isZero_3891_ = lean_nat_dec_eq(v_x_3888_, v_zero_3890_);
if (v_isZero_3891_ == 0)
{
if (lean_obj_tag(v_x_3889_) == 5)
{
lean_object* v_fn_3892_; lean_object* v_one_3893_; lean_object* v_n_3894_; 
v_fn_3892_ = lean_ctor_get(v_x_3889_, 0);
v_one_3893_ = lean_unsigned_to_nat(1u);
v_n_3894_ = lean_nat_sub(v_x_3888_, v_one_3893_);
lean_dec(v_x_3888_);
v_x_3888_ = v_n_3894_;
v_x_3889_ = v_fn_3892_;
goto _start;
}
else
{
lean_dec(v_x_3888_);
lean_inc_ref(v_x_3889_);
return v_x_3889_;
}
}
else
{
lean_dec(v_x_3888_);
lean_inc_ref(v_x_3889_);
return v_x_3889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_3896_, lean_object* v_x_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_Expr_getBoundedAppFn(v_x_3896_, v_x_3897_);
lean_dec_ref(v_x_3897_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_3899_, lean_object* v_x_3900_, lean_object* v_x_3901_){
_start:
{
if (lean_obj_tag(v_x_3899_) == 5)
{
lean_object* v_fn_3902_; lean_object* v_arg_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v_fn_3902_ = lean_ctor_get(v_x_3899_, 0);
lean_inc_ref(v_fn_3902_);
v_arg_3903_ = lean_ctor_get(v_x_3899_, 1);
lean_inc_ref(v_arg_3903_);
lean_dec_ref_known(v_x_3899_, 2);
v___x_3904_ = lean_array_set(v_x_3900_, v_x_3901_, v_arg_3903_);
v___x_3905_ = lean_unsigned_to_nat(1u);
v___x_3906_ = lean_nat_sub(v_x_3901_, v___x_3905_);
lean_dec(v_x_3901_);
v_x_3899_ = v_fn_3902_;
v_x_3900_ = v___x_3904_;
v_x_3901_ = v___x_3906_;
goto _start;
}
else
{
lean_dec(v_x_3901_);
lean_dec_ref(v_x_3899_);
return v_x_3900_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_3908_; lean_object* v_dummy_3909_; 
v___x_3908_ = lean_box(0);
v_dummy_3909_ = l_Lean_Expr_sort___override(v___x_3908_);
return v_dummy_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_3910_){
_start:
{
lean_object* v_dummy_3911_; lean_object* v_nargs_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v_dummy_3911_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3912_ = l_Lean_Expr_getAppNumArgs(v_e_3910_);
lean_inc(v_nargs_3912_);
v___x_3913_ = lean_mk_array(v_nargs_3912_, v_dummy_3911_);
v___x_3914_ = lean_unsigned_to_nat(1u);
v___x_3915_ = lean_nat_sub(v_nargs_3912_, v___x_3914_);
lean_dec(v_nargs_3912_);
v___x_3916_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3910_, v___x_3913_, v___x_3915_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_3917_, lean_object* v_x_3918_, lean_object* v_x_3919_){
_start:
{
if (lean_obj_tag(v_x_3917_) == 5)
{
lean_object* v_fn_3920_; lean_object* v_arg_3921_; lean_object* v_zero_3922_; uint8_t v_isZero_3923_; 
v_fn_3920_ = lean_ctor_get(v_x_3917_, 0);
lean_inc_ref(v_fn_3920_);
v_arg_3921_ = lean_ctor_get(v_x_3917_, 1);
lean_inc_ref(v_arg_3921_);
lean_dec_ref_known(v_x_3917_, 2);
v_zero_3922_ = lean_unsigned_to_nat(0u);
v_isZero_3923_ = lean_nat_dec_eq(v_x_3919_, v_zero_3922_);
if (v_isZero_3923_ == 0)
{
lean_object* v_one_3924_; lean_object* v_n_3925_; lean_object* v___x_3926_; 
v_one_3924_ = lean_unsigned_to_nat(1u);
v_n_3925_ = lean_nat_sub(v_x_3919_, v_one_3924_);
lean_dec(v_x_3919_);
v___x_3926_ = lean_array_set(v_x_3918_, v_n_3925_, v_arg_3921_);
v_x_3917_ = v_fn_3920_;
v_x_3918_ = v___x_3926_;
v_x_3919_ = v_n_3925_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3921_);
lean_dec_ref(v_fn_3920_);
lean_dec(v_x_3919_);
return v_x_3918_;
}
}
else
{
lean_dec(v_x_3919_);
lean_dec_ref(v_x_3917_);
return v_x_3918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_3928_, lean_object* v_e_3929_){
_start:
{
lean_object* v_dummy_3930_; lean_object* v___y_3932_; lean_object* v___x_3935_; uint8_t v___x_3936_; 
v_dummy_3930_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_3935_ = l_Lean_Expr_getAppNumArgs(v_e_3929_);
v___x_3936_ = lean_nat_dec_le(v_maxArgs_3928_, v___x_3935_);
if (v___x_3936_ == 0)
{
lean_dec(v_maxArgs_3928_);
v___y_3932_ = v___x_3935_;
goto v___jp_3931_;
}
else
{
lean_dec(v___x_3935_);
v___y_3932_ = v_maxArgs_3928_;
goto v___jp_3931_;
}
v___jp_3931_:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
lean_inc(v___y_3932_);
v___x_3933_ = lean_mk_array(v___y_3932_, v_dummy_3930_);
v___x_3934_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_3929_, v___x_3933_, v___y_3932_);
return v___x_3934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_3937_, lean_object* v_x_3938_){
_start:
{
if (lean_obj_tag(v_x_3937_) == 5)
{
lean_object* v_fn_3939_; lean_object* v_arg_3940_; lean_object* v___x_3941_; 
v_fn_3939_ = lean_ctor_get(v_x_3937_, 0);
lean_inc_ref(v_fn_3939_);
v_arg_3940_ = lean_ctor_get(v_x_3937_, 1);
lean_inc_ref(v_arg_3940_);
lean_dec_ref_known(v_x_3937_, 2);
v___x_3941_ = lean_array_push(v_x_3938_, v_arg_3940_);
v_x_3937_ = v_fn_3939_;
v_x_3938_ = v___x_3941_;
goto _start;
}
else
{
lean_dec_ref(v_x_3937_);
return v_x_3938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_3943_){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3944_ = l_Lean_Expr_getAppNumArgs(v_e_3943_);
v___x_3945_ = lean_mk_empty_array_with_capacity(v___x_3944_);
lean_dec(v___x_3944_);
v___x_3946_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3943_, v___x_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_3947_, lean_object* v_x_3948_, lean_object* v_x_3949_, lean_object* v_x_3950_){
_start:
{
if (lean_obj_tag(v_x_3948_) == 5)
{
lean_object* v_fn_3951_; lean_object* v_arg_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_fn_3951_ = lean_ctor_get(v_x_3948_, 0);
lean_inc_ref(v_fn_3951_);
v_arg_3952_ = lean_ctor_get(v_x_3948_, 1);
lean_inc_ref(v_arg_3952_);
lean_dec_ref_known(v_x_3948_, 2);
v___x_3953_ = lean_array_set(v_x_3949_, v_x_3950_, v_arg_3952_);
v___x_3954_ = lean_unsigned_to_nat(1u);
v___x_3955_ = lean_nat_sub(v_x_3950_, v___x_3954_);
lean_dec(v_x_3950_);
v_x_3948_ = v_fn_3951_;
v_x_3949_ = v___x_3953_;
v_x_3950_ = v___x_3955_;
goto _start;
}
else
{
lean_object* v___x_3957_; 
lean_dec(v_x_3950_);
v___x_3957_ = lean_apply_2(v_k_3947_, v_x_3948_, v_x_3949_);
return v___x_3957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_3958_, lean_object* v_k_3959_, lean_object* v_x_3960_, lean_object* v_x_3961_, lean_object* v_x_3962_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_Lean_Expr_withAppAux___redArg(v_k_3959_, v_x_3960_, v_x_3961_, v_x_3962_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_3964_, lean_object* v_k_3965_){
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
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_3972_, lean_object* v_e_3973_, lean_object* v_k_3974_){
_start:
{
lean_object* v_dummy_3975_; lean_object* v_nargs_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v_dummy_3975_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3976_ = l_Lean_Expr_getAppNumArgs(v_e_3973_);
lean_inc(v_nargs_3976_);
v___x_3977_ = lean_mk_array(v_nargs_3976_, v_dummy_3975_);
v___x_3978_ = lean_unsigned_to_nat(1u);
v___x_3979_ = lean_nat_sub(v_nargs_3976_, v___x_3978_);
lean_dec(v_nargs_3976_);
v___x_3980_ = l_Lean_Expr_withAppAux___redArg(v_k_3974_, v_e_3973_, v___x_3977_, v___x_3979_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_3981_, lean_object* v_x_3982_, lean_object* v_x_3983_){
_start:
{
if (lean_obj_tag(v_x_3981_) == 5)
{
lean_object* v_fn_3984_; lean_object* v_arg_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v_fn_3984_ = lean_ctor_get(v_x_3981_, 0);
lean_inc_ref(v_fn_3984_);
v_arg_3985_ = lean_ctor_get(v_x_3981_, 1);
lean_inc_ref(v_arg_3985_);
lean_dec_ref_known(v_x_3981_, 2);
v___x_3986_ = lean_array_set(v_x_3982_, v_x_3983_, v_arg_3985_);
v___x_3987_ = lean_unsigned_to_nat(1u);
v___x_3988_ = lean_nat_sub(v_x_3983_, v___x_3987_);
lean_dec(v_x_3983_);
v_x_3981_ = v_fn_3984_;
v_x_3982_ = v___x_3986_;
v_x_3983_ = v___x_3988_;
goto _start;
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
lean_dec(v_x_3983_);
v___x_3990_ = l_Lean_Expr_constName(v_x_3981_);
lean_dec_ref(v_x_3981_);
v___x_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
lean_ctor_set(v___x_3991_, 1, v_x_3982_);
return v___x_3991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_3992_){
_start:
{
lean_object* v_dummy_3993_; lean_object* v_nargs_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v_dummy_3993_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3994_ = l_Lean_Expr_getAppNumArgs(v_e_3992_);
lean_inc(v_nargs_3994_);
v___x_3995_ = lean_mk_array(v_nargs_3994_, v_dummy_3993_);
v___x_3996_ = lean_unsigned_to_nat(1u);
v___x_3997_ = lean_nat_sub(v_nargs_3994_, v___x_3996_);
lean_dec(v_nargs_3994_);
v___x_3998_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_3992_, v___x_3995_, v___x_3997_);
return v___x_3998_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3999_; 
v___x_3999_ = l_Array_instInhabited(lean_box(0));
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_4000_){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4001_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_4002_ = lean_panic_fn_borrowed(v___x_4001_, v_msg_4000_);
return v___x_4002_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4005_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_4006_ = lean_unsigned_to_nat(27u);
v___x_4007_ = lean_unsigned_to_nat(1247u);
v___x_4008_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_4009_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4010_ = l_mkPanicMessageWithDecl(v___x_4009_, v___x_4008_, v___x_4007_, v___x_4006_, v___x_4005_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v_zero_4014_; uint8_t v_isZero_4015_; 
v_zero_4014_ = lean_unsigned_to_nat(0u);
v_isZero_4015_ = lean_nat_dec_eq(v_a_4011_, v_zero_4014_);
if (v_isZero_4015_ == 1)
{
lean_dec_ref(v_a_4012_);
lean_dec(v_a_4011_);
return v_a_4013_;
}
else
{
if (lean_obj_tag(v_a_4012_) == 5)
{
lean_object* v_fn_4016_; lean_object* v_arg_4017_; lean_object* v_one_4018_; lean_object* v_n_4019_; lean_object* v___x_4020_; 
v_fn_4016_ = lean_ctor_get(v_a_4012_, 0);
lean_inc_ref(v_fn_4016_);
v_arg_4017_ = lean_ctor_get(v_a_4012_, 1);
lean_inc_ref(v_arg_4017_);
lean_dec_ref_known(v_a_4012_, 2);
v_one_4018_ = lean_unsigned_to_nat(1u);
v_n_4019_ = lean_nat_sub(v_a_4011_, v_one_4018_);
lean_dec(v_a_4011_);
v___x_4020_ = lean_array_set(v_a_4013_, v_n_4019_, v_arg_4017_);
v_a_4011_ = v_n_4019_;
v_a_4012_ = v_fn_4016_;
v_a_4013_ = v___x_4020_;
goto _start;
}
else
{
lean_object* v___x_4022_; lean_object* v___x_4023_; 
lean_dec_ref(v_a_4013_);
lean_dec_ref(v_a_4012_);
lean_dec(v_a_4011_);
v___x_4022_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_4023_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_4022_);
return v___x_4023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_4024_, lean_object* v_n_4025_){
_start:
{
lean_object* v_dummy_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v_dummy_4026_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_4025_);
v___x_4027_ = lean_mk_array(v_n_4025_, v_dummy_4026_);
v___x_4028_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_4025_, v_e_4024_, v___x_4027_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_4029_, lean_object* v_n_4030_){
_start:
{
lean_object* v_zero_4031_; uint8_t v_isZero_4032_; 
v_zero_4031_ = lean_unsigned_to_nat(0u);
v_isZero_4032_ = lean_nat_dec_eq(v_n_4030_, v_zero_4031_);
if (v_isZero_4032_ == 1)
{
lean_dec(v_n_4030_);
lean_inc_ref(v_e_4029_);
return v_e_4029_;
}
else
{
if (lean_obj_tag(v_e_4029_) == 5)
{
lean_object* v_fn_4033_; lean_object* v_one_4034_; lean_object* v_n_4035_; 
v_fn_4033_ = lean_ctor_get(v_e_4029_, 0);
v_one_4034_ = lean_unsigned_to_nat(1u);
v_n_4035_ = lean_nat_sub(v_n_4030_, v_one_4034_);
lean_dec(v_n_4030_);
v_e_4029_ = v_fn_4033_;
v_n_4030_ = v_n_4035_;
goto _start;
}
else
{
lean_dec(v_n_4030_);
lean_inc_ref(v_e_4029_);
return v_e_4029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_4037_, lean_object* v_n_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l_Lean_Expr_stripArgsN(v_e_4037_, v_n_4038_);
lean_dec_ref(v_e_4037_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_4040_, lean_object* v_n_4041_){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = l_Lean_Expr_getAppNumArgs(v_e_4040_);
v___x_4043_ = lean_nat_sub(v___x_4042_, v_n_4041_);
lean_dec(v___x_4042_);
v___x_4044_ = l_Lean_Expr_stripArgsN(v_e_4040_, v___x_4043_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_4045_, lean_object* v_n_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_Lean_Expr_getAppPrefix(v_e_4045_, v_n_4046_);
lean_dec(v_n_4046_);
lean_dec_ref(v_e_4045_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_4048_, lean_object* v_inst_4049_, lean_object* v_f_4050_, lean_object* v_x_4051_){
_start:
{
size_t v_sz_4052_; size_t v___x_4053_; lean_object* v___x_4054_; 
v_sz_4052_ = lean_array_size(v_args_4048_);
v___x_4053_ = ((size_t)0ULL);
v___x_4054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4049_, v_f_4050_, v_sz_4052_, v___x_4053_, v_args_4048_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_4056_, lean_object* v_inst_4057_, lean_object* v_f_4058_, lean_object* v_toSeq_4059_, lean_object* v_fn_4060_, lean_object* v_args_4061_){
_start:
{
lean_object* v_map_4062_; lean_object* v___f_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v_map_4062_ = lean_ctor_get(v_toFunctor_4056_, 0);
lean_inc(v_map_4062_);
lean_dec_ref(v_toFunctor_4056_);
lean_inc(v_f_4058_);
v___f_4063_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4063_, 0, v_args_4061_);
lean_closure_set(v___f_4063_, 1, v_inst_4057_);
lean_closure_set(v___f_4063_, 2, v_f_4058_);
v___x_4064_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_4065_ = lean_apply_1(v_f_4058_, v_fn_4060_);
v___x_4066_ = lean_apply_4(v_map_4062_, lean_box(0), lean_box(0), v___x_4064_, v___x_4065_);
v___x_4067_ = lean_apply_4(v_toSeq_4059_, lean_box(0), lean_box(0), v___x_4066_, v___f_4063_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_4068_, lean_object* v_f_4069_, lean_object* v_e_4070_){
_start:
{
lean_object* v_toApplicative_4071_; lean_object* v_toFunctor_4072_; lean_object* v_toSeq_4073_; lean_object* v___f_4074_; lean_object* v_dummy_4075_; lean_object* v_nargs_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v_toApplicative_4071_ = lean_ctor_get(v_inst_4068_, 0);
v_toFunctor_4072_ = lean_ctor_get(v_toApplicative_4071_, 0);
lean_inc_ref(v_toFunctor_4072_);
v_toSeq_4073_ = lean_ctor_get(v_toApplicative_4071_, 2);
lean_inc(v_toSeq_4073_);
v___f_4074_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_4074_, 0, v_toFunctor_4072_);
lean_closure_set(v___f_4074_, 1, v_inst_4068_);
lean_closure_set(v___f_4074_, 2, v_f_4069_);
lean_closure_set(v___f_4074_, 3, v_toSeq_4073_);
v_dummy_4075_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4076_ = l_Lean_Expr_getAppNumArgs(v_e_4070_);
lean_inc(v_nargs_4076_);
v___x_4077_ = lean_mk_array(v_nargs_4076_, v_dummy_4075_);
v___x_4078_ = lean_unsigned_to_nat(1u);
v___x_4079_ = lean_nat_sub(v_nargs_4076_, v___x_4078_);
lean_dec(v_nargs_4076_);
v___x_4080_ = l_Lean_Expr_withAppAux___redArg(v___f_4074_, v_e_4070_, v___x_4077_, v___x_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_4081_, lean_object* v_inst_4082_, lean_object* v_f_4083_, lean_object* v_e_4084_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_Expr_traverseApp___redArg(v_inst_4082_, v_f_4083_, v_e_4084_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_4086_, lean_object* v_x_4087_, lean_object* v_x_4088_){
_start:
{
if (lean_obj_tag(v_x_4087_) == 5)
{
lean_object* v_fn_4089_; lean_object* v_arg_4090_; lean_object* v___x_4091_; 
v_fn_4089_ = lean_ctor_get(v_x_4087_, 0);
lean_inc_ref(v_fn_4089_);
v_arg_4090_ = lean_ctor_get(v_x_4087_, 1);
lean_inc_ref(v_arg_4090_);
lean_dec_ref_known(v_x_4087_, 2);
v___x_4091_ = lean_array_push(v_x_4088_, v_arg_4090_);
v_x_4087_ = v_fn_4089_;
v_x_4088_ = v___x_4091_;
goto _start;
}
else
{
lean_object* v___x_4093_; 
v___x_4093_ = lean_apply_2(v_k_4086_, v_x_4087_, v_x_4088_);
return v___x_4093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_4094_, lean_object* v_k_4095_, lean_object* v_x_4096_, lean_object* v_x_4097_){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4095_, v_x_4096_, v_x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_4099_, lean_object* v_k_4100_){
_start:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4101_ = l_Lean_Expr_getAppNumArgs(v_e_4099_);
v___x_4102_ = lean_mk_empty_array_with_capacity(v___x_4101_);
lean_dec(v___x_4101_);
v___x_4103_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4100_, v_e_4099_, v___x_4102_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_4104_, lean_object* v_e_4105_, lean_object* v_k_4106_){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4107_ = l_Lean_Expr_getAppNumArgs(v_e_4105_);
v___x_4108_ = lean_mk_empty_array_with_capacity(v___x_4107_);
lean_dec(v___x_4107_);
v___x_4109_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4106_, v_e_4105_, v___x_4108_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_4110_, lean_object* v_x_4111_, lean_object* v_x_4112_){
_start:
{
if (lean_obj_tag(v_x_4110_) == 5)
{
lean_object* v_fn_4113_; lean_object* v_arg_4114_; lean_object* v_zero_4115_; uint8_t v_isZero_4116_; 
v_fn_4113_ = lean_ctor_get(v_x_4110_, 0);
v_arg_4114_ = lean_ctor_get(v_x_4110_, 1);
v_zero_4115_ = lean_unsigned_to_nat(0u);
v_isZero_4116_ = lean_nat_dec_eq(v_x_4111_, v_zero_4115_);
if (v_isZero_4116_ == 1)
{
lean_dec(v_x_4111_);
lean_inc_ref(v_arg_4114_);
return v_arg_4114_;
}
else
{
lean_object* v_one_4117_; lean_object* v_n_4118_; 
v_one_4117_ = lean_unsigned_to_nat(1u);
v_n_4118_ = lean_nat_sub(v_x_4111_, v_one_4117_);
lean_dec(v_x_4111_);
v_x_4110_ = v_fn_4113_;
v_x_4111_ = v_n_4118_;
goto _start;
}
}
else
{
lean_dec(v_x_4111_);
lean_inc_ref(v_x_4112_);
return v_x_4112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_4120_, lean_object* v_x_4121_, lean_object* v_x_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l_Lean_Expr_getRevArgD(v_x_4120_, v_x_4121_, v_x_4122_);
lean_dec_ref(v_x_4122_);
lean_dec_ref(v_x_4120_);
return v_res_4123_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4126_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4127_ = lean_unsigned_to_nat(20u);
v___x_4128_ = lean_unsigned_to_nat(1288u);
v___x_4129_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4130_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4131_ = l_mkPanicMessageWithDecl(v___x_4130_, v___x_4129_, v___x_4128_, v___x_4127_, v___x_4126_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4132_, lean_object* v_x_4133_){
_start:
{
if (lean_obj_tag(v_x_4132_) == 5)
{
lean_object* v_fn_4134_; lean_object* v_arg_4135_; lean_object* v_zero_4136_; uint8_t v_isZero_4137_; 
v_fn_4134_ = lean_ctor_get(v_x_4132_, 0);
v_arg_4135_ = lean_ctor_get(v_x_4132_, 1);
v_zero_4136_ = lean_unsigned_to_nat(0u);
v_isZero_4137_ = lean_nat_dec_eq(v_x_4133_, v_zero_4136_);
if (v_isZero_4137_ == 1)
{
lean_dec(v_x_4133_);
lean_inc_ref(v_arg_4135_);
return v_arg_4135_;
}
else
{
lean_object* v_one_4138_; lean_object* v_n_4139_; 
v_one_4138_ = lean_unsigned_to_nat(1u);
v_n_4139_ = lean_nat_sub(v_x_4133_, v_one_4138_);
lean_dec(v_x_4133_);
v_x_4132_ = v_fn_4134_;
v_x_4133_ = v_n_4139_;
goto _start;
}
}
else
{
lean_object* v___x_4141_; lean_object* v___x_4142_; 
lean_dec(v_x_4133_);
v___x_4141_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4142_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4141_);
return v___x_4142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4143_, lean_object* v_x_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_Lean_Expr_getRevArg_x21(v_x_4143_, v_x_4144_);
lean_dec_ref(v_x_4143_);
return v_res_4145_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4147_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4148_ = lean_unsigned_to_nat(20u);
v___x_4149_ = lean_unsigned_to_nat(1295u);
v___x_4150_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4151_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4152_ = l_mkPanicMessageWithDecl(v___x_4151_, v___x_4150_, v___x_4149_, v___x_4148_, v___x_4147_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4153_, lean_object* v_x_4154_){
_start:
{
switch(lean_obj_tag(v_x_4153_))
{
case 10:
{
lean_object* v_expr_4155_; 
v_expr_4155_ = lean_ctor_get(v_x_4153_, 1);
v_x_4153_ = v_expr_4155_;
goto _start;
}
case 5:
{
lean_object* v_fn_4157_; lean_object* v_arg_4158_; lean_object* v_zero_4159_; uint8_t v_isZero_4160_; 
v_fn_4157_ = lean_ctor_get(v_x_4153_, 0);
v_arg_4158_ = lean_ctor_get(v_x_4153_, 1);
v_zero_4159_ = lean_unsigned_to_nat(0u);
v_isZero_4160_ = lean_nat_dec_eq(v_x_4154_, v_zero_4159_);
if (v_isZero_4160_ == 1)
{
lean_dec(v_x_4154_);
lean_inc_ref(v_arg_4158_);
return v_arg_4158_;
}
else
{
lean_object* v_one_4161_; lean_object* v_n_4162_; 
v_one_4161_ = lean_unsigned_to_nat(1u);
v_n_4162_ = lean_nat_sub(v_x_4154_, v_one_4161_);
lean_dec(v_x_4154_);
v_x_4153_ = v_fn_4157_;
v_x_4154_ = v_n_4162_;
goto _start;
}
}
default: 
{
lean_object* v___x_4164_; lean_object* v___x_4165_; 
lean_dec(v_x_4154_);
v___x_4164_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4165_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4164_);
return v___x_4165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4166_, lean_object* v_x_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4166_, v_x_4167_);
lean_dec_ref(v_x_4166_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4169_, lean_object* v_i_4170_, lean_object* v_n_4171_){
_start:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4172_ = lean_nat_sub(v_n_4171_, v_i_4170_);
v___x_4173_ = lean_unsigned_to_nat(1u);
v___x_4174_ = lean_nat_sub(v___x_4172_, v___x_4173_);
lean_dec(v___x_4172_);
v___x_4175_ = l_Lean_Expr_getRevArg_x21(v_e_4169_, v___x_4174_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4176_, lean_object* v_i_4177_, lean_object* v_n_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_Lean_Expr_getArg_x21(v_e_4176_, v_i_4177_, v_n_4178_);
lean_dec(v_n_4178_);
lean_dec(v_i_4177_);
lean_dec_ref(v_e_4176_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4180_, lean_object* v_i_4181_, lean_object* v_n_4182_){
_start:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4183_ = lean_nat_sub(v_n_4182_, v_i_4181_);
v___x_4184_ = lean_unsigned_to_nat(1u);
v___x_4185_ = lean_nat_sub(v___x_4183_, v___x_4184_);
lean_dec(v___x_4183_);
v___x_4186_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4180_, v___x_4185_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4187_, lean_object* v_i_4188_, lean_object* v_n_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_Lean_Expr_getArg_x21_x27(v_e_4187_, v_i_4188_, v_n_4189_);
lean_dec(v_n_4189_);
lean_dec(v_i_4188_);
lean_dec_ref(v_e_4187_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4191_, lean_object* v_i_4192_, lean_object* v_v_u2080_4193_, lean_object* v_n_4194_){
_start:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4195_ = lean_nat_sub(v_n_4194_, v_i_4192_);
v___x_4196_ = lean_unsigned_to_nat(1u);
v___x_4197_ = lean_nat_sub(v___x_4195_, v___x_4196_);
lean_dec(v___x_4195_);
v___x_4198_ = l_Lean_Expr_getRevArgD(v_e_4191_, v___x_4197_, v_v_u2080_4193_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4199_, lean_object* v_i_4200_, lean_object* v_v_u2080_4201_, lean_object* v_n_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l_Lean_Expr_getArgD(v_e_4199_, v_i_4200_, v_v_u2080_4201_, v_n_4202_);
lean_dec(v_n_4202_);
lean_dec_ref(v_v_u2080_4201_);
lean_dec(v_i_4200_);
lean_dec_ref(v_e_4199_);
return v_res_4203_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4204_){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; uint8_t v___x_4207_; 
v___x_4205_ = lean_unsigned_to_nat(0u);
v___x_4206_ = l_Lean_Expr_looseBVarRange(v_e_4204_);
v___x_4207_ = lean_nat_dec_lt(v___x_4205_, v___x_4206_);
lean_dec(v___x_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4208_){
_start:
{
uint8_t v_res_4209_; lean_object* v_r_4210_; 
v_res_4209_ = l_Lean_Expr_hasLooseBVars(v_e_4208_);
lean_dec_ref(v_e_4208_);
v_r_4210_ = lean_box(v_res_4209_);
return v_r_4210_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4211_){
_start:
{
if (lean_obj_tag(v_e_4211_) == 7)
{
lean_object* v_body_4212_; uint8_t v___x_4213_; uint8_t v___x_4214_; 
v_body_4212_ = lean_ctor_get(v_e_4211_, 2);
v___x_4213_ = l_Lean_Expr_hasLooseBVars(v_body_4212_);
v___x_4214_ = lean_bool_not(v___x_4213_);
return v___x_4214_;
}
else
{
uint8_t v___x_4215_; 
v___x_4215_ = 0;
return v___x_4215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4216_){
_start:
{
uint8_t v_res_4217_; lean_object* v_r_4218_; 
v_res_4217_ = l_Lean_Expr_isArrow(v_e_4216_);
lean_dec_ref(v_e_4216_);
v_r_4218_ = lean_box(v_res_4217_);
return v_r_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4221_, lean_object* v_bvarIdx_4222_){
_start:
{
uint8_t v_res_4223_; lean_object* v_r_4224_; 
v_res_4223_ = lean_expr_has_loose_bvar(v_e_4221_, v_bvarIdx_4222_);
lean_dec(v_bvarIdx_4222_);
lean_dec_ref(v_e_4221_);
v_r_4224_ = lean_box(v_res_4223_);
return v_r_4224_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4225_, lean_object* v_bvarIdx_4226_, uint8_t v_considerRange_4227_){
_start:
{
if (lean_obj_tag(v_e_4225_) == 7)
{
lean_object* v_binderType_4228_; lean_object* v_body_4229_; uint8_t v_binderInfo_4230_; uint8_t v___y_4232_; uint8_t v___x_4236_; 
v_binderType_4228_ = lean_ctor_get(v_e_4225_, 1);
v_body_4229_ = lean_ctor_get(v_e_4225_, 2);
v_binderInfo_4230_ = lean_ctor_get_uint8(v_e_4225_, sizeof(void*)*3 + 8);
v___x_4236_ = lean_expr_has_loose_bvar(v_binderType_4228_, v_bvarIdx_4226_);
if (v___x_4236_ == 0)
{
v___y_4232_ = v___x_4236_;
goto v___jp_4231_;
}
else
{
uint8_t v___x_4237_; 
v___x_4237_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4230_);
if (v___x_4237_ == 0)
{
lean_object* v___x_4238_; uint8_t v___x_4239_; 
v___x_4238_ = lean_unsigned_to_nat(0u);
v___x_4239_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4229_, v___x_4238_, v_considerRange_4227_);
v___y_4232_ = v___x_4239_;
goto v___jp_4231_;
}
else
{
v___y_4232_ = v___x_4237_;
goto v___jp_4231_;
}
}
v___jp_4231_:
{
if (v___y_4232_ == 0)
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4233_ = lean_unsigned_to_nat(1u);
v___x_4234_ = lean_nat_add(v_bvarIdx_4226_, v___x_4233_);
lean_dec(v_bvarIdx_4226_);
v_e_4225_ = v_body_4229_;
v_bvarIdx_4226_ = v___x_4234_;
goto _start;
}
else
{
lean_dec(v_bvarIdx_4226_);
return v___y_4232_;
}
}
}
else
{
if (v_considerRange_4227_ == 0)
{
lean_dec(v_bvarIdx_4226_);
return v_considerRange_4227_;
}
else
{
uint8_t v___x_4240_; 
v___x_4240_ = lean_expr_has_loose_bvar(v_e_4225_, v_bvarIdx_4226_);
lean_dec(v_bvarIdx_4226_);
return v___x_4240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4241_, lean_object* v_bvarIdx_4242_, lean_object* v_considerRange_4243_){
_start:
{
uint8_t v_considerRange_boxed_4244_; uint8_t v_res_4245_; lean_object* v_r_4246_; 
v_considerRange_boxed_4244_ = lean_unbox(v_considerRange_4243_);
v_res_4245_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4241_, v_bvarIdx_4242_, v_considerRange_boxed_4244_);
lean_dec_ref(v_e_4241_);
v_r_4246_ = lean_box(v_res_4245_);
return v_r_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4250_, lean_object* v_s_4251_, lean_object* v_d_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = lean_expr_lower_loose_bvars(v_e_4250_, v_s_4251_, v_d_4252_);
lean_dec(v_d_4252_);
lean_dec(v_s_4251_);
lean_dec_ref(v_e_4250_);
return v_res_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4257_, lean_object* v_s_4258_, lean_object* v_d_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = lean_expr_lift_loose_bvars(v_e_4257_, v_s_4258_, v_d_4259_);
lean_dec(v_d_4259_);
lean_dec(v_s_4258_);
lean_dec_ref(v_e_4257_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4261_, lean_object* v_numParams_4262_, uint8_t v_considerRange_4263_){
_start:
{
if (lean_obj_tag(v_e_4261_) == 7)
{
lean_object* v_binderName_4264_; lean_object* v_binderType_4265_; lean_object* v_body_4266_; uint8_t v_binderInfo_4267_; lean_object* v_zero_4268_; uint8_t v_isZero_4269_; 
v_binderName_4264_ = lean_ctor_get(v_e_4261_, 0);
v_binderType_4265_ = lean_ctor_get(v_e_4261_, 1);
v_body_4266_ = lean_ctor_get(v_e_4261_, 2);
v_binderInfo_4267_ = lean_ctor_get_uint8(v_e_4261_, sizeof(void*)*3 + 8);
v_zero_4268_ = lean_unsigned_to_nat(0u);
v_isZero_4269_ = lean_nat_dec_eq(v_numParams_4262_, v_zero_4268_);
if (v_isZero_4269_ == 0)
{
lean_object* v_one_4270_; lean_object* v_n_4271_; lean_object* v_b_4272_; uint8_t v___y_4274_; uint8_t v___x_4278_; 
lean_inc_ref(v_body_4266_);
lean_inc_ref(v_binderType_4265_);
lean_inc(v_binderName_4264_);
lean_dec_ref_known(v_e_4261_, 3);
v_one_4270_ = lean_unsigned_to_nat(1u);
v_n_4271_ = lean_nat_sub(v_numParams_4262_, v_one_4270_);
v_b_4272_ = l_Lean_Expr_inferImplicit(v_body_4266_, v_n_4271_, v_considerRange_4263_);
lean_dec(v_n_4271_);
v___x_4278_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4267_);
if (v___x_4278_ == 0)
{
v___y_4274_ = v___x_4278_;
goto v___jp_4273_;
}
else
{
uint8_t v___x_4279_; 
v___x_4279_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4272_, v_zero_4268_, v_considerRange_4263_);
v___y_4274_ = v___x_4279_;
goto v___jp_4273_;
}
v___jp_4273_:
{
if (v___y_4274_ == 0)
{
lean_object* v___x_4275_; 
v___x_4275_ = l_Lean_Expr_forallE___override(v_binderName_4264_, v_binderType_4265_, v_b_4272_, v_binderInfo_4267_);
return v___x_4275_;
}
else
{
uint8_t v___x_4276_; lean_object* v___x_4277_; 
v___x_4276_ = 1;
v___x_4277_ = l_Lean_Expr_forallE___override(v_binderName_4264_, v_binderType_4265_, v_b_4272_, v___x_4276_);
return v___x_4277_;
}
}
}
else
{
return v_e_4261_;
}
}
else
{
return v_e_4261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4280_, lean_object* v_numParams_4281_, lean_object* v_considerRange_4282_){
_start:
{
uint8_t v_considerRange_boxed_4283_; lean_object* v_res_4284_; 
v_considerRange_boxed_4283_ = lean_unbox(v_considerRange_4282_);
v_res_4284_ = l_Lean_Expr_inferImplicit(v_e_4280_, v_numParams_4281_, v_considerRange_boxed_4283_);
lean_dec(v_numParams_4281_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4285_, lean_object* v_binderInfos_x3f_4286_){
_start:
{
if (lean_obj_tag(v_e_4285_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4286_) == 1)
{
lean_object* v_binderName_4287_; lean_object* v_binderType_4288_; lean_object* v_body_4289_; uint8_t v_binderInfo_4290_; lean_object* v_head_4291_; lean_object* v_tail_4292_; lean_object* v_b_4293_; 
v_binderName_4287_ = lean_ctor_get(v_e_4285_, 0);
lean_inc(v_binderName_4287_);
v_binderType_4288_ = lean_ctor_get(v_e_4285_, 1);
lean_inc_ref(v_binderType_4288_);
v_body_4289_ = lean_ctor_get(v_e_4285_, 2);
lean_inc_ref(v_body_4289_);
v_binderInfo_4290_ = lean_ctor_get_uint8(v_e_4285_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4285_, 3);
v_head_4291_ = lean_ctor_get(v_binderInfos_x3f_4286_, 0);
v_tail_4292_ = lean_ctor_get(v_binderInfos_x3f_4286_, 1);
v_b_4293_ = l_Lean_Expr_updateForallBinderInfos(v_body_4289_, v_tail_4292_);
if (lean_obj_tag(v_head_4291_) == 0)
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Lean_Expr_forallE___override(v_binderName_4287_, v_binderType_4288_, v_b_4293_, v_binderInfo_4290_);
return v___x_4294_;
}
else
{
lean_object* v_val_4295_; uint8_t v___x_4296_; lean_object* v___x_4297_; 
v_val_4295_ = lean_ctor_get(v_head_4291_, 0);
v___x_4296_ = lean_unbox(v_val_4295_);
v___x_4297_ = l_Lean_Expr_forallE___override(v_binderName_4287_, v_binderType_4288_, v_b_4293_, v___x_4296_);
return v___x_4297_;
}
}
else
{
return v_e_4285_;
}
}
else
{
return v_e_4285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4298_, lean_object* v_binderInfos_x3f_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_Lean_Expr_updateForallBinderInfos(v_e_4298_, v_binderInfos_x3f_4299_);
lean_dec(v_binderInfos_x3f_4299_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4301_, lean_object* v_binderNames_x3f_4302_){
_start:
{
switch(lean_obj_tag(v_e_4301_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4302_) == 1)
{
lean_object* v_binderName_4303_; lean_object* v_binderType_4304_; lean_object* v_body_4305_; uint8_t v_binderInfo_4306_; lean_object* v_head_4307_; lean_object* v_tail_4308_; lean_object* v_b_4309_; 
v_binderName_4303_ = lean_ctor_get(v_e_4301_, 0);
lean_inc(v_binderName_4303_);
v_binderType_4304_ = lean_ctor_get(v_e_4301_, 1);
lean_inc_ref(v_binderType_4304_);
v_body_4305_ = lean_ctor_get(v_e_4301_, 2);
lean_inc_ref(v_body_4305_);
v_binderInfo_4306_ = lean_ctor_get_uint8(v_e_4301_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4301_, 3);
v_head_4307_ = lean_ctor_get(v_binderNames_x3f_4302_, 0);
lean_inc(v_head_4307_);
v_tail_4308_ = lean_ctor_get(v_binderNames_x3f_4302_, 1);
lean_inc(v_tail_4308_);
lean_dec_ref_known(v_binderNames_x3f_4302_, 2);
v_b_4309_ = l_Lean_Expr_updateBinderNames(v_body_4305_, v_tail_4308_);
if (lean_obj_tag(v_head_4307_) == 0)
{
lean_object* v___x_4310_; 
v___x_4310_ = l_Lean_Expr_forallE___override(v_binderName_4303_, v_binderType_4304_, v_b_4309_, v_binderInfo_4306_);
return v___x_4310_;
}
else
{
lean_object* v_val_4311_; lean_object* v___x_4312_; 
lean_dec(v_binderName_4303_);
v_val_4311_ = lean_ctor_get(v_head_4307_, 0);
lean_inc(v_val_4311_);
lean_dec_ref_known(v_head_4307_, 1);
v___x_4312_ = l_Lean_Expr_forallE___override(v_val_4311_, v_binderType_4304_, v_b_4309_, v_binderInfo_4306_);
return v___x_4312_;
}
}
else
{
lean_dec(v_binderNames_x3f_4302_);
return v_e_4301_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4302_) == 1)
{
lean_object* v_binderName_4313_; lean_object* v_binderType_4314_; lean_object* v_body_4315_; uint8_t v_binderInfo_4316_; lean_object* v_head_4317_; lean_object* v_tail_4318_; lean_object* v_b_4319_; 
v_binderName_4313_ = lean_ctor_get(v_e_4301_, 0);
lean_inc(v_binderName_4313_);
v_binderType_4314_ = lean_ctor_get(v_e_4301_, 1);
lean_inc_ref(v_binderType_4314_);
v_body_4315_ = lean_ctor_get(v_e_4301_, 2);
lean_inc_ref(v_body_4315_);
v_binderInfo_4316_ = lean_ctor_get_uint8(v_e_4301_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4301_, 3);
v_head_4317_ = lean_ctor_get(v_binderNames_x3f_4302_, 0);
lean_inc(v_head_4317_);
v_tail_4318_ = lean_ctor_get(v_binderNames_x3f_4302_, 1);
lean_inc(v_tail_4318_);
lean_dec_ref_known(v_binderNames_x3f_4302_, 2);
v_b_4319_ = l_Lean_Expr_updateBinderNames(v_body_4315_, v_tail_4318_);
if (lean_obj_tag(v_head_4317_) == 0)
{
lean_object* v___x_4320_; 
v___x_4320_ = l_Lean_Expr_lam___override(v_binderName_4313_, v_binderType_4314_, v_b_4319_, v_binderInfo_4316_);
return v___x_4320_;
}
else
{
lean_object* v_val_4321_; lean_object* v___x_4322_; 
lean_dec(v_binderName_4313_);
v_val_4321_ = lean_ctor_get(v_head_4317_, 0);
lean_inc(v_val_4321_);
lean_dec_ref_known(v_head_4317_, 1);
v___x_4322_ = l_Lean_Expr_lam___override(v_val_4321_, v_binderType_4314_, v_b_4319_, v_binderInfo_4316_);
return v___x_4322_;
}
}
else
{
lean_dec(v_binderNames_x3f_4302_);
return v_e_4301_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4302_);
return v_e_4301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4325_, lean_object* v_subst_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = lean_expr_instantiate(v_e_4325_, v_subst_4326_);
lean_dec_ref(v_subst_4326_);
lean_dec_ref(v_e_4325_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4330_, lean_object* v_subst_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = lean_expr_instantiate1(v_e_4330_, v_subst_4331_);
lean_dec_ref(v_subst_4331_);
lean_dec_ref(v_e_4330_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4335_, lean_object* v_subst_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = lean_expr_instantiate_rev(v_e_4335_, v_subst_4336_);
lean_dec_ref(v_subst_4336_);
lean_dec_ref(v_e_4335_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4342_, lean_object* v_beginIdx_4343_, lean_object* v_endIdx_4344_, lean_object* v_subst_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = lean_expr_instantiate_range(v_e_4342_, v_beginIdx_4343_, v_endIdx_4344_, v_subst_4345_);
lean_dec_ref(v_subst_4345_);
lean_dec(v_endIdx_4344_);
lean_dec(v_beginIdx_4343_);
lean_dec_ref(v_e_4342_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4351_, lean_object* v_beginIdx_4352_, lean_object* v_endIdx_4353_, lean_object* v_subst_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = lean_expr_instantiate_rev_range(v_e_4351_, v_beginIdx_4352_, v_endIdx_4353_, v_subst_4354_);
lean_dec_ref(v_subst_4354_);
lean_dec(v_endIdx_4353_);
lean_dec(v_beginIdx_4352_);
lean_dec_ref(v_e_4351_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4358_, lean_object* v_xs_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = lean_expr_abstract(v_e_4358_, v_xs_4359_);
lean_dec_ref(v_xs_4359_);
lean_dec_ref(v_e_4358_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4364_, lean_object* v_n_4365_, lean_object* v_xs_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = lean_expr_abstract_range(v_e_4364_, v_n_4365_, v_xs_4366_);
lean_dec_ref(v_xs_4366_);
lean_dec(v_n_4365_);
lean_dec_ref(v_e_4364_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4368_, lean_object* v_fvar_4369_, lean_object* v_v_4370_){
_start:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4371_ = lean_unsigned_to_nat(1u);
v___x_4372_ = lean_mk_empty_array_with_capacity(v___x_4371_);
v___x_4373_ = lean_array_push(v___x_4372_, v_fvar_4369_);
v___x_4374_ = lean_expr_abstract(v_e_4368_, v___x_4373_);
lean_dec_ref(v___x_4373_);
v___x_4375_ = lean_expr_instantiate1(v___x_4374_, v_v_4370_);
lean_dec_ref(v___x_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4376_, lean_object* v_fvar_4377_, lean_object* v_v_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l_Lean_Expr_replaceFVar(v_e_4376_, v_fvar_4377_, v_v_4378_);
lean_dec_ref(v_v_4378_);
lean_dec_ref(v_e_4376_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4380_, lean_object* v_fvarId_4381_, lean_object* v_v_4382_){
_start:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4383_ = l_Lean_Expr_fvar___override(v_fvarId_4381_);
v___x_4384_ = l_Lean_Expr_replaceFVar(v_e_4380_, v___x_4383_, v_v_4382_);
return v___x_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4385_, lean_object* v_fvarId_4386_, lean_object* v_v_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l_Lean_Expr_replaceFVarId(v_e_4385_, v_fvarId_4386_, v_v_4387_);
lean_dec_ref(v_v_4387_);
lean_dec_ref(v_e_4385_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4389_, lean_object* v_fvars_4390_, lean_object* v_vs_4391_){
_start:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4392_ = lean_expr_abstract(v_e_4389_, v_fvars_4390_);
v___x_4393_ = lean_expr_instantiate_rev(v___x_4392_, v_vs_4391_);
lean_dec_ref(v___x_4392_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4394_, lean_object* v_fvars_4395_, lean_object* v_vs_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l_Lean_Expr_replaceFVars(v_e_4394_, v_fvars_4395_, v_vs_4396_);
lean_dec_ref(v_vs_4396_);
lean_dec_ref(v_fvars_4395_);
lean_dec_ref(v_e_4394_);
return v_res_4397_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4400_){
_start:
{
switch(lean_obj_tag(v_x_4400_))
{
case 4:
{
uint8_t v___x_4401_; 
v___x_4401_ = 1;
return v___x_4401_;
}
case 3:
{
uint8_t v___x_4402_; 
v___x_4402_ = 1;
return v___x_4402_;
}
case 0:
{
uint8_t v___x_4403_; 
v___x_4403_ = 1;
return v___x_4403_;
}
case 9:
{
uint8_t v___x_4404_; 
v___x_4404_ = 1;
return v___x_4404_;
}
case 2:
{
uint8_t v___x_4405_; 
v___x_4405_ = 1;
return v___x_4405_;
}
case 1:
{
uint8_t v___x_4406_; 
v___x_4406_ = 1;
return v___x_4406_;
}
default: 
{
uint8_t v___x_4407_; 
v___x_4407_ = 0;
return v___x_4407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4408_){
_start:
{
uint8_t v_res_4409_; lean_object* v_r_4410_; 
v_res_4409_ = l_Lean_Expr_isAtomic(v_x_4408_);
lean_dec_ref(v_x_4408_);
v_r_4410_ = lean_box(v_res_4409_);
return v_r_4410_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
v___x_4416_ = lean_box(0);
v___x_4417_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4418_ = l_Lean_Expr_const___override(v___x_4417_, v___x_4416_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4419_, lean_object* v_proof_4420_){
_start:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4421_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4422_ = l_Lean_mkAppB(v___x_4421_, v_pred_4419_, v_proof_4420_);
return v___x_4422_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4427_ = lean_box(0);
v___x_4428_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4429_ = l_Lean_Expr_const___override(v___x_4428_, v___x_4427_);
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4430_, lean_object* v_proof_4431_){
_start:
{
lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4432_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4433_ = l_Lean_mkAppB(v___x_4432_, v_pred_4430_, v_proof_4431_);
return v___x_4433_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4434_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4436_){
_start:
{
lean_inc_ref(v_val_4436_);
return v_val_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4437_);
lean_dec_ref(v_val_4437_);
return v_res_4438_;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4441_, lean_object* v_x_4442_){
_start:
{
uint8_t v___x_4443_; 
v___x_4443_ = lean_expr_equal(v_x_4441_, v_x_4442_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4444_, lean_object* v_x_4445_){
_start:
{
uint8_t v_res_4446_; lean_object* v_r_4447_; 
v_res_4446_ = l_Lean_ExprStructEq_beq(v_x_4444_, v_x_4445_);
lean_dec_ref(v_x_4445_);
lean_dec_ref(v_x_4444_);
v_r_4447_ = lean_box(v_res_4446_);
return v_r_4447_;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4448_){
_start:
{
uint64_t v___x_4449_; 
v___x_4449_ = l_Lean_Expr_hash(v_x_4448_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4450_){
_start:
{
uint64_t v_res_4451_; lean_object* v_r_4452_; 
v_res_4451_ = l_Lean_ExprStructEq_hash(v_x_4450_);
lean_dec_ref(v_x_4450_);
v_r_4452_ = lean_box_uint64(v_res_4451_);
return v_r_4452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4459_, lean_object* v_start_4460_, lean_object* v_b_4461_, lean_object* v_i_4462_){
_start:
{
uint8_t v___x_4463_; 
v___x_4463_ = lean_nat_dec_le(v_i_4462_, v_start_4460_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4464_; lean_object* v_i_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4464_ = lean_unsigned_to_nat(1u);
v_i_4465_ = lean_nat_sub(v_i_4462_, v___x_4464_);
lean_dec(v_i_4462_);
v___x_4466_ = l_Lean_instInhabitedExpr;
v___x_4467_ = lean_array_get_borrowed(v___x_4466_, v_revArgs_4459_, v_i_4465_);
lean_inc(v___x_4467_);
v___x_4468_ = l_Lean_Expr_app___override(v_b_4461_, v___x_4467_);
v_b_4461_ = v___x_4468_;
v_i_4462_ = v_i_4465_;
goto _start;
}
else
{
lean_dec(v_i_4462_);
return v_b_4461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4470_, lean_object* v_start_4471_, lean_object* v_b_4472_, lean_object* v_i_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4470_, v_start_4471_, v_b_4472_, v_i_4473_);
lean_dec(v_start_4471_);
lean_dec_ref(v_revArgs_4470_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4475_, lean_object* v_beginIdx_4476_, lean_object* v_endIdx_4477_, lean_object* v_revArgs_4478_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4478_, v_beginIdx_4476_, v_f_4475_, v_endIdx_4477_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4480_, lean_object* v_beginIdx_4481_, lean_object* v_endIdx_4482_, lean_object* v_revArgs_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l_Lean_Expr_mkAppRevRange(v_f_4480_, v_beginIdx_4481_, v_endIdx_4482_, v_revArgs_4483_);
lean_dec_ref(v_revArgs_4483_);
lean_dec(v_beginIdx_4481_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4485_, uint8_t v_useZeta_4486_, uint8_t v_preserveMData_4487_, lean_object* v_sz_4488_, lean_object* v_e_4489_, lean_object* v_i_4490_){
_start:
{
switch(lean_obj_tag(v_e_4489_))
{
case 6:
{
lean_object* v_body_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; uint8_t v___x_4499_; 
v_body_4496_ = lean_ctor_get(v_e_4489_, 2);
lean_inc_ref(v_body_4496_);
lean_dec_ref_known(v_e_4489_, 3);
v___x_4497_ = lean_unsigned_to_nat(1u);
v___x_4498_ = lean_nat_add(v_i_4490_, v___x_4497_);
lean_dec(v_i_4490_);
v___x_4499_ = lean_nat_dec_lt(v___x_4498_, v_sz_4488_);
if (v___x_4499_ == 0)
{
lean_object* v___x_4500_; 
lean_dec(v___x_4498_);
v___x_4500_ = lean_expr_instantiate(v_body_4496_, v_revArgs_4485_);
lean_dec_ref(v_body_4496_);
return v___x_4500_;
}
else
{
v_e_4489_ = v_body_4496_;
v_i_4490_ = v___x_4498_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4486_ == 0)
{
goto v___jp_4491_;
}
else
{
lean_object* v_value_4502_; lean_object* v_body_4503_; uint8_t v___x_4504_; 
v_value_4502_ = lean_ctor_get(v_e_4489_, 2);
v_body_4503_ = lean_ctor_get(v_e_4489_, 3);
v___x_4504_ = lean_nat_dec_lt(v_i_4490_, v_sz_4488_);
if (v___x_4504_ == 0)
{
goto v___jp_4491_;
}
else
{
lean_object* v___x_4505_; 
lean_inc_ref(v_body_4503_);
lean_inc_ref(v_value_4502_);
lean_dec_ref_known(v_e_4489_, 4);
v___x_4505_ = lean_expr_instantiate1(v_body_4503_, v_value_4502_);
lean_dec_ref(v_value_4502_);
lean_dec_ref(v_body_4503_);
v_e_4489_ = v___x_4505_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4487_ == 0)
{
lean_object* v_expr_4507_; 
v_expr_4507_ = lean_ctor_get(v_e_4489_, 1);
lean_inc_ref(v_expr_4507_);
lean_dec_ref_known(v_e_4489_, 2);
v_e_4489_ = v_expr_4507_;
goto _start;
}
else
{
goto v___jp_4491_;
}
}
default: 
{
goto v___jp_4491_;
}
}
v___jp_4491_:
{
lean_object* v_n_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v_n_4492_ = lean_nat_sub(v_sz_4488_, v_i_4490_);
lean_dec(v_i_4490_);
v___x_4493_ = lean_expr_instantiate_range(v_e_4489_, v_n_4492_, v_sz_4488_, v_revArgs_4485_);
lean_dec_ref(v_e_4489_);
v___x_4494_ = lean_unsigned_to_nat(0u);
v___x_4495_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4485_, v___x_4494_, v___x_4493_, v_n_4492_);
return v___x_4495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4509_, lean_object* v_useZeta_4510_, lean_object* v_preserveMData_4511_, lean_object* v_sz_4512_, lean_object* v_e_4513_, lean_object* v_i_4514_){
_start:
{
uint8_t v_useZeta_boxed_4515_; uint8_t v_preserveMData_boxed_4516_; lean_object* v_res_4517_; 
v_useZeta_boxed_4515_ = lean_unbox(v_useZeta_4510_);
v_preserveMData_boxed_4516_ = lean_unbox(v_preserveMData_4511_);
v_res_4517_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4509_, v_useZeta_boxed_4515_, v_preserveMData_boxed_4516_, v_sz_4512_, v_e_4513_, v_i_4514_);
lean_dec(v_sz_4512_);
lean_dec_ref(v_revArgs_4509_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4518_, lean_object* v_revArgs_4519_, uint8_t v_useZeta_4520_, uint8_t v_preserveMData_4521_){
_start:
{
lean_object* v_sz_4522_; lean_object* v___x_4523_; uint8_t v___x_4524_; 
v_sz_4522_ = lean_array_get_size(v_revArgs_4519_);
v___x_4523_ = lean_unsigned_to_nat(0u);
v___x_4524_ = lean_nat_dec_eq(v_sz_4522_, v___x_4523_);
if (v___x_4524_ == 0)
{
lean_object* v___x_4525_; 
v___x_4525_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4519_, v_useZeta_4520_, v_preserveMData_4521_, v_sz_4522_, v_f_4518_, v___x_4523_);
return v___x_4525_;
}
else
{
return v_f_4518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4526_, lean_object* v_revArgs_4527_, lean_object* v_useZeta_4528_, lean_object* v_preserveMData_4529_){
_start:
{
uint8_t v_useZeta_boxed_4530_; uint8_t v_preserveMData_boxed_4531_; lean_object* v_res_4532_; 
v_useZeta_boxed_4530_ = lean_unbox(v_useZeta_4528_);
v_preserveMData_boxed_4531_ = lean_unbox(v_preserveMData_4529_);
v_res_4532_ = l_Lean_Expr_betaRev(v_f_4526_, v_revArgs_4527_, v_useZeta_boxed_4530_, v_preserveMData_boxed_4531_);
lean_dec_ref(v_revArgs_4527_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4533_, lean_object* v_args_4534_){
_start:
{
lean_object* v___x_4535_; uint8_t v___x_4536_; lean_object* v___x_4537_; 
v___x_4535_ = l_Array_reverse___redArg(v_args_4534_);
v___x_4536_ = 0;
v___x_4537_ = l_Lean_Expr_betaRev(v_f_4533_, v___x_4535_, v___x_4536_, v___x_4536_);
lean_dec_ref(v___x_4535_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4538_){
_start:
{
switch(lean_obj_tag(v_x_4538_))
{
case 6:
{
lean_object* v_body_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v_body_4539_ = lean_ctor_get(v_x_4538_, 2);
v___x_4540_ = l_Lean_Expr_getNumHeadLambdas(v_body_4539_);
v___x_4541_ = lean_unsigned_to_nat(1u);
v___x_4542_ = lean_nat_add(v___x_4540_, v___x_4541_);
lean_dec(v___x_4540_);
return v___x_4542_;
}
case 10:
{
lean_object* v_expr_4543_; 
v_expr_4543_ = lean_ctor_get(v_x_4538_, 1);
v_x_4538_ = v_expr_4543_;
goto _start;
}
default: 
{
lean_object* v___x_4545_; 
v___x_4545_ = lean_unsigned_to_nat(0u);
return v___x_4545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l_Lean_Expr_getNumHeadLambdas(v_x_4546_);
lean_dec_ref(v_x_4546_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object* v_x_4548_){
_start:
{
switch(lean_obj_tag(v_x_4548_))
{
case 6:
{
lean_object* v_body_4549_; 
v_body_4549_ = lean_ctor_get(v_x_4548_, 2);
v_x_4548_ = v_body_4549_;
goto _start;
}
case 10:
{
lean_object* v_expr_4551_; 
v_expr_4551_ = lean_ctor_get(v_x_4548_, 1);
v_x_4548_ = v_expr_4551_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_4548_);
return v_x_4548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object* v_x_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l_Lean_Expr_getLambdaBody(v_x_4553_);
lean_dec_ref(v_x_4553_);
return v_res_4554_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4555_, lean_object* v_x_4556_){
_start:
{
switch(lean_obj_tag(v_x_4556_))
{
case 6:
{
uint8_t v___x_4557_; 
v___x_4557_ = 1;
return v___x_4557_;
}
case 8:
{
if (v_useZeta_4555_ == 0)
{
return v_useZeta_4555_;
}
else
{
lean_object* v_body_4558_; 
v_body_4558_ = lean_ctor_get(v_x_4556_, 3);
v_x_4556_ = v_body_4558_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4560_; 
v_expr_4560_ = lean_ctor_get(v_x_4556_, 1);
v_x_4556_ = v_expr_4560_;
goto _start;
}
default: 
{
uint8_t v___x_4562_; 
v___x_4562_ = 0;
return v___x_4562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4563_, lean_object* v_x_4564_){
_start:
{
uint8_t v_useZeta_boxed_4565_; uint8_t v_res_4566_; lean_object* v_r_4567_; 
v_useZeta_boxed_4565_ = lean_unbox(v_useZeta_4563_);
v_res_4566_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4565_, v_x_4564_);
lean_dec_ref(v_x_4564_);
v_r_4567_ = lean_box(v_res_4566_);
return v_r_4567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4568_){
_start:
{
lean_object* v_f_4569_; uint8_t v___x_4570_; uint8_t v___x_4571_; 
v_f_4569_ = l_Lean_Expr_getAppFn(v_e_4568_);
v___x_4570_ = 0;
v___x_4571_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4570_, v_f_4569_);
if (v___x_4571_ == 0)
{
lean_dec_ref(v_f_4569_);
return v_e_4568_;
}
else
{
lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4572_ = l_Lean_Expr_getAppNumArgs(v_e_4568_);
v___x_4573_ = lean_mk_empty_array_with_capacity(v___x_4572_);
lean_dec(v___x_4572_);
v___x_4574_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4568_, v___x_4573_);
v___x_4575_ = l_Lean_Expr_betaRev(v_f_4569_, v___x_4574_, v___x_4570_, v___x_4570_);
lean_dec_ref(v___x_4574_);
return v___x_4575_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4576_, uint8_t v_useZeta_4577_){
_start:
{
uint8_t v___x_4578_; 
v___x_4578_ = l_Lean_Expr_isApp(v_e_4576_);
if (v___x_4578_ == 0)
{
return v___x_4578_;
}
else
{
lean_object* v___x_4579_; uint8_t v___x_4580_; 
v___x_4579_ = l_Lean_Expr_getAppFn(v_e_4576_);
v___x_4580_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4577_, v___x_4579_);
lean_dec_ref(v___x_4579_);
return v___x_4580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4581_, lean_object* v_useZeta_4582_){
_start:
{
uint8_t v_useZeta_boxed_4583_; uint8_t v_res_4584_; lean_object* v_r_4585_; 
v_useZeta_boxed_4583_ = lean_unbox(v_useZeta_4582_);
v_res_4584_ = l_Lean_Expr_isHeadBetaTarget(v_e_4581_, v_useZeta_boxed_4583_);
lean_dec_ref(v_e_4581_);
v_r_4585_ = lean_box(v_res_4584_);
return v_r_4585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4586_, lean_object* v_x_4587_, lean_object* v_x_4588_){
_start:
{
lean_object* v_f_4590_; 
if (lean_obj_tag(v_x_4586_) == 5)
{
lean_object* v_arg_4594_; 
v_arg_4594_ = lean_ctor_get(v_x_4586_, 1);
if (lean_obj_tag(v_arg_4594_) == 0)
{
lean_object* v_fn_4595_; lean_object* v_deBruijnIndex_4596_; lean_object* v_zero_4597_; uint8_t v_isZero_4598_; 
v_fn_4595_ = lean_ctor_get(v_x_4586_, 0);
v_deBruijnIndex_4596_ = lean_ctor_get(v_arg_4594_, 0);
v_zero_4597_ = lean_unsigned_to_nat(0u);
v_isZero_4598_ = lean_nat_dec_eq(v_x_4587_, v_zero_4597_);
if (v_isZero_4598_ == 1)
{
lean_dec(v_x_4588_);
lean_dec(v_x_4587_);
v_f_4590_ = v_x_4586_;
goto v___jp_4589_;
}
else
{
uint8_t v___x_4599_; 
lean_inc(v_deBruijnIndex_4596_);
lean_inc_ref(v_fn_4595_);
lean_dec_ref_known(v_x_4586_, 2);
v___x_4599_ = lean_nat_dec_eq(v_deBruijnIndex_4596_, v_x_4588_);
lean_dec(v_deBruijnIndex_4596_);
if (v___x_4599_ == 0)
{
lean_object* v___x_4600_; 
lean_dec_ref(v_fn_4595_);
lean_dec(v_x_4588_);
lean_dec(v_x_4587_);
v___x_4600_ = lean_box(0);
return v___x_4600_;
}
else
{
lean_object* v_one_4601_; lean_object* v_n_4602_; lean_object* v___x_4603_; 
v_one_4601_ = lean_unsigned_to_nat(1u);
v_n_4602_ = lean_nat_sub(v_x_4587_, v_one_4601_);
lean_dec(v_x_4587_);
v___x_4603_ = lean_nat_add(v_x_4588_, v_one_4601_);
lean_dec(v_x_4588_);
v_x_4586_ = v_fn_4595_;
v_x_4587_ = v_n_4602_;
v_x_4588_ = v___x_4603_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4605_; uint8_t v_isZero_4606_; 
lean_dec(v_x_4588_);
v_zero_4605_ = lean_unsigned_to_nat(0u);
v_isZero_4606_ = lean_nat_dec_eq(v_x_4587_, v_zero_4605_);
lean_dec(v_x_4587_);
if (v_isZero_4606_ == 1)
{
v_f_4590_ = v_x_4586_;
goto v___jp_4589_;
}
else
{
lean_object* v___x_4607_; 
lean_dec_ref_known(v_x_4586_, 2);
v___x_4607_ = lean_box(0);
return v___x_4607_;
}
}
}
else
{
lean_object* v_zero_4608_; uint8_t v_isZero_4609_; 
lean_dec(v_x_4588_);
v_zero_4608_ = lean_unsigned_to_nat(0u);
v_isZero_4609_ = lean_nat_dec_eq(v_x_4587_, v_zero_4608_);
lean_dec(v_x_4587_);
if (v_isZero_4609_ == 1)
{
v_f_4590_ = v_x_4586_;
goto v___jp_4589_;
}
else
{
lean_object* v___x_4610_; 
lean_dec_ref(v_x_4586_);
v___x_4610_ = lean_box(0);
return v___x_4610_;
}
}
v___jp_4589_:
{
uint8_t v___x_4591_; 
v___x_4591_ = l_Lean_Expr_hasLooseBVars(v_f_4590_);
if (v___x_4591_ == 0)
{
lean_object* v___x_4592_; 
v___x_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4592_, 0, v_f_4590_);
return v___x_4592_;
}
else
{
lean_object* v___x_4593_; 
lean_dec_ref(v_f_4590_);
v___x_4593_ = lean_box(0);
return v___x_4593_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4611_, lean_object* v_x_4612_){
_start:
{
if (lean_obj_tag(v_x_4611_) == 6)
{
lean_object* v_body_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v_body_4613_ = lean_ctor_get(v_x_4611_, 2);
lean_inc_ref(v_body_4613_);
lean_dec_ref_known(v_x_4611_, 3);
v___x_4614_ = lean_unsigned_to_nat(1u);
v___x_4615_ = lean_nat_add(v_x_4612_, v___x_4614_);
lean_dec(v_x_4612_);
v_x_4611_ = v_body_4613_;
v_x_4612_ = v___x_4615_;
goto _start;
}
else
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4617_ = lean_unsigned_to_nat(0u);
v___x_4618_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4611_, v_x_4612_, v___x_4617_);
return v___x_4618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4619_){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4620_ = lean_unsigned_to_nat(0u);
v___x_4621_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4619_, v___x_4620_);
return v___x_4621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4622_){
_start:
{
if (lean_obj_tag(v_x_4622_) == 6)
{
lean_object* v_body_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
v_body_4623_ = lean_ctor_get(v_x_4622_, 2);
lean_inc_ref(v_body_4623_);
lean_dec_ref_known(v_x_4622_, 3);
v___x_4624_ = lean_unsigned_to_nat(1u);
v___x_4625_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4623_, v___x_4624_);
return v___x_4625_;
}
else
{
lean_object* v___x_4626_; 
lean_dec_ref(v_x_4622_);
v___x_4626_ = lean_box(0);
return v___x_4626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4630_){
_start:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; uint8_t v___x_4633_; 
v___x_4631_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4632_ = lean_unsigned_to_nat(2u);
v___x_4633_ = l_Lean_Expr_isAppOfArity(v_e_4630_, v___x_4631_, v___x_4632_);
if (v___x_4633_ == 0)
{
lean_object* v___x_4634_; 
v___x_4634_ = lean_box(0);
return v___x_4634_;
}
else
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = l_Lean_Expr_appArg_x21(v_e_4630_);
v___x_4636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4635_);
return v___x_4636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4637_){
_start:
{
lean_object* v_res_4638_; 
v_res_4638_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4637_);
lean_dec_ref(v_e_4637_);
return v_res_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4642_){
_start:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; 
v___x_4643_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4644_ = lean_unsigned_to_nat(2u);
v___x_4645_ = l_Lean_Expr_isAppOfArity(v_e_4642_, v___x_4643_, v___x_4644_);
if (v___x_4645_ == 0)
{
lean_object* v___x_4646_; 
v___x_4646_ = lean_box(0);
return v___x_4646_;
}
else
{
lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4647_ = l_Lean_Expr_appArg_x21(v_e_4642_);
v___x_4648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
return v___x_4648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4649_);
lean_dec_ref(v_e_4649_);
return v_res_4650_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOutParam(lean_object* v_e_4654_){
_start:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; uint8_t v___x_4657_; 
v___x_4655_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4656_ = lean_unsigned_to_nat(1u);
v___x_4657_ = l_Lean_Expr_isAppOfArity(v_e_4654_, v___x_4655_, v___x_4656_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4658_){
_start:
{
uint8_t v_res_4659_; lean_object* v_r_4660_; 
v_res_4659_ = l_Lean_Expr_isOutParam(v_e_4658_);
lean_dec_ref(v_e_4658_);
v_r_4660_ = lean_box(v_res_4659_);
return v_r_4660_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4664_){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; uint8_t v___x_4667_; 
v___x_4665_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4666_ = lean_unsigned_to_nat(1u);
v___x_4667_ = l_Lean_Expr_isAppOfArity(v_e_4664_, v___x_4665_, v___x_4666_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4668_){
_start:
{
uint8_t v_res_4669_; lean_object* v_r_4670_; 
v_res_4669_ = l_Lean_Expr_isSemiOutParam(v_e_4668_);
lean_dec_ref(v_e_4668_);
v_r_4670_ = lean_box(v_res_4669_);
return v_r_4670_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4671_){
_start:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; uint8_t v___x_4674_; 
v___x_4672_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4673_ = lean_unsigned_to_nat(2u);
v___x_4674_ = l_Lean_Expr_isAppOfArity(v_e_4671_, v___x_4672_, v___x_4673_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4675_){
_start:
{
uint8_t v_res_4676_; lean_object* v_r_4677_; 
v_res_4676_ = l_Lean_Expr_isOptParam(v_e_4675_);
lean_dec_ref(v_e_4675_);
v_r_4677_ = lean_box(v_res_4676_);
return v_r_4677_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4678_){
_start:
{
lean_object* v___x_4679_; lean_object* v___x_4680_; uint8_t v___x_4681_; 
v___x_4679_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4680_ = lean_unsigned_to_nat(2u);
v___x_4681_ = l_Lean_Expr_isAppOfArity(v_e_4678_, v___x_4679_, v___x_4680_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4682_){
_start:
{
uint8_t v_res_4683_; lean_object* v_r_4684_; 
v_res_4683_ = l_Lean_Expr_isAutoParam(v_e_4682_);
lean_dec_ref(v_e_4682_);
v_r_4684_ = lean_box(v_res_4683_);
return v_r_4684_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4685_){
_start:
{
lean_object* v___x_4686_; 
v___x_4686_ = l_Lean_Expr_getAppFn(v_e_4685_);
if (lean_obj_tag(v___x_4686_) == 4)
{
lean_object* v_declName_4687_; uint8_t v___y_4689_; lean_object* v___x_4694_; uint8_t v___x_4695_; 
v_declName_4687_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_declName_4687_);
lean_dec_ref_known(v___x_4686_, 2);
v___x_4694_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4695_ = lean_name_eq(v_declName_4687_, v___x_4694_);
if (v___x_4695_ == 0)
{
lean_object* v___x_4696_; uint8_t v___x_4697_; 
v___x_4696_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4697_ = lean_name_eq(v_declName_4687_, v___x_4696_);
v___y_4689_ = v___x_4697_;
goto v___jp_4688_;
}
else
{
v___y_4689_ = v___x_4695_;
goto v___jp_4688_;
}
v___jp_4688_:
{
if (v___y_4689_ == 0)
{
lean_object* v___x_4690_; uint8_t v___x_4691_; 
v___x_4690_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4691_ = lean_name_eq(v_declName_4687_, v___x_4690_);
if (v___x_4691_ == 0)
{
lean_object* v___x_4692_; uint8_t v___x_4693_; 
v___x_4692_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4693_ = lean_name_eq(v_declName_4687_, v___x_4692_);
lean_dec(v_declName_4687_);
return v___x_4693_;
}
else
{
lean_dec(v_declName_4687_);
return v___x_4691_;
}
}
else
{
lean_dec(v_declName_4687_);
return v___y_4689_;
}
}
}
else
{
uint8_t v___x_4698_; 
lean_dec_ref(v___x_4686_);
v___x_4698_ = 0;
return v___x_4698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4699_){
_start:
{
uint8_t v_res_4700_; lean_object* v_r_4701_; 
v_res_4700_ = l_Lean_Expr_isTypeAnnotation(v_e_4699_);
lean_dec_ref(v_e_4699_);
v_r_4701_ = lean_box(v_res_4700_);
return v_r_4701_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4702_){
_start:
{
uint8_t v___y_4704_; uint8_t v___y_4708_; uint8_t v___x_4714_; 
v___x_4714_ = l_Lean_Expr_isOptParam(v_e_4702_);
if (v___x_4714_ == 0)
{
uint8_t v___x_4715_; 
v___x_4715_ = l_Lean_Expr_isAutoParam(v_e_4702_);
v___y_4708_ = v___x_4715_;
goto v___jp_4707_;
}
else
{
v___y_4708_ = v___x_4714_;
goto v___jp_4707_;
}
v___jp_4703_:
{
if (v___y_4704_ == 0)
{
return v_e_4702_;
}
else
{
lean_object* v___x_4705_; 
v___x_4705_ = l_Lean_Expr_appArg_x21(v_e_4702_);
lean_dec_ref(v_e_4702_);
v_e_4702_ = v___x_4705_;
goto _start;
}
}
v___jp_4707_:
{
if (v___y_4708_ == 0)
{
uint8_t v___x_4709_; 
v___x_4709_ = l_Lean_Expr_isOutParam(v_e_4702_);
if (v___x_4709_ == 0)
{
uint8_t v___x_4710_; 
v___x_4710_ = l_Lean_Expr_isSemiOutParam(v_e_4702_);
v___y_4704_ = v___x_4710_;
goto v___jp_4703_;
}
else
{
v___y_4704_ = v___x_4709_;
goto v___jp_4703_;
}
}
else
{
lean_object* v___x_4711_; lean_object* v___x_4712_; 
v___x_4711_ = l_Lean_Expr_appFn_x21(v_e_4702_);
lean_dec_ref(v_e_4702_);
v___x_4712_ = l_Lean_Expr_appArg_x21(v___x_4711_);
lean_dec_ref(v___x_4711_);
v_e_4702_ = v___x_4712_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4716_){
_start:
{
lean_object* v___x_4717_; lean_object* v_e_x27_4718_; uint8_t v___x_4719_; 
v___x_4717_ = l_Lean_Expr_consumeMData(v_e_4716_);
v_e_x27_4718_ = lean_expr_consume_type_annotations(v___x_4717_);
v___x_4719_ = lean_expr_eqv(v_e_x27_4718_, v_e_4716_);
if (v___x_4719_ == 0)
{
lean_dec_ref(v_e_4716_);
v_e_4716_ = v_e_x27_4718_;
goto _start;
}
else
{
lean_dec_ref(v_e_x27_4718_);
return v_e_4716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4721_){
_start:
{
lean_object* v_fn_4722_; lean_object* v___x_4723_; 
v_fn_4722_ = lean_ctor_get(v_e_4721_, 0);
lean_inc_ref(v_fn_4722_);
lean_dec_ref(v_e_4721_);
v___x_4723_ = l_Lean_Expr_cleanupAnnotations(v_fn_4722_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* v_e_4724_, lean_object* v_h_4725_){
_start:
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4724_);
return v___x_4726_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4730_){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; uint8_t v___x_4733_; 
v___x_4731_ = l_Lean_Expr_cleanupAnnotations(v_e_4730_);
v___x_4732_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4733_ = l_Lean_Expr_isConstOf(v___x_4731_, v___x_4732_);
lean_dec_ref(v___x_4731_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4734_){
_start:
{
uint8_t v_res_4735_; lean_object* v_r_4736_; 
v_res_4735_ = l_Lean_Expr_isFalse(v_e_4734_);
v_r_4736_ = lean_box(v_res_4735_);
return v_r_4736_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4740_){
_start:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; uint8_t v___x_4743_; 
v___x_4741_ = l_Lean_Expr_cleanupAnnotations(v_e_4740_);
v___x_4742_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4743_ = l_Lean_Expr_isConstOf(v___x_4741_, v___x_4742_);
lean_dec_ref(v___x_4741_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4744_){
_start:
{
uint8_t v_res_4745_; lean_object* v_r_4746_; 
v_res_4745_ = l_Lean_Expr_isTrue(v_e_4744_);
v_r_4746_ = lean_box(v_res_4745_);
return v_r_4746_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object* v_e_4751_){
_start:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; uint8_t v___x_4754_; 
v___x_4752_ = l_Lean_Expr_cleanupAnnotations(v_e_4751_);
v___x_4753_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_4754_ = l_Lean_Expr_isConstOf(v___x_4752_, v___x_4753_);
lean_dec_ref(v___x_4752_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object* v_e_4755_){
_start:
{
uint8_t v_res_4756_; lean_object* v_r_4757_; 
v_res_4756_ = l_Lean_Expr_isBoolFalse(v_e_4755_);
v_r_4757_ = lean_box(v_res_4756_);
return v_r_4757_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object* v_e_4761_){
_start:
{
lean_object* v___x_4762_; lean_object* v___x_4763_; uint8_t v___x_4764_; 
v___x_4762_ = l_Lean_Expr_cleanupAnnotations(v_e_4761_);
v___x_4763_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_4764_ = l_Lean_Expr_isConstOf(v___x_4762_, v___x_4763_);
lean_dec_ref(v___x_4762_);
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object* v_e_4765_){
_start:
{
uint8_t v_res_4766_; lean_object* v_r_4767_; 
v_res_4766_ = l_Lean_Expr_isBoolTrue(v_e_4765_);
v_r_4767_ = lean_box(v_res_4766_);
return v_r_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* v_x_4768_){
_start:
{
switch(lean_obj_tag(v_x_4768_))
{
case 10:
{
lean_object* v_expr_4769_; 
v_expr_4769_ = lean_ctor_get(v_x_4768_, 1);
lean_inc_ref(v_expr_4769_);
lean_dec_ref_known(v_x_4768_, 2);
v_x_4768_ = v_expr_4769_;
goto _start;
}
case 7:
{
lean_object* v_body_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
v_body_4771_ = lean_ctor_get(v_x_4768_, 2);
lean_inc_ref(v_body_4771_);
lean_dec_ref_known(v_x_4768_, 3);
v___x_4772_ = l_Lean_Expr_getForallArity(v_body_4771_);
v___x_4773_ = lean_unsigned_to_nat(1u);
v___x_4774_ = lean_nat_add(v___x_4772_, v___x_4773_);
lean_dec(v___x_4772_);
return v___x_4774_;
}
default: 
{
uint8_t v___x_4775_; uint8_t v___x_4776_; 
v___x_4775_ = 0;
v___x_4776_ = l_Lean_Expr_isHeadBetaTarget(v_x_4768_, v___x_4775_);
if (v___x_4776_ == 0)
{
lean_object* v_e_x27_4777_; uint8_t v___x_4778_; uint8_t v___x_4779_; 
lean_inc_ref(v_x_4768_);
v_e_x27_4777_ = l_Lean_Expr_cleanupAnnotations(v_x_4768_);
v___x_4778_ = lean_expr_eqv(v_x_4768_, v_e_x27_4777_);
lean_dec_ref(v_x_4768_);
v___x_4779_ = lean_bool_not(v___x_4778_);
if (v___x_4779_ == 0)
{
lean_object* v___x_4780_; 
lean_dec_ref(v_e_x27_4777_);
v___x_4780_ = lean_unsigned_to_nat(0u);
return v___x_4780_;
}
else
{
v_x_4768_ = v_e_x27_4777_;
goto _start;
}
}
else
{
lean_object* v___x_4782_; 
v___x_4782_ = l_Lean_Expr_headBeta(v_x_4768_);
v_x_4768_ = v___x_4782_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4784_){
_start:
{
lean_object* v___x_4785_; uint8_t v___x_4786_; 
v___x_4785_ = l_Lean_Expr_cleanupAnnotations(v_e_4784_);
v___x_4786_ = l_Lean_Expr_isApp(v___x_4785_);
if (v___x_4786_ == 0)
{
lean_object* v___x_4787_; 
lean_dec_ref(v___x_4785_);
v___x_4787_ = lean_box(0);
return v___x_4787_;
}
else
{
lean_object* v___x_4788_; uint8_t v___x_4789_; 
v___x_4788_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4785_);
v___x_4789_ = l_Lean_Expr_isApp(v___x_4788_);
if (v___x_4789_ == 0)
{
lean_object* v___x_4790_; 
lean_dec_ref(v___x_4788_);
v___x_4790_ = lean_box(0);
return v___x_4790_;
}
else
{
lean_object* v_arg_4791_; lean_object* v___x_4792_; uint8_t v___x_4793_; 
v_arg_4791_ = lean_ctor_get(v___x_4788_, 1);
lean_inc_ref(v_arg_4791_);
v___x_4792_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4788_);
v___x_4793_ = l_Lean_Expr_isApp(v___x_4792_);
if (v___x_4793_ == 0)
{
lean_object* v___x_4794_; 
lean_dec_ref(v___x_4792_);
lean_dec_ref(v_arg_4791_);
v___x_4794_ = lean_box(0);
return v___x_4794_;
}
else
{
lean_object* v___x_4795_; lean_object* v___x_4796_; uint8_t v___x_4797_; 
v___x_4795_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4792_);
v___x_4796_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4797_ = l_Lean_Expr_isConstOf(v___x_4795_, v___x_4796_);
lean_dec_ref(v___x_4795_);
if (v___x_4797_ == 0)
{
lean_object* v___x_4798_; 
lean_dec_ref(v_arg_4791_);
v___x_4798_ = lean_box(0);
return v___x_4798_;
}
else
{
if (lean_obj_tag(v_arg_4791_) == 9)
{
lean_object* v_a_4799_; 
v_a_4799_ = lean_ctor_get(v_arg_4791_, 0);
lean_inc_ref(v_a_4799_);
lean_dec_ref_known(v_arg_4791_, 1);
if (lean_obj_tag(v_a_4799_) == 0)
{
lean_object* v_val_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4807_; 
v_val_4800_ = lean_ctor_get(v_a_4799_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v_a_4799_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4802_ = v_a_4799_;
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_val_4800_);
lean_dec(v_a_4799_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4805_; 
if (v_isShared_4803_ == 0)
{
lean_ctor_set_tag(v___x_4802_, 1);
v___x_4805_ = v___x_4802_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_val_4800_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
else
{
lean_object* v___x_4808_; 
lean_dec_ref(v_a_4799_);
v___x_4808_ = lean_box(0);
return v___x_4808_;
}
}
else
{
lean_object* v___x_4809_; 
lean_dec_ref(v_arg_4791_);
v___x_4809_ = lean_box(0);
return v___x_4809_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4815_){
_start:
{
lean_object* v___x_4828_; uint8_t v___x_4829_; 
lean_inc_ref(v_e_4815_);
v___x_4828_ = l_Lean_Expr_cleanupAnnotations(v_e_4815_);
v___x_4829_ = l_Lean_Expr_isApp(v___x_4828_);
if (v___x_4829_ == 0)
{
lean_dec_ref(v___x_4828_);
goto v___jp_4816_;
}
else
{
lean_object* v_arg_4830_; lean_object* v___x_4831_; uint8_t v___x_4832_; 
v_arg_4830_ = lean_ctor_get(v___x_4828_, 1);
lean_inc_ref(v_arg_4830_);
v___x_4831_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4828_);
v___x_4832_ = l_Lean_Expr_isApp(v___x_4831_);
if (v___x_4832_ == 0)
{
lean_dec_ref(v___x_4831_);
lean_dec_ref(v_arg_4830_);
goto v___jp_4816_;
}
else
{
lean_object* v___x_4833_; uint8_t v___x_4834_; 
v___x_4833_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4831_);
v___x_4834_ = l_Lean_Expr_isApp(v___x_4833_);
if (v___x_4834_ == 0)
{
lean_dec_ref(v___x_4833_);
lean_dec_ref(v_arg_4830_);
goto v___jp_4816_;
}
else
{
lean_object* v___x_4835_; lean_object* v___x_4836_; uint8_t v___x_4837_; 
v___x_4835_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4833_);
v___x_4836_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4837_ = l_Lean_Expr_isConstOf(v___x_4835_, v___x_4836_);
lean_dec_ref(v___x_4835_);
if (v___x_4837_ == 0)
{
lean_dec_ref(v_arg_4830_);
goto v___jp_4816_;
}
else
{
lean_object* v___x_4838_; 
lean_dec_ref(v_e_4815_);
v___x_4838_ = l_Lean_Expr_nat_x3f(v_arg_4830_);
if (lean_obj_tag(v___x_4838_) == 0)
{
lean_object* v___x_4839_; 
v___x_4839_ = lean_box(0);
return v___x_4839_;
}
else
{
lean_object* v_val_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4852_; 
v_val_4840_ = lean_ctor_get(v___x_4838_, 0);
v_isSharedCheck_4852_ = !lean_is_exclusive(v___x_4838_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4842_ = v___x_4838_;
v_isShared_4843_ = v_isSharedCheck_4852_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_val_4840_);
lean_dec(v___x_4838_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4852_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v___x_4844_; uint8_t v___x_4845_; 
v___x_4844_ = lean_unsigned_to_nat(0u);
v___x_4845_ = lean_nat_dec_eq(v_val_4840_, v___x_4844_);
if (v___x_4845_ == 0)
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4849_; 
v___x_4846_ = lean_nat_to_int(v_val_4840_);
v___x_4847_ = lean_int_neg(v___x_4846_);
lean_dec(v___x_4846_);
if (v_isShared_4843_ == 0)
{
lean_ctor_set(v___x_4842_, 0, v___x_4847_);
v___x_4849_ = v___x_4842_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4847_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
else
{
lean_object* v___x_4851_; 
lean_del_object(v___x_4842_);
lean_dec(v_val_4840_);
v___x_4851_ = lean_box(0);
return v___x_4851_;
}
}
}
}
}
}
}
v___jp_4816_:
{
lean_object* v___x_4817_; 
v___x_4817_ = l_Lean_Expr_nat_x3f(v_e_4815_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v___x_4818_; 
v___x_4818_ = lean_box(0);
return v___x_4818_;
}
else
{
lean_object* v_val_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4827_; 
v_val_4819_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4821_ = v___x_4817_;
v_isShared_4822_ = v_isSharedCheck_4827_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_val_4819_);
lean_dec(v___x_4817_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4827_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4823_; lean_object* v___x_4825_; 
v___x_4823_ = lean_nat_to_int(v_val_4819_);
if (v_isShared_4822_ == 0)
{
lean_ctor_set(v___x_4821_, 0, v___x_4823_);
v___x_4825_ = v___x_4821_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4823_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
return v___x_4825_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4853_, lean_object* v_e_4854_){
_start:
{
uint8_t v___x_4855_; uint8_t v___x_4856_; 
v___x_4855_ = l_Lean_Expr_hasFVar(v_e_4854_);
v___x_4856_ = lean_bool_not(v___x_4855_);
if (v___x_4856_ == 0)
{
uint8_t v___x_4857_; lean_object* v_d_4859_; lean_object* v_b_4860_; 
v___x_4857_ = 1;
switch(lean_obj_tag(v_e_4854_))
{
case 7:
{
lean_object* v_binderType_4863_; lean_object* v_body_4864_; 
v_binderType_4863_ = lean_ctor_get(v_e_4854_, 1);
lean_inc_ref(v_binderType_4863_);
v_body_4864_ = lean_ctor_get(v_e_4854_, 2);
lean_inc_ref(v_body_4864_);
lean_dec_ref_known(v_e_4854_, 3);
v_d_4859_ = v_binderType_4863_;
v_b_4860_ = v_body_4864_;
goto v___jp_4858_;
}
case 6:
{
lean_object* v_binderType_4865_; lean_object* v_body_4866_; 
v_binderType_4865_ = lean_ctor_get(v_e_4854_, 1);
lean_inc_ref(v_binderType_4865_);
v_body_4866_ = lean_ctor_get(v_e_4854_, 2);
lean_inc_ref(v_body_4866_);
lean_dec_ref_known(v_e_4854_, 3);
v_d_4859_ = v_binderType_4865_;
v_b_4860_ = v_body_4866_;
goto v___jp_4858_;
}
case 10:
{
lean_object* v_expr_4867_; 
v_expr_4867_ = lean_ctor_get(v_e_4854_, 1);
lean_inc_ref(v_expr_4867_);
lean_dec_ref_known(v_e_4854_, 2);
v_e_4854_ = v_expr_4867_;
goto _start;
}
case 8:
{
lean_object* v_type_4869_; lean_object* v_value_4870_; lean_object* v_body_4871_; uint8_t v___x_4872_; 
v_type_4869_ = lean_ctor_get(v_e_4854_, 1);
lean_inc_ref(v_type_4869_);
v_value_4870_ = lean_ctor_get(v_e_4854_, 2);
lean_inc_ref(v_value_4870_);
v_body_4871_ = lean_ctor_get(v_e_4854_, 3);
lean_inc_ref(v_body_4871_);
lean_dec_ref_known(v_e_4854_, 4);
lean_inc_ref(v_p_4853_);
v___x_4872_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4853_, v_type_4869_);
if (v___x_4872_ == 0)
{
uint8_t v___x_4873_; 
lean_inc_ref(v_p_4853_);
v___x_4873_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4853_, v_value_4870_);
if (v___x_4873_ == 0)
{
v_e_4854_ = v_body_4871_;
goto _start;
}
else
{
lean_dec_ref(v_body_4871_);
lean_dec_ref(v_p_4853_);
return v___x_4857_;
}
}
else
{
lean_dec_ref(v_body_4871_);
lean_dec_ref(v_value_4870_);
lean_dec_ref(v_p_4853_);
return v___x_4857_;
}
}
case 5:
{
lean_object* v_fn_4875_; lean_object* v_arg_4876_; uint8_t v___x_4877_; 
v_fn_4875_ = lean_ctor_get(v_e_4854_, 0);
lean_inc_ref(v_fn_4875_);
v_arg_4876_ = lean_ctor_get(v_e_4854_, 1);
lean_inc_ref(v_arg_4876_);
lean_dec_ref_known(v_e_4854_, 2);
lean_inc_ref(v_p_4853_);
v___x_4877_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4853_, v_fn_4875_);
if (v___x_4877_ == 0)
{
v_e_4854_ = v_arg_4876_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4876_);
lean_dec_ref(v_p_4853_);
return v___x_4857_;
}
}
case 11:
{
lean_object* v_struct_4879_; 
v_struct_4879_ = lean_ctor_get(v_e_4854_, 2);
lean_inc_ref(v_struct_4879_);
lean_dec_ref_known(v_e_4854_, 3);
v_e_4854_ = v_struct_4879_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4881_; lean_object* v___x_4882_; uint8_t v___x_4883_; 
v_fvarId_4881_ = lean_ctor_get(v_e_4854_, 0);
lean_inc(v_fvarId_4881_);
lean_dec_ref_known(v_e_4854_, 1);
v___x_4882_ = lean_apply_1(v_p_4853_, v_fvarId_4881_);
v___x_4883_ = lean_unbox(v___x_4882_);
return v___x_4883_;
}
default: 
{
lean_dec_ref(v_e_4854_);
lean_dec_ref(v_p_4853_);
return v___x_4856_;
}
}
v___jp_4858_:
{
uint8_t v___x_4861_; 
lean_inc_ref(v_p_4853_);
v___x_4861_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4853_, v_d_4859_);
if (v___x_4861_ == 0)
{
v_e_4854_ = v_b_4860_;
goto _start;
}
else
{
lean_dec_ref(v_b_4860_);
lean_dec_ref(v_p_4853_);
return v___x_4857_;
}
}
}
else
{
uint8_t v___x_4884_; 
lean_dec_ref(v_e_4854_);
lean_dec_ref(v_p_4853_);
v___x_4884_ = 0;
return v___x_4884_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_4885_, lean_object* v_e_4886_){
_start:
{
uint8_t v_res_4887_; lean_object* v_r_4888_; 
v_res_4887_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4885_, v_e_4886_);
v_r_4888_ = lean_box(v_res_4887_);
return v_r_4888_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_4889_, lean_object* v_p_4890_){
_start:
{
uint8_t v___x_4891_; 
v___x_4891_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4890_, v_e_4889_);
return v___x_4891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_4892_, lean_object* v_p_4893_){
_start:
{
uint8_t v_res_4894_; lean_object* v_r_4895_; 
v_res_4894_ = l_Lean_Expr_hasAnyFVar(v_e_4892_, v_p_4893_);
v_r_4895_ = lean_box(v_res_4894_);
return v_r_4895_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_4896_, lean_object* v_e_4897_){
_start:
{
uint8_t v___x_4898_; uint8_t v___x_4899_; 
v___x_4898_ = l_Lean_Expr_hasFVar(v_e_4897_);
v___x_4899_ = lean_bool_not(v___x_4898_);
if (v___x_4899_ == 0)
{
uint8_t v___x_4900_; lean_object* v_d_4902_; lean_object* v_b_4903_; 
v___x_4900_ = 1;
switch(lean_obj_tag(v_e_4897_))
{
case 7:
{
lean_object* v_binderType_4906_; lean_object* v_body_4907_; 
v_binderType_4906_ = lean_ctor_get(v_e_4897_, 1);
v_body_4907_ = lean_ctor_get(v_e_4897_, 2);
v_d_4902_ = v_binderType_4906_;
v_b_4903_ = v_body_4907_;
goto v___jp_4901_;
}
case 6:
{
lean_object* v_binderType_4908_; lean_object* v_body_4909_; 
v_binderType_4908_ = lean_ctor_get(v_e_4897_, 1);
v_body_4909_ = lean_ctor_get(v_e_4897_, 2);
v_d_4902_ = v_binderType_4908_;
v_b_4903_ = v_body_4909_;
goto v___jp_4901_;
}
case 10:
{
lean_object* v_expr_4910_; 
v_expr_4910_ = lean_ctor_get(v_e_4897_, 1);
v_e_4897_ = v_expr_4910_;
goto _start;
}
case 8:
{
lean_object* v_type_4912_; lean_object* v_value_4913_; lean_object* v_body_4914_; uint8_t v___x_4915_; 
v_type_4912_ = lean_ctor_get(v_e_4897_, 1);
v_value_4913_ = lean_ctor_get(v_e_4897_, 2);
v_body_4914_ = lean_ctor_get(v_e_4897_, 3);
v___x_4915_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4896_, v_type_4912_);
if (v___x_4915_ == 0)
{
uint8_t v___x_4916_; 
v___x_4916_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4896_, v_value_4913_);
if (v___x_4916_ == 0)
{
v_e_4897_ = v_body_4914_;
goto _start;
}
else
{
return v___x_4900_;
}
}
else
{
return v___x_4900_;
}
}
case 5:
{
lean_object* v_fn_4918_; lean_object* v_arg_4919_; uint8_t v___x_4920_; 
v_fn_4918_ = lean_ctor_get(v_e_4897_, 0);
v_arg_4919_ = lean_ctor_get(v_e_4897_, 1);
v___x_4920_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4896_, v_fn_4918_);
if (v___x_4920_ == 0)
{
v_e_4897_ = v_arg_4919_;
goto _start;
}
else
{
return v___x_4900_;
}
}
case 11:
{
lean_object* v_struct_4922_; 
v_struct_4922_ = lean_ctor_get(v_e_4897_, 2);
v_e_4897_ = v_struct_4922_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4924_; uint8_t v___x_4925_; 
v_fvarId_4924_ = lean_ctor_get(v_e_4897_, 0);
v___x_4925_ = lean_name_eq(v_fvarId_4924_, v_fvarId_4896_);
return v___x_4925_;
}
default: 
{
return v___x_4899_;
}
}
v___jp_4901_:
{
uint8_t v___x_4904_; 
v___x_4904_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4896_, v_d_4902_);
if (v___x_4904_ == 0)
{
v_e_4897_ = v_b_4903_;
goto _start;
}
else
{
return v___x_4900_;
}
}
}
else
{
uint8_t v___x_4926_; 
v___x_4926_ = 0;
return v___x_4926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_4927_, lean_object* v_e_4928_){
_start:
{
uint8_t v_res_4929_; lean_object* v_r_4930_; 
v_res_4929_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4927_, v_e_4928_);
lean_dec_ref(v_e_4928_);
lean_dec(v_fvarId_4927_);
v_r_4930_ = lean_box(v_res_4929_);
return v_r_4930_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_4931_, lean_object* v_fvarId_4932_){
_start:
{
uint8_t v___x_4933_; 
v___x_4933_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4932_, v_e_4931_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_4934_, lean_object* v_fvarId_4935_){
_start:
{
uint8_t v_res_4936_; lean_object* v_r_4937_; 
v_res_4936_ = l_Lean_Expr_containsFVar(v_e_4934_, v_fvarId_4935_);
lean_dec(v_fvarId_4935_);
lean_dec_ref(v_e_4934_);
v_r_4937_ = lean_box(v_res_4936_);
return v_r_4937_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4939_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_4940_ = lean_unsigned_to_nat(18u);
v___x_4941_ = lean_unsigned_to_nat(1847u);
v___x_4942_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_4943_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4944_ = l_mkPanicMessageWithDecl(v___x_4943_, v___x_4942_, v___x_4941_, v___x_4940_, v___x_4939_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_4945_, lean_object* v_newFn_4946_, lean_object* v_newArg_4947_){
_start:
{
uint8_t v___y_4949_; 
if (lean_obj_tag(v_e_4945_) == 5)
{
lean_object* v_fn_4951_; lean_object* v_arg_4952_; size_t v___x_4953_; size_t v___x_4954_; uint8_t v___x_4955_; 
v_fn_4951_ = lean_ctor_get(v_e_4945_, 0);
v_arg_4952_ = lean_ctor_get(v_e_4945_, 1);
v___x_4953_ = lean_ptr_addr(v_fn_4951_);
v___x_4954_ = lean_ptr_addr(v_newFn_4946_);
v___x_4955_ = lean_usize_dec_eq(v___x_4953_, v___x_4954_);
if (v___x_4955_ == 0)
{
v___y_4949_ = v___x_4955_;
goto v___jp_4948_;
}
else
{
size_t v___x_4956_; size_t v___x_4957_; uint8_t v___x_4958_; 
v___x_4956_ = lean_ptr_addr(v_arg_4952_);
v___x_4957_ = lean_ptr_addr(v_newArg_4947_);
v___x_4958_ = lean_usize_dec_eq(v___x_4956_, v___x_4957_);
v___y_4949_ = v___x_4958_;
goto v___jp_4948_;
}
}
else
{
lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
lean_dec_ref(v_newArg_4947_);
lean_dec_ref(v_newFn_4946_);
v___x_4959_ = l_Lean_instInhabitedExpr;
v___x_4960_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_4961_ = l_panic___redArg(v___x_4959_, v___x_4960_);
return v___x_4961_;
}
v___jp_4948_:
{
if (v___y_4949_ == 0)
{
lean_object* v___x_4950_; 
v___x_4950_ = l_Lean_Expr_app___override(v_newFn_4946_, v_newArg_4947_);
return v___x_4950_;
}
else
{
lean_dec_ref(v_newArg_4947_);
lean_dec_ref(v_newFn_4946_);
lean_inc_ref(v_e_4945_);
return v_e_4945_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_4962_, lean_object* v_newFn_4963_, lean_object* v_newArg_4964_){
_start:
{
lean_object* v_res_4965_; 
v_res_4965_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_4962_, v_newFn_4963_, v_newArg_4964_);
lean_dec_ref(v_e_4962_);
return v_res_4965_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4967_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_4968_ = lean_unsigned_to_nat(20u);
v___x_4969_ = lean_unsigned_to_nat(1858u);
v___x_4970_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_4971_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4972_ = l_mkPanicMessageWithDecl(v___x_4971_, v___x_4970_, v___x_4969_, v___x_4968_, v___x_4967_);
return v___x_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_4973_, lean_object* v_fvarIdNew_4974_){
_start:
{
if (lean_obj_tag(v_e_4973_) == 1)
{
lean_object* v_fvarId_4975_; uint8_t v___x_4976_; 
v_fvarId_4975_ = lean_ctor_get(v_e_4973_, 0);
v___x_4976_ = lean_name_eq(v_fvarId_4975_, v_fvarIdNew_4974_);
if (v___x_4976_ == 0)
{
lean_object* v___x_4977_; 
v___x_4977_ = l_Lean_Expr_fvar___override(v_fvarIdNew_4974_);
return v___x_4977_;
}
else
{
lean_dec(v_fvarIdNew_4974_);
lean_inc_ref(v_e_4973_);
return v_e_4973_;
}
}
else
{
lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
lean_dec(v_fvarIdNew_4974_);
v___x_4978_ = l_Lean_instInhabitedExpr;
v___x_4979_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_4980_ = l_panic___redArg(v___x_4978_, v___x_4979_);
return v___x_4980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_4981_, lean_object* v_fvarIdNew_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l_Lean_Expr_updateFVar_x21(v_e_4981_, v_fvarIdNew_4982_);
lean_dec_ref(v_e_4981_);
return v_res_4983_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4985_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_4986_ = lean_unsigned_to_nat(18u);
v___x_4987_ = lean_unsigned_to_nat(1863u);
v___x_4988_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_4989_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4990_ = l_mkPanicMessageWithDecl(v___x_4989_, v___x_4988_, v___x_4987_, v___x_4986_, v___x_4985_);
return v___x_4990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_4991_, lean_object* v_newLevels_4992_){
_start:
{
if (lean_obj_tag(v_e_4991_) == 4)
{
lean_object* v_declName_4993_; lean_object* v_us_4994_; uint8_t v___x_4995_; 
v_declName_4993_ = lean_ctor_get(v_e_4991_, 0);
v_us_4994_ = lean_ctor_get(v_e_4991_, 1);
v___x_4995_ = l_ptrEqList___redArg(v_us_4994_, v_newLevels_4992_);
if (v___x_4995_ == 0)
{
lean_object* v___x_4996_; 
lean_inc(v_declName_4993_);
lean_dec_ref_known(v_e_4991_, 2);
v___x_4996_ = l_Lean_Expr_const___override(v_declName_4993_, v_newLevels_4992_);
return v___x_4996_;
}
else
{
lean_dec(v_newLevels_4992_);
return v_e_4991_;
}
}
else
{
lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
lean_dec(v_newLevels_4992_);
lean_dec_ref(v_e_4991_);
v___x_4997_ = l_Lean_instInhabitedExpr;
v___x_4998_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_4999_ = l_panic___redArg(v___x_4997_, v___x_4998_);
return v___x_4999_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; 
v___x_5002_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_5003_ = lean_unsigned_to_nat(14u);
v___x_5004_ = lean_unsigned_to_nat(1874u);
v___x_5005_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_5006_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5007_ = l_mkPanicMessageWithDecl(v___x_5006_, v___x_5005_, v___x_5004_, v___x_5003_, v___x_5002_);
return v___x_5007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_5008_, lean_object* v_u_x27_5009_){
_start:
{
if (lean_obj_tag(v_e_5008_) == 3)
{
lean_object* v_u_5010_; size_t v___x_5011_; size_t v___x_5012_; uint8_t v___x_5013_; 
v_u_5010_ = lean_ctor_get(v_e_5008_, 0);
v___x_5011_ = lean_ptr_addr(v_u_5010_);
v___x_5012_ = lean_ptr_addr(v_u_x27_5009_);
v___x_5013_ = lean_usize_dec_eq(v___x_5011_, v___x_5012_);
if (v___x_5013_ == 0)
{
lean_object* v___x_5014_; 
v___x_5014_ = l_Lean_Expr_sort___override(v_u_x27_5009_);
return v___x_5014_;
}
else
{
lean_dec(v_u_x27_5009_);
lean_inc_ref(v_e_5008_);
return v_e_5008_;
}
}
else
{
lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
lean_dec(v_u_x27_5009_);
v___x_5015_ = l_Lean_instInhabitedExpr;
v___x_5016_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_5017_ = l_panic___redArg(v___x_5015_, v___x_5016_);
return v___x_5017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_5018_, lean_object* v_u_x27_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_5018_, v_u_x27_5019_);
lean_dec_ref(v_e_5018_);
return v_res_5020_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; 
v___x_5023_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_5024_ = lean_unsigned_to_nat(17u);
v___x_5025_ = lean_unsigned_to_nat(1885u);
v___x_5026_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_5027_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5028_ = l_mkPanicMessageWithDecl(v___x_5027_, v___x_5026_, v___x_5025_, v___x_5024_, v___x_5023_);
return v___x_5028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_5029_, lean_object* v_newExpr_5030_){
_start:
{
if (lean_obj_tag(v_e_5029_) == 10)
{
lean_object* v_data_5031_; lean_object* v_expr_5032_; size_t v___x_5033_; size_t v___x_5034_; uint8_t v___x_5035_; 
v_data_5031_ = lean_ctor_get(v_e_5029_, 0);
v_expr_5032_ = lean_ctor_get(v_e_5029_, 1);
v___x_5033_ = lean_ptr_addr(v_expr_5032_);
v___x_5034_ = lean_ptr_addr(v_newExpr_5030_);
v___x_5035_ = lean_usize_dec_eq(v___x_5033_, v___x_5034_);
if (v___x_5035_ == 0)
{
lean_object* v___x_5036_; 
lean_inc(v_data_5031_);
lean_dec_ref_known(v_e_5029_, 2);
v___x_5036_ = l_Lean_Expr_mdata___override(v_data_5031_, v_newExpr_5030_);
return v___x_5036_;
}
else
{
lean_dec_ref(v_newExpr_5030_);
return v_e_5029_;
}
}
else
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; 
lean_dec_ref(v_newExpr_5030_);
lean_dec_ref(v_e_5029_);
v___x_5037_ = l_Lean_instInhabitedExpr;
v___x_5038_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_5039_ = l_panic___redArg(v___x_5037_, v___x_5038_);
return v___x_5039_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; 
v___x_5042_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_5043_ = lean_unsigned_to_nat(18u);
v___x_5044_ = lean_unsigned_to_nat(1896u);
v___x_5045_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_5046_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5047_ = l_mkPanicMessageWithDecl(v___x_5046_, v___x_5045_, v___x_5044_, v___x_5043_, v___x_5042_);
return v___x_5047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_5048_, lean_object* v_newExpr_5049_){
_start:
{
if (lean_obj_tag(v_e_5048_) == 11)
{
lean_object* v_typeName_5050_; lean_object* v_idx_5051_; lean_object* v_struct_5052_; size_t v___x_5053_; size_t v___x_5054_; uint8_t v___x_5055_; 
v_typeName_5050_ = lean_ctor_get(v_e_5048_, 0);
v_idx_5051_ = lean_ctor_get(v_e_5048_, 1);
v_struct_5052_ = lean_ctor_get(v_e_5048_, 2);
v___x_5053_ = lean_ptr_addr(v_struct_5052_);
v___x_5054_ = lean_ptr_addr(v_newExpr_5049_);
v___x_5055_ = lean_usize_dec_eq(v___x_5053_, v___x_5054_);
if (v___x_5055_ == 0)
{
lean_object* v___x_5056_; 
lean_inc(v_idx_5051_);
lean_inc(v_typeName_5050_);
lean_dec_ref_known(v_e_5048_, 3);
v___x_5056_ = l_Lean_Expr_proj___override(v_typeName_5050_, v_idx_5051_, v_newExpr_5049_);
return v___x_5056_;
}
else
{
lean_dec_ref(v_newExpr_5049_);
return v_e_5048_;
}
}
else
{
lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
lean_dec_ref(v_newExpr_5049_);
lean_dec_ref(v_e_5048_);
v___x_5057_ = l_Lean_instInhabitedExpr;
v___x_5058_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_5059_ = l_panic___redArg(v___x_5057_, v___x_5058_);
return v___x_5059_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v___x_5062_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5063_ = lean_unsigned_to_nat(23u);
v___x_5064_ = lean_unsigned_to_nat(1911u);
v___x_5065_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_5066_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5067_ = l_mkPanicMessageWithDecl(v___x_5066_, v___x_5065_, v___x_5064_, v___x_5063_, v___x_5062_);
return v___x_5067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_5068_, uint8_t v_newBinfo_5069_, lean_object* v_newDomain_5070_, lean_object* v_newBody_5071_){
_start:
{
if (lean_obj_tag(v_e_5068_) == 7)
{
lean_object* v_binderName_5072_; lean_object* v_binderType_5073_; lean_object* v_body_5074_; uint8_t v_binderInfo_5075_; uint8_t v___y_5077_; size_t v___x_5081_; size_t v___x_5082_; uint8_t v___x_5083_; 
v_binderName_5072_ = lean_ctor_get(v_e_5068_, 0);
v_binderType_5073_ = lean_ctor_get(v_e_5068_, 1);
v_body_5074_ = lean_ctor_get(v_e_5068_, 2);
v_binderInfo_5075_ = lean_ctor_get_uint8(v_e_5068_, sizeof(void*)*3 + 8);
v___x_5081_ = lean_ptr_addr(v_binderType_5073_);
v___x_5082_ = lean_ptr_addr(v_newDomain_5070_);
v___x_5083_ = lean_usize_dec_eq(v___x_5081_, v___x_5082_);
if (v___x_5083_ == 0)
{
v___y_5077_ = v___x_5083_;
goto v___jp_5076_;
}
else
{
size_t v___x_5084_; size_t v___x_5085_; uint8_t v___x_5086_; 
v___x_5084_ = lean_ptr_addr(v_body_5074_);
v___x_5085_ = lean_ptr_addr(v_newBody_5071_);
v___x_5086_ = lean_usize_dec_eq(v___x_5084_, v___x_5085_);
v___y_5077_ = v___x_5086_;
goto v___jp_5076_;
}
v___jp_5076_:
{
if (v___y_5077_ == 0)
{
lean_object* v___x_5078_; 
lean_inc(v_binderName_5072_);
lean_dec_ref_known(v_e_5068_, 3);
v___x_5078_ = l_Lean_Expr_forallE___override(v_binderName_5072_, v_newDomain_5070_, v_newBody_5071_, v_newBinfo_5069_);
return v___x_5078_;
}
else
{
uint8_t v___x_5079_; 
v___x_5079_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5075_, v_newBinfo_5069_);
if (v___x_5079_ == 0)
{
lean_object* v___x_5080_; 
lean_inc(v_binderName_5072_);
lean_dec_ref_known(v_e_5068_, 3);
v___x_5080_ = l_Lean_Expr_forallE___override(v_binderName_5072_, v_newDomain_5070_, v_newBody_5071_, v_newBinfo_5069_);
return v___x_5080_;
}
else
{
lean_dec_ref(v_newBody_5071_);
lean_dec_ref(v_newDomain_5070_);
return v_e_5068_;
}
}
}
}
else
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
lean_dec_ref(v_newBody_5071_);
lean_dec_ref(v_newDomain_5070_);
lean_dec_ref(v_e_5068_);
v___x_5087_ = l_Lean_instInhabitedExpr;
v___x_5088_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_5089_ = l_panic___redArg(v___x_5087_, v___x_5088_);
return v___x_5089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_5090_, lean_object* v_newBinfo_5091_, lean_object* v_newDomain_5092_, lean_object* v_newBody_5093_){
_start:
{
uint8_t v_newBinfo_boxed_5094_; lean_object* v_res_5095_; 
v_newBinfo_boxed_5094_ = lean_unbox(v_newBinfo_5091_);
v_res_5095_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5090_, v_newBinfo_boxed_5094_, v_newDomain_5092_, v_newBody_5093_);
return v_res_5095_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; 
v___x_5097_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5098_ = lean_unsigned_to_nat(24u);
v___x_5099_ = lean_unsigned_to_nat(1922u);
v___x_5100_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_5101_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5102_ = l_mkPanicMessageWithDecl(v___x_5101_, v___x_5100_, v___x_5099_, v___x_5098_, v___x_5097_);
return v___x_5102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_5103_, lean_object* v_newDomain_5104_, lean_object* v_newBody_5105_){
_start:
{
if (lean_obj_tag(v_e_5103_) == 7)
{
lean_object* v_binderName_5106_; lean_object* v_binderType_5107_; lean_object* v_body_5108_; uint8_t v_binderInfo_5109_; uint8_t v___y_5111_; size_t v___x_5115_; size_t v___x_5116_; uint8_t v___x_5117_; 
v_binderName_5106_ = lean_ctor_get(v_e_5103_, 0);
v_binderType_5107_ = lean_ctor_get(v_e_5103_, 1);
v_body_5108_ = lean_ctor_get(v_e_5103_, 2);
v_binderInfo_5109_ = lean_ctor_get_uint8(v_e_5103_, sizeof(void*)*3 + 8);
v___x_5115_ = lean_ptr_addr(v_binderType_5107_);
v___x_5116_ = lean_ptr_addr(v_newDomain_5104_);
v___x_5117_ = lean_usize_dec_eq(v___x_5115_, v___x_5116_);
if (v___x_5117_ == 0)
{
v___y_5111_ = v___x_5117_;
goto v___jp_5110_;
}
else
{
size_t v___x_5118_; size_t v___x_5119_; uint8_t v___x_5120_; 
v___x_5118_ = lean_ptr_addr(v_body_5108_);
v___x_5119_ = lean_ptr_addr(v_newBody_5105_);
v___x_5120_ = lean_usize_dec_eq(v___x_5118_, v___x_5119_);
v___y_5111_ = v___x_5120_;
goto v___jp_5110_;
}
v___jp_5110_:
{
if (v___y_5111_ == 0)
{
lean_object* v___x_5112_; 
lean_inc(v_binderName_5106_);
lean_dec_ref_known(v_e_5103_, 3);
v___x_5112_ = l_Lean_Expr_forallE___override(v_binderName_5106_, v_newDomain_5104_, v_newBody_5105_, v_binderInfo_5109_);
return v___x_5112_;
}
else
{
uint8_t v___x_5113_; 
v___x_5113_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5109_, v_binderInfo_5109_);
if (v___x_5113_ == 0)
{
lean_object* v___x_5114_; 
lean_inc(v_binderName_5106_);
lean_dec_ref_known(v_e_5103_, 3);
v___x_5114_ = l_Lean_Expr_forallE___override(v_binderName_5106_, v_newDomain_5104_, v_newBody_5105_, v_binderInfo_5109_);
return v___x_5114_;
}
else
{
lean_dec_ref(v_newBody_5105_);
lean_dec_ref(v_newDomain_5104_);
return v_e_5103_;
}
}
}
}
else
{
lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; 
lean_dec_ref(v_newBody_5105_);
lean_dec_ref(v_newDomain_5104_);
lean_dec_ref(v_e_5103_);
v___x_5121_ = l_Lean_instInhabitedExpr;
v___x_5122_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_5123_ = l_panic___redArg(v___x_5121_, v___x_5122_);
return v___x_5123_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; 
v___x_5126_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5127_ = lean_unsigned_to_nat(19u);
v___x_5128_ = lean_unsigned_to_nat(1931u);
v___x_5129_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_5130_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5131_ = l_mkPanicMessageWithDecl(v___x_5130_, v___x_5129_, v___x_5128_, v___x_5127_, v___x_5126_);
return v___x_5131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_5132_, uint8_t v_newBinfo_5133_, lean_object* v_newDomain_5134_, lean_object* v_newBody_5135_){
_start:
{
if (lean_obj_tag(v_e_5132_) == 6)
{
lean_object* v_binderName_5136_; lean_object* v_binderType_5137_; lean_object* v_body_5138_; uint8_t v_binderInfo_5139_; uint8_t v___y_5141_; size_t v___x_5145_; size_t v___x_5146_; uint8_t v___x_5147_; 
v_binderName_5136_ = lean_ctor_get(v_e_5132_, 0);
v_binderType_5137_ = lean_ctor_get(v_e_5132_, 1);
v_body_5138_ = lean_ctor_get(v_e_5132_, 2);
v_binderInfo_5139_ = lean_ctor_get_uint8(v_e_5132_, sizeof(void*)*3 + 8);
v___x_5145_ = lean_ptr_addr(v_binderType_5137_);
v___x_5146_ = lean_ptr_addr(v_newDomain_5134_);
v___x_5147_ = lean_usize_dec_eq(v___x_5145_, v___x_5146_);
if (v___x_5147_ == 0)
{
v___y_5141_ = v___x_5147_;
goto v___jp_5140_;
}
else
{
size_t v___x_5148_; size_t v___x_5149_; uint8_t v___x_5150_; 
v___x_5148_ = lean_ptr_addr(v_body_5138_);
v___x_5149_ = lean_ptr_addr(v_newBody_5135_);
v___x_5150_ = lean_usize_dec_eq(v___x_5148_, v___x_5149_);
v___y_5141_ = v___x_5150_;
goto v___jp_5140_;
}
v___jp_5140_:
{
if (v___y_5141_ == 0)
{
lean_object* v___x_5142_; 
lean_inc(v_binderName_5136_);
lean_dec_ref_known(v_e_5132_, 3);
v___x_5142_ = l_Lean_Expr_lam___override(v_binderName_5136_, v_newDomain_5134_, v_newBody_5135_, v_newBinfo_5133_);
return v___x_5142_;
}
else
{
uint8_t v___x_5143_; 
v___x_5143_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5139_, v_newBinfo_5133_);
if (v___x_5143_ == 0)
{
lean_object* v___x_5144_; 
lean_inc(v_binderName_5136_);
lean_dec_ref_known(v_e_5132_, 3);
v___x_5144_ = l_Lean_Expr_lam___override(v_binderName_5136_, v_newDomain_5134_, v_newBody_5135_, v_newBinfo_5133_);
return v___x_5144_;
}
else
{
lean_dec_ref(v_newBody_5135_);
lean_dec_ref(v_newDomain_5134_);
return v_e_5132_;
}
}
}
}
else
{
lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; 
lean_dec_ref(v_newBody_5135_);
lean_dec_ref(v_newDomain_5134_);
lean_dec_ref(v_e_5132_);
v___x_5151_ = l_Lean_instInhabitedExpr;
v___x_5152_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_5153_ = l_panic___redArg(v___x_5151_, v___x_5152_);
return v___x_5153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_5154_, lean_object* v_newBinfo_5155_, lean_object* v_newDomain_5156_, lean_object* v_newBody_5157_){
_start:
{
uint8_t v_newBinfo_boxed_5158_; lean_object* v_res_5159_; 
v_newBinfo_boxed_5158_ = lean_unbox(v_newBinfo_5155_);
v_res_5159_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5154_, v_newBinfo_boxed_5158_, v_newDomain_5156_, v_newBody_5157_);
return v_res_5159_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; 
v___x_5161_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5162_ = lean_unsigned_to_nat(20u);
v___x_5163_ = lean_unsigned_to_nat(1942u);
v___x_5164_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5165_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5166_ = l_mkPanicMessageWithDecl(v___x_5165_, v___x_5164_, v___x_5163_, v___x_5162_, v___x_5161_);
return v___x_5166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5167_, lean_object* v_newDomain_5168_, lean_object* v_newBody_5169_){
_start:
{
if (lean_obj_tag(v_e_5167_) == 6)
{
lean_object* v_binderName_5170_; lean_object* v_binderType_5171_; lean_object* v_body_5172_; uint8_t v_binderInfo_5173_; uint8_t v___y_5175_; size_t v___x_5179_; size_t v___x_5180_; uint8_t v___x_5181_; 
v_binderName_5170_ = lean_ctor_get(v_e_5167_, 0);
v_binderType_5171_ = lean_ctor_get(v_e_5167_, 1);
v_body_5172_ = lean_ctor_get(v_e_5167_, 2);
v_binderInfo_5173_ = lean_ctor_get_uint8(v_e_5167_, sizeof(void*)*3 + 8);
v___x_5179_ = lean_ptr_addr(v_binderType_5171_);
v___x_5180_ = lean_ptr_addr(v_newDomain_5168_);
v___x_5181_ = lean_usize_dec_eq(v___x_5179_, v___x_5180_);
if (v___x_5181_ == 0)
{
v___y_5175_ = v___x_5181_;
goto v___jp_5174_;
}
else
{
size_t v___x_5182_; size_t v___x_5183_; uint8_t v___x_5184_; 
v___x_5182_ = lean_ptr_addr(v_body_5172_);
v___x_5183_ = lean_ptr_addr(v_newBody_5169_);
v___x_5184_ = lean_usize_dec_eq(v___x_5182_, v___x_5183_);
v___y_5175_ = v___x_5184_;
goto v___jp_5174_;
}
v___jp_5174_:
{
if (v___y_5175_ == 0)
{
lean_object* v___x_5176_; 
lean_inc(v_binderName_5170_);
lean_dec_ref_known(v_e_5167_, 3);
v___x_5176_ = l_Lean_Expr_lam___override(v_binderName_5170_, v_newDomain_5168_, v_newBody_5169_, v_binderInfo_5173_);
return v___x_5176_;
}
else
{
uint8_t v___x_5177_; 
v___x_5177_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5173_, v_binderInfo_5173_);
if (v___x_5177_ == 0)
{
lean_object* v___x_5178_; 
lean_inc(v_binderName_5170_);
lean_dec_ref_known(v_e_5167_, 3);
v___x_5178_ = l_Lean_Expr_lam___override(v_binderName_5170_, v_newDomain_5168_, v_newBody_5169_, v_binderInfo_5173_);
return v___x_5178_;
}
else
{
lean_dec_ref(v_newBody_5169_);
lean_dec_ref(v_newDomain_5168_);
return v_e_5167_;
}
}
}
}
else
{
lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; 
lean_dec_ref(v_newBody_5169_);
lean_dec_ref(v_newDomain_5168_);
lean_dec_ref(v_e_5167_);
v___x_5185_ = l_Lean_instInhabitedExpr;
v___x_5186_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5187_ = l_panic___redArg(v___x_5185_, v___x_5186_);
return v___x_5187_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; 
v___x_5189_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5190_ = lean_unsigned_to_nat(22u);
v___x_5191_ = lean_unsigned_to_nat(1951u);
v___x_5192_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5193_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5194_ = l_mkPanicMessageWithDecl(v___x_5193_, v___x_5192_, v___x_5191_, v___x_5190_, v___x_5189_);
return v___x_5194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5195_, lean_object* v_newType_5196_, lean_object* v_newVal_5197_, lean_object* v_newBody_5198_, uint8_t v_newNondep_5199_){
_start:
{
if (lean_obj_tag(v_e_5195_) == 8)
{
lean_object* v_declName_5200_; lean_object* v_type_5201_; lean_object* v_value_5202_; lean_object* v_body_5203_; uint8_t v_nondep_5204_; uint8_t v___y_5206_; size_t v___x_5214_; size_t v___x_5215_; uint8_t v___x_5216_; 
v_declName_5200_ = lean_ctor_get(v_e_5195_, 0);
v_type_5201_ = lean_ctor_get(v_e_5195_, 1);
v_value_5202_ = lean_ctor_get(v_e_5195_, 2);
v_body_5203_ = lean_ctor_get(v_e_5195_, 3);
v_nondep_5204_ = lean_ctor_get_uint8(v_e_5195_, sizeof(void*)*4 + 8);
v___x_5214_ = lean_ptr_addr(v_type_5201_);
v___x_5215_ = lean_ptr_addr(v_newType_5196_);
v___x_5216_ = lean_usize_dec_eq(v___x_5214_, v___x_5215_);
if (v___x_5216_ == 0)
{
v___y_5206_ = v___x_5216_;
goto v___jp_5205_;
}
else
{
size_t v___x_5217_; size_t v___x_5218_; uint8_t v___x_5219_; 
v___x_5217_ = lean_ptr_addr(v_value_5202_);
v___x_5218_ = lean_ptr_addr(v_newVal_5197_);
v___x_5219_ = lean_usize_dec_eq(v___x_5217_, v___x_5218_);
v___y_5206_ = v___x_5219_;
goto v___jp_5205_;
}
v___jp_5205_:
{
if (v___y_5206_ == 0)
{
lean_object* v___x_5207_; 
lean_inc(v_declName_5200_);
lean_dec_ref_known(v_e_5195_, 4);
v___x_5207_ = l_Lean_Expr_letE___override(v_declName_5200_, v_newType_5196_, v_newVal_5197_, v_newBody_5198_, v_newNondep_5199_);
return v___x_5207_;
}
else
{
size_t v___x_5208_; size_t v___x_5209_; uint8_t v___x_5210_; 
v___x_5208_ = lean_ptr_addr(v_body_5203_);
v___x_5209_ = lean_ptr_addr(v_newBody_5198_);
v___x_5210_ = lean_usize_dec_eq(v___x_5208_, v___x_5209_);
if (v___x_5210_ == 0)
{
lean_object* v___x_5211_; 
lean_inc(v_declName_5200_);
lean_dec_ref_known(v_e_5195_, 4);
v___x_5211_ = l_Lean_Expr_letE___override(v_declName_5200_, v_newType_5196_, v_newVal_5197_, v_newBody_5198_, v_newNondep_5199_);
return v___x_5211_;
}
else
{
if (v_nondep_5204_ == 0)
{
if (v_newNondep_5199_ == 0)
{
lean_dec_ref(v_newBody_5198_);
lean_dec_ref(v_newVal_5197_);
lean_dec_ref(v_newType_5196_);
return v_e_5195_;
}
else
{
lean_object* v___x_5212_; 
lean_inc(v_declName_5200_);
lean_dec_ref_known(v_e_5195_, 4);
v___x_5212_ = l_Lean_Expr_letE___override(v_declName_5200_, v_newType_5196_, v_newVal_5197_, v_newBody_5198_, v_newNondep_5199_);
return v___x_5212_;
}
}
else
{
if (v_newNondep_5199_ == 0)
{
lean_object* v___x_5213_; 
lean_inc(v_declName_5200_);
lean_dec_ref_known(v_e_5195_, 4);
v___x_5213_ = l_Lean_Expr_letE___override(v_declName_5200_, v_newType_5196_, v_newVal_5197_, v_newBody_5198_, v_newNondep_5199_);
return v___x_5213_;
}
else
{
lean_dec_ref(v_newBody_5198_);
lean_dec_ref(v_newVal_5197_);
lean_dec_ref(v_newType_5196_);
return v_e_5195_;
}
}
}
}
}
}
else
{
lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; 
lean_dec_ref(v_newBody_5198_);
lean_dec_ref(v_newVal_5197_);
lean_dec_ref(v_newType_5196_);
lean_dec_ref(v_e_5195_);
v___x_5220_ = l_Lean_instInhabitedExpr;
v___x_5221_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5222_ = l_panic___redArg(v___x_5220_, v___x_5221_);
return v___x_5222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5223_, lean_object* v_newType_5224_, lean_object* v_newVal_5225_, lean_object* v_newBody_5226_, lean_object* v_newNondep_5227_){
_start:
{
uint8_t v_newNondep_boxed_5228_; lean_object* v_res_5229_; 
v_newNondep_boxed_5228_ = lean_unbox(v_newNondep_5227_);
v_res_5229_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5223_, v_newType_5224_, v_newVal_5225_, v_newBody_5226_, v_newNondep_boxed_5228_);
return v_res_5229_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
v___x_5231_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5232_ = lean_unsigned_to_nat(27u);
v___x_5233_ = lean_unsigned_to_nat(1964u);
v___x_5234_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5235_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5236_ = l_mkPanicMessageWithDecl(v___x_5235_, v___x_5234_, v___x_5233_, v___x_5232_, v___x_5231_);
return v___x_5236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5237_, lean_object* v_newType_5238_, lean_object* v_newVal_5239_, lean_object* v_newBody_5240_){
_start:
{
if (lean_obj_tag(v_e_5237_) == 8)
{
lean_object* v_declName_5241_; lean_object* v_type_5242_; lean_object* v_value_5243_; lean_object* v_body_5244_; uint8_t v_nondep_5245_; uint8_t v___y_5247_; size_t v___x_5253_; size_t v___x_5254_; uint8_t v___x_5255_; 
v_declName_5241_ = lean_ctor_get(v_e_5237_, 0);
v_type_5242_ = lean_ctor_get(v_e_5237_, 1);
v_value_5243_ = lean_ctor_get(v_e_5237_, 2);
v_body_5244_ = lean_ctor_get(v_e_5237_, 3);
v_nondep_5245_ = lean_ctor_get_uint8(v_e_5237_, sizeof(void*)*4 + 8);
v___x_5253_ = lean_ptr_addr(v_type_5242_);
v___x_5254_ = lean_ptr_addr(v_newType_5238_);
v___x_5255_ = lean_usize_dec_eq(v___x_5253_, v___x_5254_);
if (v___x_5255_ == 0)
{
v___y_5247_ = v___x_5255_;
goto v___jp_5246_;
}
else
{
size_t v___x_5256_; size_t v___x_5257_; uint8_t v___x_5258_; 
v___x_5256_ = lean_ptr_addr(v_value_5243_);
v___x_5257_ = lean_ptr_addr(v_newVal_5239_);
v___x_5258_ = lean_usize_dec_eq(v___x_5256_, v___x_5257_);
v___y_5247_ = v___x_5258_;
goto v___jp_5246_;
}
v___jp_5246_:
{
if (v___y_5247_ == 0)
{
lean_object* v___x_5248_; 
lean_inc(v_declName_5241_);
lean_dec_ref_known(v_e_5237_, 4);
v___x_5248_ = l_Lean_Expr_letE___override(v_declName_5241_, v_newType_5238_, v_newVal_5239_, v_newBody_5240_, v_nondep_5245_);
return v___x_5248_;
}
else
{
size_t v___x_5249_; size_t v___x_5250_; uint8_t v___x_5251_; 
v___x_5249_ = lean_ptr_addr(v_body_5244_);
v___x_5250_ = lean_ptr_addr(v_newBody_5240_);
v___x_5251_ = lean_usize_dec_eq(v___x_5249_, v___x_5250_);
if (v___x_5251_ == 0)
{
lean_object* v___x_5252_; 
lean_inc(v_declName_5241_);
lean_dec_ref_known(v_e_5237_, 4);
v___x_5252_ = l_Lean_Expr_letE___override(v_declName_5241_, v_newType_5238_, v_newVal_5239_, v_newBody_5240_, v_nondep_5245_);
return v___x_5252_;
}
else
{
lean_dec_ref(v_newBody_5240_);
lean_dec_ref(v_newVal_5239_);
lean_dec_ref(v_newType_5238_);
return v_e_5237_;
}
}
}
}
else
{
lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; 
lean_dec_ref(v_newBody_5240_);
lean_dec_ref(v_newVal_5239_);
lean_dec_ref(v_newType_5238_);
lean_dec_ref(v_e_5237_);
v___x_5259_ = l_Lean_instInhabitedExpr;
v___x_5260_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5261_ = l_panic___redArg(v___x_5259_, v___x_5260_);
return v___x_5261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5262_, lean_object* v_x_5263_){
_start:
{
if (lean_obj_tag(v_x_5262_) == 5)
{
lean_object* v_fn_5264_; lean_object* v_arg_5265_; lean_object* v___x_5266_; uint8_t v___y_5268_; size_t v___x_5270_; size_t v___x_5271_; uint8_t v___x_5272_; 
v_fn_5264_ = lean_ctor_get(v_x_5262_, 0);
v_arg_5265_ = lean_ctor_get(v_x_5262_, 1);
lean_inc_ref(v_fn_5264_);
v___x_5266_ = l_Lean_Expr_updateFn(v_fn_5264_, v_x_5263_);
v___x_5270_ = lean_ptr_addr(v_fn_5264_);
v___x_5271_ = lean_ptr_addr(v___x_5266_);
v___x_5272_ = lean_usize_dec_eq(v___x_5270_, v___x_5271_);
if (v___x_5272_ == 0)
{
v___y_5268_ = v___x_5272_;
goto v___jp_5267_;
}
else
{
size_t v___x_5273_; uint8_t v___x_5274_; 
v___x_5273_ = lean_ptr_addr(v_arg_5265_);
v___x_5274_ = lean_usize_dec_eq(v___x_5273_, v___x_5273_);
v___y_5268_ = v___x_5274_;
goto v___jp_5267_;
}
v___jp_5267_:
{
if (v___y_5268_ == 0)
{
lean_object* v___x_5269_; 
lean_inc_ref(v_arg_5265_);
lean_dec_ref_known(v_x_5262_, 2);
v___x_5269_ = l_Lean_Expr_app___override(v___x_5266_, v_arg_5265_);
return v___x_5269_;
}
else
{
lean_dec_ref(v___x_5266_);
return v_x_5262_;
}
}
}
else
{
lean_dec_ref(v_x_5262_);
lean_inc_ref(v_x_5263_);
return v_x_5263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5275_, lean_object* v_x_5276_){
_start:
{
lean_object* v_res_5277_; 
v_res_5277_ = l_Lean_Expr_updateFn(v_x_5275_, v_x_5276_);
lean_dec_ref(v_x_5276_);
return v_res_5277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5278_){
_start:
{
if (lean_obj_tag(v_e_5278_) == 6)
{
lean_object* v_binderName_5279_; lean_object* v_binderType_5280_; lean_object* v_body_5281_; uint8_t v_binderInfo_5282_; lean_object* v_b_x27_5283_; uint8_t v___y_5285_; uint8_t v___y_5290_; 
v_binderName_5279_ = lean_ctor_get(v_e_5278_, 0);
v_binderType_5280_ = lean_ctor_get(v_e_5278_, 1);
v_body_5281_ = lean_ctor_get(v_e_5278_, 2);
v_binderInfo_5282_ = lean_ctor_get_uint8(v_e_5278_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5281_);
v_b_x27_5283_ = l_Lean_Expr_eta(v_body_5281_);
if (lean_obj_tag(v_b_x27_5283_) == 5)
{
lean_object* v_arg_5300_; 
v_arg_5300_ = lean_ctor_get(v_b_x27_5283_, 1);
lean_inc_ref(v_arg_5300_);
if (lean_obj_tag(v_arg_5300_) == 0)
{
lean_object* v_fn_5301_; lean_object* v_deBruijnIndex_5302_; lean_object* v___x_5303_; uint8_t v___x_5304_; 
v_fn_5301_ = lean_ctor_get(v_b_x27_5283_, 0);
lean_inc_ref(v_fn_5301_);
v_deBruijnIndex_5302_ = lean_ctor_get(v_arg_5300_, 0);
lean_inc(v_deBruijnIndex_5302_);
lean_dec_ref_known(v_arg_5300_, 1);
v___x_5303_ = lean_unsigned_to_nat(0u);
v___x_5304_ = lean_nat_dec_eq(v_deBruijnIndex_5302_, v___x_5303_);
lean_dec(v_deBruijnIndex_5302_);
if (v___x_5304_ == 0)
{
lean_dec_ref(v_fn_5301_);
goto v___jp_5294_;
}
else
{
uint8_t v___x_5305_; uint8_t v___x_5306_; 
v___x_5305_ = lean_expr_has_loose_bvar(v_fn_5301_, v___x_5303_);
v___x_5306_ = lean_bool_not(v___x_5305_);
if (v___x_5306_ == 0)
{
size_t v___x_5307_; uint8_t v___x_5308_; 
lean_dec_ref(v_fn_5301_);
v___x_5307_ = lean_ptr_addr(v_binderType_5280_);
v___x_5308_ = lean_usize_dec_eq(v___x_5307_, v___x_5307_);
if (v___x_5308_ == 0)
{
v___y_5285_ = v___x_5308_;
goto v___jp_5284_;
}
else
{
size_t v___x_5309_; size_t v___x_5310_; uint8_t v___x_5311_; 
v___x_5309_ = lean_ptr_addr(v_body_5281_);
v___x_5310_ = lean_ptr_addr(v_b_x27_5283_);
v___x_5311_ = lean_usize_dec_eq(v___x_5309_, v___x_5310_);
v___y_5285_ = v___x_5311_;
goto v___jp_5284_;
}
}
else
{
lean_object* v___x_5312_; lean_object* v___x_5313_; 
lean_dec_ref_known(v_b_x27_5283_, 2);
lean_dec_ref_known(v_e_5278_, 3);
v___x_5312_ = lean_unsigned_to_nat(1u);
v___x_5313_ = lean_expr_lower_loose_bvars(v_fn_5301_, v___x_5312_, v___x_5312_);
lean_dec_ref(v_fn_5301_);
return v___x_5313_;
}
}
}
else
{
lean_dec_ref(v_arg_5300_);
goto v___jp_5294_;
}
}
else
{
goto v___jp_5294_;
}
v___jp_5284_:
{
if (v___y_5285_ == 0)
{
lean_object* v___x_5286_; 
lean_inc_ref(v_binderType_5280_);
lean_inc(v_binderName_5279_);
lean_dec_ref_known(v_e_5278_, 3);
v___x_5286_ = l_Lean_Expr_lam___override(v_binderName_5279_, v_binderType_5280_, v_b_x27_5283_, v_binderInfo_5282_);
return v___x_5286_;
}
else
{
uint8_t v___x_5287_; 
v___x_5287_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5282_, v_binderInfo_5282_);
if (v___x_5287_ == 0)
{
lean_object* v___x_5288_; 
lean_inc_ref(v_binderType_5280_);
lean_inc(v_binderName_5279_);
lean_dec_ref_known(v_e_5278_, 3);
v___x_5288_ = l_Lean_Expr_lam___override(v_binderName_5279_, v_binderType_5280_, v_b_x27_5283_, v_binderInfo_5282_);
return v___x_5288_;
}
else
{
lean_dec_ref(v_b_x27_5283_);
return v_e_5278_;
}
}
}
v___jp_5289_:
{
if (v___y_5290_ == 0)
{
lean_object* v___x_5291_; 
lean_inc_ref(v_binderType_5280_);
lean_inc(v_binderName_5279_);
lean_dec_ref_known(v_e_5278_, 3);
v___x_5291_ = l_Lean_Expr_lam___override(v_binderName_5279_, v_binderType_5280_, v_b_x27_5283_, v_binderInfo_5282_);
return v___x_5291_;
}
else
{
uint8_t v___x_5292_; 
v___x_5292_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5282_, v_binderInfo_5282_);
if (v___x_5292_ == 0)
{
lean_object* v___x_5293_; 
lean_inc_ref(v_binderType_5280_);
lean_inc(v_binderName_5279_);
lean_dec_ref_known(v_e_5278_, 3);
v___x_5293_ = l_Lean_Expr_lam___override(v_binderName_5279_, v_binderType_5280_, v_b_x27_5283_, v_binderInfo_5282_);
return v___x_5293_;
}
else
{
lean_dec_ref(v_b_x27_5283_);
return v_e_5278_;
}
}
}
v___jp_5294_:
{
size_t v___x_5295_; uint8_t v___x_5296_; 
v___x_5295_ = lean_ptr_addr(v_binderType_5280_);
v___x_5296_ = lean_usize_dec_eq(v___x_5295_, v___x_5295_);
if (v___x_5296_ == 0)
{
v___y_5290_ = v___x_5296_;
goto v___jp_5289_;
}
else
{
size_t v___x_5297_; size_t v___x_5298_; uint8_t v___x_5299_; 
v___x_5297_ = lean_ptr_addr(v_body_5281_);
v___x_5298_ = lean_ptr_addr(v_b_x27_5283_);
v___x_5299_ = lean_usize_dec_eq(v___x_5297_, v___x_5298_);
v___y_5290_ = v___x_5299_;
goto v___jp_5289_;
}
}
}
else
{
return v_e_5278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5314_, lean_object* v_optionName_5315_, lean_object* v_inst_5316_, lean_object* v_val_5317_){
_start:
{
lean_object* v_toDataValue_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; 
v_toDataValue_5318_ = lean_ctor_get(v_inst_5316_, 0);
lean_inc_ref(v_toDataValue_5318_);
lean_dec_ref(v_inst_5316_);
v___x_5319_ = lean_box(0);
v___x_5320_ = lean_apply_1(v_toDataValue_5318_, v_val_5317_);
v___x_5321_ = l_Lean_KVMap_insert(v___x_5319_, v_optionName_5315_, v___x_5320_);
v___x_5322_ = l_Lean_Expr_mdata___override(v___x_5321_, v_e_5314_);
return v___x_5322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5323_, lean_object* v_e_5324_, lean_object* v_optionName_5325_, lean_object* v_inst_5326_, lean_object* v_val_5327_){
_start:
{
lean_object* v___x_5328_; 
v___x_5328_ = l_Lean_Expr_setOption___redArg(v_e_5324_, v_optionName_5325_, v_inst_5326_, v_val_5327_);
return v___x_5328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5329_, lean_object* v_optionName_5330_, uint8_t v_val_5331_){
_start:
{
lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; 
v___x_5332_ = lean_box(0);
v___x_5333_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5333_, 0, v_val_5331_);
v___x_5334_ = l_Lean_KVMap_insert(v___x_5332_, v_optionName_5330_, v___x_5333_);
v___x_5335_ = l_Lean_Expr_mdata___override(v___x_5334_, v_e_5329_);
return v___x_5335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5336_, lean_object* v_optionName_5337_, lean_object* v_val_5338_){
_start:
{
uint8_t v_val_boxed_5339_; lean_object* v_res_5340_; 
v_val_boxed_5339_ = lean_unbox(v_val_5338_);
v_res_5340_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5336_, v_optionName_5337_, v_val_boxed_5339_);
return v_res_5340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5346_, uint8_t v_flag_5347_){
_start:
{
lean_object* v___x_5348_; lean_object* v___x_5349_; 
v___x_5348_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5349_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5346_, v___x_5348_, v_flag_5347_);
return v___x_5349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5350_, lean_object* v_flag_5351_){
_start:
{
uint8_t v_flag_boxed_5352_; lean_object* v_res_5353_; 
v_flag_boxed_5352_ = lean_unbox(v_flag_5351_);
v_res_5353_ = l_Lean_Expr_setPPExplicit(v_e_5350_, v_flag_boxed_5352_);
return v_res_5353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5358_, uint8_t v_flag_5359_){
_start:
{
lean_object* v___x_5360_; lean_object* v___x_5361_; 
v___x_5360_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5361_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5358_, v___x_5360_, v_flag_5359_);
return v___x_5361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5362_, lean_object* v_flag_5363_){
_start:
{
uint8_t v_flag_boxed_5364_; lean_object* v_res_5365_; 
v_flag_boxed_5364_ = lean_unbox(v_flag_5363_);
v_res_5365_ = l_Lean_Expr_setPPUniverses(v_e_5362_, v_flag_boxed_5364_);
return v_res_5365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5370_, uint8_t v_flag_5371_){
_start:
{
lean_object* v___x_5372_; lean_object* v___x_5373_; 
v___x_5372_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5373_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5370_, v___x_5372_, v_flag_5371_);
return v___x_5373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5374_, lean_object* v_flag_5375_){
_start:
{
uint8_t v_flag_boxed_5376_; lean_object* v_res_5377_; 
v_flag_boxed_5376_ = lean_unbox(v_flag_5375_);
v_res_5377_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5374_, v_flag_boxed_5376_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5382_, uint8_t v_flag_5383_){
_start:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; 
v___x_5384_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5385_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5382_, v___x_5384_, v_flag_5383_);
return v___x_5385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5386_, lean_object* v_flag_5387_){
_start:
{
uint8_t v_flag_boxed_5388_; lean_object* v_res_5389_; 
v_flag_boxed_5388_ = lean_unbox(v_flag_5387_);
v_res_5389_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5386_, v_flag_boxed_5388_);
return v_res_5389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5394_, uint8_t v_flag_5395_){
_start:
{
lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5396_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5397_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5394_, v___x_5396_, v_flag_5395_);
return v___x_5397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5398_, lean_object* v_flag_5399_){
_start:
{
uint8_t v_flag_boxed_5400_; lean_object* v_res_5401_; 
v_flag_boxed_5400_ = lean_unbox(v_flag_5399_);
v_res_5401_ = l_Lean_Expr_setPPNumericTypes(v_e_5398_, v_flag_boxed_5400_);
return v_res_5401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5402_, size_t v_i_5403_, lean_object* v_bs_5404_){
_start:
{
uint8_t v___x_5405_; 
v___x_5405_ = lean_usize_dec_lt(v_i_5403_, v_sz_5402_);
if (v___x_5405_ == 0)
{
return v_bs_5404_;
}
else
{
uint8_t v___x_5406_; lean_object* v_v_5407_; lean_object* v___x_5408_; lean_object* v_bs_x27_5409_; lean_object* v___x_5410_; size_t v___x_5411_; size_t v___x_5412_; lean_object* v___x_5413_; 
v___x_5406_ = 0;
v_v_5407_ = lean_array_uget(v_bs_5404_, v_i_5403_);
v___x_5408_ = lean_unsigned_to_nat(0u);
v_bs_x27_5409_ = lean_array_uset(v_bs_5404_, v_i_5403_, v___x_5408_);
v___x_5410_ = l_Lean_Expr_setPPExplicit(v_v_5407_, v___x_5406_);
v___x_5411_ = ((size_t)1ULL);
v___x_5412_ = lean_usize_add(v_i_5403_, v___x_5411_);
v___x_5413_ = lean_array_uset(v_bs_x27_5409_, v_i_5403_, v___x_5410_);
v_i_5403_ = v___x_5412_;
v_bs_5404_ = v___x_5413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5415_, lean_object* v_i_5416_, lean_object* v_bs_5417_){
_start:
{
size_t v_sz_boxed_5418_; size_t v_i_boxed_5419_; lean_object* v_res_5420_; 
v_sz_boxed_5418_ = lean_unbox_usize(v_sz_5415_);
lean_dec(v_sz_5415_);
v_i_boxed_5419_ = lean_unbox_usize(v_i_5416_);
lean_dec(v_i_5416_);
v_res_5420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5418_, v_i_boxed_5419_, v_bs_5417_);
return v_res_5420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5421_){
_start:
{
if (lean_obj_tag(v_e_5421_) == 5)
{
lean_object* v___x_5422_; uint8_t v___x_5423_; lean_object* v_f_5424_; lean_object* v_dummy_5425_; lean_object* v_nargs_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; size_t v_sz_5431_; size_t v___x_5432_; lean_object* v_args_5433_; lean_object* v___x_5434_; uint8_t v___x_5435_; lean_object* v___x_5436_; 
v___x_5422_ = l_Lean_Expr_getAppFn(v_e_5421_);
v___x_5423_ = 0;
v_f_5424_ = l_Lean_Expr_setPPExplicit(v___x_5422_, v___x_5423_);
v_dummy_5425_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5426_ = l_Lean_Expr_getAppNumArgs(v_e_5421_);
lean_inc(v_nargs_5426_);
v___x_5427_ = lean_mk_array(v_nargs_5426_, v_dummy_5425_);
v___x_5428_ = lean_unsigned_to_nat(1u);
v___x_5429_ = lean_nat_sub(v_nargs_5426_, v___x_5428_);
lean_dec(v_nargs_5426_);
v___x_5430_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5421_, v___x_5427_, v___x_5429_);
v_sz_5431_ = lean_array_size(v___x_5430_);
v___x_5432_ = ((size_t)0ULL);
v_args_5433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5431_, v___x_5432_, v___x_5430_);
v___x_5434_ = l_Lean_mkAppN(v_f_5424_, v_args_5433_);
lean_dec_ref(v_args_5433_);
v___x_5435_ = 1;
v___x_5436_ = l_Lean_Expr_setPPExplicit(v___x_5434_, v___x_5435_);
return v___x_5436_;
}
else
{
return v_e_5421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5437_, size_t v_i_5438_, lean_object* v_bs_5439_){
_start:
{
uint8_t v___x_5440_; 
v___x_5440_ = lean_usize_dec_lt(v_i_5438_, v_sz_5437_);
if (v___x_5440_ == 0)
{
return v_bs_5439_;
}
else
{
lean_object* v_v_5441_; lean_object* v___x_5442_; lean_object* v_bs_x27_5443_; lean_object* v___y_5445_; uint8_t v___x_5450_; 
v_v_5441_ = lean_array_uget(v_bs_5439_, v_i_5438_);
v___x_5442_ = lean_unsigned_to_nat(0u);
v_bs_x27_5443_ = lean_array_uset(v_bs_5439_, v_i_5438_, v___x_5442_);
v___x_5450_ = l_Lean_Expr_hasMVar(v_v_5441_);
if (v___x_5450_ == 0)
{
lean_object* v___x_5451_; 
v___x_5451_ = l_Lean_Expr_setPPExplicit(v_v_5441_, v___x_5450_);
v___y_5445_ = v___x_5451_;
goto v___jp_5444_;
}
else
{
v___y_5445_ = v_v_5441_;
goto v___jp_5444_;
}
v___jp_5444_:
{
size_t v___x_5446_; size_t v___x_5447_; lean_object* v___x_5448_; 
v___x_5446_ = ((size_t)1ULL);
v___x_5447_ = lean_usize_add(v_i_5438_, v___x_5446_);
v___x_5448_ = lean_array_uset(v_bs_x27_5443_, v_i_5438_, v___y_5445_);
v_i_5438_ = v___x_5447_;
v_bs_5439_ = v___x_5448_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5452_, lean_object* v_i_5453_, lean_object* v_bs_5454_){
_start:
{
size_t v_sz_boxed_5455_; size_t v_i_boxed_5456_; lean_object* v_res_5457_; 
v_sz_boxed_5455_ = lean_unbox_usize(v_sz_5452_);
lean_dec(v_sz_5452_);
v_i_boxed_5456_ = lean_unbox_usize(v_i_5453_);
lean_dec(v_i_5453_);
v_res_5457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5455_, v_i_boxed_5456_, v_bs_5454_);
return v_res_5457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5458_){
_start:
{
if (lean_obj_tag(v_e_5458_) == 5)
{
lean_object* v___x_5459_; uint8_t v___x_5460_; lean_object* v_f_5461_; lean_object* v_dummy_5462_; lean_object* v_nargs_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; size_t v_sz_5468_; size_t v___x_5469_; lean_object* v_args_5470_; lean_object* v___x_5471_; uint8_t v___x_5472_; lean_object* v___x_5473_; 
v___x_5459_ = l_Lean_Expr_getAppFn(v_e_5458_);
v___x_5460_ = 0;
v_f_5461_ = l_Lean_Expr_setPPExplicit(v___x_5459_, v___x_5460_);
v_dummy_5462_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5463_ = l_Lean_Expr_getAppNumArgs(v_e_5458_);
lean_inc(v_nargs_5463_);
v___x_5464_ = lean_mk_array(v_nargs_5463_, v_dummy_5462_);
v___x_5465_ = lean_unsigned_to_nat(1u);
v___x_5466_ = lean_nat_sub(v_nargs_5463_, v___x_5465_);
lean_dec(v_nargs_5463_);
v___x_5467_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5458_, v___x_5464_, v___x_5466_);
v_sz_5468_ = lean_array_size(v___x_5467_);
v___x_5469_ = ((size_t)0ULL);
v_args_5470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5468_, v___x_5469_, v___x_5467_);
v___x_5471_ = l_Lean_mkAppN(v_f_5461_, v_args_5470_);
lean_dec_ref(v_args_5470_);
v___x_5472_ = 1;
v___x_5473_ = l_Lean_Expr_setPPExplicit(v___x_5471_, v___x_5472_);
return v___x_5473_;
}
else
{
return v_e_5458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5474_, lean_object* v_body_5475_, lean_object* v_x_5476_){
_start:
{
lean_object* v___x_5477_; 
v___x_5477_ = lean_apply_1(v_f_5474_, v_body_5475_);
return v___x_5477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5478_, lean_object* v_binderType_5479_, lean_object* v_x_5480_){
_start:
{
lean_object* v___x_5481_; 
v___x_5481_ = lean_apply_1(v_f_5478_, v_binderType_5479_);
return v___x_5481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5482_, lean_object* v_value_5483_, lean_object* v_x_5484_){
_start:
{
lean_object* v___x_5485_; 
v___x_5485_ = lean_apply_1(v_f_5482_, v_value_5483_);
return v___x_5485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5486_, lean_object* v_type_5487_, lean_object* v_x_5488_){
_start:
{
lean_object* v___x_5489_; 
v___x_5489_ = lean_apply_1(v_f_5486_, v_type_5487_);
return v___x_5489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5490_, lean_object* v_arg_5491_, lean_object* v_x_5492_){
_start:
{
lean_object* v___x_5493_; 
v___x_5493_ = lean_apply_1(v_f_5490_, v_arg_5491_);
return v___x_5493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5494_, lean_object* v_fn_5495_, lean_object* v_x_5496_){
_start:
{
lean_object* v___x_5497_; 
v___x_5497_ = lean_apply_1(v_f_5494_, v_fn_5495_);
return v___x_5497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5498_, lean_object* v_f_5499_, lean_object* v_x_5500_){
_start:
{
switch(lean_obj_tag(v_x_5500_))
{
case 7:
{
lean_object* v_toPure_5501_; lean_object* v_toSeq_5502_; lean_object* v_binderType_5503_; lean_object* v_body_5504_; lean_object* v___f_5505_; lean_object* v___f_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; 
v_toPure_5501_ = lean_ctor_get(v_inst_5498_, 1);
lean_inc(v_toPure_5501_);
v_toSeq_5502_ = lean_ctor_get(v_inst_5498_, 2);
lean_inc_n(v_toSeq_5502_, 2);
lean_dec_ref(v_inst_5498_);
v_binderType_5503_ = lean_ctor_get(v_x_5500_, 1);
v_body_5504_ = lean_ctor_get(v_x_5500_, 2);
lean_inc_ref(v_body_5504_);
lean_inc(v_f_5499_);
v___f_5505_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5505_, 0, v_f_5499_);
lean_closure_set(v___f_5505_, 1, v_body_5504_);
lean_inc_ref(v_binderType_5503_);
v___f_5506_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5506_, 0, v_f_5499_);
lean_closure_set(v___f_5506_, 1, v_binderType_5503_);
v___x_5507_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5507_, 0, v_x_5500_);
v___x_5508_ = lean_apply_2(v_toPure_5501_, lean_box(0), v___x_5507_);
v___x_5509_ = lean_apply_4(v_toSeq_5502_, lean_box(0), lean_box(0), v___x_5508_, v___f_5506_);
v___x_5510_ = lean_apply_4(v_toSeq_5502_, lean_box(0), lean_box(0), v___x_5509_, v___f_5505_);
return v___x_5510_;
}
case 6:
{
lean_object* v_toPure_5511_; lean_object* v_toSeq_5512_; lean_object* v_binderType_5513_; lean_object* v_body_5514_; lean_object* v___f_5515_; lean_object* v___f_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; 
v_toPure_5511_ = lean_ctor_get(v_inst_5498_, 1);
lean_inc(v_toPure_5511_);
v_toSeq_5512_ = lean_ctor_get(v_inst_5498_, 2);
lean_inc_n(v_toSeq_5512_, 2);
lean_dec_ref(v_inst_5498_);
v_binderType_5513_ = lean_ctor_get(v_x_5500_, 1);
v_body_5514_ = lean_ctor_get(v_x_5500_, 2);
lean_inc_ref(v_body_5514_);
lean_inc(v_f_5499_);
v___f_5515_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5515_, 0, v_f_5499_);
lean_closure_set(v___f_5515_, 1, v_body_5514_);
lean_inc_ref(v_binderType_5513_);
v___f_5516_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5516_, 0, v_f_5499_);
lean_closure_set(v___f_5516_, 1, v_binderType_5513_);
v___x_5517_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5517_, 0, v_x_5500_);
v___x_5518_ = lean_apply_2(v_toPure_5511_, lean_box(0), v___x_5517_);
v___x_5519_ = lean_apply_4(v_toSeq_5512_, lean_box(0), lean_box(0), v___x_5518_, v___f_5516_);
v___x_5520_ = lean_apply_4(v_toSeq_5512_, lean_box(0), lean_box(0), v___x_5519_, v___f_5515_);
return v___x_5520_;
}
case 10:
{
lean_object* v_toFunctor_5521_; lean_object* v_expr_5522_; lean_object* v_map_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; 
v_toFunctor_5521_ = lean_ctor_get(v_inst_5498_, 0);
lean_inc_ref(v_toFunctor_5521_);
lean_dec_ref(v_inst_5498_);
v_expr_5522_ = lean_ctor_get(v_x_5500_, 1);
lean_inc_ref(v_expr_5522_);
v_map_5523_ = lean_ctor_get(v_toFunctor_5521_, 0);
lean_inc(v_map_5523_);
lean_dec_ref(v_toFunctor_5521_);
v___x_5524_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5524_, 0, v_x_5500_);
v___x_5525_ = lean_apply_1(v_f_5499_, v_expr_5522_);
v___x_5526_ = lean_apply_4(v_map_5523_, lean_box(0), lean_box(0), v___x_5524_, v___x_5525_);
return v___x_5526_;
}
case 8:
{
lean_object* v_toPure_5527_; lean_object* v_toSeq_5528_; lean_object* v_type_5529_; lean_object* v_value_5530_; lean_object* v_body_5531_; lean_object* v___f_5532_; lean_object* v___f_5533_; lean_object* v___f_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; 
v_toPure_5527_ = lean_ctor_get(v_inst_5498_, 1);
lean_inc(v_toPure_5527_);
v_toSeq_5528_ = lean_ctor_get(v_inst_5498_, 2);
lean_inc_n(v_toSeq_5528_, 3);
lean_dec_ref(v_inst_5498_);
v_type_5529_ = lean_ctor_get(v_x_5500_, 1);
v_value_5530_ = lean_ctor_get(v_x_5500_, 2);
v_body_5531_ = lean_ctor_get(v_x_5500_, 3);
lean_inc_ref(v_body_5531_);
lean_inc_n(v_f_5499_, 2);
v___f_5532_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5532_, 0, v_f_5499_);
lean_closure_set(v___f_5532_, 1, v_body_5531_);
lean_inc_ref(v_value_5530_);
v___f_5533_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5533_, 0, v_f_5499_);
lean_closure_set(v___f_5533_, 1, v_value_5530_);
lean_inc_ref(v_type_5529_);
v___f_5534_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5534_, 0, v_f_5499_);
lean_closure_set(v___f_5534_, 1, v_type_5529_);
v___x_5535_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5535_, 0, v_x_5500_);
v___x_5536_ = lean_apply_2(v_toPure_5527_, lean_box(0), v___x_5535_);
v___x_5537_ = lean_apply_4(v_toSeq_5528_, lean_box(0), lean_box(0), v___x_5536_, v___f_5534_);
v___x_5538_ = lean_apply_4(v_toSeq_5528_, lean_box(0), lean_box(0), v___x_5537_, v___f_5533_);
v___x_5539_ = lean_apply_4(v_toSeq_5528_, lean_box(0), lean_box(0), v___x_5538_, v___f_5532_);
return v___x_5539_;
}
case 5:
{
lean_object* v_toPure_5540_; lean_object* v_toSeq_5541_; lean_object* v_fn_5542_; lean_object* v_arg_5543_; lean_object* v___f_5544_; lean_object* v___f_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; 
v_toPure_5540_ = lean_ctor_get(v_inst_5498_, 1);
lean_inc(v_toPure_5540_);
v_toSeq_5541_ = lean_ctor_get(v_inst_5498_, 2);
lean_inc_n(v_toSeq_5541_, 2);
lean_dec_ref(v_inst_5498_);
v_fn_5542_ = lean_ctor_get(v_x_5500_, 0);
v_arg_5543_ = lean_ctor_get(v_x_5500_, 1);
lean_inc_ref(v_arg_5543_);
lean_inc(v_f_5499_);
v___f_5544_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5544_, 0, v_f_5499_);
lean_closure_set(v___f_5544_, 1, v_arg_5543_);
lean_inc_ref(v_fn_5542_);
v___f_5545_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5545_, 0, v_f_5499_);
lean_closure_set(v___f_5545_, 1, v_fn_5542_);
v___x_5546_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5546_, 0, v_x_5500_);
v___x_5547_ = lean_apply_2(v_toPure_5540_, lean_box(0), v___x_5546_);
v___x_5548_ = lean_apply_4(v_toSeq_5541_, lean_box(0), lean_box(0), v___x_5547_, v___f_5545_);
v___x_5549_ = lean_apply_4(v_toSeq_5541_, lean_box(0), lean_box(0), v___x_5548_, v___f_5544_);
return v___x_5549_;
}
case 11:
{
lean_object* v_toFunctor_5550_; lean_object* v_struct_5551_; lean_object* v_map_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; 
v_toFunctor_5550_ = lean_ctor_get(v_inst_5498_, 0);
lean_inc_ref(v_toFunctor_5550_);
lean_dec_ref(v_inst_5498_);
v_struct_5551_ = lean_ctor_get(v_x_5500_, 2);
lean_inc_ref(v_struct_5551_);
v_map_5552_ = lean_ctor_get(v_toFunctor_5550_, 0);
lean_inc(v_map_5552_);
lean_dec_ref(v_toFunctor_5550_);
v___x_5553_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5553_, 0, v_x_5500_);
v___x_5554_ = lean_apply_1(v_f_5499_, v_struct_5551_);
v___x_5555_ = lean_apply_4(v_map_5552_, lean_box(0), lean_box(0), v___x_5553_, v___x_5554_);
return v___x_5555_;
}
default: 
{
lean_object* v_toPure_5556_; lean_object* v___x_5557_; 
lean_dec(v_f_5499_);
v_toPure_5556_ = lean_ctor_get(v_inst_5498_, 1);
lean_inc(v_toPure_5556_);
lean_dec_ref(v_inst_5498_);
v___x_5557_ = lean_apply_2(v_toPure_5556_, lean_box(0), v_x_5500_);
return v___x_5557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5558_, lean_object* v_inst_5559_, lean_object* v_f_5560_, lean_object* v_x_5561_){
_start:
{
lean_object* v___x_5562_; 
v___x_5562_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5559_, v_f_5560_, v_x_5561_);
return v___x_5562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5563_){
_start:
{
lean_object* v_snd_5564_; 
v_snd_5564_ = lean_ctor_get(v_self_5563_, 1);
lean_inc(v_snd_5564_);
return v_snd_5564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5565_){
_start:
{
lean_object* v_res_5566_; 
v_res_5566_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5565_);
lean_dec_ref(v_self_5565_);
return v_res_5566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5567_, lean_object* v_snd_5568_){
_start:
{
lean_object* v___x_5569_; 
v___x_5569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5569_, 0, v_e_x27_5567_);
lean_ctor_set(v___x_5569_, 1, v_snd_5568_);
return v___x_5569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5570_, lean_object* v_map_5571_, lean_object* v_e_x27_5572_, lean_object* v_a_5573_){
_start:
{
lean_object* v___f_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; 
lean_inc_ref(v_e_x27_5572_);
v___f_5574_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5574_, 0, v_e_x27_5572_);
v___x_5575_ = lean_apply_2(v_f_5570_, v_a_5573_, v_e_x27_5572_);
v___x_5576_ = lean_apply_4(v_map_5571_, lean_box(0), lean_box(0), v___f_5574_, v___x_5575_);
return v___x_5576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5578_, lean_object* v_f_5579_, lean_object* v_init_5580_, lean_object* v_e_5581_){
_start:
{
lean_object* v_toApplicative_5582_; lean_object* v_toFunctor_5583_; lean_object* v___x_5585_; uint8_t v_isShared_5586_; uint8_t v_isSharedCheck_5610_; 
v_toApplicative_5582_ = lean_ctor_get(v_inst_5578_, 0);
lean_inc_ref(v_toApplicative_5582_);
v_toFunctor_5583_ = lean_ctor_get(v_toApplicative_5582_, 0);
v_isSharedCheck_5610_ = !lean_is_exclusive(v_toApplicative_5582_);
if (v_isSharedCheck_5610_ == 0)
{
lean_object* v_unused_5611_; lean_object* v_unused_5612_; lean_object* v_unused_5613_; lean_object* v_unused_5614_; 
v_unused_5611_ = lean_ctor_get(v_toApplicative_5582_, 4);
lean_dec(v_unused_5611_);
v_unused_5612_ = lean_ctor_get(v_toApplicative_5582_, 3);
lean_dec(v_unused_5612_);
v_unused_5613_ = lean_ctor_get(v_toApplicative_5582_, 2);
lean_dec(v_unused_5613_);
v_unused_5614_ = lean_ctor_get(v_toApplicative_5582_, 1);
lean_dec(v_unused_5614_);
v___x_5585_ = v_toApplicative_5582_;
v_isShared_5586_ = v_isSharedCheck_5610_;
goto v_resetjp_5584_;
}
else
{
lean_inc(v_toFunctor_5583_);
lean_dec(v_toApplicative_5582_);
v___x_5585_ = lean_box(0);
v_isShared_5586_ = v_isSharedCheck_5610_;
goto v_resetjp_5584_;
}
v_resetjp_5584_:
{
lean_object* v_map_5587_; lean_object* v___x_5589_; uint8_t v_isShared_5590_; uint8_t v_isSharedCheck_5608_; 
v_map_5587_ = lean_ctor_get(v_toFunctor_5583_, 0);
v_isSharedCheck_5608_ = !lean_is_exclusive(v_toFunctor_5583_);
if (v_isSharedCheck_5608_ == 0)
{
lean_object* v_unused_5609_; 
v_unused_5609_ = lean_ctor_get(v_toFunctor_5583_, 1);
lean_dec(v_unused_5609_);
v___x_5589_ = v_toFunctor_5583_;
v_isShared_5590_ = v_isSharedCheck_5608_;
goto v_resetjp_5588_;
}
else
{
lean_inc(v_map_5587_);
lean_dec(v_toFunctor_5583_);
v___x_5589_ = lean_box(0);
v_isShared_5590_ = v_isSharedCheck_5608_;
goto v_resetjp_5588_;
}
v_resetjp_5588_:
{
lean_object* v___f_5591_; lean_object* v___f_5592_; lean_object* v___f_5593_; lean_object* v___f_5594_; lean_object* v___f_5595_; lean_object* v___f_5596_; lean_object* v___x_5597_; lean_object* v___x_5599_; 
v___f_5591_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5587_);
v___f_5592_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5592_, 0, v_f_5579_);
lean_closure_set(v___f_5592_, 1, v_map_5587_);
lean_inc_ref_n(v_inst_5578_, 5);
v___f_5593_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5593_, 0, v_inst_5578_);
v___f_5594_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5594_, 0, v_inst_5578_);
v___f_5595_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5595_, 0, v_inst_5578_);
v___f_5596_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5596_, 0, v_inst_5578_);
v___x_5597_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5597_, 0, lean_box(0));
lean_closure_set(v___x_5597_, 1, lean_box(0));
lean_closure_set(v___x_5597_, 2, v_inst_5578_);
if (v_isShared_5590_ == 0)
{
lean_ctor_set(v___x_5589_, 1, v___f_5593_);
lean_ctor_set(v___x_5589_, 0, v___x_5597_);
v___x_5599_ = v___x_5589_;
goto v_reusejp_5598_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v___x_5597_);
lean_ctor_set(v_reuseFailAlloc_5607_, 1, v___f_5593_);
v___x_5599_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5598_;
}
v_reusejp_5598_:
{
lean_object* v___x_5600_; lean_object* v___x_5602_; 
v___x_5600_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5600_, 0, lean_box(0));
lean_closure_set(v___x_5600_, 1, lean_box(0));
lean_closure_set(v___x_5600_, 2, v_inst_5578_);
if (v_isShared_5586_ == 0)
{
lean_ctor_set(v___x_5585_, 4, v___f_5596_);
lean_ctor_set(v___x_5585_, 3, v___f_5595_);
lean_ctor_set(v___x_5585_, 2, v___f_5594_);
lean_ctor_set(v___x_5585_, 1, v___x_5600_);
lean_ctor_set(v___x_5585_, 0, v___x_5599_);
v___x_5602_ = v___x_5585_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v___x_5599_);
lean_ctor_set(v_reuseFailAlloc_5606_, 1, v___x_5600_);
lean_ctor_set(v_reuseFailAlloc_5606_, 2, v___f_5594_);
lean_ctor_set(v_reuseFailAlloc_5606_, 3, v___f_5595_);
lean_ctor_set(v_reuseFailAlloc_5606_, 4, v___f_5596_);
v___x_5602_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
lean_object* v___x_18__overap_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; 
v___x_18__overap_5603_ = l_Lean_Expr_traverseChildren___redArg(v___x_5602_, v___f_5592_, v_e_5581_);
v___x_5604_ = lean_apply_1(v___x_18__overap_5603_, v_init_5580_);
v___x_5605_ = lean_apply_4(v_map_5587_, lean_box(0), lean_box(0), v___f_5591_, v___x_5604_);
return v___x_5605_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5615_, lean_object* v_m_5616_, lean_object* v_inst_5617_, lean_object* v_f_5618_, lean_object* v_init_5619_, lean_object* v_e_5620_){
_start:
{
lean_object* v___x_5621_; 
v___x_5621_ = l_Lean_Expr_foldlM___redArg(v_inst_5617_, v_f_5618_, v_init_5619_, v_e_5620_);
return v___x_5621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5622_){
_start:
{
lean_object* v_d_5624_; lean_object* v_b_5625_; 
switch(lean_obj_tag(v_x_5622_))
{
case 5:
{
lean_object* v_fn_5631_; lean_object* v_arg_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; 
v_fn_5631_ = lean_ctor_get(v_x_5622_, 0);
v_arg_5632_ = lean_ctor_get(v_x_5622_, 1);
v___x_5633_ = lean_unsigned_to_nat(1u);
v___x_5634_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5631_);
v___x_5635_ = lean_nat_add(v___x_5633_, v___x_5634_);
lean_dec(v___x_5634_);
v___x_5636_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5632_);
v___x_5637_ = lean_nat_add(v___x_5635_, v___x_5636_);
lean_dec(v___x_5636_);
lean_dec(v___x_5635_);
return v___x_5637_;
}
case 6:
{
lean_object* v_binderType_5638_; lean_object* v_body_5639_; 
v_binderType_5638_ = lean_ctor_get(v_x_5622_, 1);
v_body_5639_ = lean_ctor_get(v_x_5622_, 2);
v_d_5624_ = v_binderType_5638_;
v_b_5625_ = v_body_5639_;
goto v___jp_5623_;
}
case 7:
{
lean_object* v_binderType_5640_; lean_object* v_body_5641_; 
v_binderType_5640_ = lean_ctor_get(v_x_5622_, 1);
v_body_5641_ = lean_ctor_get(v_x_5622_, 2);
v_d_5624_ = v_binderType_5640_;
v_b_5625_ = v_body_5641_;
goto v___jp_5623_;
}
case 8:
{
lean_object* v_type_5642_; lean_object* v_value_5643_; lean_object* v_body_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; 
v_type_5642_ = lean_ctor_get(v_x_5622_, 1);
v_value_5643_ = lean_ctor_get(v_x_5622_, 2);
v_body_5644_ = lean_ctor_get(v_x_5622_, 3);
v___x_5645_ = lean_unsigned_to_nat(1u);
v___x_5646_ = l_Lean_Expr_sizeWithoutSharing(v_type_5642_);
v___x_5647_ = lean_nat_add(v___x_5645_, v___x_5646_);
lean_dec(v___x_5646_);
v___x_5648_ = l_Lean_Expr_sizeWithoutSharing(v_value_5643_);
v___x_5649_ = lean_nat_add(v___x_5647_, v___x_5648_);
lean_dec(v___x_5648_);
lean_dec(v___x_5647_);
v___x_5650_ = l_Lean_Expr_sizeWithoutSharing(v_body_5644_);
v___x_5651_ = lean_nat_add(v___x_5649_, v___x_5650_);
lean_dec(v___x_5650_);
lean_dec(v___x_5649_);
return v___x_5651_;
}
case 10:
{
lean_object* v_expr_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; 
v_expr_5652_ = lean_ctor_get(v_x_5622_, 1);
v___x_5653_ = lean_unsigned_to_nat(1u);
v___x_5654_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5652_);
v___x_5655_ = lean_nat_add(v___x_5653_, v___x_5654_);
lean_dec(v___x_5654_);
return v___x_5655_;
}
case 11:
{
lean_object* v_struct_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; 
v_struct_5656_ = lean_ctor_get(v_x_5622_, 2);
v___x_5657_ = lean_unsigned_to_nat(1u);
v___x_5658_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5656_);
v___x_5659_ = lean_nat_add(v___x_5657_, v___x_5658_);
lean_dec(v___x_5658_);
return v___x_5659_;
}
default: 
{
lean_object* v___x_5660_; 
v___x_5660_ = lean_unsigned_to_nat(1u);
return v___x_5660_;
}
}
v___jp_5623_:
{
lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; 
v___x_5626_ = lean_unsigned_to_nat(1u);
v___x_5627_ = l_Lean_Expr_sizeWithoutSharing(v_d_5624_);
v___x_5628_ = lean_nat_add(v___x_5626_, v___x_5627_);
lean_dec(v___x_5627_);
v___x_5629_ = l_Lean_Expr_sizeWithoutSharing(v_b_5625_);
v___x_5630_ = lean_nat_add(v___x_5628_, v___x_5629_);
lean_dec(v___x_5629_);
lean_dec(v___x_5628_);
return v___x_5630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5661_){
_start:
{
lean_object* v_res_5662_; 
v_res_5662_ = l_Lean_Expr_sizeWithoutSharing(v_x_5661_);
lean_dec_ref(v_x_5661_);
return v_res_5662_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5665_, lean_object* v_e_5666_){
_start:
{
lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; 
v___x_5667_ = l_Lean_KVMap_empty;
v___x_5668_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5669_ = l_Lean_KVMap_insert(v___x_5667_, v_kind_5665_, v___x_5668_);
v___x_5670_ = l_Lean_Expr_mdata___override(v___x_5669_, v_e_5666_);
return v___x_5670_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5671_, lean_object* v_e_5672_){
_start:
{
if (lean_obj_tag(v_e_5672_) == 10)
{
lean_object* v_data_5673_; lean_object* v_expr_5674_; uint8_t v___y_5676_; lean_object* v___x_5679_; lean_object* v___x_5680_; uint8_t v___x_5681_; 
v_data_5673_ = lean_ctor_get(v_e_5672_, 0);
v_expr_5674_ = lean_ctor_get(v_e_5672_, 1);
v___x_5679_ = l_Lean_KVMap_size(v_data_5673_);
v___x_5680_ = lean_unsigned_to_nat(1u);
v___x_5681_ = lean_nat_dec_eq(v___x_5679_, v___x_5680_);
lean_dec(v___x_5679_);
if (v___x_5681_ == 0)
{
v___y_5676_ = v___x_5681_;
goto v___jp_5675_;
}
else
{
uint8_t v___x_5682_; uint8_t v___x_5683_; 
v___x_5682_ = 0;
v___x_5683_ = l_Lean_KVMap_getBool(v_data_5673_, v_kind_5671_, v___x_5682_);
v___y_5676_ = v___x_5683_;
goto v___jp_5675_;
}
v___jp_5675_:
{
if (v___y_5676_ == 0)
{
lean_object* v___x_5677_; 
v___x_5677_ = lean_box(0);
return v___x_5677_;
}
else
{
lean_object* v___x_5678_; 
lean_inc_ref(v_expr_5674_);
v___x_5678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5678_, 0, v_expr_5674_);
return v___x_5678_;
}
}
}
else
{
lean_object* v___x_5684_; 
v___x_5684_ = lean_box(0);
return v___x_5684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* v_kind_5685_, lean_object* v_e_5686_){
_start:
{
lean_object* v_res_5687_; 
v_res_5687_ = l_Lean_annotation_x3f(v_kind_5685_, v_e_5686_);
lean_dec_ref(v_e_5686_);
lean_dec(v_kind_5685_);
return v_res_5687_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* v_e_5691_){
_start:
{
lean_object* v___x_5692_; lean_object* v___x_5693_; 
v___x_5692_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5693_ = l_Lean_mkAnnotation(v___x_5692_, v_e_5691_);
return v___x_5693_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* v_e_5694_){
_start:
{
lean_object* v___x_5695_; lean_object* v___x_5696_; 
v___x_5695_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5696_ = l_Lean_annotation_x3f(v___x_5695_, v_e_5694_);
return v___x_5696_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* v_e_5697_){
_start:
{
lean_object* v_res_5698_; 
v_res_5698_ = l_Lean_inaccessible_x3f(v_e_5697_);
lean_dec_ref(v_e_5697_);
return v_res_5698_;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* v_p_5703_){
_start:
{
if (lean_obj_tag(v_p_5703_) == 10)
{
lean_object* v_data_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; 
v_data_5704_ = lean_ctor_get(v_p_5703_, 0);
v___x_5705_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5706_ = l_Lean_KVMap_find(v_data_5704_, v___x_5705_);
if (lean_obj_tag(v___x_5706_) == 1)
{
lean_object* v_val_5707_; lean_object* v___x_5709_; uint8_t v_isShared_5710_; uint8_t v_isSharedCheck_5718_; 
v_val_5707_ = lean_ctor_get(v___x_5706_, 0);
v_isSharedCheck_5718_ = !lean_is_exclusive(v___x_5706_);
if (v_isSharedCheck_5718_ == 0)
{
v___x_5709_ = v___x_5706_;
v_isShared_5710_ = v_isSharedCheck_5718_;
goto v_resetjp_5708_;
}
else
{
lean_inc(v_val_5707_);
lean_dec(v___x_5706_);
v___x_5709_ = lean_box(0);
v_isShared_5710_ = v_isSharedCheck_5718_;
goto v_resetjp_5708_;
}
v_resetjp_5708_:
{
if (lean_obj_tag(v_val_5707_) == 5)
{
lean_object* v_v_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5715_; 
v_v_5711_ = lean_ctor_get(v_val_5707_, 0);
lean_inc(v_v_5711_);
lean_dec_ref_known(v_val_5707_, 1);
v___x_5712_ = l_Lean_Expr_mdataExpr_x21(v_p_5703_);
v___x_5713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5713_, 0, v_v_5711_);
lean_ctor_set(v___x_5713_, 1, v___x_5712_);
if (v_isShared_5710_ == 0)
{
lean_ctor_set(v___x_5709_, 0, v___x_5713_);
v___x_5715_ = v___x_5709_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5716_; 
v_reuseFailAlloc_5716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5716_, 0, v___x_5713_);
v___x_5715_ = v_reuseFailAlloc_5716_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
return v___x_5715_;
}
}
else
{
lean_object* v___x_5717_; 
lean_del_object(v___x_5709_);
lean_dec(v_val_5707_);
v___x_5717_ = lean_box(0);
return v___x_5717_;
}
}
}
else
{
lean_object* v___x_5719_; 
lean_dec(v___x_5706_);
v___x_5719_ = lean_box(0);
return v___x_5719_;
}
}
else
{
lean_object* v___x_5720_; 
v___x_5720_ = lean_box(0);
return v___x_5720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* v_p_5721_){
_start:
{
lean_object* v_res_5722_; 
v_res_5722_ = l_Lean_patternWithRef_x3f(v_p_5721_);
lean_dec_ref(v_p_5721_);
return v_res_5722_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object* v_p_5723_){
_start:
{
lean_object* v___x_5724_; 
v___x_5724_ = l_Lean_patternWithRef_x3f(v_p_5723_);
if (lean_obj_tag(v___x_5724_) == 0)
{
uint8_t v___x_5725_; 
v___x_5725_ = 0;
return v___x_5725_;
}
else
{
uint8_t v___x_5726_; 
lean_dec_ref_known(v___x_5724_, 1);
v___x_5726_ = 1;
return v___x_5726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* v_p_5727_){
_start:
{
uint8_t v_res_5728_; lean_object* v_r_5729_; 
v_res_5728_ = l_Lean_isPatternWithRef(v_p_5727_);
lean_dec_ref(v_p_5727_);
v_r_5729_ = lean_box(v_res_5728_);
return v_r_5729_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* v_p_5730_, lean_object* v_stx_5731_){
_start:
{
lean_object* v___x_5732_; 
v___x_5732_ = l_Lean_patternWithRef_x3f(v_p_5730_);
if (lean_obj_tag(v___x_5732_) == 0)
{
lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; 
v___x_5733_ = l_Lean_KVMap_empty;
v___x_5734_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5735_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_5735_, 0, v_stx_5731_);
v___x_5736_ = l_Lean_KVMap_insert(v___x_5733_, v___x_5734_, v___x_5735_);
v___x_5737_ = l_Lean_Expr_mdata___override(v___x_5736_, v_p_5730_);
return v___x_5737_;
}
else
{
lean_dec_ref_known(v___x_5732_, 1);
lean_dec(v_stx_5731_);
return v_p_5730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* v_e_5738_){
_start:
{
lean_object* v___x_5739_; 
v___x_5739_ = l_Lean_inaccessible_x3f(v_e_5738_);
if (lean_obj_tag(v___x_5739_) == 1)
{
return v___x_5739_;
}
else
{
lean_object* v___x_5740_; 
lean_dec(v___x_5739_);
v___x_5740_ = l_Lean_patternWithRef_x3f(v_e_5738_);
if (lean_obj_tag(v___x_5740_) == 1)
{
lean_object* v_val_5741_; lean_object* v___x_5743_; uint8_t v_isShared_5744_; uint8_t v_isSharedCheck_5749_; 
v_val_5741_ = lean_ctor_get(v___x_5740_, 0);
v_isSharedCheck_5749_ = !lean_is_exclusive(v___x_5740_);
if (v_isSharedCheck_5749_ == 0)
{
v___x_5743_ = v___x_5740_;
v_isShared_5744_ = v_isSharedCheck_5749_;
goto v_resetjp_5742_;
}
else
{
lean_inc(v_val_5741_);
lean_dec(v___x_5740_);
v___x_5743_ = lean_box(0);
v_isShared_5744_ = v_isSharedCheck_5749_;
goto v_resetjp_5742_;
}
v_resetjp_5742_:
{
lean_object* v_snd_5745_; lean_object* v___x_5747_; 
v_snd_5745_ = lean_ctor_get(v_val_5741_, 1);
lean_inc(v_snd_5745_);
lean_dec(v_val_5741_);
if (v_isShared_5744_ == 0)
{
lean_ctor_set(v___x_5743_, 0, v_snd_5745_);
v___x_5747_ = v___x_5743_;
goto v_reusejp_5746_;
}
else
{
lean_object* v_reuseFailAlloc_5748_; 
v_reuseFailAlloc_5748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5748_, 0, v_snd_5745_);
v___x_5747_ = v_reuseFailAlloc_5748_;
goto v_reusejp_5746_;
}
v_reusejp_5746_:
{
return v___x_5747_;
}
}
}
else
{
lean_object* v___x_5750_; 
lean_dec(v___x_5740_);
v___x_5750_ = lean_box(0);
return v___x_5750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* v_e_5751_){
_start:
{
lean_object* v_res_5752_; 
v_res_5752_ = l_Lean_patternAnnotation_x3f(v_e_5751_);
lean_dec_ref(v_e_5751_);
return v_res_5752_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* v_e_5756_){
_start:
{
lean_object* v___x_5757_; lean_object* v___x_5758_; 
v___x_5757_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5758_ = l_Lean_mkAnnotation(v___x_5757_, v_e_5756_);
return v___x_5758_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* v_e_5762_){
_start:
{
lean_object* v___x_5763_; lean_object* v___x_5764_; 
v___x_5763_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5764_ = l_Lean_annotation_x3f(v___x_5763_, v_e_5762_);
if (lean_obj_tag(v___x_5764_) == 0)
{
return v___x_5764_;
}
else
{
lean_object* v_val_5765_; lean_object* v___x_5767_; uint8_t v_isShared_5768_; uint8_t v_isSharedCheck_5778_; 
v_val_5765_ = lean_ctor_get(v___x_5764_, 0);
v_isSharedCheck_5778_ = !lean_is_exclusive(v___x_5764_);
if (v_isSharedCheck_5778_ == 0)
{
v___x_5767_ = v___x_5764_;
v_isShared_5768_ = v_isSharedCheck_5778_;
goto v_resetjp_5766_;
}
else
{
lean_inc(v_val_5765_);
lean_dec(v___x_5764_);
v___x_5767_ = lean_box(0);
v_isShared_5768_ = v_isSharedCheck_5778_;
goto v_resetjp_5766_;
}
v_resetjp_5766_:
{
lean_object* v___x_5769_; lean_object* v___x_5770_; uint8_t v___x_5771_; 
v___x_5769_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5770_ = lean_unsigned_to_nat(3u);
v___x_5771_ = l_Lean_Expr_isAppOfArity(v_val_5765_, v___x_5769_, v___x_5770_);
if (v___x_5771_ == 0)
{
lean_object* v___x_5772_; 
lean_del_object(v___x_5767_);
lean_dec(v_val_5765_);
v___x_5772_ = lean_box(0);
return v___x_5772_;
}
else
{
lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5776_; 
v___x_5773_ = l_Lean_Expr_appFn_x21(v_val_5765_);
lean_dec(v_val_5765_);
v___x_5774_ = l_Lean_Expr_appArg_x21(v___x_5773_);
lean_dec_ref(v___x_5773_);
if (v_isShared_5768_ == 0)
{
lean_ctor_set(v___x_5767_, 0, v___x_5774_);
v___x_5776_ = v___x_5767_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5777_; 
v_reuseFailAlloc_5777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5777_, 0, v___x_5774_);
v___x_5776_ = v_reuseFailAlloc_5777_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
return v___x_5776_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* v_e_5779_){
_start:
{
lean_object* v_res_5780_; 
v_res_5780_ = l_Lean_isLHSGoal_x3f(v_e_5779_);
lean_dec_ref(v_e_5779_);
return v_res_5780_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* v_toPure_5781_, lean_object* v_____do__lift_5782_){
_start:
{
lean_object* v___x_5783_; 
v___x_5783_ = lean_apply_2(v_toPure_5781_, lean_box(0), v_____do__lift_5782_);
return v___x_5783_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* v_inst_5784_, lean_object* v_inst_5785_){
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* v_m_5792_, lean_object* v_inst_5793_, lean_object* v_inst_5794_){
_start:
{
lean_object* v___x_5795_; 
v___x_5795_ = l_Lean_mkFreshFVarId___redArg(v_inst_5793_, v_inst_5794_);
return v___x_5795_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* v_inst_5796_, lean_object* v_inst_5797_){
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
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* v_m_5804_, lean_object* v_inst_5805_, lean_object* v_inst_5806_){
_start:
{
lean_object* v___x_5807_; 
v___x_5807_ = l_Lean_mkFreshMVarId___redArg(v_inst_5805_, v_inst_5806_);
return v___x_5807_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* v_inst_5808_, lean_object* v_inst_5809_){
_start:
{
lean_object* v_toApplicative_5810_; lean_object* v_toBind_5811_; lean_object* v_toPure_5812_; lean_object* v___x_5813_; lean_object* v___f_5814_; lean_object* v___x_5815_; 
v_toApplicative_5810_ = lean_ctor_get(v_inst_5808_, 0);
v_toBind_5811_ = lean_ctor_get(v_inst_5808_, 1);
lean_inc(v_toBind_5811_);
v_toPure_5812_ = lean_ctor_get(v_toApplicative_5810_, 1);
lean_inc(v_toPure_5812_);
v___x_5813_ = l_Lean_mkFreshId___redArg(v_inst_5808_, v_inst_5809_);
v___f_5814_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5814_, 0, v_toPure_5812_);
v___x_5815_ = lean_apply_4(v_toBind_5811_, lean_box(0), lean_box(0), v___x_5813_, v___f_5814_);
return v___x_5815_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* v_m_5816_, lean_object* v_inst_5817_, lean_object* v_inst_5818_){
_start:
{
lean_object* v___x_5819_; 
v___x_5819_ = l_Lean_mkFreshLMVarId___redArg(v_inst_5817_, v_inst_5818_);
return v___x_5819_;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2(void){
_start:
{
lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; 
v___x_5823_ = lean_box(0);
v___x_5824_ = ((lean_object*)(l_Lean_mkNot___closed__1));
v___x_5825_ = l_Lean_Expr_const___override(v___x_5824_, v___x_5823_);
return v___x_5825_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* v_p_5826_){
_start:
{
lean_object* v___x_5827_; lean_object* v___x_5828_; 
v___x_5827_ = lean_obj_once(&l_Lean_mkNot___closed__2, &l_Lean_mkNot___closed__2_once, _init_l_Lean_mkNot___closed__2);
v___x_5828_ = l_Lean_Expr_app___override(v___x_5827_, v_p_5826_);
return v___x_5828_;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2(void){
_start:
{
lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; 
v___x_5832_ = lean_box(0);
v___x_5833_ = ((lean_object*)(l_Lean_mkOr___closed__1));
v___x_5834_ = l_Lean_Expr_const___override(v___x_5833_, v___x_5832_);
return v___x_5834_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* v_p_5835_, lean_object* v_q_5836_){
_start:
{
lean_object* v___x_5837_; lean_object* v___x_5838_; 
v___x_5837_ = lean_obj_once(&l_Lean_mkOr___closed__2, &l_Lean_mkOr___closed__2_once, _init_l_Lean_mkOr___closed__2);
v___x_5838_ = l_Lean_mkAppB(v___x_5837_, v_p_5835_, v_q_5836_);
return v___x_5838_;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2(void){
_start:
{
lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; 
v___x_5842_ = lean_box(0);
v___x_5843_ = ((lean_object*)(l_Lean_mkAnd___closed__1));
v___x_5844_ = l_Lean_Expr_const___override(v___x_5843_, v___x_5842_);
return v___x_5844_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* v_p_5845_, lean_object* v_q_5846_){
_start:
{
lean_object* v___x_5847_; lean_object* v___x_5848_; 
v___x_5847_ = lean_obj_once(&l_Lean_mkAnd___closed__2, &l_Lean_mkAnd___closed__2_once, _init_l_Lean_mkAnd___closed__2);
v___x_5848_ = l_Lean_mkAppB(v___x_5847_, v_p_5845_, v_q_5846_);
return v___x_5848_;
}
}
static lean_object* _init_l_Lean_mkAndN___closed__0(void){
_start:
{
lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; 
v___x_5849_ = lean_box(0);
v___x_5850_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_5851_ = l_Lean_Expr_const___override(v___x_5850_, v___x_5849_);
return v___x_5851_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* v_x_5852_){
_start:
{
if (lean_obj_tag(v_x_5852_) == 0)
{
lean_object* v___x_5853_; 
v___x_5853_ = lean_obj_once(&l_Lean_mkAndN___closed__0, &l_Lean_mkAndN___closed__0_once, _init_l_Lean_mkAndN___closed__0);
return v___x_5853_;
}
else
{
lean_object* v_tail_5854_; 
v_tail_5854_ = lean_ctor_get(v_x_5852_, 1);
if (lean_obj_tag(v_tail_5854_) == 0)
{
lean_object* v_head_5855_; 
v_head_5855_ = lean_ctor_get(v_x_5852_, 0);
lean_inc(v_head_5855_);
lean_dec_ref_known(v_x_5852_, 2);
return v_head_5855_;
}
else
{
lean_object* v_head_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; 
lean_inc(v_tail_5854_);
v_head_5856_ = lean_ctor_get(v_x_5852_, 0);
lean_inc(v_head_5856_);
lean_dec_ref_known(v_x_5852_, 2);
v___x_5857_ = l_Lean_mkAndN(v_tail_5854_);
v___x_5858_ = l_Lean_mkAnd(v_head_5856_, v___x_5857_);
return v___x_5858_;
}
}
}
}
static lean_object* _init_l_Lean_mkEM___closed__3(void){
_start:
{
lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; 
v___x_5864_ = lean_box(0);
v___x_5865_ = ((lean_object*)(l_Lean_mkEM___closed__2));
v___x_5866_ = l_Lean_Expr_const___override(v___x_5865_, v___x_5864_);
return v___x_5866_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* v_p_5867_){
_start:
{
lean_object* v___x_5868_; lean_object* v___x_5869_; 
v___x_5868_ = lean_obj_once(&l_Lean_mkEM___closed__3, &l_Lean_mkEM___closed__3_once, _init_l_Lean_mkEM___closed__3);
v___x_5869_ = l_Lean_Expr_app___override(v___x_5868_, v_p_5867_);
return v___x_5869_;
}
}
static lean_object* _init_l_Lean_mkIff___closed__2(void){
_start:
{
lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; 
v___x_5873_ = lean_box(0);
v___x_5874_ = ((lean_object*)(l_Lean_mkIff___closed__1));
v___x_5875_ = l_Lean_Expr_const___override(v___x_5874_, v___x_5873_);
return v___x_5875_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* v_p_5876_, lean_object* v_q_5877_){
_start:
{
lean_object* v___x_5878_; lean_object* v___x_5879_; 
v___x_5878_ = lean_obj_once(&l_Lean_mkIff___closed__2, &l_Lean_mkIff___closed__2_once, _init_l_Lean_mkIff___closed__2);
v___x_5879_ = l_Lean_mkAppB(v___x_5878_, v_p_5876_, v_q_5877_);
return v___x_5879_;
}
}
static lean_object* _init_l_Lean_Nat_mkType(void){
_start:
{
lean_object* v___x_5880_; 
v___x_5880_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_5880_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; 
v___x_5884_ = lean_box(0);
v___x_5885_ = ((lean_object*)(l_Lean_Nat_mkInstAdd___closed__1));
v___x_5886_ = l_Lean_Expr_const___override(v___x_5885_, v___x_5884_);
return v___x_5886_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd(void){
_start:
{
lean_object* v___x_5887_; 
v___x_5887_ = lean_obj_once(&l_Lean_Nat_mkInstAdd___closed__2, &l_Lean_Nat_mkInstAdd___closed__2_once, _init_l_Lean_Nat_mkInstAdd___closed__2);
return v___x_5887_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__2(void){
_start:
{
lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; 
v___x_5891_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5892_ = ((lean_object*)(l_Lean_Nat_mkInstHAdd___closed__1));
v___x_5893_ = l_Lean_Expr_const___override(v___x_5892_, v___x_5891_);
return v___x_5893_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__3(void){
_start:
{
lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; 
v___x_5894_ = l_Lean_Nat_mkInstAdd;
v___x_5895_ = l_Lean_Nat_mkType;
v___x_5896_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_5897_ = l_Lean_mkAppB(v___x_5896_, v___x_5895_, v___x_5894_);
return v___x_5897_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd(void){
_start:
{
lean_object* v___x_5898_; 
v___x_5898_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__3, &l_Lean_Nat_mkInstHAdd___closed__3_once, _init_l_Lean_Nat_mkInstHAdd___closed__3);
return v___x_5898_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; 
v___x_5902_ = lean_box(0);
v___x_5903_ = ((lean_object*)(l_Lean_Nat_mkInstSub___closed__1));
v___x_5904_ = l_Lean_Expr_const___override(v___x_5903_, v___x_5902_);
return v___x_5904_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub(void){
_start:
{
lean_object* v___x_5905_; 
v___x_5905_ = lean_obj_once(&l_Lean_Nat_mkInstSub___closed__2, &l_Lean_Nat_mkInstSub___closed__2_once, _init_l_Lean_Nat_mkInstSub___closed__2);
return v___x_5905_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__2(void){
_start:
{
lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; 
v___x_5909_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5910_ = ((lean_object*)(l_Lean_Nat_mkInstHSub___closed__1));
v___x_5911_ = l_Lean_Expr_const___override(v___x_5910_, v___x_5909_);
return v___x_5911_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__3(void){
_start:
{
lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; 
v___x_5912_ = l_Lean_Nat_mkInstSub;
v___x_5913_ = l_Lean_Nat_mkType;
v___x_5914_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_5915_ = l_Lean_mkAppB(v___x_5914_, v___x_5913_, v___x_5912_);
return v___x_5915_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub(void){
_start:
{
lean_object* v___x_5916_; 
v___x_5916_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__3, &l_Lean_Nat_mkInstHSub___closed__3_once, _init_l_Lean_Nat_mkInstHSub___closed__3);
return v___x_5916_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; 
v___x_5920_ = lean_box(0);
v___x_5921_ = ((lean_object*)(l_Lean_Nat_mkInstMul___closed__1));
v___x_5922_ = l_Lean_Expr_const___override(v___x_5921_, v___x_5920_);
return v___x_5922_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul(void){
_start:
{
lean_object* v___x_5923_; 
v___x_5923_ = lean_obj_once(&l_Lean_Nat_mkInstMul___closed__2, &l_Lean_Nat_mkInstMul___closed__2_once, _init_l_Lean_Nat_mkInstMul___closed__2);
return v___x_5923_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__2(void){
_start:
{
lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; 
v___x_5927_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5928_ = ((lean_object*)(l_Lean_Nat_mkInstHMul___closed__1));
v___x_5929_ = l_Lean_Expr_const___override(v___x_5928_, v___x_5927_);
return v___x_5929_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; 
v___x_5930_ = l_Lean_Nat_mkInstMul;
v___x_5931_ = l_Lean_Nat_mkType;
v___x_5932_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_5933_ = l_Lean_mkAppB(v___x_5932_, v___x_5931_, v___x_5930_);
return v___x_5933_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul(void){
_start:
{
lean_object* v___x_5934_; 
v___x_5934_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__3, &l_Lean_Nat_mkInstHMul___closed__3_once, _init_l_Lean_Nat_mkInstHMul___closed__3);
return v___x_5934_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv___closed__2(void){
_start:
{
lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; 
v___x_5939_ = lean_box(0);
v___x_5940_ = ((lean_object*)(l_Lean_Nat_mkInstDiv___closed__1));
v___x_5941_ = l_Lean_Expr_const___override(v___x_5940_, v___x_5939_);
return v___x_5941_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv(void){
_start:
{
lean_object* v___x_5942_; 
v___x_5942_ = lean_obj_once(&l_Lean_Nat_mkInstDiv___closed__2, &l_Lean_Nat_mkInstDiv___closed__2_once, _init_l_Lean_Nat_mkInstDiv___closed__2);
return v___x_5942_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__2(void){
_start:
{
lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; 
v___x_5946_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5947_ = ((lean_object*)(l_Lean_Nat_mkInstHDiv___closed__1));
v___x_5948_ = l_Lean_Expr_const___override(v___x_5947_, v___x_5946_);
return v___x_5948_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__3(void){
_start:
{
lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; 
v___x_5949_ = l_Lean_Nat_mkInstDiv;
v___x_5950_ = l_Lean_Nat_mkType;
v___x_5951_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_5952_ = l_Lean_mkAppB(v___x_5951_, v___x_5950_, v___x_5949_);
return v___x_5952_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv(void){
_start:
{
lean_object* v___x_5953_; 
v___x_5953_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__3, &l_Lean_Nat_mkInstHDiv___closed__3_once, _init_l_Lean_Nat_mkInstHDiv___closed__3);
return v___x_5953_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod___closed__2(void){
_start:
{
lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; 
v___x_5958_ = lean_box(0);
v___x_5959_ = ((lean_object*)(l_Lean_Nat_mkInstMod___closed__1));
v___x_5960_ = l_Lean_Expr_const___override(v___x_5959_, v___x_5958_);
return v___x_5960_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod(void){
_start:
{
lean_object* v___x_5961_; 
v___x_5961_ = lean_obj_once(&l_Lean_Nat_mkInstMod___closed__2, &l_Lean_Nat_mkInstMod___closed__2_once, _init_l_Lean_Nat_mkInstMod___closed__2);
return v___x_5961_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__2(void){
_start:
{
lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; 
v___x_5965_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5966_ = ((lean_object*)(l_Lean_Nat_mkInstHMod___closed__1));
v___x_5967_ = l_Lean_Expr_const___override(v___x_5966_, v___x_5965_);
return v___x_5967_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__3(void){
_start:
{
lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; 
v___x_5968_ = l_Lean_Nat_mkInstMod;
v___x_5969_ = l_Lean_Nat_mkType;
v___x_5970_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_5971_ = l_Lean_mkAppB(v___x_5970_, v___x_5969_, v___x_5968_);
return v___x_5971_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod(void){
_start:
{
lean_object* v___x_5972_; 
v___x_5972_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__3, &l_Lean_Nat_mkInstHMod___closed__3_once, _init_l_Lean_Nat_mkInstHMod___closed__3);
return v___x_5972_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow___closed__2(void){
_start:
{
lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; 
v___x_5976_ = lean_box(0);
v___x_5977_ = ((lean_object*)(l_Lean_Nat_mkInstNatPow___closed__1));
v___x_5978_ = l_Lean_Expr_const___override(v___x_5977_, v___x_5976_);
return v___x_5978_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow(void){
_start:
{
lean_object* v___x_5979_; 
v___x_5979_ = lean_obj_once(&l_Lean_Nat_mkInstNatPow___closed__2, &l_Lean_Nat_mkInstNatPow___closed__2_once, _init_l_Lean_Nat_mkInstNatPow___closed__2);
return v___x_5979_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; 
v___x_5983_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5984_ = ((lean_object*)(l_Lean_Nat_mkInstPow___closed__1));
v___x_5985_ = l_Lean_Expr_const___override(v___x_5984_, v___x_5983_);
return v___x_5985_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__3(void){
_start:
{
lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; 
v___x_5986_ = l_Lean_Nat_mkInstNatPow;
v___x_5987_ = l_Lean_Nat_mkType;
v___x_5988_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_5989_ = l_Lean_mkAppB(v___x_5988_, v___x_5987_, v___x_5986_);
return v___x_5989_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow(void){
_start:
{
lean_object* v___x_5990_; 
v___x_5990_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__3, &l_Lean_Nat_mkInstPow___closed__3_once, _init_l_Lean_Nat_mkInstPow___closed__3);
return v___x_5990_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__3(void){
_start:
{
lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; 
v___x_5997_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__2));
v___x_5998_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__1));
v___x_5999_ = l_Lean_Expr_const___override(v___x_5998_, v___x_5997_);
return v___x_5999_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__4(void){
_start:
{
lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; 
v___x_6000_ = l_Lean_Nat_mkInstPow;
v___x_6001_ = l_Lean_Nat_mkType;
v___x_6002_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6003_ = l_Lean_mkApp3(v___x_6002_, v___x_6001_, v___x_6001_, v___x_6000_);
return v___x_6003_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow(void){
_start:
{
lean_object* v___x_6004_; 
v___x_6004_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__4, &l_Lean_Nat_mkInstHPow___closed__4_once, _init_l_Lean_Nat_mkInstHPow___closed__4);
return v___x_6004_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; 
v___x_6008_ = lean_box(0);
v___x_6009_ = ((lean_object*)(l_Lean_Nat_mkInstLT___closed__1));
v___x_6010_ = l_Lean_Expr_const___override(v___x_6009_, v___x_6008_);
return v___x_6010_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT(void){
_start:
{
lean_object* v___x_6011_; 
v___x_6011_ = lean_obj_once(&l_Lean_Nat_mkInstLT___closed__2, &l_Lean_Nat_mkInstLT___closed__2_once, _init_l_Lean_Nat_mkInstLT___closed__2);
return v___x_6011_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; 
v___x_6015_ = lean_box(0);
v___x_6016_ = ((lean_object*)(l_Lean_Nat_mkInstLE___closed__1));
v___x_6017_ = l_Lean_Expr_const___override(v___x_6016_, v___x_6015_);
return v___x_6017_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE(void){
_start:
{
lean_object* v___x_6018_; 
v___x_6018_ = lean_obj_once(&l_Lean_Nat_mkInstLE___closed__2, &l_Lean_Nat_mkInstLE___closed__2_once, _init_l_Lean_Nat_mkInstLE___closed__2);
return v___x_6018_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3(void){
_start:
{
lean_object* v___x_6024_; lean_object* v___x_6025_; 
v___x_6024_ = lean_unsigned_to_nat(0u);
v___x_6025_ = l_Lean_Level_ofNat(v___x_6024_);
return v___x_6025_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4(void){
_start:
{
lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; 
v___x_6026_ = lean_box(0);
v___x_6027_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6028_, 0, v___x_6027_);
lean_ctor_set(v___x_6028_, 1, v___x_6026_);
return v___x_6028_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5(void){
_start:
{
lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; 
v___x_6029_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6030_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6030_);
lean_ctor_set(v___x_6031_, 1, v___x_6029_);
return v___x_6031_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6(void){
_start:
{
lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; 
v___x_6032_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__5, &l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5);
v___x_6033_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6033_);
lean_ctor_set(v___x_6034_, 1, v___x_6032_);
return v___x_6034_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7(void){
_start:
{
lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; 
v___x_6035_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6036_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natAddFn___closed__2));
v___x_6037_ = l_Lean_Expr_const___override(v___x_6036_, v___x_6035_);
return v___x_6037_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8(void){
_start:
{
lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; 
v___x_6038_ = l_Lean_Nat_mkInstHAdd;
v___x_6039_ = l_Lean_Nat_mkType;
v___x_6040_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6041_ = l_Lean_mkApp4(v___x_6040_, v___x_6039_, v___x_6039_, v___x_6039_, v___x_6038_);
return v___x_6041_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn(void){
_start:
{
lean_object* v___x_6042_; 
v___x_6042_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__8, &l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8);
return v___x_6042_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3(void){
_start:
{
lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; 
v___x_6048_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6049_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natSubFn___closed__2));
v___x_6050_ = l_Lean_Expr_const___override(v___x_6049_, v___x_6048_);
return v___x_6050_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4(void){
_start:
{
lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; 
v___x_6051_ = l_Lean_Nat_mkInstHSub;
v___x_6052_ = l_Lean_Nat_mkType;
v___x_6053_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6054_ = l_Lean_mkApp4(v___x_6053_, v___x_6052_, v___x_6052_, v___x_6052_, v___x_6051_);
return v___x_6054_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn(void){
_start:
{
lean_object* v___x_6055_; 
v___x_6055_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__4, &l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4);
return v___x_6055_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3(void){
_start:
{
lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; 
v___x_6061_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6062_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natMulFn___closed__2));
v___x_6063_ = l_Lean_Expr_const___override(v___x_6062_, v___x_6061_);
return v___x_6063_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4(void){
_start:
{
lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; 
v___x_6064_ = l_Lean_Nat_mkInstHMul;
v___x_6065_ = l_Lean_Nat_mkType;
v___x_6066_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6067_ = l_Lean_mkApp4(v___x_6066_, v___x_6065_, v___x_6065_, v___x_6065_, v___x_6064_);
return v___x_6067_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn(void){
_start:
{
lean_object* v___x_6068_; 
v___x_6068_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__4, &l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4);
return v___x_6068_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3(void){
_start:
{
lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; 
v___x_6074_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6075_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natPowFn___closed__2));
v___x_6076_ = l_Lean_Expr_const___override(v___x_6075_, v___x_6074_);
return v___x_6076_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4(void){
_start:
{
lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; 
v___x_6077_ = l_Lean_Nat_mkInstHPow;
v___x_6078_ = l_Lean_Nat_mkType;
v___x_6079_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6080_ = l_Lean_mkApp4(v___x_6079_, v___x_6078_, v___x_6078_, v___x_6078_, v___x_6077_);
return v___x_6080_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn(void){
_start:
{
lean_object* v___x_6081_; 
v___x_6081_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__4, &l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4);
return v___x_6081_;
}
}
static lean_object* _init_l_Lean_mkNatSucc___closed__2(void){
_start:
{
lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; 
v___x_6086_ = lean_box(0);
v___x_6087_ = ((lean_object*)(l_Lean_mkNatSucc___closed__1));
v___x_6088_ = l_Lean_Expr_const___override(v___x_6087_, v___x_6086_);
return v___x_6088_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* v_a_6089_){
_start:
{
lean_object* v___x_6090_; lean_object* v___x_6091_; 
v___x_6090_ = lean_obj_once(&l_Lean_mkNatSucc___closed__2, &l_Lean_mkNatSucc___closed__2_once, _init_l_Lean_mkNatSucc___closed__2);
v___x_6091_ = l_Lean_Expr_app___override(v___x_6090_, v_a_6089_);
return v___x_6091_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* v_a_6092_, lean_object* v_b_6093_){
_start:
{
lean_object* v___x_6094_; lean_object* v___x_6095_; 
v___x_6094_ = l___private_Lean_Expr_0__Lean_natAddFn;
v___x_6095_ = l_Lean_mkAppB(v___x_6094_, v_a_6092_, v_b_6093_);
return v___x_6095_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* v_a_6096_, lean_object* v_b_6097_){
_start:
{
lean_object* v___x_6098_; lean_object* v___x_6099_; 
v___x_6098_ = l___private_Lean_Expr_0__Lean_natSubFn;
v___x_6099_ = l_Lean_mkAppB(v___x_6098_, v_a_6096_, v_b_6097_);
return v___x_6099_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* v_a_6100_, lean_object* v_b_6101_){
_start:
{
lean_object* v___x_6102_; lean_object* v___x_6103_; 
v___x_6102_ = l___private_Lean_Expr_0__Lean_natMulFn;
v___x_6103_ = l_Lean_mkAppB(v___x_6102_, v_a_6100_, v_b_6101_);
return v___x_6103_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object* v_a_6104_, lean_object* v_b_6105_){
_start:
{
lean_object* v___x_6106_; lean_object* v___x_6107_; 
v___x_6106_ = l___private_Lean_Expr_0__Lean_natPowFn;
v___x_6107_ = l_Lean_mkAppB(v___x_6106_, v_a_6104_, v_b_6105_);
return v___x_6107_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3(void){
_start:
{
lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; 
v___x_6113_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6114_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natLEPred___closed__2));
v___x_6115_ = l_Lean_Expr_const___override(v___x_6114_, v___x_6113_);
return v___x_6115_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4(void){
_start:
{
lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; 
v___x_6116_ = l_Lean_Nat_mkInstLE;
v___x_6117_ = l_Lean_Nat_mkType;
v___x_6118_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6119_ = l_Lean_mkAppB(v___x_6118_, v___x_6117_, v___x_6116_);
return v___x_6119_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred(void){
_start:
{
lean_object* v___x_6120_; 
v___x_6120_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__4, &l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4);
return v___x_6120_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* v_a_6121_, lean_object* v_b_6122_){
_start:
{
lean_object* v___x_6123_; lean_object* v___x_6124_; 
v___x_6123_ = l___private_Lean_Expr_0__Lean_natLEPred;
v___x_6124_ = l_Lean_mkAppB(v___x_6123_, v_a_6121_, v_b_6122_);
return v___x_6124_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0(void){
_start:
{
lean_object* v___x_6125_; lean_object* v___x_6126_; 
v___x_6125_ = lean_unsigned_to_nat(1u);
v___x_6126_ = l_Lean_Level_ofNat(v___x_6125_);
return v___x_6126_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1(void){
_start:
{
lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; 
v___x_6127_ = lean_box(0);
v___x_6128_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__0, &l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0);
v___x_6129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6128_);
lean_ctor_set(v___x_6129_, 1, v___x_6127_);
return v___x_6129_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2(void){
_start:
{
lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; 
v___x_6130_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__1, &l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1);
v___x_6131_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_6132_ = l_Lean_Expr_const___override(v___x_6131_, v___x_6130_);
return v___x_6132_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3(void){
_start:
{
lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; 
v___x_6133_ = l_Lean_Nat_mkType;
v___x_6134_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6135_ = l_Lean_Expr_app___override(v___x_6134_, v___x_6133_);
return v___x_6135_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred(void){
_start:
{
lean_object* v___x_6136_; 
v___x_6136_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__3, &l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3);
return v___x_6136_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* v_a_6137_, lean_object* v_b_6138_){
_start:
{
lean_object* v___x_6139_; lean_object* v___x_6140_; 
v___x_6139_ = l___private_Lean_Expr_0__Lean_natEqPred;
v___x_6140_ = l_Lean_mkAppB(v___x_6139_, v_a_6137_, v_b_6138_);
return v___x_6140_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__0(void){
_start:
{
lean_object* v___x_6141_; lean_object* v___x_6142_; 
v___x_6141_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6142_ = l_Lean_Expr_sort___override(v___x_6141_);
return v___x_6142_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__1(void){
_start:
{
lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; 
v___x_6143_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__0, &l___private_Lean_Expr_0__Lean_propEq___closed__0_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__0);
v___x_6144_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6145_ = l_Lean_Expr_app___override(v___x_6144_, v___x_6143_);
return v___x_6145_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq(void){
_start:
{
lean_object* v___x_6146_; 
v___x_6146_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__1, &l___private_Lean_Expr_0__Lean_propEq___closed__1_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__1);
return v___x_6146_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* v_a_6147_, lean_object* v_b_6148_){
_start:
{
lean_object* v___x_6149_; lean_object* v___x_6150_; 
v___x_6149_ = l___private_Lean_Expr_0__Lean_propEq;
v___x_6150_ = l_Lean_mkAppB(v___x_6149_, v_a_6147_, v_b_6148_);
return v___x_6150_;
}
}
static lean_object* _init_l_Lean_Int_mkType___closed__2(void){
_start:
{
lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; 
v___x_6154_ = lean_box(0);
v___x_6155_ = ((lean_object*)(l_Lean_Int_mkType___closed__1));
v___x_6156_ = l_Lean_Expr_const___override(v___x_6155_, v___x_6154_);
return v___x_6156_;
}
}
static lean_object* _init_l_Lean_Int_mkType(void){
_start:
{
lean_object* v___x_6157_; 
v___x_6157_ = lean_obj_once(&l_Lean_Int_mkType___closed__2, &l_Lean_Int_mkType___closed__2_once, _init_l_Lean_Int_mkType___closed__2);
return v___x_6157_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg___closed__2(void){
_start:
{
lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; 
v___x_6162_ = lean_box(0);
v___x_6163_ = ((lean_object*)(l_Lean_Int_mkInstNeg___closed__1));
v___x_6164_ = l_Lean_Expr_const___override(v___x_6163_, v___x_6162_);
return v___x_6164_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg(void){
_start:
{
lean_object* v___x_6165_; 
v___x_6165_ = lean_obj_once(&l_Lean_Int_mkInstNeg___closed__2, &l_Lean_Int_mkInstNeg___closed__2_once, _init_l_Lean_Int_mkInstNeg___closed__2);
return v___x_6165_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; 
v___x_6170_ = lean_box(0);
v___x_6171_ = ((lean_object*)(l_Lean_Int_mkInstAdd___closed__1));
v___x_6172_ = l_Lean_Expr_const___override(v___x_6171_, v___x_6170_);
return v___x_6172_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd(void){
_start:
{
lean_object* v___x_6173_; 
v___x_6173_ = lean_obj_once(&l_Lean_Int_mkInstAdd___closed__2, &l_Lean_Int_mkInstAdd___closed__2_once, _init_l_Lean_Int_mkInstAdd___closed__2);
return v___x_6173_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd___closed__0(void){
_start:
{
lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; 
v___x_6174_ = l_Lean_Int_mkInstAdd;
v___x_6175_ = l_Lean_Int_mkType;
v___x_6176_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6177_ = l_Lean_mkAppB(v___x_6176_, v___x_6175_, v___x_6174_);
return v___x_6177_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd(void){
_start:
{
lean_object* v___x_6178_; 
v___x_6178_ = lean_obj_once(&l_Lean_Int_mkInstHAdd___closed__0, &l_Lean_Int_mkInstHAdd___closed__0_once, _init_l_Lean_Int_mkInstHAdd___closed__0);
return v___x_6178_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; 
v___x_6183_ = lean_box(0);
v___x_6184_ = ((lean_object*)(l_Lean_Int_mkInstSub___closed__1));
v___x_6185_ = l_Lean_Expr_const___override(v___x_6184_, v___x_6183_);
return v___x_6185_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub(void){
_start:
{
lean_object* v___x_6186_; 
v___x_6186_ = lean_obj_once(&l_Lean_Int_mkInstSub___closed__2, &l_Lean_Int_mkInstSub___closed__2_once, _init_l_Lean_Int_mkInstSub___closed__2);
return v___x_6186_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub___closed__0(void){
_start:
{
lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; 
v___x_6187_ = l_Lean_Int_mkInstSub;
v___x_6188_ = l_Lean_Int_mkType;
v___x_6189_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6190_ = l_Lean_mkAppB(v___x_6189_, v___x_6188_, v___x_6187_);
return v___x_6190_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub(void){
_start:
{
lean_object* v___x_6191_; 
v___x_6191_ = lean_obj_once(&l_Lean_Int_mkInstHSub___closed__0, &l_Lean_Int_mkInstHSub___closed__0_once, _init_l_Lean_Int_mkInstHSub___closed__0);
return v___x_6191_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; 
v___x_6196_ = lean_box(0);
v___x_6197_ = ((lean_object*)(l_Lean_Int_mkInstMul___closed__1));
v___x_6198_ = l_Lean_Expr_const___override(v___x_6197_, v___x_6196_);
return v___x_6198_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul(void){
_start:
{
lean_object* v___x_6199_; 
v___x_6199_ = lean_obj_once(&l_Lean_Int_mkInstMul___closed__2, &l_Lean_Int_mkInstMul___closed__2_once, _init_l_Lean_Int_mkInstMul___closed__2);
return v___x_6199_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul___closed__0(void){
_start:
{
lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; 
v___x_6200_ = l_Lean_Int_mkInstMul;
v___x_6201_ = l_Lean_Int_mkType;
v___x_6202_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6203_ = l_Lean_mkAppB(v___x_6202_, v___x_6201_, v___x_6200_);
return v___x_6203_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul(void){
_start:
{
lean_object* v___x_6204_; 
v___x_6204_ = lean_obj_once(&l_Lean_Int_mkInstHMul___closed__0, &l_Lean_Int_mkInstHMul___closed__0_once, _init_l_Lean_Int_mkInstHMul___closed__0);
return v___x_6204_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv___closed__1(void){
_start:
{
lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; 
v___x_6208_ = lean_box(0);
v___x_6209_ = ((lean_object*)(l_Lean_Int_mkInstDiv___closed__0));
v___x_6210_ = l_Lean_Expr_const___override(v___x_6209_, v___x_6208_);
return v___x_6210_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv(void){
_start:
{
lean_object* v___x_6211_; 
v___x_6211_ = lean_obj_once(&l_Lean_Int_mkInstDiv___closed__1, &l_Lean_Int_mkInstDiv___closed__1_once, _init_l_Lean_Int_mkInstDiv___closed__1);
return v___x_6211_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv___closed__0(void){
_start:
{
lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; 
v___x_6212_ = l_Lean_Int_mkInstDiv;
v___x_6213_ = l_Lean_Int_mkType;
v___x_6214_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6215_ = l_Lean_mkAppB(v___x_6214_, v___x_6213_, v___x_6212_);
return v___x_6215_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv(void){
_start:
{
lean_object* v___x_6216_; 
v___x_6216_ = lean_obj_once(&l_Lean_Int_mkInstHDiv___closed__0, &l_Lean_Int_mkInstHDiv___closed__0_once, _init_l_Lean_Int_mkInstHDiv___closed__0);
return v___x_6216_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod___closed__1(void){
_start:
{
lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; 
v___x_6220_ = lean_box(0);
v___x_6221_ = ((lean_object*)(l_Lean_Int_mkInstMod___closed__0));
v___x_6222_ = l_Lean_Expr_const___override(v___x_6221_, v___x_6220_);
return v___x_6222_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod(void){
_start:
{
lean_object* v___x_6223_; 
v___x_6223_ = lean_obj_once(&l_Lean_Int_mkInstMod___closed__1, &l_Lean_Int_mkInstMod___closed__1_once, _init_l_Lean_Int_mkInstMod___closed__1);
return v___x_6223_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod___closed__0(void){
_start:
{
lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; 
v___x_6224_ = l_Lean_Int_mkInstMod;
v___x_6225_ = l_Lean_Int_mkType;
v___x_6226_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6227_ = l_Lean_mkAppB(v___x_6226_, v___x_6225_, v___x_6224_);
return v___x_6227_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod(void){
_start:
{
lean_object* v___x_6228_; 
v___x_6228_ = lean_obj_once(&l_Lean_Int_mkInstHMod___closed__0, &l_Lean_Int_mkInstHMod___closed__0_once, _init_l_Lean_Int_mkInstHMod___closed__0);
return v___x_6228_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6233_; lean_object* v___x_6234_; lean_object* v___x_6235_; 
v___x_6233_ = lean_box(0);
v___x_6234_ = ((lean_object*)(l_Lean_Int_mkInstPow___closed__1));
v___x_6235_ = l_Lean_Expr_const___override(v___x_6234_, v___x_6233_);
return v___x_6235_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow(void){
_start:
{
lean_object* v___x_6236_; 
v___x_6236_ = lean_obj_once(&l_Lean_Int_mkInstPow___closed__2, &l_Lean_Int_mkInstPow___closed__2_once, _init_l_Lean_Int_mkInstPow___closed__2);
return v___x_6236_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat___closed__0(void){
_start:
{
lean_object* v___x_6237_; lean_object* v___x_6238_; lean_object* v___x_6239_; lean_object* v___x_6240_; 
v___x_6237_ = l_Lean_Int_mkInstPow;
v___x_6238_ = l_Lean_Int_mkType;
v___x_6239_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6240_ = l_Lean_mkAppB(v___x_6239_, v___x_6238_, v___x_6237_);
return v___x_6240_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat(void){
_start:
{
lean_object* v___x_6241_; 
v___x_6241_ = lean_obj_once(&l_Lean_Int_mkInstPowNat___closed__0, &l_Lean_Int_mkInstPowNat___closed__0_once, _init_l_Lean_Int_mkInstPowNat___closed__0);
return v___x_6241_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow___closed__0(void){
_start:
{
lean_object* v___x_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; 
v___x_6242_ = l_Lean_Int_mkInstPowNat;
v___x_6243_ = l_Lean_Nat_mkType;
v___x_6244_ = l_Lean_Int_mkType;
v___x_6245_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6246_ = l_Lean_mkApp3(v___x_6245_, v___x_6244_, v___x_6243_, v___x_6242_);
return v___x_6246_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow(void){
_start:
{
lean_object* v___x_6247_; 
v___x_6247_ = lean_obj_once(&l_Lean_Int_mkInstHPow___closed__0, &l_Lean_Int_mkInstHPow___closed__0_once, _init_l_Lean_Int_mkInstHPow___closed__0);
return v___x_6247_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; 
v___x_6252_ = lean_box(0);
v___x_6253_ = ((lean_object*)(l_Lean_Int_mkInstLT___closed__1));
v___x_6254_ = l_Lean_Expr_const___override(v___x_6253_, v___x_6252_);
return v___x_6254_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT(void){
_start:
{
lean_object* v___x_6255_; 
v___x_6255_ = lean_obj_once(&l_Lean_Int_mkInstLT___closed__2, &l_Lean_Int_mkInstLT___closed__2_once, _init_l_Lean_Int_mkInstLT___closed__2);
return v___x_6255_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; 
v___x_6260_ = lean_box(0);
v___x_6261_ = ((lean_object*)(l_Lean_Int_mkInstLE___closed__1));
v___x_6262_ = l_Lean_Expr_const___override(v___x_6261_, v___x_6260_);
return v___x_6262_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE(void){
_start:
{
lean_object* v___x_6263_; 
v___x_6263_ = lean_obj_once(&l_Lean_Int_mkInstLE___closed__2, &l_Lean_Int_mkInstLE___closed__2_once, _init_l_Lean_Int_mkInstLE___closed__2);
return v___x_6263_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast___closed__2(void){
_start:
{
lean_object* v___x_6267_; lean_object* v___x_6268_; lean_object* v___x_6269_; 
v___x_6267_ = lean_box(0);
v___x_6268_ = ((lean_object*)(l_Lean_Int_mkInstNatCast___closed__1));
v___x_6269_ = l_Lean_Expr_const___override(v___x_6268_, v___x_6267_);
return v___x_6269_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast(void){
_start:
{
lean_object* v___x_6270_; 
v___x_6270_ = lean_obj_once(&l_Lean_Int_mkInstNatCast___closed__2, &l_Lean_Int_mkInstNatCast___closed__2_once, _init_l_Lean_Int_mkInstNatCast___closed__2);
return v___x_6270_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0(void){
_start:
{
lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___x_6273_; 
v___x_6271_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6272_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_6273_ = l_Lean_Expr_const___override(v___x_6272_, v___x_6271_);
return v___x_6273_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1(void){
_start:
{
lean_object* v___x_6274_; lean_object* v___x_6275_; lean_object* v___x_6276_; lean_object* v___x_6277_; 
v___x_6274_ = l_Lean_Int_mkInstNeg;
v___x_6275_ = l_Lean_Int_mkType;
v___x_6276_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__0, &l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0);
v___x_6277_ = l_Lean_mkAppB(v___x_6276_, v___x_6275_, v___x_6274_);
return v___x_6277_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn(void){
_start:
{
lean_object* v___x_6278_; 
v___x_6278_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__1, &l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1);
return v___x_6278_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0(void){
_start:
{
lean_object* v___x_6279_; lean_object* v___x_6280_; lean_object* v___x_6281_; lean_object* v___x_6282_; 
v___x_6279_ = l_Lean_Int_mkInstHAdd;
v___x_6280_ = l_Lean_Int_mkType;
v___x_6281_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6282_ = l_Lean_mkApp4(v___x_6281_, v___x_6280_, v___x_6280_, v___x_6280_, v___x_6279_);
return v___x_6282_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn(void){
_start:
{
lean_object* v___x_6283_; 
v___x_6283_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intAddFn___closed__0, &l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0);
return v___x_6283_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0(void){
_start:
{
lean_object* v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; 
v___x_6284_ = l_Lean_Int_mkInstHSub;
v___x_6285_ = l_Lean_Int_mkType;
v___x_6286_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6287_ = l_Lean_mkApp4(v___x_6286_, v___x_6285_, v___x_6285_, v___x_6285_, v___x_6284_);
return v___x_6287_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn(void){
_start:
{
lean_object* v___x_6288_; 
v___x_6288_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intSubFn___closed__0, &l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0);
return v___x_6288_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0(void){
_start:
{
lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; 
v___x_6289_ = l_Lean_Int_mkInstHMul;
v___x_6290_ = l_Lean_Int_mkType;
v___x_6291_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6292_ = l_Lean_mkApp4(v___x_6291_, v___x_6290_, v___x_6290_, v___x_6290_, v___x_6289_);
return v___x_6292_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn(void){
_start:
{
lean_object* v___x_6293_; 
v___x_6293_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intMulFn___closed__0, &l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0);
return v___x_6293_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3(void){
_start:
{
lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; 
v___x_6299_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6300_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intDivFn___closed__2));
v___x_6301_ = l_Lean_Expr_const___override(v___x_6300_, v___x_6299_);
return v___x_6301_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4(void){
_start:
{
lean_object* v___x_6302_; lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; 
v___x_6302_ = l_Lean_Int_mkInstHDiv;
v___x_6303_ = l_Lean_Int_mkType;
v___x_6304_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__3, &l___private_Lean_Expr_0__Lean_intDivFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3);
v___x_6305_ = l_Lean_mkApp4(v___x_6304_, v___x_6303_, v___x_6303_, v___x_6303_, v___x_6302_);
return v___x_6305_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn(void){
_start:
{
lean_object* v___x_6306_; 
v___x_6306_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__4, &l___private_Lean_Expr_0__Lean_intDivFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4);
return v___x_6306_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3(void){
_start:
{
lean_object* v___x_6312_; lean_object* v___x_6313_; lean_object* v___x_6314_; 
v___x_6312_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6313_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intModFn___closed__2));
v___x_6314_ = l_Lean_Expr_const___override(v___x_6313_, v___x_6312_);
return v___x_6314_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4(void){
_start:
{
lean_object* v___x_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; lean_object* v___x_6318_; 
v___x_6315_ = l_Lean_Int_mkInstHMod;
v___x_6316_ = l_Lean_Int_mkType;
v___x_6317_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__3, &l___private_Lean_Expr_0__Lean_intModFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3);
v___x_6318_ = l_Lean_mkApp4(v___x_6317_, v___x_6316_, v___x_6316_, v___x_6316_, v___x_6315_);
return v___x_6318_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn(void){
_start:
{
lean_object* v___x_6319_; 
v___x_6319_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__4, &l___private_Lean_Expr_0__Lean_intModFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4);
return v___x_6319_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0(void){
_start:
{
lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v___x_6322_; lean_object* v___x_6323_; lean_object* v___x_6324_; 
v___x_6320_ = l_Lean_Int_mkInstHPow;
v___x_6321_ = l_Lean_Nat_mkType;
v___x_6322_ = l_Lean_Int_mkType;
v___x_6323_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6324_ = l_Lean_mkApp4(v___x_6323_, v___x_6322_, v___x_6321_, v___x_6322_, v___x_6320_);
return v___x_6324_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn(void){
_start:
{
lean_object* v___x_6325_; 
v___x_6325_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0, &l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0);
return v___x_6325_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3(void){
_start:
{
lean_object* v___x_6331_; lean_object* v___x_6332_; lean_object* v___x_6333_; 
v___x_6331_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6332_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2));
v___x_6333_ = l_Lean_Expr_const___override(v___x_6332_, v___x_6331_);
return v___x_6333_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4(void){
_start:
{
lean_object* v___x_6334_; lean_object* v___x_6335_; lean_object* v___x_6336_; lean_object* v___x_6337_; 
v___x_6334_ = l_Lean_Int_mkInstNatCast;
v___x_6335_ = l_Lean_Int_mkType;
v___x_6336_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3);
v___x_6337_ = l_Lean_mkAppB(v___x_6336_, v___x_6335_, v___x_6334_);
return v___x_6337_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn(void){
_start:
{
lean_object* v___x_6338_; 
v___x_6338_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4);
return v___x_6338_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* v_a_6339_){
_start:
{
lean_object* v___x_6340_; lean_object* v___x_6341_; 
v___x_6340_ = l___private_Lean_Expr_0__Lean_intNegFn;
v___x_6341_ = l_Lean_Expr_app___override(v___x_6340_, v_a_6339_);
return v___x_6341_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* v_a_6342_, lean_object* v_b_6343_){
_start:
{
lean_object* v___x_6344_; lean_object* v___x_6345_; 
v___x_6344_ = l___private_Lean_Expr_0__Lean_intAddFn;
v___x_6345_ = l_Lean_mkAppB(v___x_6344_, v_a_6342_, v_b_6343_);
return v___x_6345_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* v_a_6346_, lean_object* v_b_6347_){
_start:
{
lean_object* v___x_6348_; lean_object* v___x_6349_; 
v___x_6348_ = l___private_Lean_Expr_0__Lean_intSubFn;
v___x_6349_ = l_Lean_mkAppB(v___x_6348_, v_a_6346_, v_b_6347_);
return v___x_6349_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* v_a_6350_, lean_object* v_b_6351_){
_start:
{
lean_object* v___x_6352_; lean_object* v___x_6353_; 
v___x_6352_ = l___private_Lean_Expr_0__Lean_intMulFn;
v___x_6353_ = l_Lean_mkAppB(v___x_6352_, v_a_6350_, v_b_6351_);
return v___x_6353_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* v_a_6354_, lean_object* v_b_6355_){
_start:
{
lean_object* v___x_6356_; lean_object* v___x_6357_; 
v___x_6356_ = l___private_Lean_Expr_0__Lean_intDivFn;
v___x_6357_ = l_Lean_mkAppB(v___x_6356_, v_a_6354_, v_b_6355_);
return v___x_6357_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* v_a_6358_, lean_object* v_b_6359_){
_start:
{
lean_object* v___x_6360_; lean_object* v___x_6361_; 
v___x_6360_ = l___private_Lean_Expr_0__Lean_intModFn;
v___x_6361_ = l_Lean_mkAppB(v___x_6360_, v_a_6358_, v_b_6359_);
return v___x_6361_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* v_a_6362_){
_start:
{
lean_object* v___x_6363_; lean_object* v___x_6364_; 
v___x_6363_ = l___private_Lean_Expr_0__Lean_intNatCastFn;
v___x_6364_ = l_Lean_Expr_app___override(v___x_6363_, v_a_6362_);
return v___x_6364_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object* v_a_6365_, lean_object* v_b_6366_){
_start:
{
lean_object* v___x_6367_; lean_object* v___x_6368_; 
v___x_6367_ = l___private_Lean_Expr_0__Lean_intPowNatFn;
v___x_6368_ = l_Lean_mkAppB(v___x_6367_, v_a_6365_, v_b_6366_);
return v___x_6368_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0(void){
_start:
{
lean_object* v___x_6369_; lean_object* v___x_6370_; lean_object* v___x_6371_; lean_object* v___x_6372_; 
v___x_6369_ = l_Lean_Int_mkInstLE;
v___x_6370_ = l_Lean_Int_mkType;
v___x_6371_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6372_ = l_Lean_mkAppB(v___x_6371_, v___x_6370_, v___x_6369_);
return v___x_6372_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred(void){
_start:
{
lean_object* v___x_6373_; 
v___x_6373_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLEPred___closed__0, &l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0);
return v___x_6373_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* v_a_6374_, lean_object* v_b_6375_){
_start:
{
lean_object* v___x_6376_; lean_object* v___x_6377_; 
v___x_6376_ = l___private_Lean_Expr_0__Lean_intLEPred;
v___x_6377_ = l_Lean_mkAppB(v___x_6376_, v_a_6374_, v_b_6375_);
return v___x_6377_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3(void){
_start:
{
lean_object* v___x_6383_; lean_object* v___x_6384_; lean_object* v___x_6385_; 
v___x_6383_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6384_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intLTPred___closed__2));
v___x_6385_ = l_Lean_Expr_const___override(v___x_6384_, v___x_6383_);
return v___x_6385_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4(void){
_start:
{
lean_object* v___x_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; lean_object* v___x_6389_; 
v___x_6386_ = l_Lean_Int_mkInstLT;
v___x_6387_ = l_Lean_Int_mkType;
v___x_6388_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__3, &l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3);
v___x_6389_ = l_Lean_mkAppB(v___x_6388_, v___x_6387_, v___x_6386_);
return v___x_6389_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred(void){
_start:
{
lean_object* v___x_6390_; 
v___x_6390_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__4, &l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4);
return v___x_6390_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object* v_a_6391_, lean_object* v_b_6392_){
_start:
{
lean_object* v___x_6393_; lean_object* v___x_6394_; 
v___x_6393_ = l___private_Lean_Expr_0__Lean_intLTPred;
v___x_6394_ = l_Lean_mkAppB(v___x_6393_, v_a_6391_, v_b_6392_);
return v___x_6394_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0(void){
_start:
{
lean_object* v___x_6395_; lean_object* v___x_6396_; lean_object* v___x_6397_; 
v___x_6395_ = l_Lean_Int_mkType;
v___x_6396_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6397_ = l_Lean_Expr_app___override(v___x_6396_, v___x_6395_);
return v___x_6397_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred(void){
_start:
{
lean_object* v___x_6398_; 
v___x_6398_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intEqPred___closed__0, &l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0);
return v___x_6398_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* v_a_6399_, lean_object* v_b_6400_){
_start:
{
lean_object* v___x_6401_; lean_object* v___x_6402_; 
v___x_6401_ = l___private_Lean_Expr_0__Lean_intEqPred;
v___x_6402_ = l_Lean_mkAppB(v___x_6401_, v_a_6399_, v_b_6400_);
return v___x_6402_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__3(void){
_start:
{
lean_object* v___x_6408_; lean_object* v___x_6409_; lean_object* v___x_6410_; 
v___x_6408_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6409_ = ((lean_object*)(l_Lean_mkIntDvd___closed__2));
v___x_6410_ = l_Lean_Expr_const___override(v___x_6409_, v___x_6408_);
return v___x_6410_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__6(void){
_start:
{
lean_object* v___x_6415_; lean_object* v___x_6416_; lean_object* v___x_6417_; 
v___x_6415_ = lean_box(0);
v___x_6416_ = ((lean_object*)(l_Lean_mkIntDvd___closed__5));
v___x_6417_ = l_Lean_Expr_const___override(v___x_6416_, v___x_6415_);
return v___x_6417_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* v_a_6418_, lean_object* v_b_6419_){
_start:
{
lean_object* v___x_6420_; lean_object* v___x_6421_; lean_object* v___x_6422_; lean_object* v___x_6423_; 
v___x_6420_ = lean_obj_once(&l_Lean_mkIntDvd___closed__3, &l_Lean_mkIntDvd___closed__3_once, _init_l_Lean_mkIntDvd___closed__3);
v___x_6421_ = l_Lean_Int_mkType;
v___x_6422_ = lean_obj_once(&l_Lean_mkIntDvd___closed__6, &l_Lean_mkIntDvd___closed__6_once, _init_l_Lean_mkIntDvd___closed__6);
v___x_6423_ = l_Lean_mkApp4(v___x_6420_, v___x_6421_, v___x_6422_, v_a_6418_, v_b_6419_);
return v___x_6423_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__2(void){
_start:
{
lean_object* v___x_6427_; lean_object* v___x_6428_; lean_object* v___x_6429_; 
v___x_6427_ = lean_box(0);
v___x_6428_ = ((lean_object*)(l_Lean_mkIntLit___closed__1));
v___x_6429_ = l_Lean_Expr_const___override(v___x_6428_, v___x_6427_);
return v___x_6429_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__3(void){
_start:
{
lean_object* v___x_6430_; lean_object* v___x_6431_; 
v___x_6430_ = lean_unsigned_to_nat(0u);
v___x_6431_ = lean_nat_to_int(v___x_6430_);
return v___x_6431_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* v_n_6432_){
_start:
{
lean_object* v___x_6433_; lean_object* v_r_6434_; lean_object* v___x_6435_; lean_object* v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v_r_6439_; lean_object* v___x_6440_; uint8_t v___x_6441_; 
v___x_6433_ = lean_nat_abs(v_n_6432_);
v_r_6434_ = l_Lean_mkRawNatLit(v___x_6433_);
v___x_6435_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_6436_ = l_Lean_Int_mkType;
v___x_6437_ = lean_obj_once(&l_Lean_mkIntLit___closed__2, &l_Lean_mkIntLit___closed__2_once, _init_l_Lean_mkIntLit___closed__2);
lean_inc_ref(v_r_6434_);
v___x_6438_ = l_Lean_Expr_app___override(v___x_6437_, v_r_6434_);
v_r_6439_ = l_Lean_mkApp3(v___x_6435_, v___x_6436_, v_r_6434_, v___x_6438_);
v___x_6440_ = lean_obj_once(&l_Lean_mkIntLit___closed__3, &l_Lean_mkIntLit___closed__3_once, _init_l_Lean_mkIntLit___closed__3);
v___x_6441_ = lean_int_dec_lt(v_n_6432_, v___x_6440_);
if (v___x_6441_ == 0)
{
return v_r_6439_;
}
else
{
lean_object* v___x_6442_; 
v___x_6442_ = l_Lean_mkIntNeg(v_r_6439_);
return v___x_6442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* v_n_6443_){
_start:
{
lean_object* v_res_6444_; 
v_res_6444_ = l_Lean_mkIntLit(v_n_6443_);
lean_dec(v_n_6443_);
return v_res_6444_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6449_; lean_object* v___x_6450_; 
v___x_6449_ = lean_box(0);
v___x_6450_ = l_Lean_Level_succ___override(v___x_6449_);
return v___x_6450_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6451_; lean_object* v___x_6452_; lean_object* v___x_6453_; 
v___x_6451_ = lean_box(0);
v___x_6452_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__2, &l_Lean_reflBoolTrue___closed__2_once, _init_l_Lean_reflBoolTrue___closed__2);
v___x_6453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6453_, 0, v___x_6452_);
lean_ctor_set(v___x_6453_, 1, v___x_6451_);
return v___x_6453_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6454_; lean_object* v___x_6455_; lean_object* v___x_6456_; 
v___x_6454_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__3, &l_Lean_reflBoolTrue___closed__3_once, _init_l_Lean_reflBoolTrue___closed__3);
v___x_6455_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__1));
v___x_6456_ = l_Lean_Expr_const___override(v___x_6455_, v___x_6454_);
return v___x_6456_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__6(void){
_start:
{
lean_object* v___x_6459_; lean_object* v___x_6460_; lean_object* v___x_6461_; 
v___x_6459_ = lean_box(0);
v___x_6460_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__5));
v___x_6461_ = l_Lean_Expr_const___override(v___x_6460_, v___x_6459_);
return v___x_6461_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__7(void){
_start:
{
lean_object* v___x_6462_; lean_object* v___x_6463_; lean_object* v___x_6464_; 
v___x_6462_ = lean_box(0);
v___x_6463_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_6464_ = l_Lean_Expr_const___override(v___x_6463_, v___x_6462_);
return v___x_6464_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__8(void){
_start:
{
lean_object* v___x_6465_; lean_object* v___x_6466_; lean_object* v___x_6467_; lean_object* v___x_6468_; 
v___x_6465_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6466_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6467_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6468_ = l_Lean_mkAppB(v___x_6467_, v___x_6466_, v___x_6465_);
return v___x_6468_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue(void){
_start:
{
lean_object* v___x_6469_; 
v___x_6469_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__8, &l_Lean_reflBoolTrue___closed__8_once, _init_l_Lean_reflBoolTrue___closed__8);
return v___x_6469_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; 
v___x_6470_ = lean_box(0);
v___x_6471_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_6472_ = l_Lean_Expr_const___override(v___x_6471_, v___x_6470_);
return v___x_6472_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6473_; lean_object* v___x_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; 
v___x_6473_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6474_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6475_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6476_ = l_Lean_mkAppB(v___x_6475_, v___x_6474_, v___x_6473_);
return v___x_6476_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse(void){
_start:
{
lean_object* v___x_6477_; 
v___x_6477_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
return v___x_6477_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; 
v___x_6481_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6482_ = ((lean_object*)(l_Lean_eagerReflBoolTrue___closed__1));
v___x_6483_ = l_Lean_Expr_const___override(v___x_6482_, v___x_6481_);
return v___x_6483_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; 
v___x_6484_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6485_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6486_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6487_ = l_Lean_mkApp3(v___x_6486_, v___x_6485_, v___x_6484_, v___x_6484_);
return v___x_6487_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v___x_6490_; lean_object* v___x_6491_; 
v___x_6488_ = l_Lean_reflBoolTrue;
v___x_6489_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__3, &l_Lean_eagerReflBoolTrue___closed__3_once, _init_l_Lean_eagerReflBoolTrue___closed__3);
v___x_6490_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6491_ = l_Lean_mkAppB(v___x_6490_, v___x_6489_, v___x_6488_);
return v___x_6491_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue(void){
_start:
{
lean_object* v___x_6492_; 
v___x_6492_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__4, &l_Lean_eagerReflBoolTrue___closed__4_once, _init_l_Lean_eagerReflBoolTrue___closed__4);
return v___x_6492_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; lean_object* v___x_6496_; 
v___x_6493_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6494_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6495_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6496_ = l_Lean_mkApp3(v___x_6495_, v___x_6494_, v___x_6493_, v___x_6493_);
return v___x_6496_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6497_; lean_object* v___x_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; 
v___x_6497_ = l_Lean_reflBoolFalse;
v___x_6498_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__0, &l_Lean_eagerReflBoolFalse___closed__0_once, _init_l_Lean_eagerReflBoolFalse___closed__0);
v___x_6499_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6500_ = l_Lean_mkAppB(v___x_6499_, v___x_6498_, v___x_6497_);
return v___x_6500_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse(void){
_start:
{
lean_object* v___x_6501_; 
v___x_6501_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__1, &l_Lean_eagerReflBoolFalse___closed__1_once, _init_l_Lean_eagerReflBoolFalse___closed__1);
return v___x_6501_;
}
}
static lean_object* _init_l_Lean_Expr_replaceFn___closed__2(void){
_start:
{
lean_object* v___x_6504_; lean_object* v___x_6505_; lean_object* v___x_6506_; lean_object* v___x_6507_; lean_object* v___x_6508_; lean_object* v___x_6509_; 
v___x_6504_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__1));
v___x_6505_ = lean_unsigned_to_nat(9u);
v___x_6506_ = lean_unsigned_to_nat(2441u);
v___x_6507_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__0));
v___x_6508_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_6509_ = l_mkPanicMessageWithDecl(v___x_6508_, v___x_6507_, v___x_6506_, v___x_6505_, v___x_6504_);
return v___x_6509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object* v_e_6510_, lean_object* v_declName_6511_){
_start:
{
switch(lean_obj_tag(v_e_6510_))
{
case 5:
{
lean_object* v_fn_6512_; lean_object* v_arg_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; 
v_fn_6512_ = lean_ctor_get(v_e_6510_, 0);
lean_inc_ref(v_fn_6512_);
v_arg_6513_ = lean_ctor_get(v_e_6510_, 1);
lean_inc_ref(v_arg_6513_);
lean_dec_ref_known(v_e_6510_, 2);
v___x_6514_ = l_Lean_Expr_replaceFn(v_fn_6512_, v_declName_6511_);
v___x_6515_ = l_Lean_Expr_app___override(v___x_6514_, v_arg_6513_);
return v___x_6515_;
}
case 4:
{
lean_object* v_us_6516_; lean_object* v___x_6517_; 
v_us_6516_ = lean_ctor_get(v_e_6510_, 1);
lean_inc(v_us_6516_);
lean_dec_ref_known(v_e_6510_, 2);
v___x_6517_ = l_Lean_Expr_const___override(v_declName_6511_, v_us_6516_);
return v___x_6517_;
}
default: 
{
lean_object* v___x_6518_; lean_object* v___x_6519_; 
lean_dec(v_declName_6511_);
lean_dec_ref(v_e_6510_);
v___x_6518_ = lean_obj_once(&l_Lean_Expr_replaceFn___closed__2, &l_Lean_Expr_replaceFn___closed__2_once, _init_l_Lean_Expr_replaceFn___closed__2);
v___x_6519_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_6518_);
return v___x_6519_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Lean_Level(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Expr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
