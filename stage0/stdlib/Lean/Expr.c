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
LEAN_EXPORT uint8_t lean_expr_has_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVarEx___boxed(lean_object*);
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
static const lean_string_object l_Lean_mkSimpleThunkType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_mkSimpleThunkType___closed__0 = (const lean_object*)&l_Lean_mkSimpleThunkType___closed__0_value;
static const lean_ctor_object l_Lean_mkSimpleThunkType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkSimpleThunkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_mkSimpleThunkType___closed__1 = (const lean_object*)&l_Lean_mkSimpleThunkType___closed__1_value;
static lean_once_cell_t l_Lean_mkSimpleThunkType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkSimpleThunkType___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object*);
static const lean_string_object l_Lean_mkSimpleThunk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_mkSimpleThunk___closed__0 = (const lean_object*)&l_Lean_mkSimpleThunk___closed__0_value;
static const lean_ctor_object l_Lean_mkSimpleThunk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkSimpleThunk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_mkSimpleThunk___closed__1 = (const lean_object*)&l_Lean_mkSimpleThunk___closed__1_value;
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
LEAN_EXPORT uint8_t lean_is_out_param(lean_object*);
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
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_val_8_);
return v___x_9_;
}
else
{
lean_object* v_val_10_; lean_object* v___x_11_; 
v_val_10_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_val_10_);
lean_dec_ref(v_t_6_);
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
lean_object* v_r_522_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v_r_532_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v_r_545_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v_r_558_; lean_object* v_r_565_; lean_object* v___x_576_; uint64_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_r_580_; uint32_t v___x_581_; uint32_t v___x_582_; uint8_t v___x_583_; 
v___x_576_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__7));
v___x_577_ = l_Lean_Expr_Data_hash(v_v_519_);
v___x_578_ = lean_uint64_to_nat(v___x_577_);
v___x_579_ = l_Nat_reprFast(v___x_578_);
v_r_580_ = lean_string_append(v___x_576_, v___x_579_);
lean_dec_ref(v___x_579_);
v___x_581_ = l_Lean_Expr_Data_looseBVarRange(v_v_519_);
v___x_582_ = 0;
v___x_583_ = lean_uint32_dec_eq(v___x_581_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_r_590_; 
v___x_584_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__8));
v___x_585_ = lean_string_append(v_r_580_, v___x_584_);
v___x_586_ = lean_uint32_to_nat(v___x_581_);
v___x_587_ = l_Nat_reprFast(v___x_586_);
v___x_588_ = lean_string_append(v___x_585_, v___x_587_);
lean_dec_ref(v___x_587_);
v___x_589_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_590_ = lean_string_append(v___x_588_, v___x_589_);
v_r_565_ = v_r_590_;
goto v___jp_564_;
}
else
{
v_r_565_ = v_r_580_;
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
uint8_t v___x_566_; uint8_t v___x_567_; uint8_t v___x_568_; 
v___x_566_ = l_Lean_Expr_Data_approxDepth(v_v_519_);
v___x_567_ = 0;
v___x_568_ = lean_uint8_dec_eq(v___x_566_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_r_575_; 
v___x_569_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__6));
v___x_570_ = lean_string_append(v_r_565_, v___x_569_);
v___x_571_ = lean_uint8_to_nat(v___x_566_);
v___x_572_ = l_Nat_reprFast(v___x_571_);
v___x_573_ = lean_string_append(v___x_570_, v___x_572_);
lean_dec_ref(v___x_572_);
v___x_574_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_575_ = lean_string_append(v___x_573_, v___x_574_);
v_r_558_ = v_r_575_;
goto v___jp_557_;
}
else
{
v_r_558_ = v_r_565_;
goto v___jp_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0___boxed(lean_object* v_v_591_, lean_object* v_prec_592_){
_start:
{
uint64_t v_v_boxed_593_; lean_object* v_res_594_; 
v_v_boxed_593_ = lean_unbox_uint64(v_v_591_);
lean_dec_ref(v_v_591_);
v_res_594_ = l_Lean_instReprData__1___lam__0(v_v_boxed_593_, v_prec_592_);
lean_dec(v_prec_592_);
return v_res_594_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId_default(void){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = lean_box(0);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId(void){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = lean_box(0);
return v___x_598_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqFVarId_beq(lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = lean_name_eq(v_x_599_, v_x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
uint8_t v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l_Lean_instBEqFVarId_beq(v_x_602_, v_x_603_);
lean_dec(v_x_603_);
lean_dec(v_x_602_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
static uint64_t _init_l_Lean_instHashableFVarId_hash___closed__0(void){
_start:
{
lean_object* v___x_608_; uint64_t v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(1723u);
v___x_609_ = lean_uint64_of_nat(v___x_608_);
return v___x_609_;
}
}
static uint64_t _init_l_Lean_instHashableFVarId_hash___closed__1(void){
_start:
{
uint64_t v___x_610_; uint64_t v___x_611_; uint64_t v___x_612_; 
v___x_610_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
v___x_611_ = 0ULL;
v___x_612_ = lean_uint64_mix_hash(v___x_611_, v___x_610_);
return v___x_612_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableFVarId_hash(lean_object* v_x_613_){
_start:
{
uint64_t v___x_614_; 
v___x_614_ = 0ULL;
if (lean_obj_tag(v_x_613_) == 0)
{
uint64_t v___x_615_; 
v___x_615_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__1, &l_Lean_instHashableFVarId_hash___closed__1_once, _init_l_Lean_instHashableFVarId_hash___closed__1);
return v___x_615_;
}
else
{
uint64_t v_hash_616_; uint64_t v___x_617_; 
v_hash_616_ = lean_ctor_get_uint64(v_x_613_, sizeof(void*)*2);
v___x_617_ = lean_uint64_mix_hash(v___x_614_, v_hash_616_);
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object* v_x_618_){
_start:
{
uint64_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l_Lean_instHashableFVarId_hash(v_x_618_);
lean_dec(v_x_618_);
v_r_620_ = lean_box_uint64(v_res_619_);
return v_r_620_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lean_box(1);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet(void){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = lean_box(1);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = lean_box(1);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet(void){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_box(1);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___aux__1(lean_object* v_e_630_){
_start:
{
lean_object* v___f_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___f_631_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_632_ = lean_box(1);
lean_inc(v_e_630_);
v___x_633_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___f_631_, v_e_630_, v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_box(0);
v___x_635_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_631_, v_e_630_, v___x_634_, v___x_632_);
return v___x_635_;
}
else
{
lean_dec(v_e_630_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object* v_k_636_, lean_object* v_v_637_, lean_object* v_t_638_){
_start:
{
if (lean_obj_tag(v_t_638_) == 0)
{
lean_object* v_size_639_; lean_object* v_k_640_; lean_object* v_v_641_; lean_object* v_l_642_; lean_object* v_r_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_923_; 
v_size_639_ = lean_ctor_get(v_t_638_, 0);
v_k_640_ = lean_ctor_get(v_t_638_, 1);
v_v_641_ = lean_ctor_get(v_t_638_, 2);
v_l_642_ = lean_ctor_get(v_t_638_, 3);
v_r_643_ = lean_ctor_get(v_t_638_, 4);
v_isSharedCheck_923_ = !lean_is_exclusive(v_t_638_);
if (v_isSharedCheck_923_ == 0)
{
v___x_645_ = v_t_638_;
v_isShared_646_ = v_isSharedCheck_923_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_r_643_);
lean_inc(v_l_642_);
lean_inc(v_v_641_);
lean_inc(v_k_640_);
lean_inc(v_size_639_);
lean_dec(v_t_638_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_923_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
uint8_t v___x_647_; 
v___x_647_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_636_, v_k_640_);
switch(v___x_647_)
{
case 0:
{
lean_object* v_impl_648_; lean_object* v___x_649_; 
lean_dec(v_size_639_);
v_impl_648_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_636_, v_v_637_, v_l_642_);
v___x_649_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_643_) == 0)
{
lean_object* v_size_650_; lean_object* v_size_651_; lean_object* v_k_652_; lean_object* v_v_653_; lean_object* v_l_654_; lean_object* v_r_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_size_650_ = lean_ctor_get(v_r_643_, 0);
v_size_651_ = lean_ctor_get(v_impl_648_, 0);
lean_inc(v_size_651_);
v_k_652_ = lean_ctor_get(v_impl_648_, 1);
lean_inc(v_k_652_);
v_v_653_ = lean_ctor_get(v_impl_648_, 2);
lean_inc(v_v_653_);
v_l_654_ = lean_ctor_get(v_impl_648_, 3);
lean_inc(v_l_654_);
v_r_655_ = lean_ctor_get(v_impl_648_, 4);
lean_inc(v_r_655_);
v___x_656_ = lean_unsigned_to_nat(3u);
v___x_657_ = lean_nat_mul(v___x_656_, v_size_650_);
v___x_658_ = lean_nat_dec_lt(v___x_657_, v_size_651_);
lean_dec(v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
lean_dec(v_r_655_);
lean_dec(v_l_654_);
lean_dec(v_v_653_);
lean_dec(v_k_652_);
v___x_659_ = lean_nat_add(v___x_649_, v_size_651_);
lean_dec(v_size_651_);
v___x_660_ = lean_nat_add(v___x_659_, v_size_650_);
lean_dec(v___x_659_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 3, v_impl_648_);
lean_ctor_set(v___x_645_, 0, v___x_660_);
v___x_662_ = v___x_645_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_663_, 3, v_impl_648_);
lean_ctor_set(v_reuseFailAlloc_663_, 4, v_r_643_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
else
{
lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_729_; 
v_isSharedCheck_729_ = !lean_is_exclusive(v_impl_648_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; lean_object* v_unused_731_; lean_object* v_unused_732_; lean_object* v_unused_733_; lean_object* v_unused_734_; 
v_unused_730_ = lean_ctor_get(v_impl_648_, 4);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_impl_648_, 3);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_impl_648_, 2);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_impl_648_, 1);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_impl_648_, 0);
lean_dec(v_unused_734_);
v___x_665_ = v_impl_648_;
v_isShared_666_ = v_isSharedCheck_729_;
goto v_resetjp_664_;
}
else
{
lean_dec(v_impl_648_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_729_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_size_667_; lean_object* v_size_668_; lean_object* v_k_669_; lean_object* v_v_670_; lean_object* v_l_671_; lean_object* v_r_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v_size_667_ = lean_ctor_get(v_l_654_, 0);
v_size_668_ = lean_ctor_get(v_r_655_, 0);
v_k_669_ = lean_ctor_get(v_r_655_, 1);
v_v_670_ = lean_ctor_get(v_r_655_, 2);
v_l_671_ = lean_ctor_get(v_r_655_, 3);
v_r_672_ = lean_ctor_get(v_r_655_, 4);
v___x_673_ = lean_unsigned_to_nat(2u);
v___x_674_ = lean_nat_mul(v___x_673_, v_size_667_);
v___x_675_ = lean_nat_dec_lt(v_size_668_, v___x_674_);
lean_dec(v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_704_; 
lean_inc(v_r_672_);
lean_inc(v_l_671_);
lean_inc(v_v_670_);
lean_inc(v_k_669_);
v_isSharedCheck_704_ = !lean_is_exclusive(v_r_655_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; lean_object* v_unused_706_; lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; 
v_unused_705_ = lean_ctor_get(v_r_655_, 4);
lean_dec(v_unused_705_);
v_unused_706_ = lean_ctor_get(v_r_655_, 3);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_r_655_, 2);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_r_655_, 1);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_r_655_, 0);
lean_dec(v_unused_709_);
v___x_677_ = v_r_655_;
v_isShared_678_ = v_isSharedCheck_704_;
goto v_resetjp_676_;
}
else
{
lean_dec(v_r_655_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_704_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___x_692_; lean_object* v___y_694_; 
v___x_679_ = lean_nat_add(v___x_649_, v_size_651_);
lean_dec(v_size_651_);
v___x_680_ = lean_nat_add(v___x_679_, v_size_650_);
lean_dec(v___x_679_);
v___x_692_ = lean_nat_add(v___x_649_, v_size_667_);
if (lean_obj_tag(v_l_671_) == 0)
{
lean_object* v_size_702_; 
v_size_702_ = lean_ctor_get(v_l_671_, 0);
lean_inc(v_size_702_);
v___y_694_ = v_size_702_;
goto v___jp_693_;
}
else
{
lean_object* v___x_703_; 
v___x_703_ = lean_unsigned_to_nat(0u);
v___y_694_ = v___x_703_;
goto v___jp_693_;
}
v___jp_681_:
{
lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_685_ = lean_nat_add(v___y_682_, v___y_684_);
lean_dec(v___y_684_);
lean_dec(v___y_682_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 4, v_r_643_);
lean_ctor_set(v___x_677_, 3, v_r_672_);
lean_ctor_set(v___x_677_, 2, v_v_641_);
lean_ctor_set(v___x_677_, 1, v_k_640_);
lean_ctor_set(v___x_677_, 0, v___x_685_);
v___x_687_ = v___x_677_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_691_, 3, v_r_672_);
lean_ctor_set(v_reuseFailAlloc_691_, 4, v_r_643_);
v___x_687_ = v_reuseFailAlloc_691_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_689_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 4, v___x_687_);
lean_ctor_set(v___x_665_, 3, v___y_683_);
lean_ctor_set(v___x_665_, 2, v_v_670_);
lean_ctor_set(v___x_665_, 1, v_k_669_);
lean_ctor_set(v___x_665_, 0, v___x_680_);
v___x_689_ = v___x_665_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_k_669_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v_v_670_);
lean_ctor_set(v_reuseFailAlloc_690_, 3, v___y_683_);
lean_ctor_set(v_reuseFailAlloc_690_, 4, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
v___jp_693_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = lean_nat_add(v___x_692_, v___y_694_);
lean_dec(v___y_694_);
lean_dec(v___x_692_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 4, v_l_671_);
lean_ctor_set(v___x_645_, 3, v_l_654_);
lean_ctor_set(v___x_645_, 2, v_v_653_);
lean_ctor_set(v___x_645_, 1, v_k_652_);
lean_ctor_set(v___x_645_, 0, v___x_695_);
v___x_697_ = v___x_645_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_k_652_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_v_653_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_l_654_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_l_671_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; 
v___x_698_ = lean_nat_add(v___x_649_, v_size_650_);
if (lean_obj_tag(v_r_672_) == 0)
{
lean_object* v_size_699_; 
v_size_699_ = lean_ctor_get(v_r_672_, 0);
lean_inc(v_size_699_);
v___y_682_ = v___x_698_;
v___y_683_ = v___x_697_;
v___y_684_ = v_size_699_;
goto v___jp_681_;
}
else
{
lean_object* v___x_700_; 
v___x_700_ = lean_unsigned_to_nat(0u);
v___y_682_ = v___x_698_;
v___y_683_ = v___x_697_;
v___y_684_ = v___x_700_;
goto v___jp_681_;
}
}
}
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
lean_del_object(v___x_645_);
v___x_710_ = lean_nat_add(v___x_649_, v_size_651_);
lean_dec(v_size_651_);
v___x_711_ = lean_nat_add(v___x_710_, v_size_650_);
lean_dec(v___x_710_);
v___x_712_ = lean_nat_add(v___x_649_, v_size_650_);
v___x_713_ = lean_nat_add(v___x_712_, v_size_668_);
lean_dec(v___x_712_);
lean_inc_ref(v_r_643_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 4, v_r_643_);
lean_ctor_set(v___x_665_, 3, v_r_655_);
lean_ctor_set(v___x_665_, 2, v_v_641_);
lean_ctor_set(v___x_665_, 1, v_k_640_);
lean_ctor_set(v___x_665_, 0, v___x_713_);
v___x_715_ = v___x_665_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v_r_655_);
lean_ctor_set(v_reuseFailAlloc_728_, 4, v_r_643_);
v___x_715_ = v_reuseFailAlloc_728_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
v_isSharedCheck_722_ = !lean_is_exclusive(v_r_643_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; lean_object* v_unused_724_; lean_object* v_unused_725_; lean_object* v_unused_726_; lean_object* v_unused_727_; 
v_unused_723_ = lean_ctor_get(v_r_643_, 4);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_r_643_, 3);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v_r_643_, 2);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_r_643_, 1);
lean_dec(v_unused_726_);
v_unused_727_ = lean_ctor_get(v_r_643_, 0);
lean_dec(v_unused_727_);
v___x_717_ = v_r_643_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_dec(v_r_643_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 4, v___x_715_);
lean_ctor_set(v___x_717_, 3, v_l_654_);
lean_ctor_set(v___x_717_, 2, v_v_653_);
lean_ctor_set(v___x_717_, 1, v_k_652_);
lean_ctor_set(v___x_717_, 0, v___x_711_);
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_k_652_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_v_653_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_l_654_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v___x_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_735_; 
v_l_735_ = lean_ctor_get(v_impl_648_, 3);
lean_inc(v_l_735_);
if (lean_obj_tag(v_l_735_) == 0)
{
lean_object* v_r_736_; lean_object* v_k_737_; lean_object* v_v_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_749_; 
v_r_736_ = lean_ctor_get(v_impl_648_, 4);
v_k_737_ = lean_ctor_get(v_impl_648_, 1);
v_v_738_ = lean_ctor_get(v_impl_648_, 2);
v_isSharedCheck_749_ = !lean_is_exclusive(v_impl_648_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; lean_object* v_unused_751_; 
v_unused_750_ = lean_ctor_get(v_impl_648_, 3);
lean_dec(v_unused_750_);
v_unused_751_ = lean_ctor_get(v_impl_648_, 0);
lean_dec(v_unused_751_);
v___x_740_ = v_impl_648_;
v_isShared_741_ = v_isSharedCheck_749_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_r_736_);
lean_inc(v_v_738_);
lean_inc(v_k_737_);
lean_dec(v_impl_648_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_749_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_736_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 3, v_r_736_);
lean_ctor_set(v___x_740_, 2, v_v_641_);
lean_ctor_set(v___x_740_, 1, v_k_640_);
lean_ctor_set(v___x_740_, 0, v___x_649_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_r_736_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v_r_736_);
v___x_744_ = v_reuseFailAlloc_748_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_746_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 4, v___x_744_);
lean_ctor_set(v___x_645_, 3, v_l_735_);
lean_ctor_set(v___x_645_, 2, v_v_738_);
lean_ctor_set(v___x_645_, 1, v_k_737_);
lean_ctor_set(v___x_645_, 0, v___x_742_);
v___x_746_ = v___x_645_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_k_737_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_v_738_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_l_735_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_object* v_r_752_; 
v_r_752_ = lean_ctor_get(v_impl_648_, 4);
lean_inc(v_r_752_);
if (lean_obj_tag(v_r_752_) == 0)
{
lean_object* v_k_753_; lean_object* v_v_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_777_; 
v_k_753_ = lean_ctor_get(v_impl_648_, 1);
v_v_754_ = lean_ctor_get(v_impl_648_, 2);
v_isSharedCheck_777_ = !lean_is_exclusive(v_impl_648_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; lean_object* v_unused_779_; lean_object* v_unused_780_; 
v_unused_778_ = lean_ctor_get(v_impl_648_, 4);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_impl_648_, 3);
lean_dec(v_unused_779_);
v_unused_780_ = lean_ctor_get(v_impl_648_, 0);
lean_dec(v_unused_780_);
v___x_756_ = v_impl_648_;
v_isShared_757_ = v_isSharedCheck_777_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_v_754_);
lean_inc(v_k_753_);
lean_dec(v_impl_648_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_777_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_k_758_; lean_object* v_v_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_773_; 
v_k_758_ = lean_ctor_get(v_r_752_, 1);
v_v_759_ = lean_ctor_get(v_r_752_, 2);
v_isSharedCheck_773_ = !lean_is_exclusive(v_r_752_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; lean_object* v_unused_775_; lean_object* v_unused_776_; 
v_unused_774_ = lean_ctor_get(v_r_752_, 4);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_r_752_, 3);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_r_752_, 0);
lean_dec(v_unused_776_);
v___x_761_ = v_r_752_;
v_isShared_762_ = v_isSharedCheck_773_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_v_759_);
lean_inc(v_k_758_);
lean_dec(v_r_752_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_773_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = lean_unsigned_to_nat(3u);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 4, v_l_735_);
lean_ctor_set(v___x_761_, 3, v_l_735_);
lean_ctor_set(v___x_761_, 2, v_v_754_);
lean_ctor_set(v___x_761_, 1, v_k_753_);
lean_ctor_set(v___x_761_, 0, v___x_649_);
v___x_765_ = v___x_761_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_k_753_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_v_754_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_l_735_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_l_735_);
v___x_765_ = v_reuseFailAlloc_772_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v_l_735_);
lean_ctor_set(v___x_756_, 2, v_v_641_);
lean_ctor_set(v___x_756_, 1, v_k_640_);
lean_ctor_set(v___x_756_, 0, v___x_649_);
v___x_767_ = v___x_756_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_l_735_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_l_735_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 4, v___x_767_);
lean_ctor_set(v___x_645_, 3, v___x_765_);
lean_ctor_set(v___x_645_, 2, v_v_759_);
lean_ctor_set(v___x_645_, 1, v_k_758_);
lean_ctor_set(v___x_645_, 0, v___x_763_);
v___x_769_ = v___x_645_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_781_ = lean_unsigned_to_nat(2u);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 4, v_r_752_);
lean_ctor_set(v___x_645_, 3, v_impl_648_);
lean_ctor_set(v___x_645_, 0, v___x_781_);
v___x_783_ = v___x_645_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_impl_648_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_r_752_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
case 1:
{
lean_object* v___x_786_; 
lean_dec(v_v_641_);
lean_dec(v_k_640_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 2, v_v_637_);
lean_ctor_set(v___x_645_, 1, v_k_636_);
v___x_786_ = v___x_645_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_size_639_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_k_636_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_v_637_);
lean_ctor_set(v_reuseFailAlloc_787_, 3, v_l_642_);
lean_ctor_set(v_reuseFailAlloc_787_, 4, v_r_643_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
default: 
{
lean_object* v_impl_788_; lean_object* v___x_789_; 
lean_dec(v_size_639_);
v_impl_788_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_636_, v_v_637_, v_r_643_);
v___x_789_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_642_) == 0)
{
lean_object* v_size_790_; lean_object* v_size_791_; lean_object* v_k_792_; lean_object* v_v_793_; lean_object* v_l_794_; lean_object* v_r_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v_size_790_ = lean_ctor_get(v_l_642_, 0);
v_size_791_ = lean_ctor_get(v_impl_788_, 0);
lean_inc(v_size_791_);
v_k_792_ = lean_ctor_get(v_impl_788_, 1);
lean_inc(v_k_792_);
v_v_793_ = lean_ctor_get(v_impl_788_, 2);
lean_inc(v_v_793_);
v_l_794_ = lean_ctor_get(v_impl_788_, 3);
lean_inc(v_l_794_);
v_r_795_ = lean_ctor_get(v_impl_788_, 4);
lean_inc(v_r_795_);
v___x_796_ = lean_unsigned_to_nat(3u);
v___x_797_ = lean_nat_mul(v___x_796_, v_size_790_);
v___x_798_ = lean_nat_dec_lt(v___x_797_, v_size_791_);
lean_dec(v___x_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
lean_dec(v_r_795_);
lean_dec(v_l_794_);
lean_dec(v_v_793_);
lean_dec(v_k_792_);
v___x_799_ = lean_nat_add(v___x_789_, v_size_790_);
v___x_800_ = lean_nat_add(v___x_799_, v_size_791_);
lean_dec(v_size_791_);
lean_dec(v___x_799_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 4, v_impl_788_);
lean_ctor_set(v___x_645_, 0, v___x_800_);
v___x_802_ = v___x_645_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_803_, 3, v_l_642_);
lean_ctor_set(v_reuseFailAlloc_803_, 4, v_impl_788_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
else
{
lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_867_; 
v_isSharedCheck_867_ = !lean_is_exclusive(v_impl_788_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; lean_object* v_unused_869_; lean_object* v_unused_870_; lean_object* v_unused_871_; lean_object* v_unused_872_; 
v_unused_868_ = lean_ctor_get(v_impl_788_, 4);
lean_dec(v_unused_868_);
v_unused_869_ = lean_ctor_get(v_impl_788_, 3);
lean_dec(v_unused_869_);
v_unused_870_ = lean_ctor_get(v_impl_788_, 2);
lean_dec(v_unused_870_);
v_unused_871_ = lean_ctor_get(v_impl_788_, 1);
lean_dec(v_unused_871_);
v_unused_872_ = lean_ctor_get(v_impl_788_, 0);
lean_dec(v_unused_872_);
v___x_805_ = v_impl_788_;
v_isShared_806_ = v_isSharedCheck_867_;
goto v_resetjp_804_;
}
else
{
lean_dec(v_impl_788_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_867_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_size_807_; lean_object* v_k_808_; lean_object* v_v_809_; lean_object* v_l_810_; lean_object* v_r_811_; lean_object* v_size_812_; lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v_size_807_ = lean_ctor_get(v_l_794_, 0);
v_k_808_ = lean_ctor_get(v_l_794_, 1);
v_v_809_ = lean_ctor_get(v_l_794_, 2);
v_l_810_ = lean_ctor_get(v_l_794_, 3);
v_r_811_ = lean_ctor_get(v_l_794_, 4);
v_size_812_ = lean_ctor_get(v_r_795_, 0);
v___x_813_ = lean_unsigned_to_nat(2u);
v___x_814_ = lean_nat_mul(v___x_813_, v_size_812_);
v___x_815_ = lean_nat_dec_lt(v_size_807_, v___x_814_);
lean_dec(v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_843_; 
lean_inc(v_r_811_);
lean_inc(v_l_810_);
lean_inc(v_v_809_);
lean_inc(v_k_808_);
v_isSharedCheck_843_ = !lean_is_exclusive(v_l_794_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; lean_object* v_unused_845_; lean_object* v_unused_846_; lean_object* v_unused_847_; lean_object* v_unused_848_; 
v_unused_844_ = lean_ctor_get(v_l_794_, 4);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_l_794_, 3);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v_l_794_, 2);
lean_dec(v_unused_846_);
v_unused_847_ = lean_ctor_get(v_l_794_, 1);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_l_794_, 0);
lean_dec(v_unused_848_);
v___x_817_ = v_l_794_;
v_isShared_818_ = v_isSharedCheck_843_;
goto v_resetjp_816_;
}
else
{
lean_dec(v_l_794_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_843_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_833_; 
v___x_819_ = lean_nat_add(v___x_789_, v_size_790_);
v___x_820_ = lean_nat_add(v___x_819_, v_size_791_);
lean_dec(v_size_791_);
if (lean_obj_tag(v_l_810_) == 0)
{
lean_object* v_size_841_; 
v_size_841_ = lean_ctor_get(v_l_810_, 0);
lean_inc(v_size_841_);
v___y_833_ = v_size_841_;
goto v___jp_832_;
}
else
{
lean_object* v___x_842_; 
v___x_842_ = lean_unsigned_to_nat(0u);
v___y_833_ = v___x_842_;
goto v___jp_832_;
}
v___jp_821_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_nat_add(v___y_822_, v___y_824_);
lean_dec(v___y_824_);
lean_dec(v___y_822_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 4, v_r_795_);
lean_ctor_set(v___x_817_, 3, v_r_811_);
lean_ctor_set(v___x_817_, 2, v_v_793_);
lean_ctor_set(v___x_817_, 1, v_k_792_);
lean_ctor_set(v___x_817_, 0, v___x_825_);
v___x_827_ = v___x_817_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_k_792_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_v_793_);
lean_ctor_set(v_reuseFailAlloc_831_, 3, v_r_811_);
lean_ctor_set(v_reuseFailAlloc_831_, 4, v_r_795_);
v___x_827_ = v_reuseFailAlloc_831_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_829_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 4, v___x_827_);
lean_ctor_set(v___x_805_, 3, v___y_823_);
lean_ctor_set(v___x_805_, 2, v_v_809_);
lean_ctor_set(v___x_805_, 1, v_k_808_);
lean_ctor_set(v___x_805_, 0, v___x_820_);
v___x_829_ = v___x_805_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_k_808_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v_v_809_);
lean_ctor_set(v_reuseFailAlloc_830_, 3, v___y_823_);
lean_ctor_set(v_reuseFailAlloc_830_, 4, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
v___jp_832_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = lean_nat_add(v___x_819_, v___y_833_);
lean_dec(v___y_833_);
lean_dec(v___x_819_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 4, v_l_810_);
lean_ctor_set(v___x_645_, 0, v___x_834_);
v___x_836_ = v___x_645_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_l_642_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v_l_810_);
v___x_836_ = v_reuseFailAlloc_840_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; 
v___x_837_ = lean_nat_add(v___x_789_, v_size_812_);
if (lean_obj_tag(v_r_811_) == 0)
{
lean_object* v_size_838_; 
v_size_838_ = lean_ctor_get(v_r_811_, 0);
lean_inc(v_size_838_);
v___y_822_ = v___x_837_;
v___y_823_ = v___x_836_;
v___y_824_ = v_size_838_;
goto v___jp_821_;
}
else
{
lean_object* v___x_839_; 
v___x_839_ = lean_unsigned_to_nat(0u);
v___y_822_ = v___x_837_;
v___y_823_ = v___x_836_;
v___y_824_ = v___x_839_;
goto v___jp_821_;
}
}
}
}
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
lean_del_object(v___x_645_);
v___x_849_ = lean_nat_add(v___x_789_, v_size_790_);
v___x_850_ = lean_nat_add(v___x_849_, v_size_791_);
lean_dec(v_size_791_);
v___x_851_ = lean_nat_add(v___x_849_, v_size_807_);
lean_dec(v___x_849_);
lean_inc_ref(v_l_642_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 4, v_l_794_);
lean_ctor_set(v___x_805_, 3, v_l_642_);
lean_ctor_set(v___x_805_, 2, v_v_641_);
lean_ctor_set(v___x_805_, 1, v_k_640_);
lean_ctor_set(v___x_805_, 0, v___x_851_);
v___x_853_ = v___x_805_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v_l_642_);
lean_ctor_set(v_reuseFailAlloc_866_, 4, v_l_794_);
v___x_853_ = v_reuseFailAlloc_866_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_isSharedCheck_860_ = !lean_is_exclusive(v_l_642_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; lean_object* v_unused_862_; lean_object* v_unused_863_; lean_object* v_unused_864_; lean_object* v_unused_865_; 
v_unused_861_ = lean_ctor_get(v_l_642_, 4);
lean_dec(v_unused_861_);
v_unused_862_ = lean_ctor_get(v_l_642_, 3);
lean_dec(v_unused_862_);
v_unused_863_ = lean_ctor_get(v_l_642_, 2);
lean_dec(v_unused_863_);
v_unused_864_ = lean_ctor_get(v_l_642_, 1);
lean_dec(v_unused_864_);
v_unused_865_ = lean_ctor_get(v_l_642_, 0);
lean_dec(v_unused_865_);
v___x_855_ = v_l_642_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_dec(v_l_642_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 4, v_r_795_);
lean_ctor_set(v___x_855_, 3, v___x_853_);
lean_ctor_set(v___x_855_, 2, v_v_793_);
lean_ctor_set(v___x_855_, 1, v_k_792_);
lean_ctor_set(v___x_855_, 0, v___x_850_);
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_k_792_);
lean_ctor_set(v_reuseFailAlloc_859_, 2, v_v_793_);
lean_ctor_set(v_reuseFailAlloc_859_, 3, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_859_, 4, v_r_795_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_873_; 
v_l_873_ = lean_ctor_get(v_impl_788_, 3);
lean_inc(v_l_873_);
if (lean_obj_tag(v_l_873_) == 0)
{
lean_object* v_r_874_; lean_object* v_k_875_; lean_object* v_v_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_899_; 
v_r_874_ = lean_ctor_get(v_impl_788_, 4);
v_k_875_ = lean_ctor_get(v_impl_788_, 1);
v_v_876_ = lean_ctor_get(v_impl_788_, 2);
v_isSharedCheck_899_ = !lean_is_exclusive(v_impl_788_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; lean_object* v_unused_901_; 
v_unused_900_ = lean_ctor_get(v_impl_788_, 3);
lean_dec(v_unused_900_);
v_unused_901_ = lean_ctor_get(v_impl_788_, 0);
lean_dec(v_unused_901_);
v___x_878_ = v_impl_788_;
v_isShared_879_ = v_isSharedCheck_899_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_r_874_);
lean_inc(v_v_876_);
lean_inc(v_k_875_);
lean_dec(v_impl_788_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_899_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_k_880_; lean_object* v_v_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_895_; 
v_k_880_ = lean_ctor_get(v_l_873_, 1);
v_v_881_ = lean_ctor_get(v_l_873_, 2);
v_isSharedCheck_895_ = !lean_is_exclusive(v_l_873_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; lean_object* v_unused_897_; lean_object* v_unused_898_; 
v_unused_896_ = lean_ctor_get(v_l_873_, 4);
lean_dec(v_unused_896_);
v_unused_897_ = lean_ctor_get(v_l_873_, 3);
lean_dec(v_unused_897_);
v_unused_898_ = lean_ctor_get(v_l_873_, 0);
lean_dec(v_unused_898_);
v___x_883_ = v_l_873_;
v_isShared_884_ = v_isSharedCheck_895_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_v_881_);
lean_inc(v_k_880_);
lean_dec(v_l_873_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_895_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_874_, 2);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 4, v_r_874_);
lean_ctor_set(v___x_883_, 3, v_r_874_);
lean_ctor_set(v___x_883_, 2, v_v_641_);
lean_ctor_set(v___x_883_, 1, v_k_640_);
lean_ctor_set(v___x_883_, 0, v___x_789_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_r_874_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v_r_874_);
v___x_887_ = v_reuseFailAlloc_894_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_889_; 
lean_inc(v_r_874_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 3, v_r_874_);
lean_ctor_set(v___x_878_, 0, v___x_789_);
v___x_889_ = v___x_878_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_k_875_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_v_876_);
lean_ctor_set(v_reuseFailAlloc_893_, 3, v_r_874_);
lean_ctor_set(v_reuseFailAlloc_893_, 4, v_r_874_);
v___x_889_ = v_reuseFailAlloc_893_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_891_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 4, v___x_889_);
lean_ctor_set(v___x_645_, 3, v___x_887_);
lean_ctor_set(v___x_645_, 2, v_v_881_);
lean_ctor_set(v___x_645_, 1, v_k_880_);
lean_ctor_set(v___x_645_, 0, v___x_885_);
v___x_891_ = v___x_645_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_k_880_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_v_881_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_892_, 4, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
}
else
{
lean_object* v_r_902_; 
v_r_902_ = lean_ctor_get(v_impl_788_, 4);
lean_inc(v_r_902_);
if (lean_obj_tag(v_r_902_) == 0)
{
lean_object* v_k_903_; lean_object* v_v_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_915_; 
v_k_903_ = lean_ctor_get(v_impl_788_, 1);
v_v_904_ = lean_ctor_get(v_impl_788_, 2);
v_isSharedCheck_915_ = !lean_is_exclusive(v_impl_788_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; lean_object* v_unused_917_; lean_object* v_unused_918_; 
v_unused_916_ = lean_ctor_get(v_impl_788_, 4);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_impl_788_, 3);
lean_dec(v_unused_917_);
v_unused_918_ = lean_ctor_get(v_impl_788_, 0);
lean_dec(v_unused_918_);
v___x_906_ = v_impl_788_;
v_isShared_907_ = v_isSharedCheck_915_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_v_904_);
lean_inc(v_k_903_);
lean_dec(v_impl_788_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_915_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = lean_unsigned_to_nat(3u);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 4, v_l_873_);
lean_ctor_set(v___x_906_, 2, v_v_641_);
lean_ctor_set(v___x_906_, 1, v_k_640_);
lean_ctor_set(v___x_906_, 0, v___x_789_);
v___x_910_ = v___x_906_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v_l_873_);
lean_ctor_set(v_reuseFailAlloc_914_, 4, v_l_873_);
v___x_910_ = v_reuseFailAlloc_914_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_912_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 4, v_r_902_);
lean_ctor_set(v___x_645_, 3, v___x_910_);
lean_ctor_set(v___x_645_, 2, v_v_904_);
lean_ctor_set(v___x_645_, 1, v_k_903_);
lean_ctor_set(v___x_645_, 0, v___x_908_);
v___x_912_ = v___x_645_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_k_903_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_v_904_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_r_902_);
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
else
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = lean_unsigned_to_nat(2u);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 4, v_impl_788_);
lean_ctor_set(v___x_645_, 3, v_r_902_);
lean_ctor_set(v___x_645_, 0, v___x_919_);
v___x_921_ = v___x_645_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_r_902_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v_impl_788_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
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
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v_k_636_);
lean_ctor_set(v___x_925_, 2, v_v_637_);
lean_ctor_set(v___x_925_, 3, v_t_638_);
lean_ctor_set(v___x_925_, 4, v_t_638_);
return v___x_925_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(lean_object* v_k_926_, lean_object* v_t_927_){
_start:
{
if (lean_obj_tag(v_t_927_) == 0)
{
lean_object* v_k_928_; lean_object* v_l_929_; lean_object* v_r_930_; uint8_t v___x_931_; 
v_k_928_ = lean_ctor_get(v_t_927_, 1);
v_l_929_ = lean_ctor_get(v_t_927_, 3);
v_r_930_ = lean_ctor_get(v_t_927_, 4);
v___x_931_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_926_, v_k_928_);
switch(v___x_931_)
{
case 0:
{
v_t_927_ = v_l_929_;
goto _start;
}
case 1:
{
uint8_t v___x_933_; 
v___x_933_ = 1;
return v___x_933_;
}
default: 
{
v_t_927_ = v_r_930_;
goto _start;
}
}
}
else
{
uint8_t v___x_935_; 
v___x_935_ = 0;
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg___boxed(lean_object* v_k_936_, lean_object* v_t_937_){
_start:
{
uint8_t v_res_938_; lean_object* v_r_939_; 
v_res_938_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_936_, v_t_937_);
lean_dec(v_t_937_);
lean_dec(v_k_936_);
v_r_939_ = lean_box(v_res_938_);
return v_r_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object* v___y_940_){
_start:
{
lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_941_ = lean_box(1);
v___x_942_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v___y_940_, v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_box(0);
v___x_944_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___y_940_, v___x_943_, v___x_941_);
return v___x_944_;
}
else
{
lean_dec(v___y_940_);
return v___x_941_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(lean_object* v_00_u03b2_947_, lean_object* v_k_948_, lean_object* v_t_949_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_948_, v_t_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___boxed(lean_object* v_00_u03b2_951_, lean_object* v_k_952_, lean_object* v_t_953_){
_start:
{
uint8_t v_res_954_; lean_object* v_r_955_; 
v_res_954_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(v_00_u03b2_951_, v_k_952_, v_t_953_);
lean_dec(v_t_953_);
lean_dec(v_k_952_);
v_r_955_ = lean_box(v_res_954_);
return v_r_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1(lean_object* v_00_u03b2_956_, lean_object* v_k_957_, lean_object* v_v_958_, lean_object* v_t_959_, lean_object* v_hl_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_957_, v_v_958_, v_t_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_962_, lean_object* v_a_963_, lean_object* v_b_964_, lean_object* v_c_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = lean_apply_2(v_f_962_, v_a_963_, v_c_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_967_, lean_object* v_____do__lift_968_){
_start:
{
lean_object* v_a_969_; lean_object* v___x_970_; 
v_a_969_ = lean_ctor_get(v_____do__lift_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref(v_____do__lift_968_);
v___x_970_ = lean_apply_2(v_toPure_967_, lean_box(0), v_a_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg(lean_object* v_inst_971_, lean_object* v_m_972_, lean_object* v_init_973_, lean_object* v_f_974_){
_start:
{
lean_object* v_toApplicative_975_; lean_object* v_toBind_976_; lean_object* v_toPure_977_; lean_object* v___f_978_; lean_object* v___x_979_; lean_object* v___f_980_; lean_object* v___x_981_; 
v_toApplicative_975_ = lean_ctor_get(v_inst_971_, 0);
v_toBind_976_ = lean_ctor_get(v_inst_971_, 1);
lean_inc(v_toBind_976_);
v_toPure_977_ = lean_ctor_get(v_toApplicative_975_, 1);
lean_inc(v_toPure_977_);
v___f_978_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_978_, 0, v_f_974_);
v___x_979_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_971_, v___f_978_, v_init_973_, v_m_972_);
v___f_980_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_980_, 0, v_toPure_977_);
v___x_981_ = lean_apply_4(v_toBind_976_, lean_box(0), lean_box(0), v___x_979_, v___f_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1(lean_object* v_m_982_, lean_object* v_inst_983_, lean_object* v_00_u03b2_984_, lean_object* v_m_985_, lean_object* v_init_986_, lean_object* v_f_987_){
_start:
{
lean_object* v_toApplicative_988_; lean_object* v_toBind_989_; lean_object* v_toPure_990_; lean_object* v___f_991_; lean_object* v___x_992_; lean_object* v___f_993_; lean_object* v___x_994_; 
v_toApplicative_988_ = lean_ctor_get(v_inst_983_, 0);
v_toBind_989_ = lean_ctor_get(v_inst_983_, 1);
lean_inc(v_toBind_989_);
v_toPure_990_ = lean_ctor_get(v_toApplicative_988_, 1);
lean_inc(v_toPure_990_);
v___f_991_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_991_, 0, v_f_987_);
v___x_992_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_983_, v___f_991_, v_init_986_, v_m_985_);
v___f_993_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_993_, 0, v_toPure_990_);
v___x_994_ = lean_apply_4(v_toBind_989_, lean_box(0), lean_box(0), v___x_992_, v___f_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___redArg(lean_object* v_inst_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_996_, 0, lean_box(0));
lean_closure_set(v___x_996_, 1, v_inst_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad(lean_object* v_m_997_, lean_object* v_inst_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_999_, 0, lean_box(0));
lean_closure_set(v___x_999_, 1, v_inst_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object* v_s_1000_, lean_object* v_fvarId_1001_){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_fvarId_1001_, v_s_1000_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_box(0);
v___x_1004_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1001_, v___x_1003_, v_s_1000_);
return v___x_1004_;
}
else
{
lean_dec(v_fvarId_1001_);
return v_s_1000_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(lean_object* v_init_1005_, lean_object* v_x_1006_){
_start:
{
if (lean_obj_tag(v_x_1006_) == 0)
{
lean_object* v_k_1007_; lean_object* v_l_1008_; lean_object* v_r_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_k_1007_ = lean_ctor_get(v_x_1006_, 1);
lean_inc(v_k_1007_);
v_l_1008_ = lean_ctor_get(v_x_1006_, 3);
lean_inc(v_l_1008_);
v_r_1009_ = lean_ctor_get(v_x_1006_, 4);
lean_inc(v_r_1009_);
lean_dec_ref(v_x_1006_);
v___x_1010_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_1005_, v_l_1008_);
v___x_1011_ = l_Lean_FVarIdSet_insert(v___x_1010_, v_k_1007_);
v_init_1005_ = v___x_1011_;
v_x_1006_ = v_r_1009_;
goto _start;
}
else
{
return v_init_1005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_union(lean_object* v_vs_u2081_1013_, lean_object* v_vs_u2082_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_vs_u2082_1014_, v_vs_u2081_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0(lean_object* v_init_1016_, lean_object* v_t_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_1016_, v_t_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList(lean_object* v_l_1019_){
_start:
{
lean_object* v___f_1020_; lean_object* v___x_1021_; 
v___f_1020_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1021_ = l_Std_TreeSet_ofList___redArg(v_l_1019_, v___f_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList___boxed(lean_object* v_l_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_FVarIdSet_ofList(v_l_1022_);
lean_dec(v_l_1022_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object* v_l_1024_){
_start:
{
lean_object* v___f_1025_; lean_object* v___x_1026_; 
v___f_1025_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1026_ = l_Std_TreeSet_ofArray___redArg(v_l_1024_, v___f_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object* v_l_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_FVarIdSet_ofArray(v_l_1027_);
lean_dec_ref(v_l_1027_);
return v_res_1028_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_unsigned_to_nat(16u);
v___x_1031_ = lean_mk_array(v___x_1030_, v___x_1029_);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0);
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v___x_1032_);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet(void){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1037_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet(void){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object* v_s_1039_, lean_object* v_fvarId_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1040_, v_a_1041_, v_s_1039_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object* v_00_u03b1_1043_, lean_object* v_s_1044_, lean_object* v_fvarId_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1045_, v_a_1046_, v_s_1044_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1(lean_object* v_00_u03b1_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_box(1);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* v_00_u03b1_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_box(1);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* v_00_u03b1_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_box(1);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId_default(void){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_box(0);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId(void){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_box(0);
return v___x_1055_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMVarId_beq(lean_object* v_x_1056_, lean_object* v_x_1057_){
_start:
{
uint8_t v___x_1058_; 
v___x_1058_ = lean_name_eq(v_x_1056_, v_x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object* v_x_1059_, lean_object* v_x_1060_){
_start:
{
uint8_t v_res_1061_; lean_object* v_r_1062_; 
v_res_1061_ = l_Lean_instBEqMVarId_beq(v_x_1059_, v_x_1060_);
lean_dec(v_x_1060_);
lean_dec(v_x_1059_);
v_r_1062_ = lean_box(v_res_1061_);
return v_r_1062_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableMVarId_hash(lean_object* v_x_1065_){
_start:
{
uint64_t v___x_1066_; 
v___x_1066_ = 0ULL;
if (lean_obj_tag(v_x_1065_) == 0)
{
uint64_t v___x_1067_; 
v___x_1067_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__1, &l_Lean_instHashableFVarId_hash___closed__1_once, _init_l_Lean_instHashableFVarId_hash___closed__1);
return v___x_1067_;
}
else
{
uint64_t v_hash_1068_; uint64_t v___x_1069_; 
v_hash_1068_ = lean_ctor_get_uint64(v_x_1065_, sizeof(void*)*2);
v___x_1069_ = lean_uint64_mix_hash(v___x_1066_, v_hash_1068_);
return v___x_1069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object* v_x_1070_){
_start:
{
uint64_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Lean_instHashableMVarId_hash(v_x_1070_);
lean_dec(v_x_1070_);
v_r_1072_ = lean_box_uint64(v_res_1071_);
return v_r_1072_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_box(1);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet(void){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_box(1);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_box(1);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet(void){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_box(1);
return v___x_1079_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object* v_k_1080_, lean_object* v_t_1081_){
_start:
{
if (lean_obj_tag(v_t_1081_) == 0)
{
lean_object* v_k_1082_; lean_object* v_l_1083_; lean_object* v_r_1084_; uint8_t v___x_1085_; 
v_k_1082_ = lean_ctor_get(v_t_1081_, 1);
v_l_1083_ = lean_ctor_get(v_t_1081_, 3);
v_r_1084_ = lean_ctor_get(v_t_1081_, 4);
v___x_1085_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1080_, v_k_1082_);
switch(v___x_1085_)
{
case 0:
{
v_t_1081_ = v_l_1083_;
goto _start;
}
case 1:
{
uint8_t v___x_1087_; 
v___x_1087_ = 1;
return v___x_1087_;
}
default: 
{
v_t_1081_ = v_r_1084_;
goto _start;
}
}
}
else
{
uint8_t v___x_1089_; 
v___x_1089_ = 0;
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object* v_k_1090_, lean_object* v_t_1091_){
_start:
{
uint8_t v_res_1092_; lean_object* v_r_1093_; 
v_res_1092_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1090_, v_t_1091_);
lean_dec(v_t_1091_);
lean_dec(v_k_1090_);
v_r_1093_ = lean_box(v_res_1092_);
return v_r_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object* v_k_1094_, lean_object* v_v_1095_, lean_object* v_t_1096_){
_start:
{
if (lean_obj_tag(v_t_1096_) == 0)
{
lean_object* v_size_1097_; lean_object* v_k_1098_; lean_object* v_v_1099_; lean_object* v_l_1100_; lean_object* v_r_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1381_; 
v_size_1097_ = lean_ctor_get(v_t_1096_, 0);
v_k_1098_ = lean_ctor_get(v_t_1096_, 1);
v_v_1099_ = lean_ctor_get(v_t_1096_, 2);
v_l_1100_ = lean_ctor_get(v_t_1096_, 3);
v_r_1101_ = lean_ctor_get(v_t_1096_, 4);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_t_1096_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1103_ = v_t_1096_;
v_isShared_1104_ = v_isSharedCheck_1381_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_r_1101_);
lean_inc(v_l_1100_);
lean_inc(v_v_1099_);
lean_inc(v_k_1098_);
lean_inc(v_size_1097_);
lean_dec(v_t_1096_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1381_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
uint8_t v___x_1105_; 
v___x_1105_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1094_, v_k_1098_);
switch(v___x_1105_)
{
case 0:
{
lean_object* v_impl_1106_; lean_object* v___x_1107_; 
lean_dec(v_size_1097_);
v_impl_1106_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1094_, v_v_1095_, v_l_1100_);
v___x_1107_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1101_) == 0)
{
lean_object* v_size_1108_; lean_object* v_size_1109_; lean_object* v_k_1110_; lean_object* v_v_1111_; lean_object* v_l_1112_; lean_object* v_r_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_size_1108_ = lean_ctor_get(v_r_1101_, 0);
v_size_1109_ = lean_ctor_get(v_impl_1106_, 0);
lean_inc(v_size_1109_);
v_k_1110_ = lean_ctor_get(v_impl_1106_, 1);
lean_inc(v_k_1110_);
v_v_1111_ = lean_ctor_get(v_impl_1106_, 2);
lean_inc(v_v_1111_);
v_l_1112_ = lean_ctor_get(v_impl_1106_, 3);
lean_inc(v_l_1112_);
v_r_1113_ = lean_ctor_get(v_impl_1106_, 4);
lean_inc(v_r_1113_);
v___x_1114_ = lean_unsigned_to_nat(3u);
v___x_1115_ = lean_nat_mul(v___x_1114_, v_size_1108_);
v___x_1116_ = lean_nat_dec_lt(v___x_1115_, v_size_1109_);
lean_dec(v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
lean_dec(v_r_1113_);
lean_dec(v_l_1112_);
lean_dec(v_v_1111_);
lean_dec(v_k_1110_);
v___x_1117_ = lean_nat_add(v___x_1107_, v_size_1109_);
lean_dec(v_size_1109_);
v___x_1118_ = lean_nat_add(v___x_1117_, v_size_1108_);
lean_dec(v___x_1117_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 3, v_impl_1106_);
lean_ctor_set(v___x_1103_, 0, v___x_1118_);
v___x_1120_ = v___x_1103_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_k_1098_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_v_1099_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_impl_1106_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_r_1101_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
else
{
lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1187_; 
v_isSharedCheck_1187_ = !lean_is_exclusive(v_impl_1106_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; lean_object* v_unused_1189_; lean_object* v_unused_1190_; lean_object* v_unused_1191_; lean_object* v_unused_1192_; 
v_unused_1188_ = lean_ctor_get(v_impl_1106_, 4);
lean_dec(v_unused_1188_);
v_unused_1189_ = lean_ctor_get(v_impl_1106_, 3);
lean_dec(v_unused_1189_);
v_unused_1190_ = lean_ctor_get(v_impl_1106_, 2);
lean_dec(v_unused_1190_);
v_unused_1191_ = lean_ctor_get(v_impl_1106_, 1);
lean_dec(v_unused_1191_);
v_unused_1192_ = lean_ctor_get(v_impl_1106_, 0);
lean_dec(v_unused_1192_);
v___x_1123_ = v_impl_1106_;
v_isShared_1124_ = v_isSharedCheck_1187_;
goto v_resetjp_1122_;
}
else
{
lean_dec(v_impl_1106_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1187_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_size_1125_; lean_object* v_size_1126_; lean_object* v_k_1127_; lean_object* v_v_1128_; lean_object* v_l_1129_; lean_object* v_r_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_size_1125_ = lean_ctor_get(v_l_1112_, 0);
v_size_1126_ = lean_ctor_get(v_r_1113_, 0);
v_k_1127_ = lean_ctor_get(v_r_1113_, 1);
v_v_1128_ = lean_ctor_get(v_r_1113_, 2);
v_l_1129_ = lean_ctor_get(v_r_1113_, 3);
v_r_1130_ = lean_ctor_get(v_r_1113_, 4);
v___x_1131_ = lean_unsigned_to_nat(2u);
v___x_1132_ = lean_nat_mul(v___x_1131_, v_size_1125_);
v___x_1133_ = lean_nat_dec_lt(v_size_1126_, v___x_1132_);
lean_dec(v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1162_; 
lean_inc(v_r_1130_);
lean_inc(v_l_1129_);
lean_inc(v_v_1128_);
lean_inc(v_k_1127_);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_r_1113_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; lean_object* v_unused_1164_; lean_object* v_unused_1165_; lean_object* v_unused_1166_; lean_object* v_unused_1167_; 
v_unused_1163_ = lean_ctor_get(v_r_1113_, 4);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_r_1113_, 3);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_r_1113_, 2);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_r_1113_, 1);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v_r_1113_, 0);
lean_dec(v_unused_1167_);
v___x_1135_ = v_r_1113_;
v_isShared_1136_ = v_isSharedCheck_1162_;
goto v_resetjp_1134_;
}
else
{
lean_dec(v_r_1113_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1162_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___x_1150_; lean_object* v___y_1152_; 
v___x_1137_ = lean_nat_add(v___x_1107_, v_size_1109_);
lean_dec(v_size_1109_);
v___x_1138_ = lean_nat_add(v___x_1137_, v_size_1108_);
lean_dec(v___x_1137_);
v___x_1150_ = lean_nat_add(v___x_1107_, v_size_1125_);
if (lean_obj_tag(v_l_1129_) == 0)
{
lean_object* v_size_1160_; 
v_size_1160_ = lean_ctor_get(v_l_1129_, 0);
lean_inc(v_size_1160_);
v___y_1152_ = v_size_1160_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_unsigned_to_nat(0u);
v___y_1152_ = v___x_1161_;
goto v___jp_1151_;
}
v___jp_1139_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = lean_nat_add(v___y_1140_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec(v___y_1140_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 4, v_r_1101_);
lean_ctor_set(v___x_1135_, 3, v_r_1130_);
lean_ctor_set(v___x_1135_, 2, v_v_1099_);
lean_ctor_set(v___x_1135_, 1, v_k_1098_);
lean_ctor_set(v___x_1135_, 0, v___x_1143_);
v___x_1145_ = v___x_1135_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_k_1098_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_v_1099_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_r_1130_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_r_1101_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 4, v___x_1145_);
lean_ctor_set(v___x_1123_, 3, v___y_1141_);
lean_ctor_set(v___x_1123_, 2, v_v_1128_);
lean_ctor_set(v___x_1123_, 1, v_k_1127_);
lean_ctor_set(v___x_1123_, 0, v___x_1138_);
v___x_1147_ = v___x_1123_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_k_1127_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_v_1128_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v___y_1141_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
v___jp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = lean_nat_add(v___x_1150_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec(v___x_1150_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v_l_1129_);
lean_ctor_set(v___x_1103_, 3, v_l_1112_);
lean_ctor_set(v___x_1103_, 2, v_v_1111_);
lean_ctor_set(v___x_1103_, 1, v_k_1110_);
lean_ctor_set(v___x_1103_, 0, v___x_1153_);
v___x_1155_ = v___x_1103_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_k_1110_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_v_1111_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_l_1112_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_l_1129_);
v___x_1155_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_nat_add(v___x_1107_, v_size_1108_);
if (lean_obj_tag(v_r_1130_) == 0)
{
lean_object* v_size_1157_; 
v_size_1157_ = lean_ctor_get(v_r_1130_, 0);
lean_inc(v_size_1157_);
v___y_1140_ = v___x_1156_;
v___y_1141_ = v___x_1155_;
v___y_1142_ = v_size_1157_;
goto v___jp_1139_;
}
else
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_unsigned_to_nat(0u);
v___y_1140_ = v___x_1156_;
v___y_1141_ = v___x_1155_;
v___y_1142_ = v___x_1158_;
goto v___jp_1139_;
}
}
}
}
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_del_object(v___x_1103_);
v___x_1168_ = lean_nat_add(v___x_1107_, v_size_1109_);
lean_dec(v_size_1109_);
v___x_1169_ = lean_nat_add(v___x_1168_, v_size_1108_);
lean_dec(v___x_1168_);
v___x_1170_ = lean_nat_add(v___x_1107_, v_size_1108_);
v___x_1171_ = lean_nat_add(v___x_1170_, v_size_1126_);
lean_dec(v___x_1170_);
lean_inc_ref(v_r_1101_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 4, v_r_1101_);
lean_ctor_set(v___x_1123_, 3, v_r_1113_);
lean_ctor_set(v___x_1123_, 2, v_v_1099_);
lean_ctor_set(v___x_1123_, 1, v_k_1098_);
lean_ctor_set(v___x_1123_, 0, v___x_1171_);
v___x_1173_ = v___x_1123_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_k_1098_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_v_1099_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v_r_1113_);
lean_ctor_set(v_reuseFailAlloc_1186_, 4, v_r_1101_);
v___x_1173_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
v_isSharedCheck_1180_ = !lean_is_exclusive(v_r_1101_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; lean_object* v_unused_1182_; lean_object* v_unused_1183_; lean_object* v_unused_1184_; lean_object* v_unused_1185_; 
v_unused_1181_ = lean_ctor_get(v_r_1101_, 4);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_r_1101_, 3);
lean_dec(v_unused_1182_);
v_unused_1183_ = lean_ctor_get(v_r_1101_, 2);
lean_dec(v_unused_1183_);
v_unused_1184_ = lean_ctor_get(v_r_1101_, 1);
lean_dec(v_unused_1184_);
v_unused_1185_ = lean_ctor_get(v_r_1101_, 0);
lean_dec(v_unused_1185_);
v___x_1175_ = v_r_1101_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_dec(v_r_1101_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 4, v___x_1173_);
lean_ctor_set(v___x_1175_, 3, v_l_1112_);
lean_ctor_set(v___x_1175_, 2, v_v_1111_);
lean_ctor_set(v___x_1175_, 1, v_k_1110_);
lean_ctor_set(v___x_1175_, 0, v___x_1169_);
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_k_1110_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_v_1111_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_l_1112_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v___x_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1193_; 
v_l_1193_ = lean_ctor_get(v_impl_1106_, 3);
lean_inc(v_l_1193_);
if (lean_obj_tag(v_l_1193_) == 0)
{
lean_object* v_r_1194_; lean_object* v_k_1195_; lean_object* v_v_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1207_; 
v_r_1194_ = lean_ctor_get(v_impl_1106_, 4);
v_k_1195_ = lean_ctor_get(v_impl_1106_, 1);
v_v_1196_ = lean_ctor_get(v_impl_1106_, 2);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_impl_1106_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; lean_object* v_unused_1209_; 
v_unused_1208_ = lean_ctor_get(v_impl_1106_, 3);
lean_dec(v_unused_1208_);
v_unused_1209_ = lean_ctor_get(v_impl_1106_, 0);
lean_dec(v_unused_1209_);
v___x_1198_ = v_impl_1106_;
v_isShared_1199_ = v_isSharedCheck_1207_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_r_1194_);
lean_inc(v_v_1196_);
lean_inc(v_k_1195_);
lean_dec(v_impl_1106_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1207_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1200_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1194_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 3, v_r_1194_);
lean_ctor_set(v___x_1198_, 2, v_v_1099_);
lean_ctor_set(v___x_1198_, 1, v_k_1098_);
lean_ctor_set(v___x_1198_, 0, v___x_1107_);
v___x_1202_ = v___x_1198_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_k_1098_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_v_1099_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_r_1194_);
lean_ctor_set(v_reuseFailAlloc_1206_, 4, v_r_1194_);
v___x_1202_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1204_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v___x_1202_);
lean_ctor_set(v___x_1103_, 3, v_l_1193_);
lean_ctor_set(v___x_1103_, 2, v_v_1196_);
lean_ctor_set(v___x_1103_, 1, v_k_1195_);
lean_ctor_set(v___x_1103_, 0, v___x_1200_);
v___x_1204_ = v___x_1103_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_l_1193_);
lean_ctor_set(v_reuseFailAlloc_1205_, 4, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v_r_1210_; 
v_r_1210_ = lean_ctor_get(v_impl_1106_, 4);
lean_inc(v_r_1210_);
if (lean_obj_tag(v_r_1210_) == 0)
{
lean_object* v_k_1211_; lean_object* v_v_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1235_; 
v_k_1211_ = lean_ctor_get(v_impl_1106_, 1);
v_v_1212_ = lean_ctor_get(v_impl_1106_, 2);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_impl_1106_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; lean_object* v_unused_1237_; lean_object* v_unused_1238_; 
v_unused_1236_ = lean_ctor_get(v_impl_1106_, 4);
lean_dec(v_unused_1236_);
v_unused_1237_ = lean_ctor_get(v_impl_1106_, 3);
lean_dec(v_unused_1237_);
v_unused_1238_ = lean_ctor_get(v_impl_1106_, 0);
lean_dec(v_unused_1238_);
v___x_1214_ = v_impl_1106_;
v_isShared_1215_ = v_isSharedCheck_1235_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_v_1212_);
lean_inc(v_k_1211_);
lean_dec(v_impl_1106_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1235_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v_k_1216_; lean_object* v_v_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1231_; 
v_k_1216_ = lean_ctor_get(v_r_1210_, 1);
v_v_1217_ = lean_ctor_get(v_r_1210_, 2);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_r_1210_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; lean_object* v_unused_1233_; lean_object* v_unused_1234_; 
v_unused_1232_ = lean_ctor_get(v_r_1210_, 4);
lean_dec(v_unused_1232_);
v_unused_1233_ = lean_ctor_get(v_r_1210_, 3);
lean_dec(v_unused_1233_);
v_unused_1234_ = lean_ctor_get(v_r_1210_, 0);
lean_dec(v_unused_1234_);
v___x_1219_ = v_r_1210_;
v_isShared_1220_ = v_isSharedCheck_1231_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_v_1217_);
lean_inc(v_k_1216_);
lean_dec(v_r_1210_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1231_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1221_ = lean_unsigned_to_nat(3u);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 4, v_l_1193_);
lean_ctor_set(v___x_1219_, 3, v_l_1193_);
lean_ctor_set(v___x_1219_, 2, v_v_1212_);
lean_ctor_set(v___x_1219_, 1, v_k_1211_);
lean_ctor_set(v___x_1219_, 0, v___x_1107_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_k_1211_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_v_1212_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_l_1193_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_l_1193_);
v___x_1223_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1225_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 4, v_l_1193_);
lean_ctor_set(v___x_1214_, 2, v_v_1099_);
lean_ctor_set(v___x_1214_, 1, v_k_1098_);
lean_ctor_set(v___x_1214_, 0, v___x_1107_);
v___x_1225_ = v___x_1214_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_k_1098_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v_v_1099_);
lean_ctor_set(v_reuseFailAlloc_1229_, 3, v_l_1193_);
lean_ctor_set(v_reuseFailAlloc_1229_, 4, v_l_1193_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v___x_1225_);
lean_ctor_set(v___x_1103_, 3, v___x_1223_);
lean_ctor_set(v___x_1103_, 2, v_v_1217_);
lean_ctor_set(v___x_1103_, 1, v_k_1216_);
lean_ctor_set(v___x_1103_, 0, v___x_1221_);
v___x_1227_ = v___x_1103_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1239_ = lean_unsigned_to_nat(2u);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v_r_1210_);
lean_ctor_set(v___x_1103_, 3, v_impl_1106_);
lean_ctor_set(v___x_1103_, 0, v___x_1239_);
v___x_1241_ = v___x_1103_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_k_1098_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_v_1099_);
lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_impl_1106_);
lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_r_1210_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1244_; 
lean_dec(v_v_1099_);
lean_dec(v_k_1098_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 2, v_v_1095_);
lean_ctor_set(v___x_1103_, 1, v_k_1094_);
v___x_1244_ = v___x_1103_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_size_1097_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_k_1094_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_v_1095_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_l_1100_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v_r_1101_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
default: 
{
lean_object* v_impl_1246_; lean_object* v___x_1247_; 
lean_dec(v_size_1097_);
v_impl_1246_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1094_, v_v_1095_, v_r_1101_);
v___x_1247_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1100_) == 0)
{
lean_object* v_size_1248_; lean_object* v_size_1249_; lean_object* v_k_1250_; lean_object* v_v_1251_; lean_object* v_l_1252_; lean_object* v_r_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_size_1248_ = lean_ctor_get(v_l_1100_, 0);
v_size_1249_ = lean_ctor_get(v_impl_1246_, 0);
lean_inc(v_size_1249_);
v_k_1250_ = lean_ctor_get(v_impl_1246_, 1);
lean_inc(v_k_1250_);
v_v_1251_ = lean_ctor_get(v_impl_1246_, 2);
lean_inc(v_v_1251_);
v_l_1252_ = lean_ctor_get(v_impl_1246_, 3);
lean_inc(v_l_1252_);
v_r_1253_ = lean_ctor_get(v_impl_1246_, 4);
lean_inc(v_r_1253_);
v___x_1254_ = lean_unsigned_to_nat(3u);
v___x_1255_ = lean_nat_mul(v___x_1254_, v_size_1248_);
v___x_1256_ = lean_nat_dec_lt(v___x_1255_, v_size_1249_);
lean_dec(v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
lean_dec(v_r_1253_);
lean_dec(v_l_1252_);
lean_dec(v_v_1251_);
lean_dec(v_k_1250_);
v___x_1257_ = lean_nat_add(v___x_1247_, v_size_1248_);
v___x_1258_ = lean_nat_add(v___x_1257_, v_size_1249_);
lean_dec(v_size_1249_);
lean_dec(v___x_1257_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v_impl_1246_);
lean_ctor_set(v___x_1103_, 0, v___x_1258_);
v___x_1260_ = v___x_1103_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_k_1098_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_v_1099_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v_l_1100_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_impl_1246_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
else
{
lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1325_; 
v_isSharedCheck_1325_ = !lean_is_exclusive(v_impl_1246_);
if (v_isSharedCheck_1325_ == 0)
{
lean_object* v_unused_1326_; lean_object* v_unused_1327_; lean_object* v_unused_1328_; lean_object* v_unused_1329_; lean_object* v_unused_1330_; 
v_unused_1326_ = lean_ctor_get(v_impl_1246_, 4);
lean_dec(v_unused_1326_);
v_unused_1327_ = lean_ctor_get(v_impl_1246_, 3);
lean_dec(v_unused_1327_);
v_unused_1328_ = lean_ctor_get(v_impl_1246_, 2);
lean_dec(v_unused_1328_);
v_unused_1329_ = lean_ctor_get(v_impl_1246_, 1);
lean_dec(v_unused_1329_);
v_unused_1330_ = lean_ctor_get(v_impl_1246_, 0);
lean_dec(v_unused_1330_);
v___x_1263_ = v_impl_1246_;
v_isShared_1264_ = v_isSharedCheck_1325_;
goto v_resetjp_1262_;
}
else
{
lean_dec(v_impl_1246_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1325_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v_size_1265_; lean_object* v_k_1266_; lean_object* v_v_1267_; lean_object* v_l_1268_; lean_object* v_r_1269_; lean_object* v_size_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v_size_1265_ = lean_ctor_get(v_l_1252_, 0);
v_k_1266_ = lean_ctor_get(v_l_1252_, 1);
v_v_1267_ = lean_ctor_get(v_l_1252_, 2);
v_l_1268_ = lean_ctor_get(v_l_1252_, 3);
v_r_1269_ = lean_ctor_get(v_l_1252_, 4);
v_size_1270_ = lean_ctor_get(v_r_1253_, 0);
v___x_1271_ = lean_unsigned_to_nat(2u);
v___x_1272_ = lean_nat_mul(v___x_1271_, v_size_1270_);
v___x_1273_ = lean_nat_dec_lt(v_size_1265_, v___x_1272_);
lean_dec(v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1301_; 
lean_inc(v_r_1269_);
lean_inc(v_l_1268_);
lean_inc(v_v_1267_);
lean_inc(v_k_1266_);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_l_1252_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; lean_object* v_unused_1303_; lean_object* v_unused_1304_; lean_object* v_unused_1305_; lean_object* v_unused_1306_; 
v_unused_1302_ = lean_ctor_get(v_l_1252_, 4);
lean_dec(v_unused_1302_);
v_unused_1303_ = lean_ctor_get(v_l_1252_, 3);
lean_dec(v_unused_1303_);
v_unused_1304_ = lean_ctor_get(v_l_1252_, 2);
lean_dec(v_unused_1304_);
v_unused_1305_ = lean_ctor_get(v_l_1252_, 1);
lean_dec(v_unused_1305_);
v_unused_1306_ = lean_ctor_get(v_l_1252_, 0);
lean_dec(v_unused_1306_);
v___x_1275_ = v_l_1252_;
v_isShared_1276_ = v_isSharedCheck_1301_;
goto v_resetjp_1274_;
}
else
{
lean_dec(v_l_1252_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1301_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1291_; 
v___x_1277_ = lean_nat_add(v___x_1247_, v_size_1248_);
v___x_1278_ = lean_nat_add(v___x_1277_, v_size_1249_);
lean_dec(v_size_1249_);
if (lean_obj_tag(v_l_1268_) == 0)
{
lean_object* v_size_1299_; 
v_size_1299_ = lean_ctor_get(v_l_1268_, 0);
lean_inc(v_size_1299_);
v___y_1291_ = v_size_1299_;
goto v___jp_1290_;
}
else
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_unsigned_to_nat(0u);
v___y_1291_ = v___x_1300_;
goto v___jp_1290_;
}
v___jp_1279_:
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1283_ = lean_nat_add(v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec(v___y_1281_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 4, v_r_1253_);
lean_ctor_set(v___x_1275_, 3, v_r_1269_);
lean_ctor_set(v___x_1275_, 2, v_v_1251_);
lean_ctor_set(v___x_1275_, 1, v_k_1250_);
lean_ctor_set(v___x_1275_, 0, v___x_1283_);
v___x_1285_ = v___x_1275_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v_r_1269_);
lean_ctor_set(v_reuseFailAlloc_1289_, 4, v_r_1253_);
v___x_1285_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1287_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 4, v___x_1285_);
lean_ctor_set(v___x_1263_, 3, v___y_1280_);
lean_ctor_set(v___x_1263_, 2, v_v_1267_);
lean_ctor_set(v___x_1263_, 1, v_k_1266_);
lean_ctor_set(v___x_1263_, 0, v___x_1278_);
v___x_1287_ = v___x_1263_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_k_1266_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_v_1267_);
lean_ctor_set(v_reuseFailAlloc_1288_, 3, v___y_1280_);
lean_ctor_set(v_reuseFailAlloc_1288_, 4, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
v___jp_1290_:
{
lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1292_ = lean_nat_add(v___x_1277_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec(v___x_1277_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v_l_1268_);
lean_ctor_set(v___x_1103_, 0, v___x_1292_);
v___x_1294_ = v___x_1103_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_k_1098_);
lean_ctor_set(v_reuseFailAlloc_1298_, 2, v_v_1099_);
lean_ctor_set(v_reuseFailAlloc_1298_, 3, v_l_1100_);
lean_ctor_set(v_reuseFailAlloc_1298_, 4, v_l_1268_);
v___x_1294_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; 
v___x_1295_ = lean_nat_add(v___x_1247_, v_size_1270_);
if (lean_obj_tag(v_r_1269_) == 0)
{
lean_object* v_size_1296_; 
v_size_1296_ = lean_ctor_get(v_r_1269_, 0);
lean_inc(v_size_1296_);
v___y_1280_ = v___x_1294_;
v___y_1281_ = v___x_1295_;
v___y_1282_ = v_size_1296_;
goto v___jp_1279_;
}
else
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_unsigned_to_nat(0u);
v___y_1280_ = v___x_1294_;
v___y_1281_ = v___x_1295_;
v___y_1282_ = v___x_1297_;
goto v___jp_1279_;
}
}
}
}
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1311_; 
lean_del_object(v___x_1103_);
v___x_1307_ = lean_nat_add(v___x_1247_, v_size_1248_);
v___x_1308_ = lean_nat_add(v___x_1307_, v_size_1249_);
lean_dec(v_size_1249_);
v___x_1309_ = lean_nat_add(v___x_1307_, v_size_1265_);
lean_dec(v___x_1307_);
lean_inc_ref(v_l_1100_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 4, v_l_1252_);
lean_ctor_set(v___x_1263_, 3, v_l_1100_);
lean_ctor_set(v___x_1263_, 2, v_v_1099_);
lean_ctor_set(v___x_1263_, 1, v_k_1098_);
lean_ctor_set(v___x_1263_, 0, v___x_1309_);
v___x_1311_ = v___x_1263_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_k_1098_);
lean_ctor_set(v_reuseFailAlloc_1324_, 2, v_v_1099_);
lean_ctor_set(v_reuseFailAlloc_1324_, 3, v_l_1100_);
lean_ctor_set(v_reuseFailAlloc_1324_, 4, v_l_1252_);
v___x_1311_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
v_isSharedCheck_1318_ = !lean_is_exclusive(v_l_1100_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; lean_object* v_unused_1320_; lean_object* v_unused_1321_; lean_object* v_unused_1322_; lean_object* v_unused_1323_; 
v_unused_1319_ = lean_ctor_get(v_l_1100_, 4);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_l_1100_, 3);
lean_dec(v_unused_1320_);
v_unused_1321_ = lean_ctor_get(v_l_1100_, 2);
lean_dec(v_unused_1321_);
v_unused_1322_ = lean_ctor_get(v_l_1100_, 1);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v_l_1100_, 0);
lean_dec(v_unused_1323_);
v___x_1313_ = v_l_1100_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_dec(v_l_1100_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 4, v_r_1253_);
lean_ctor_set(v___x_1313_, 3, v___x_1311_);
lean_ctor_set(v___x_1313_, 2, v_v_1251_);
lean_ctor_set(v___x_1313_, 1, v_k_1250_);
lean_ctor_set(v___x_1313_, 0, v___x_1308_);
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1317_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1317_, 3, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1317_, 4, v_r_1253_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1331_; 
v_l_1331_ = lean_ctor_get(v_impl_1246_, 3);
lean_inc(v_l_1331_);
if (lean_obj_tag(v_l_1331_) == 0)
{
lean_object* v_r_1332_; lean_object* v_k_1333_; lean_object* v_v_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1357_; 
v_r_1332_ = lean_ctor_get(v_impl_1246_, 4);
v_k_1333_ = lean_ctor_get(v_impl_1246_, 1);
v_v_1334_ = lean_ctor_get(v_impl_1246_, 2);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_impl_1246_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; lean_object* v_unused_1359_; 
v_unused_1358_ = lean_ctor_get(v_impl_1246_, 3);
lean_dec(v_unused_1358_);
v_unused_1359_ = lean_ctor_get(v_impl_1246_, 0);
lean_dec(v_unused_1359_);
v___x_1336_ = v_impl_1246_;
v_isShared_1337_ = v_isSharedCheck_1357_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_r_1332_);
lean_inc(v_v_1334_);
lean_inc(v_k_1333_);
lean_dec(v_impl_1246_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1357_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_k_1338_; lean_object* v_v_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1353_; 
v_k_1338_ = lean_ctor_get(v_l_1331_, 1);
v_v_1339_ = lean_ctor_get(v_l_1331_, 2);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_l_1331_);
if (v_isSharedCheck_1353_ == 0)
{
lean_object* v_unused_1354_; lean_object* v_unused_1355_; lean_object* v_unused_1356_; 
v_unused_1354_ = lean_ctor_get(v_l_1331_, 4);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v_l_1331_, 3);
lean_dec(v_unused_1355_);
v_unused_1356_ = lean_ctor_get(v_l_1331_, 0);
lean_dec(v_unused_1356_);
v___x_1341_ = v_l_1331_;
v_isShared_1342_ = v_isSharedCheck_1353_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_v_1339_);
lean_inc(v_k_1338_);
lean_dec(v_l_1331_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1353_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1343_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1332_, 2);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 4, v_r_1332_);
lean_ctor_set(v___x_1341_, 3, v_r_1332_);
lean_ctor_set(v___x_1341_, 2, v_v_1099_);
lean_ctor_set(v___x_1341_, 1, v_k_1098_);
lean_ctor_set(v___x_1341_, 0, v___x_1247_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_k_1098_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_v_1099_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v_r_1332_);
lean_ctor_set(v_reuseFailAlloc_1352_, 4, v_r_1332_);
v___x_1345_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1347_; 
lean_inc(v_r_1332_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 3, v_r_1332_);
lean_ctor_set(v___x_1336_, 0, v___x_1247_);
v___x_1347_ = v___x_1336_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_k_1333_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v_v_1334_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v_r_1332_);
lean_ctor_set(v_reuseFailAlloc_1351_, 4, v_r_1332_);
v___x_1347_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1349_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v___x_1347_);
lean_ctor_set(v___x_1103_, 3, v___x_1345_);
lean_ctor_set(v___x_1103_, 2, v_v_1339_);
lean_ctor_set(v___x_1103_, 1, v_k_1338_);
lean_ctor_set(v___x_1103_, 0, v___x_1343_);
v___x_1349_ = v___x_1103_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_k_1338_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_v_1339_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
}
else
{
lean_object* v_r_1360_; 
v_r_1360_ = lean_ctor_get(v_impl_1246_, 4);
lean_inc(v_r_1360_);
if (lean_obj_tag(v_r_1360_) == 0)
{
lean_object* v_k_1361_; lean_object* v_v_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1373_; 
v_k_1361_ = lean_ctor_get(v_impl_1246_, 1);
v_v_1362_ = lean_ctor_get(v_impl_1246_, 2);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_impl_1246_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; lean_object* v_unused_1375_; lean_object* v_unused_1376_; 
v_unused_1374_ = lean_ctor_get(v_impl_1246_, 4);
lean_dec(v_unused_1374_);
v_unused_1375_ = lean_ctor_get(v_impl_1246_, 3);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v_impl_1246_, 0);
lean_dec(v_unused_1376_);
v___x_1364_ = v_impl_1246_;
v_isShared_1365_ = v_isSharedCheck_1373_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_v_1362_);
lean_inc(v_k_1361_);
lean_dec(v_impl_1246_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1373_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = lean_unsigned_to_nat(3u);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 4, v_l_1331_);
lean_ctor_set(v___x_1364_, 2, v_v_1099_);
lean_ctor_set(v___x_1364_, 1, v_k_1098_);
lean_ctor_set(v___x_1364_, 0, v___x_1247_);
v___x_1368_ = v___x_1364_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_k_1098_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_v_1099_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v_l_1331_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v_l_1331_);
v___x_1368_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1370_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v_r_1360_);
lean_ctor_set(v___x_1103_, 3, v___x_1368_);
lean_ctor_set(v___x_1103_, 2, v_v_1362_);
lean_ctor_set(v___x_1103_, 1, v_k_1361_);
lean_ctor_set(v___x_1103_, 0, v___x_1366_);
v___x_1370_ = v___x_1103_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1371_, 4, v_r_1360_);
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
else
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = lean_unsigned_to_nat(2u);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v_impl_1246_);
lean_ctor_set(v___x_1103_, 3, v_r_1360_);
lean_ctor_set(v___x_1103_, 0, v___x_1377_);
v___x_1379_ = v___x_1103_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_k_1098_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_v_1099_);
lean_ctor_set(v_reuseFailAlloc_1380_, 3, v_r_1360_);
lean_ctor_set(v_reuseFailAlloc_1380_, 4, v_impl_1246_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
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
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_unsigned_to_nat(1u);
v___x_1383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v_k_1094_);
lean_ctor_set(v___x_1383_, 2, v_v_1095_);
lean_ctor_set(v___x_1383_, 3, v_t_1096_);
lean_ctor_set(v___x_1383_, 4, v_t_1096_);
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object* v_s_1384_, lean_object* v_mvarId_1385_){
_start:
{
uint8_t v___x_1386_; 
v___x_1386_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_mvarId_1385_, v_s_1384_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = lean_box(0);
v___x_1388_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1385_, v___x_1387_, v_s_1384_);
return v___x_1388_;
}
else
{
lean_dec(v_mvarId_1385_);
return v_s_1384_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object* v_00_u03b2_1389_, lean_object* v_k_1390_, lean_object* v_t_1391_){
_start:
{
uint8_t v___x_1392_; 
v___x_1392_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1390_, v_t_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object* v_00_u03b2_1393_, lean_object* v_k_1394_, lean_object* v_t_1395_){
_start:
{
uint8_t v_res_1396_; lean_object* v_r_1397_; 
v_res_1396_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(v_00_u03b2_1393_, v_k_1394_, v_t_1395_);
lean_dec(v_t_1395_);
lean_dec(v_k_1394_);
v_r_1397_ = lean_box(v_res_1396_);
return v_r_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object* v_00_u03b2_1398_, lean_object* v_k_1399_, lean_object* v_v_1400_, lean_object* v_t_1401_, lean_object* v_hl_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1399_, v_v_1400_, v_t_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object* v_l_1404_){
_start:
{
lean_object* v___f_1405_; lean_object* v___x_1406_; 
v___f_1405_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1406_ = l_Std_TreeSet_ofList___redArg(v_l_1404_, v___f_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList___boxed(lean_object* v_l_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_MVarIdSet_ofList(v_l_1407_);
lean_dec(v_l_1407_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object* v_l_1409_){
_start:
{
lean_object* v___f_1410_; lean_object* v___x_1411_; 
v___f_1410_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1411_ = l_Std_TreeSet_ofArray___redArg(v_l_1409_, v___f_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object* v_l_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_MVarIdSet_ofArray(v_l_1412_);
lean_dec_ref(v_l_1412_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1414_, lean_object* v_m_1415_, lean_object* v_init_1416_, lean_object* v_f_1417_){
_start:
{
lean_object* v_toApplicative_1418_; lean_object* v_toBind_1419_; lean_object* v_toPure_1420_; lean_object* v___f_1421_; lean_object* v___x_1422_; lean_object* v___f_1423_; lean_object* v___x_1424_; 
v_toApplicative_1418_ = lean_ctor_get(v_inst_1414_, 0);
v_toBind_1419_ = lean_ctor_get(v_inst_1414_, 1);
lean_inc(v_toBind_1419_);
v_toPure_1420_ = lean_ctor_get(v_toApplicative_1418_, 1);
lean_inc(v_toPure_1420_);
v___f_1421_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1421_, 0, v_f_1417_);
v___x_1422_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1414_, v___f_1421_, v_init_1416_, v_m_1415_);
v___f_1423_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1423_, 0, v_toPure_1420_);
v___x_1424_ = lean_apply_4(v_toBind_1419_, lean_box(0), lean_box(0), v___x_1422_, v___f_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1(lean_object* v_m_1425_, lean_object* v_inst_1426_, lean_object* v_00_u03b2_1427_, lean_object* v_m_1428_, lean_object* v_init_1429_, lean_object* v_f_1430_){
_start:
{
lean_object* v_toApplicative_1431_; lean_object* v_toBind_1432_; lean_object* v_toPure_1433_; lean_object* v___f_1434_; lean_object* v___x_1435_; lean_object* v___f_1436_; lean_object* v___x_1437_; 
v_toApplicative_1431_ = lean_ctor_get(v_inst_1426_, 0);
v_toBind_1432_ = lean_ctor_get(v_inst_1426_, 1);
lean_inc(v_toBind_1432_);
v_toPure_1433_ = lean_ctor_get(v_toApplicative_1431_, 1);
lean_inc(v_toPure_1433_);
v___f_1434_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1434_, 0, v_f_1430_);
v___x_1435_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1426_, v___f_1434_, v_init_1429_, v_m_1428_);
v___f_1436_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1436_, 0, v_toPure_1433_);
v___x_1437_ = lean_apply_4(v_toBind_1432_, lean_box(0), lean_box(0), v___x_1435_, v___f_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object* v_inst_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1439_, 0, lean_box(0));
lean_closure_set(v___x_1439_, 1, v_inst_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object* v_m_1440_, lean_object* v_inst_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1442_, 0, lean_box(0));
lean_closure_set(v___x_1442_, 1, v_inst_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object* v_s_1443_, lean_object* v_mvarId_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1444_, v_a_1445_, v_s_1443_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object* v_00_u03b1_1447_, lean_object* v_s_1448_, lean_object* v_mvarId_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1449_, v_a_1450_, v_s_1448_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object* v_00_u03b1_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_box(1);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* v_00_u03b1_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_box(1);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_1456_, lean_object* v_a_1457_, lean_object* v_b_1458_, lean_object* v_c_1459_){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v_a_1457_);
lean_ctor_set(v___x_1460_, 1, v_b_1458_);
v___x_1461_ = lean_apply_2(v_f_1456_, v___x_1460_, v_c_1459_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1462_, lean_object* v_m_1463_, lean_object* v_init_1464_, lean_object* v_f_1465_){
_start:
{
lean_object* v_toApplicative_1466_; lean_object* v_toBind_1467_; lean_object* v_toPure_1468_; lean_object* v___f_1469_; lean_object* v___x_1470_; lean_object* v___f_1471_; lean_object* v___x_1472_; 
v_toApplicative_1466_ = lean_ctor_get(v_inst_1462_, 0);
v_toBind_1467_ = lean_ctor_get(v_inst_1462_, 1);
lean_inc(v_toBind_1467_);
v_toPure_1468_ = lean_ctor_get(v_toApplicative_1466_, 1);
lean_inc(v_toPure_1468_);
v___f_1469_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1469_, 0, v_f_1465_);
v___x_1470_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1462_, v___f_1469_, v_init_1464_, v_m_1463_);
v___f_1471_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1471_, 0, v_toPure_1468_);
v___x_1472_ = lean_apply_4(v_toBind_1467_, lean_box(0), lean_box(0), v___x_1470_, v___f_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object* v_m_1473_, lean_object* v_00_u03b1_1474_, lean_object* v_inst_1475_, lean_object* v_00_u03b2_1476_, lean_object* v_m_1477_, lean_object* v_init_1478_, lean_object* v_f_1479_){
_start:
{
lean_object* v_toApplicative_1480_; lean_object* v_toBind_1481_; lean_object* v_toPure_1482_; lean_object* v___f_1483_; lean_object* v___x_1484_; lean_object* v___f_1485_; lean_object* v___x_1486_; 
v_toApplicative_1480_ = lean_ctor_get(v_inst_1475_, 0);
v_toBind_1481_ = lean_ctor_get(v_inst_1475_, 1);
lean_inc(v_toBind_1481_);
v_toPure_1482_ = lean_ctor_get(v_toApplicative_1480_, 1);
lean_inc(v_toPure_1482_);
v___f_1483_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1483_, 0, v_f_1479_);
v___x_1484_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1475_, v___f_1483_, v_init_1478_, v_m_1477_);
v___f_1485_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1485_, 0, v_toPure_1482_);
v___x_1486_ = lean_apply_4(v_toBind_1481_, lean_box(0), lean_box(0), v___x_1484_, v___f_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object* v_inst_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1488_, 0, lean_box(0));
lean_closure_set(v___x_1488_, 1, lean_box(0));
lean_closure_set(v___x_1488_, 2, v_inst_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object* v_m_1489_, lean_object* v_00_u03b1_1490_, lean_object* v_inst_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1492_, 0, lean_box(0));
lean_closure_set(v___x_1492_, 1, lean_box(0));
lean_closure_set(v___x_1492_, 2, v_inst_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* v_00_u03b1_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_box(1);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx(lean_object* v_x_1495_){
_start:
{
switch(lean_obj_tag(v_x_1495_))
{
case 0:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_unsigned_to_nat(0u);
return v___x_1496_;
}
case 1:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_unsigned_to_nat(1u);
return v___x_1497_;
}
case 2:
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_unsigned_to_nat(2u);
return v___x_1498_;
}
case 3:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_unsigned_to_nat(3u);
return v___x_1499_;
}
case 4:
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_unsigned_to_nat(4u);
return v___x_1500_;
}
case 5:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_unsigned_to_nat(5u);
return v___x_1501_;
}
case 6:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_unsigned_to_nat(6u);
return v___x_1502_;
}
case 7:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_unsigned_to_nat(7u);
return v___x_1503_;
}
case 8:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_unsigned_to_nat(8u);
return v___x_1504_;
}
case 9:
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_unsigned_to_nat(9u);
return v___x_1505_;
}
case 10:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_unsigned_to_nat(10u);
return v___x_1506_;
}
default: 
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_unsigned_to_nat(11u);
return v___x_1507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___boxed(lean_object* v_x_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Expr_ctorIdx(v_x_1508_);
lean_dec_ref(v_x_1508_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object* v_t_1510_, lean_object* v_k_1511_){
_start:
{
switch(lean_obj_tag(v_t_1510_))
{
case 4:
{
lean_object* v_declName_1512_; lean_object* v_us_1513_; lean_object* v___x_1514_; 
v_declName_1512_ = lean_ctor_get(v_t_1510_, 0);
lean_inc(v_declName_1512_);
v_us_1513_ = lean_ctor_get(v_t_1510_, 1);
lean_inc(v_us_1513_);
lean_dec_ref(v_t_1510_);
v___x_1514_ = lean_apply_2(v_k_1511_, v_declName_1512_, v_us_1513_);
return v___x_1514_;
}
case 5:
{
lean_object* v_fn_1515_; lean_object* v_arg_1516_; lean_object* v___x_1517_; 
v_fn_1515_ = lean_ctor_get(v_t_1510_, 0);
lean_inc_ref(v_fn_1515_);
v_arg_1516_ = lean_ctor_get(v_t_1510_, 1);
lean_inc_ref(v_arg_1516_);
lean_dec_ref(v_t_1510_);
v___x_1517_ = lean_apply_2(v_k_1511_, v_fn_1515_, v_arg_1516_);
return v___x_1517_;
}
case 6:
{
lean_object* v_binderName_1518_; lean_object* v_binderType_1519_; lean_object* v_body_1520_; uint8_t v_binderInfo_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v_binderName_1518_ = lean_ctor_get(v_t_1510_, 0);
lean_inc(v_binderName_1518_);
v_binderType_1519_ = lean_ctor_get(v_t_1510_, 1);
lean_inc_ref(v_binderType_1519_);
v_body_1520_ = lean_ctor_get(v_t_1510_, 2);
lean_inc_ref(v_body_1520_);
v_binderInfo_1521_ = lean_ctor_get_uint8(v_t_1510_, sizeof(void*)*3);
lean_dec_ref(v_t_1510_);
v___x_1522_ = lean_box(v_binderInfo_1521_);
v___x_1523_ = lean_apply_4(v_k_1511_, v_binderName_1518_, v_binderType_1519_, v_body_1520_, v___x_1522_);
return v___x_1523_;
}
case 7:
{
lean_object* v_binderName_1524_; lean_object* v_binderType_1525_; lean_object* v_body_1526_; uint8_t v_binderInfo_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_binderName_1524_ = lean_ctor_get(v_t_1510_, 0);
lean_inc(v_binderName_1524_);
v_binderType_1525_ = lean_ctor_get(v_t_1510_, 1);
lean_inc_ref(v_binderType_1525_);
v_body_1526_ = lean_ctor_get(v_t_1510_, 2);
lean_inc_ref(v_body_1526_);
v_binderInfo_1527_ = lean_ctor_get_uint8(v_t_1510_, sizeof(void*)*3);
lean_dec_ref(v_t_1510_);
v___x_1528_ = lean_box(v_binderInfo_1527_);
v___x_1529_ = lean_apply_4(v_k_1511_, v_binderName_1524_, v_binderType_1525_, v_body_1526_, v___x_1528_);
return v___x_1529_;
}
case 8:
{
lean_object* v_declName_1530_; lean_object* v_type_1531_; lean_object* v_value_1532_; lean_object* v_body_1533_; uint8_t v_nondep_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_declName_1530_ = lean_ctor_get(v_t_1510_, 0);
lean_inc(v_declName_1530_);
v_type_1531_ = lean_ctor_get(v_t_1510_, 1);
lean_inc_ref(v_type_1531_);
v_value_1532_ = lean_ctor_get(v_t_1510_, 2);
lean_inc_ref(v_value_1532_);
v_body_1533_ = lean_ctor_get(v_t_1510_, 3);
lean_inc_ref(v_body_1533_);
v_nondep_1534_ = lean_ctor_get_uint8(v_t_1510_, sizeof(void*)*4);
lean_dec_ref(v_t_1510_);
v___x_1535_ = lean_box(v_nondep_1534_);
v___x_1536_ = lean_apply_5(v_k_1511_, v_declName_1530_, v_type_1531_, v_value_1532_, v_body_1533_, v___x_1535_);
return v___x_1536_;
}
case 9:
{
lean_object* v_a_1537_; lean_object* v___x_1538_; 
v_a_1537_ = lean_ctor_get(v_t_1510_, 0);
lean_inc_ref(v_a_1537_);
lean_dec_ref(v_t_1510_);
v___x_1538_ = lean_apply_1(v_k_1511_, v_a_1537_);
return v___x_1538_;
}
case 10:
{
lean_object* v_data_1539_; lean_object* v_expr_1540_; lean_object* v___x_1541_; 
v_data_1539_ = lean_ctor_get(v_t_1510_, 0);
lean_inc(v_data_1539_);
v_expr_1540_ = lean_ctor_get(v_t_1510_, 1);
lean_inc_ref(v_expr_1540_);
lean_dec_ref(v_t_1510_);
v___x_1541_ = lean_apply_2(v_k_1511_, v_data_1539_, v_expr_1540_);
return v___x_1541_;
}
case 11:
{
lean_object* v_typeName_1542_; lean_object* v_idx_1543_; lean_object* v_struct_1544_; lean_object* v___x_1545_; 
v_typeName_1542_ = lean_ctor_get(v_t_1510_, 0);
lean_inc(v_typeName_1542_);
v_idx_1543_ = lean_ctor_get(v_t_1510_, 1);
lean_inc(v_idx_1543_);
v_struct_1544_ = lean_ctor_get(v_t_1510_, 2);
lean_inc_ref(v_struct_1544_);
lean_dec_ref(v_t_1510_);
v___x_1545_ = lean_apply_3(v_k_1511_, v_typeName_1542_, v_idx_1543_, v_struct_1544_);
return v___x_1545_;
}
default: 
{
lean_object* v_deBruijnIndex_1546_; lean_object* v___x_1547_; 
v_deBruijnIndex_1546_ = lean_ctor_get(v_t_1510_, 0);
lean_inc(v_deBruijnIndex_1546_);
lean_dec_ref(v_t_1510_);
v___x_1547_ = lean_apply_1(v_k_1511_, v_deBruijnIndex_1546_);
return v___x_1547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object* v_motive_1548_, lean_object* v_ctorIdx_1549_, lean_object* v_t_1550_, lean_object* v_h_1551_, lean_object* v_k_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_Expr_ctorElim___redArg(v_t_1550_, v_k_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object* v_motive_1554_, lean_object* v_ctorIdx_1555_, lean_object* v_t_1556_, lean_object* v_h_1557_, lean_object* v_k_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_Expr_ctorElim(v_motive_1554_, v_ctorIdx_1555_, v_t_1556_, v_h_1557_, v_k_1558_);
lean_dec(v_ctorIdx_1555_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object* v_t_1560_, lean_object* v_bvar_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Expr_ctorElim___redArg(v_t_1560_, v_bvar_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object* v_motive_1563_, lean_object* v_t_1564_, lean_object* v_h_1565_, lean_object* v_bvar_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Expr_ctorElim___redArg(v_t_1564_, v_bvar_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object* v_t_1568_, lean_object* v_fvar_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Expr_ctorElim___redArg(v_t_1568_, v_fvar_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object* v_motive_1571_, lean_object* v_t_1572_, lean_object* v_h_1573_, lean_object* v_fvar_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_Expr_ctorElim___redArg(v_t_1572_, v_fvar_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object* v_t_1576_, lean_object* v_mvar_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Expr_ctorElim___redArg(v_t_1576_, v_mvar_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object* v_motive_1579_, lean_object* v_t_1580_, lean_object* v_h_1581_, lean_object* v_mvar_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_Expr_ctorElim___redArg(v_t_1580_, v_mvar_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object* v_t_1584_, lean_object* v_sort_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Expr_ctorElim___redArg(v_t_1584_, v_sort_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object* v_motive_1587_, lean_object* v_t_1588_, lean_object* v_h_1589_, lean_object* v_sort_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_Expr_ctorElim___redArg(v_t_1588_, v_sort_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object* v_t_1592_, lean_object* v_const_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Expr_ctorElim___redArg(v_t_1592_, v_const_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object* v_motive_1595_, lean_object* v_t_1596_, lean_object* v_h_1597_, lean_object* v_const_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Expr_ctorElim___redArg(v_t_1596_, v_const_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object* v_t_1600_, lean_object* v_app_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_Expr_ctorElim___redArg(v_t_1600_, v_app_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object* v_motive_1603_, lean_object* v_t_1604_, lean_object* v_h_1605_, lean_object* v_app_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_Expr_ctorElim___redArg(v_t_1604_, v_app_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object* v_t_1608_, lean_object* v_lam_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Expr_ctorElim___redArg(v_t_1608_, v_lam_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object* v_motive_1611_, lean_object* v_t_1612_, lean_object* v_h_1613_, lean_object* v_lam_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_Expr_ctorElim___redArg(v_t_1612_, v_lam_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object* v_t_1616_, lean_object* v_forallE_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_Expr_ctorElim___redArg(v_t_1616_, v_forallE_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object* v_motive_1619_, lean_object* v_t_1620_, lean_object* v_h_1621_, lean_object* v_forallE_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Expr_ctorElim___redArg(v_t_1620_, v_forallE_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object* v_t_1624_, lean_object* v_letE_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Expr_ctorElim___redArg(v_t_1624_, v_letE_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object* v_motive_1627_, lean_object* v_t_1628_, lean_object* v_h_1629_, lean_object* v_letE_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Expr_ctorElim___redArg(v_t_1628_, v_letE_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object* v_t_1632_, lean_object* v_lit_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Expr_ctorElim___redArg(v_t_1632_, v_lit_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object* v_motive_1635_, lean_object* v_t_1636_, lean_object* v_h_1637_, lean_object* v_lit_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Expr_ctorElim___redArg(v_t_1636_, v_lit_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object* v_t_1640_, lean_object* v_mdata_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Expr_ctorElim___redArg(v_t_1640_, v_mdata_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object* v_motive_1643_, lean_object* v_t_1644_, lean_object* v_h_1645_, lean_object* v_mdata_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Expr_ctorElim___redArg(v_t_1644_, v_mdata_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object* v_t_1648_, lean_object* v_proj_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Expr_ctorElim___redArg(v_t_1648_, v_proj_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object* v_motive_1651_, lean_object* v_t_1652_, lean_object* v_h_1653_, lean_object* v_proj_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_Expr_ctorElim___redArg(v_t_1652_, v_proj_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* v_a_00___x40___internal___hyg_1657_){
_start:
{
uint64_t v_res_1658_; lean_object* v_r_1659_; 
v_res_1658_ = lean_expr_data(v_a_00___x40___internal___hyg_1657_);
lean_dec_ref(v_a_00___x40___internal___hyg_1657_);
v_r_1659_ = lean_box_uint64(v_res_1658_);
return v_r_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object* v_t_1660_, lean_object* v_bvar_1661_, lean_object* v_fvar_1662_, lean_object* v_mvar_1663_, lean_object* v_sort_1664_, lean_object* v_const_1665_, lean_object* v_app_1666_, lean_object* v_lam_1667_, lean_object* v_forallE_1668_, lean_object* v_letE_1669_, lean_object* v_lit_1670_, lean_object* v_mdata_1671_, lean_object* v_proj_1672_){
_start:
{
switch(lean_obj_tag(v_t_1660_))
{
case 0:
{
lean_object* v_deBruijnIndex_1673_; lean_object* v___x_1674_; 
lean_dec(v_proj_1672_);
lean_dec(v_mdata_1671_);
lean_dec(v_lit_1670_);
lean_dec(v_letE_1669_);
lean_dec(v_forallE_1668_);
lean_dec(v_lam_1667_);
lean_dec(v_app_1666_);
lean_dec(v_const_1665_);
lean_dec(v_sort_1664_);
lean_dec(v_mvar_1663_);
lean_dec(v_fvar_1662_);
v_deBruijnIndex_1673_ = lean_ctor_get(v_t_1660_, 0);
lean_inc(v_deBruijnIndex_1673_);
lean_dec_ref(v_t_1660_);
v___x_1674_ = lean_apply_1(v_bvar_1661_, v_deBruijnIndex_1673_);
return v___x_1674_;
}
case 1:
{
lean_object* v_fvarId_1675_; lean_object* v___x_1676_; 
lean_dec(v_proj_1672_);
lean_dec(v_mdata_1671_);
lean_dec(v_lit_1670_);
lean_dec(v_letE_1669_);
lean_dec(v_forallE_1668_);
lean_dec(v_lam_1667_);
lean_dec(v_app_1666_);
lean_dec(v_const_1665_);
lean_dec(v_sort_1664_);
lean_dec(v_mvar_1663_);
lean_dec(v_bvar_1661_);
v_fvarId_1675_ = lean_ctor_get(v_t_1660_, 0);
lean_inc(v_fvarId_1675_);
lean_dec_ref(v_t_1660_);
v___x_1676_ = lean_apply_1(v_fvar_1662_, v_fvarId_1675_);
return v___x_1676_;
}
case 2:
{
lean_object* v_mvarId_1677_; lean_object* v___x_1678_; 
lean_dec(v_proj_1672_);
lean_dec(v_mdata_1671_);
lean_dec(v_lit_1670_);
lean_dec(v_letE_1669_);
lean_dec(v_forallE_1668_);
lean_dec(v_lam_1667_);
lean_dec(v_app_1666_);
lean_dec(v_const_1665_);
lean_dec(v_sort_1664_);
lean_dec(v_fvar_1662_);
lean_dec(v_bvar_1661_);
v_mvarId_1677_ = lean_ctor_get(v_t_1660_, 0);
lean_inc(v_mvarId_1677_);
lean_dec_ref(v_t_1660_);
v___x_1678_ = lean_apply_1(v_mvar_1663_, v_mvarId_1677_);
return v___x_1678_;
}
case 3:
{
lean_object* v_u_1679_; lean_object* v___x_1680_; 
lean_dec(v_proj_1672_);
lean_dec(v_mdata_1671_);
lean_dec(v_lit_1670_);
lean_dec(v_letE_1669_);
lean_dec(v_forallE_1668_);
lean_dec(v_lam_1667_);
lean_dec(v_app_1666_);
lean_dec(v_const_1665_);
lean_dec(v_mvar_1663_);
lean_dec(v_fvar_1662_);
lean_dec(v_bvar_1661_);
v_u_1679_ = lean_ctor_get(v_t_1660_, 0);
lean_inc(v_u_1679_);
lean_dec_ref(v_t_1660_);
v___x_1680_ = lean_apply_1(v_sort_1664_, v_u_1679_);
return v___x_1680_;
}
case 4:
{
lean_object* v_declName_1681_; lean_object* v_us_1682_; lean_object* v___x_1683_; 
lean_dec(v_proj_1672_);
lean_dec(v_mdata_1671_);
lean_dec(v_lit_1670_);
lean_dec(v_letE_1669_);
lean_dec(v_forallE_1668_);
lean_dec(v_lam_1667_);
lean_dec(v_app_1666_);
lean_dec(v_sort_1664_);
lean_dec(v_mvar_1663_);
lean_dec(v_fvar_1662_);
lean_dec(v_bvar_1661_);
v_declName_1681_ = lean_ctor_get(v_t_1660_, 0);
lean_inc(v_declName_1681_);
v_us_1682_ = lean_ctor_get(v_t_1660_, 1);
lean_inc(v_us_1682_);
lean_dec_ref(v_t_1660_);
v___x_1683_ = lean_apply_2(v_const_1665_, v_declName_1681_, v_us_1682_);
return v___x_1683_;
}
case 5:
{
lean_object* v_fn_1684_; lean_object* v_arg_1685_; lean_object* v___x_1686_; 
lean_dec(v_proj_1672_);
lean_dec(v_mdata_1671_);
lean_dec(v_lit_1670_);
lean_dec(v_letE_1669_);
lean_dec(v_forallE_1668_);
lean_dec(v_lam_1667_);
lean_dec(v_const_1665_);
lean_dec(v_sort_1664_);
lean_dec(v_mvar_1663_);
lean_dec(v_fvar_1662_);
lean_dec(v_bvar_1661_);
v_fn_1684_ = lean_ctor_get(v_t_1660_, 0);
lean_inc_ref(v_fn_1684_);
v_arg_1685_ = lean_ctor_get(v_t_1660_, 1);
lean_inc_ref(v_arg_1685_);
lean_dec_ref(v_t_1660_);
v___x_1686_ = lean_apply_2(v_app_1666_, v_fn_1684_, v_arg_1685_);
return v___x_1686_;
}
case 6:
{
lean_object* v_binderName_1687_; lean_object* v_binderType_1688_; lean_object* v_body_1689_; uint8_t v_binderInfo_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec(v_proj_1672_);
lean_dec(v_mdata_1671_);
lean_dec(v_lit_1670_);
lean_dec(v_letE_1669_);
lean_dec(v_forallE_1668_);
lean_dec(v_app_1666_);
lean_dec(v_const_1665_);
lean_dec(v_sort_1664_);
lean_dec(v_mvar_1663_);
lean_dec(v_fvar_1662_);
lean_dec(v_bvar_1661_);
v_binderName_1687_ = lean_ctor_get(v_t_1660_, 0);
lean_inc(v_binderName_1687_);
v_binderType_1688_ = lean_ctor_get(v_t_1660_, 1);
lean_inc_ref(v_binderType_1688_);
v_body_1689_ = lean_ctor_get(v_t_1660_, 2);
lean_inc_ref(v_body_1689_);
v_binderInfo_1690_ = lean_ctor_get_uint8(v_t_1660_, sizeof(void*)*3 + 8);
lean_dec_ref(v_t_1660_);
v___x_1691_ = lean_box(v_binderInfo_1690_);
v___x_1692_ = lean_apply_4(v_lam_1667_, v_binderName_1687_, v_binderType_1688_, v_body_1689_, v___x_1691_);
return v___x_1692_;
}
case 7:
{
lean_object* v_binderName_1693_; lean_object* v_binderType_1694_; lean_object* v_body_1695_; uint8_t v_binderInfo_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_dec(v_proj_1672_);
lean_dec(v_mdata_1671_);
lean_dec(v_lit_1670_);
lean_dec(v_letE_1669_);
lean_dec(v_lam_1667_);
lean_dec(v_app_1666_);
lean_dec(v_const_1665_);
lean_dec(v_sort_1664_);
lean_dec(v_mvar_1663_);
lean_dec(v_fvar_1662_);
lean_dec(v_bvar_1661_);
v_binderName_1693_ = lean_ctor_get(v_t_1660_, 0);
lean_inc(v_binderName_1693_);
v_binderType_1694_ = lean_ctor_get(v_t_1660_, 1);
lean_inc_ref(v_binderType_1694_);
v_body_1695_ = lean_ctor_get(v_t_1660_, 2);
lean_inc_ref(v_body_1695_);
v_binderInfo_1696_ = lean_ctor_get_uint8(v_t_1660_, sizeof(void*)*3 + 8);
lean_dec_ref(v_t_1660_);
v___x_1697_ = lean_box(v_binderInfo_1696_);
v___x_1698_ = lean_apply_4(v_forallE_1668_, v_binderName_1693_, v_binderType_1694_, v_body_1695_, v___x_1697_);
return v___x_1698_;
}
case 8:
{
lean_object* v_declName_1699_; lean_object* v_type_1700_; lean_object* v_value_1701_; lean_object* v_body_1702_; uint8_t v_nondep_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec(v_proj_1672_);
lean_dec(v_mdata_1671_);
lean_dec(v_lit_1670_);
lean_dec(v_forallE_1668_);
lean_dec(v_lam_1667_);
lean_dec(v_app_1666_);
lean_dec(v_const_1665_);
lean_dec(v_sort_1664_);
lean_dec(v_mvar_1663_);
lean_dec(v_fvar_1662_);
lean_dec(v_bvar_1661_);
v_declName_1699_ = lean_ctor_get(v_t_1660_, 0);
lean_inc(v_declName_1699_);
v_type_1700_ = lean_ctor_get(v_t_1660_, 1);
lean_inc_ref(v_type_1700_);
v_value_1701_ = lean_ctor_get(v_t_1660_, 2);
lean_inc_ref(v_value_1701_);
v_body_1702_ = lean_ctor_get(v_t_1660_, 3);
lean_inc_ref(v_body_1702_);
v_nondep_1703_ = lean_ctor_get_uint8(v_t_1660_, sizeof(void*)*4 + 8);
lean_dec_ref(v_t_1660_);
v___x_1704_ = lean_box(v_nondep_1703_);
v___x_1705_ = lean_apply_5(v_letE_1669_, v_declName_1699_, v_type_1700_, v_value_1701_, v_body_1702_, v___x_1704_);
return v___x_1705_;
}
case 9:
{
lean_object* v_a_1706_; lean_object* v___x_1707_; 
lean_dec(v_proj_1672_);
lean_dec(v_mdata_1671_);
lean_dec(v_letE_1669_);
lean_dec(v_forallE_1668_);
lean_dec(v_lam_1667_);
lean_dec(v_app_1666_);
lean_dec(v_const_1665_);
lean_dec(v_sort_1664_);
lean_dec(v_mvar_1663_);
lean_dec(v_fvar_1662_);
lean_dec(v_bvar_1661_);
v_a_1706_ = lean_ctor_get(v_t_1660_, 0);
lean_inc_ref(v_a_1706_);
lean_dec_ref(v_t_1660_);
v___x_1707_ = lean_apply_1(v_lit_1670_, v_a_1706_);
return v___x_1707_;
}
case 10:
{
lean_object* v_data_1708_; lean_object* v_expr_1709_; lean_object* v___x_1710_; 
lean_dec(v_proj_1672_);
lean_dec(v_lit_1670_);
lean_dec(v_letE_1669_);
lean_dec(v_forallE_1668_);
lean_dec(v_lam_1667_);
lean_dec(v_app_1666_);
lean_dec(v_const_1665_);
lean_dec(v_sort_1664_);
lean_dec(v_mvar_1663_);
lean_dec(v_fvar_1662_);
lean_dec(v_bvar_1661_);
v_data_1708_ = lean_ctor_get(v_t_1660_, 0);
lean_inc(v_data_1708_);
v_expr_1709_ = lean_ctor_get(v_t_1660_, 1);
lean_inc_ref(v_expr_1709_);
lean_dec_ref(v_t_1660_);
v___x_1710_ = lean_apply_2(v_mdata_1671_, v_data_1708_, v_expr_1709_);
return v___x_1710_;
}
default: 
{
lean_object* v_typeName_1711_; lean_object* v_idx_1712_; lean_object* v_struct_1713_; lean_object* v___x_1714_; 
lean_dec(v_mdata_1671_);
lean_dec(v_lit_1670_);
lean_dec(v_letE_1669_);
lean_dec(v_forallE_1668_);
lean_dec(v_lam_1667_);
lean_dec(v_app_1666_);
lean_dec(v_const_1665_);
lean_dec(v_sort_1664_);
lean_dec(v_mvar_1663_);
lean_dec(v_fvar_1662_);
lean_dec(v_bvar_1661_);
v_typeName_1711_ = lean_ctor_get(v_t_1660_, 0);
lean_inc(v_typeName_1711_);
v_idx_1712_ = lean_ctor_get(v_t_1660_, 1);
lean_inc(v_idx_1712_);
v_struct_1713_ = lean_ctor_get(v_t_1660_, 2);
lean_inc_ref(v_struct_1713_);
lean_dec_ref(v_t_1660_);
v___x_1714_ = lean_apply_3(v_proj_1672_, v_typeName_1711_, v_idx_1712_, v_struct_1713_);
return v___x_1714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* v_motive_1715_, lean_object* v_t_1716_, lean_object* v_bvar_1717_, lean_object* v_fvar_1718_, lean_object* v_mvar_1719_, lean_object* v_sort_1720_, lean_object* v_const_1721_, lean_object* v_app_1722_, lean_object* v_lam_1723_, lean_object* v_forallE_1724_, lean_object* v_letE_1725_, lean_object* v_lit_1726_, lean_object* v_mdata_1727_, lean_object* v_proj_1728_){
_start:
{
switch(lean_obj_tag(v_t_1716_))
{
case 0:
{
lean_object* v_deBruijnIndex_1729_; lean_object* v___x_1730_; 
lean_dec(v_proj_1728_);
lean_dec(v_mdata_1727_);
lean_dec(v_lit_1726_);
lean_dec(v_letE_1725_);
lean_dec(v_forallE_1724_);
lean_dec(v_lam_1723_);
lean_dec(v_app_1722_);
lean_dec(v_const_1721_);
lean_dec(v_sort_1720_);
lean_dec(v_mvar_1719_);
lean_dec(v_fvar_1718_);
v_deBruijnIndex_1729_ = lean_ctor_get(v_t_1716_, 0);
lean_inc(v_deBruijnIndex_1729_);
lean_dec_ref(v_t_1716_);
v___x_1730_ = lean_apply_1(v_bvar_1717_, v_deBruijnIndex_1729_);
return v___x_1730_;
}
case 1:
{
lean_object* v_fvarId_1731_; lean_object* v___x_1732_; 
lean_dec(v_proj_1728_);
lean_dec(v_mdata_1727_);
lean_dec(v_lit_1726_);
lean_dec(v_letE_1725_);
lean_dec(v_forallE_1724_);
lean_dec(v_lam_1723_);
lean_dec(v_app_1722_);
lean_dec(v_const_1721_);
lean_dec(v_sort_1720_);
lean_dec(v_mvar_1719_);
lean_dec(v_bvar_1717_);
v_fvarId_1731_ = lean_ctor_get(v_t_1716_, 0);
lean_inc(v_fvarId_1731_);
lean_dec_ref(v_t_1716_);
v___x_1732_ = lean_apply_1(v_fvar_1718_, v_fvarId_1731_);
return v___x_1732_;
}
case 2:
{
lean_object* v_mvarId_1733_; lean_object* v___x_1734_; 
lean_dec(v_proj_1728_);
lean_dec(v_mdata_1727_);
lean_dec(v_lit_1726_);
lean_dec(v_letE_1725_);
lean_dec(v_forallE_1724_);
lean_dec(v_lam_1723_);
lean_dec(v_app_1722_);
lean_dec(v_const_1721_);
lean_dec(v_sort_1720_);
lean_dec(v_fvar_1718_);
lean_dec(v_bvar_1717_);
v_mvarId_1733_ = lean_ctor_get(v_t_1716_, 0);
lean_inc(v_mvarId_1733_);
lean_dec_ref(v_t_1716_);
v___x_1734_ = lean_apply_1(v_mvar_1719_, v_mvarId_1733_);
return v___x_1734_;
}
case 3:
{
lean_object* v_u_1735_; lean_object* v___x_1736_; 
lean_dec(v_proj_1728_);
lean_dec(v_mdata_1727_);
lean_dec(v_lit_1726_);
lean_dec(v_letE_1725_);
lean_dec(v_forallE_1724_);
lean_dec(v_lam_1723_);
lean_dec(v_app_1722_);
lean_dec(v_const_1721_);
lean_dec(v_mvar_1719_);
lean_dec(v_fvar_1718_);
lean_dec(v_bvar_1717_);
v_u_1735_ = lean_ctor_get(v_t_1716_, 0);
lean_inc(v_u_1735_);
lean_dec_ref(v_t_1716_);
v___x_1736_ = lean_apply_1(v_sort_1720_, v_u_1735_);
return v___x_1736_;
}
case 4:
{
lean_object* v_declName_1737_; lean_object* v_us_1738_; lean_object* v___x_1739_; 
lean_dec(v_proj_1728_);
lean_dec(v_mdata_1727_);
lean_dec(v_lit_1726_);
lean_dec(v_letE_1725_);
lean_dec(v_forallE_1724_);
lean_dec(v_lam_1723_);
lean_dec(v_app_1722_);
lean_dec(v_sort_1720_);
lean_dec(v_mvar_1719_);
lean_dec(v_fvar_1718_);
lean_dec(v_bvar_1717_);
v_declName_1737_ = lean_ctor_get(v_t_1716_, 0);
lean_inc(v_declName_1737_);
v_us_1738_ = lean_ctor_get(v_t_1716_, 1);
lean_inc(v_us_1738_);
lean_dec_ref(v_t_1716_);
v___x_1739_ = lean_apply_2(v_const_1721_, v_declName_1737_, v_us_1738_);
return v___x_1739_;
}
case 5:
{
lean_object* v_fn_1740_; lean_object* v_arg_1741_; lean_object* v___x_1742_; 
lean_dec(v_proj_1728_);
lean_dec(v_mdata_1727_);
lean_dec(v_lit_1726_);
lean_dec(v_letE_1725_);
lean_dec(v_forallE_1724_);
lean_dec(v_lam_1723_);
lean_dec(v_const_1721_);
lean_dec(v_sort_1720_);
lean_dec(v_mvar_1719_);
lean_dec(v_fvar_1718_);
lean_dec(v_bvar_1717_);
v_fn_1740_ = lean_ctor_get(v_t_1716_, 0);
lean_inc_ref(v_fn_1740_);
v_arg_1741_ = lean_ctor_get(v_t_1716_, 1);
lean_inc_ref(v_arg_1741_);
lean_dec_ref(v_t_1716_);
v___x_1742_ = lean_apply_2(v_app_1722_, v_fn_1740_, v_arg_1741_);
return v___x_1742_;
}
case 6:
{
lean_object* v_binderName_1743_; lean_object* v_binderType_1744_; lean_object* v_body_1745_; uint8_t v_binderInfo_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec(v_proj_1728_);
lean_dec(v_mdata_1727_);
lean_dec(v_lit_1726_);
lean_dec(v_letE_1725_);
lean_dec(v_forallE_1724_);
lean_dec(v_app_1722_);
lean_dec(v_const_1721_);
lean_dec(v_sort_1720_);
lean_dec(v_mvar_1719_);
lean_dec(v_fvar_1718_);
lean_dec(v_bvar_1717_);
v_binderName_1743_ = lean_ctor_get(v_t_1716_, 0);
lean_inc(v_binderName_1743_);
v_binderType_1744_ = lean_ctor_get(v_t_1716_, 1);
lean_inc_ref(v_binderType_1744_);
v_body_1745_ = lean_ctor_get(v_t_1716_, 2);
lean_inc_ref(v_body_1745_);
v_binderInfo_1746_ = lean_ctor_get_uint8(v_t_1716_, sizeof(void*)*3 + 8);
lean_dec_ref(v_t_1716_);
v___x_1747_ = lean_box(v_binderInfo_1746_);
v___x_1748_ = lean_apply_4(v_lam_1723_, v_binderName_1743_, v_binderType_1744_, v_body_1745_, v___x_1747_);
return v___x_1748_;
}
case 7:
{
lean_object* v_binderName_1749_; lean_object* v_binderType_1750_; lean_object* v_body_1751_; uint8_t v_binderInfo_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec(v_proj_1728_);
lean_dec(v_mdata_1727_);
lean_dec(v_lit_1726_);
lean_dec(v_letE_1725_);
lean_dec(v_lam_1723_);
lean_dec(v_app_1722_);
lean_dec(v_const_1721_);
lean_dec(v_sort_1720_);
lean_dec(v_mvar_1719_);
lean_dec(v_fvar_1718_);
lean_dec(v_bvar_1717_);
v_binderName_1749_ = lean_ctor_get(v_t_1716_, 0);
lean_inc(v_binderName_1749_);
v_binderType_1750_ = lean_ctor_get(v_t_1716_, 1);
lean_inc_ref(v_binderType_1750_);
v_body_1751_ = lean_ctor_get(v_t_1716_, 2);
lean_inc_ref(v_body_1751_);
v_binderInfo_1752_ = lean_ctor_get_uint8(v_t_1716_, sizeof(void*)*3 + 8);
lean_dec_ref(v_t_1716_);
v___x_1753_ = lean_box(v_binderInfo_1752_);
v___x_1754_ = lean_apply_4(v_forallE_1724_, v_binderName_1749_, v_binderType_1750_, v_body_1751_, v___x_1753_);
return v___x_1754_;
}
case 8:
{
lean_object* v_declName_1755_; lean_object* v_type_1756_; lean_object* v_value_1757_; lean_object* v_body_1758_; uint8_t v_nondep_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec(v_proj_1728_);
lean_dec(v_mdata_1727_);
lean_dec(v_lit_1726_);
lean_dec(v_forallE_1724_);
lean_dec(v_lam_1723_);
lean_dec(v_app_1722_);
lean_dec(v_const_1721_);
lean_dec(v_sort_1720_);
lean_dec(v_mvar_1719_);
lean_dec(v_fvar_1718_);
lean_dec(v_bvar_1717_);
v_declName_1755_ = lean_ctor_get(v_t_1716_, 0);
lean_inc(v_declName_1755_);
v_type_1756_ = lean_ctor_get(v_t_1716_, 1);
lean_inc_ref(v_type_1756_);
v_value_1757_ = lean_ctor_get(v_t_1716_, 2);
lean_inc_ref(v_value_1757_);
v_body_1758_ = lean_ctor_get(v_t_1716_, 3);
lean_inc_ref(v_body_1758_);
v_nondep_1759_ = lean_ctor_get_uint8(v_t_1716_, sizeof(void*)*4 + 8);
lean_dec_ref(v_t_1716_);
v___x_1760_ = lean_box(v_nondep_1759_);
v___x_1761_ = lean_apply_5(v_letE_1725_, v_declName_1755_, v_type_1756_, v_value_1757_, v_body_1758_, v___x_1760_);
return v___x_1761_;
}
case 9:
{
lean_object* v_a_1762_; lean_object* v___x_1763_; 
lean_dec(v_proj_1728_);
lean_dec(v_mdata_1727_);
lean_dec(v_letE_1725_);
lean_dec(v_forallE_1724_);
lean_dec(v_lam_1723_);
lean_dec(v_app_1722_);
lean_dec(v_const_1721_);
lean_dec(v_sort_1720_);
lean_dec(v_mvar_1719_);
lean_dec(v_fvar_1718_);
lean_dec(v_bvar_1717_);
v_a_1762_ = lean_ctor_get(v_t_1716_, 0);
lean_inc_ref(v_a_1762_);
lean_dec_ref(v_t_1716_);
v___x_1763_ = lean_apply_1(v_lit_1726_, v_a_1762_);
return v___x_1763_;
}
case 10:
{
lean_object* v_data_1764_; lean_object* v_expr_1765_; lean_object* v___x_1766_; 
lean_dec(v_proj_1728_);
lean_dec(v_lit_1726_);
lean_dec(v_letE_1725_);
lean_dec(v_forallE_1724_);
lean_dec(v_lam_1723_);
lean_dec(v_app_1722_);
lean_dec(v_const_1721_);
lean_dec(v_sort_1720_);
lean_dec(v_mvar_1719_);
lean_dec(v_fvar_1718_);
lean_dec(v_bvar_1717_);
v_data_1764_ = lean_ctor_get(v_t_1716_, 0);
lean_inc(v_data_1764_);
v_expr_1765_ = lean_ctor_get(v_t_1716_, 1);
lean_inc_ref(v_expr_1765_);
lean_dec_ref(v_t_1716_);
v___x_1766_ = lean_apply_2(v_mdata_1727_, v_data_1764_, v_expr_1765_);
return v___x_1766_;
}
default: 
{
lean_object* v_typeName_1767_; lean_object* v_idx_1768_; lean_object* v_struct_1769_; lean_object* v___x_1770_; 
lean_dec(v_mdata_1727_);
lean_dec(v_lit_1726_);
lean_dec(v_letE_1725_);
lean_dec(v_forallE_1724_);
lean_dec(v_lam_1723_);
lean_dec(v_app_1722_);
lean_dec(v_const_1721_);
lean_dec(v_sort_1720_);
lean_dec(v_mvar_1719_);
lean_dec(v_fvar_1718_);
lean_dec(v_bvar_1717_);
v_typeName_1767_ = lean_ctor_get(v_t_1716_, 0);
lean_inc(v_typeName_1767_);
v_idx_1768_ = lean_ctor_get(v_t_1716_, 1);
lean_inc(v_idx_1768_);
v_struct_1769_ = lean_ctor_get(v_t_1716_, 2);
lean_inc_ref(v_struct_1769_);
lean_dec_ref(v_t_1716_);
v___x_1770_ = lean_apply_3(v_proj_1728_, v_typeName_1767_, v_idx_1768_, v_struct_1769_);
return v___x_1770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* v_deBruijnIndex_1771_){
_start:
{
uint64_t v___x_1772_; uint64_t v___x_1773_; uint64_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; uint32_t v___x_1777_; uint8_t v___x_1778_; uint64_t v___x_1779_; lean_object* v___x_1780_; 
v___x_1772_ = 7ULL;
v___x_1773_ = lean_uint64_of_nat(v_deBruijnIndex_1771_);
v___x_1774_ = lean_uint64_mix_hash(v___x_1772_, v___x_1773_);
v___x_1775_ = lean_unsigned_to_nat(1u);
v___x_1776_ = lean_nat_add(v_deBruijnIndex_1771_, v___x_1775_);
v___x_1777_ = 0;
v___x_1778_ = 0;
v___x_1779_ = lean_expr_mk_data(v___x_1774_, v___x_1776_, v___x_1777_, v___x_1778_, v___x_1778_, v___x_1778_, v___x_1778_);
v___x_1780_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1780_, 0, v_deBruijnIndex_1771_);
lean_ctor_set_uint64(v___x_1780_, sizeof(void*)*1, v___x_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* v_fvarId_1781_){
_start:
{
uint64_t v___x_1782_; uint64_t v___x_1783_; uint64_t v___x_1784_; lean_object* v___x_1785_; uint32_t v___x_1786_; uint8_t v___x_1787_; uint8_t v___x_1788_; uint64_t v___x_1789_; lean_object* v___x_1790_; 
v___x_1782_ = 13ULL;
v___x_1783_ = l_Lean_instHashableFVarId_hash(v_fvarId_1781_);
v___x_1784_ = lean_uint64_mix_hash(v___x_1782_, v___x_1783_);
v___x_1785_ = lean_unsigned_to_nat(0u);
v___x_1786_ = 0;
v___x_1787_ = 1;
v___x_1788_ = 0;
v___x_1789_ = lean_expr_mk_data(v___x_1784_, v___x_1785_, v___x_1786_, v___x_1787_, v___x_1788_, v___x_1788_, v___x_1788_);
v___x_1790_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_1790_, 0, v_fvarId_1781_);
lean_ctor_set_uint64(v___x_1790_, sizeof(void*)*1, v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* v_mvarId_1791_){
_start:
{
uint64_t v___x_1792_; uint64_t v___x_1793_; uint64_t v___x_1794_; lean_object* v___x_1795_; uint32_t v___x_1796_; uint8_t v___x_1797_; uint8_t v___x_1798_; uint64_t v___x_1799_; lean_object* v___x_1800_; 
v___x_1792_ = 17ULL;
v___x_1793_ = l_Lean_instHashableMVarId_hash(v_mvarId_1791_);
v___x_1794_ = lean_uint64_mix_hash(v___x_1792_, v___x_1793_);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = 0;
v___x_1797_ = 0;
v___x_1798_ = 1;
v___x_1799_ = lean_expr_mk_data(v___x_1794_, v___x_1795_, v___x_1796_, v___x_1797_, v___x_1798_, v___x_1797_, v___x_1797_);
v___x_1800_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_1800_, 0, v_mvarId_1791_);
lean_ctor_set_uint64(v___x_1800_, sizeof(void*)*1, v___x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* v_u_1801_){
_start:
{
uint64_t v___x_1802_; uint64_t v___x_1803_; uint64_t v___x_1804_; lean_object* v___x_1805_; uint32_t v___x_1806_; uint8_t v___x_1807_; uint8_t v___x_1808_; uint8_t v___x_1809_; uint64_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1802_ = 11ULL;
v___x_1803_ = l_Lean_Level_hash(v_u_1801_);
v___x_1804_ = lean_uint64_mix_hash(v___x_1802_, v___x_1803_);
v___x_1805_ = lean_unsigned_to_nat(0u);
v___x_1806_ = 0;
v___x_1807_ = 0;
v___x_1808_ = l_Lean_Level_hasMVar(v_u_1801_);
v___x_1809_ = l_Lean_Level_hasParam(v_u_1801_);
v___x_1810_ = lean_expr_mk_data(v___x_1804_, v___x_1805_, v___x_1806_, v___x_1807_, v___x_1807_, v___x_1808_, v___x_1809_);
v___x_1811_ = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(v___x_1811_, 0, v_u_1801_);
lean_ctor_set_uint64(v___x_1811_, sizeof(void*)*1, v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* v_fn_1812_, lean_object* v_arg_1813_){
_start:
{
uint64_t v___x_1814_; uint64_t v___x_1815_; uint64_t v___x_1816_; lean_object* v___x_1817_; 
v___x_1814_ = lean_expr_data(v_fn_1812_);
v___x_1815_ = lean_expr_data(v_arg_1813_);
v___x_1816_ = lean_expr_mk_app_data(v___x_1814_, v___x_1815_);
v___x_1817_ = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(v___x_1817_, 0, v_fn_1812_);
lean_ctor_set(v___x_1817_, 1, v_arg_1813_);
lean_ctor_set_uint64(v___x_1817_, sizeof(void*)*2, v___x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object* v_binderName_1818_, lean_object* v_binderType_1819_, lean_object* v_body_1820_, uint8_t v_binderInfo_1821_){
_start:
{
uint32_t v___y_1823_; uint8_t v___y_1824_; uint8_t v___y_1825_; uint8_t v___y_1826_; lean_object* v___y_1827_; uint64_t v___y_1828_; uint8_t v___y_1829_; uint64_t v___x_1832_; uint8_t v___x_1833_; uint32_t v___x_1834_; uint64_t v___x_1835_; uint32_t v___y_1837_; uint8_t v___y_1838_; uint8_t v___y_1839_; uint64_t v___y_1840_; lean_object* v___y_1841_; uint8_t v___y_1842_; uint32_t v___y_1846_; uint8_t v___y_1847_; lean_object* v___y_1848_; uint64_t v___y_1849_; uint8_t v___y_1850_; uint32_t v___y_1854_; uint64_t v___y_1855_; lean_object* v___y_1856_; uint8_t v___y_1857_; uint32_t v___y_1861_; uint64_t v___y_1862_; lean_object* v___y_1863_; uint32_t v___y_1867_; uint8_t v___x_1882_; uint32_t v___x_1883_; uint8_t v___x_1884_; 
v___x_1832_ = lean_expr_data(v_binderType_1819_);
v___x_1833_ = l_Lean_Expr_Data_approxDepth(v___x_1832_);
v___x_1834_ = lean_uint8_to_uint32(v___x_1833_);
v___x_1835_ = lean_expr_data(v_body_1820_);
v___x_1882_ = l_Lean_Expr_Data_approxDepth(v___x_1835_);
v___x_1883_ = lean_uint8_to_uint32(v___x_1882_);
v___x_1884_ = lean_uint32_dec_le(v___x_1834_, v___x_1883_);
if (v___x_1884_ == 0)
{
v___y_1867_ = v___x_1834_;
goto v___jp_1866_;
}
else
{
v___y_1867_ = v___x_1883_;
goto v___jp_1866_;
}
v___jp_1822_:
{
uint64_t v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = lean_expr_mk_data(v___y_1828_, v___y_1827_, v___y_1823_, v___y_1825_, v___y_1826_, v___y_1824_, v___y_1829_);
v___x_1831_ = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(v___x_1831_, 0, v_binderName_1818_);
lean_ctor_set(v___x_1831_, 1, v_binderType_1819_);
lean_ctor_set(v___x_1831_, 2, v_body_1820_);
lean_ctor_set_uint64(v___x_1831_, sizeof(void*)*3, v___x_1830_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 8, v_binderInfo_1821_);
return v___x_1831_;
}
v___jp_1836_:
{
uint8_t v___x_1843_; 
v___x_1843_ = l_Lean_Expr_Data_hasLevelParam(v___x_1832_);
if (v___x_1843_ == 0)
{
uint8_t v___x_1844_; 
v___x_1844_ = l_Lean_Expr_Data_hasLevelParam(v___x_1835_);
v___y_1823_ = v___y_1837_;
v___y_1824_ = v___y_1842_;
v___y_1825_ = v___y_1838_;
v___y_1826_ = v___y_1839_;
v___y_1827_ = v___y_1841_;
v___y_1828_ = v___y_1840_;
v___y_1829_ = v___x_1844_;
goto v___jp_1822_;
}
else
{
v___y_1823_ = v___y_1837_;
v___y_1824_ = v___y_1842_;
v___y_1825_ = v___y_1838_;
v___y_1826_ = v___y_1839_;
v___y_1827_ = v___y_1841_;
v___y_1828_ = v___y_1840_;
v___y_1829_ = v___x_1843_;
goto v___jp_1822_;
}
}
v___jp_1845_:
{
uint8_t v___x_1851_; 
v___x_1851_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1832_);
if (v___x_1851_ == 0)
{
uint8_t v___x_1852_; 
v___x_1852_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1835_);
v___y_1837_ = v___y_1846_;
v___y_1838_ = v___y_1847_;
v___y_1839_ = v___y_1850_;
v___y_1840_ = v___y_1849_;
v___y_1841_ = v___y_1848_;
v___y_1842_ = v___x_1852_;
goto v___jp_1836_;
}
else
{
v___y_1837_ = v___y_1846_;
v___y_1838_ = v___y_1847_;
v___y_1839_ = v___y_1850_;
v___y_1840_ = v___y_1849_;
v___y_1841_ = v___y_1848_;
v___y_1842_ = v___x_1851_;
goto v___jp_1836_;
}
}
v___jp_1853_:
{
uint8_t v___x_1858_; 
v___x_1858_ = l_Lean_Expr_Data_hasExprMVar(v___x_1832_);
if (v___x_1858_ == 0)
{
uint8_t v___x_1859_; 
v___x_1859_ = l_Lean_Expr_Data_hasExprMVar(v___x_1835_);
v___y_1846_ = v___y_1854_;
v___y_1847_ = v___y_1857_;
v___y_1848_ = v___y_1856_;
v___y_1849_ = v___y_1855_;
v___y_1850_ = v___x_1859_;
goto v___jp_1845_;
}
else
{
v___y_1846_ = v___y_1854_;
v___y_1847_ = v___y_1857_;
v___y_1848_ = v___y_1856_;
v___y_1849_ = v___y_1855_;
v___y_1850_ = v___x_1858_;
goto v___jp_1845_;
}
}
v___jp_1860_:
{
uint8_t v___x_1864_; 
v___x_1864_ = l_Lean_Expr_Data_hasFVar(v___x_1832_);
if (v___x_1864_ == 0)
{
uint8_t v___x_1865_; 
v___x_1865_ = l_Lean_Expr_Data_hasFVar(v___x_1835_);
v___y_1854_ = v___y_1861_;
v___y_1855_ = v___y_1862_;
v___y_1856_ = v___y_1863_;
v___y_1857_ = v___x_1865_;
goto v___jp_1853_;
}
else
{
v___y_1854_ = v___y_1861_;
v___y_1855_ = v___y_1862_;
v___y_1856_ = v___y_1863_;
v___y_1857_ = v___x_1864_;
goto v___jp_1853_;
}
}
v___jp_1866_:
{
lean_object* v___x_1868_; uint32_t v___x_1869_; uint32_t v___x_1870_; uint64_t v___x_1871_; uint64_t v___x_1872_; uint64_t v___x_1873_; uint64_t v___x_1874_; uint64_t v___x_1875_; uint32_t v___x_1876_; lean_object* v___x_1877_; uint32_t v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v___x_1868_ = lean_unsigned_to_nat(1u);
v___x_1869_ = 1;
v___x_1870_ = lean_uint32_add(v___y_1867_, v___x_1869_);
v___x_1871_ = lean_uint32_to_uint64(v___x_1870_);
v___x_1872_ = l_Lean_Expr_Data_hash(v___x_1832_);
v___x_1873_ = l_Lean_Expr_Data_hash(v___x_1835_);
v___x_1874_ = lean_uint64_mix_hash(v___x_1872_, v___x_1873_);
v___x_1875_ = lean_uint64_mix_hash(v___x_1871_, v___x_1874_);
v___x_1876_ = l_Lean_Expr_Data_looseBVarRange(v___x_1832_);
v___x_1877_ = lean_uint32_to_nat(v___x_1876_);
v___x_1878_ = l_Lean_Expr_Data_looseBVarRange(v___x_1835_);
v___x_1879_ = lean_uint32_to_nat(v___x_1878_);
v___x_1880_ = lean_nat_sub(v___x_1879_, v___x_1868_);
lean_dec(v___x_1879_);
v___x_1881_ = lean_nat_dec_le(v___x_1877_, v___x_1880_);
if (v___x_1881_ == 0)
{
lean_dec(v___x_1880_);
v___y_1861_ = v___x_1870_;
v___y_1862_ = v___x_1875_;
v___y_1863_ = v___x_1877_;
goto v___jp_1860_;
}
else
{
lean_dec(v___x_1877_);
v___y_1861_ = v___x_1870_;
v___y_1862_ = v___x_1875_;
v___y_1863_ = v___x_1880_;
goto v___jp_1860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* v_binderName_1885_, lean_object* v_binderType_1886_, lean_object* v_body_1887_, lean_object* v_binderInfo_1888_){
_start:
{
uint8_t v_binderInfo_boxed_1889_; lean_object* v_res_1890_; 
v_binderInfo_boxed_1889_ = lean_unbox(v_binderInfo_1888_);
v_res_1890_ = l_Lean_Expr_lam___override(v_binderName_1885_, v_binderType_1886_, v_body_1887_, v_binderInfo_boxed_1889_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object* v_binderName_1891_, lean_object* v_binderType_1892_, lean_object* v_body_1893_, uint8_t v_binderInfo_1894_){
_start:
{
uint8_t v___y_1896_; uint8_t v___y_1897_; lean_object* v___y_1898_; uint64_t v___y_1899_; uint8_t v___y_1900_; uint32_t v___y_1901_; uint8_t v___y_1902_; uint64_t v___x_1905_; uint8_t v___x_1906_; uint32_t v___x_1907_; uint64_t v___x_1908_; uint8_t v___y_1910_; lean_object* v___y_1911_; uint64_t v___y_1912_; uint32_t v___y_1913_; uint8_t v___y_1914_; uint8_t v___y_1915_; uint8_t v___y_1919_; lean_object* v___y_1920_; uint64_t v___y_1921_; uint32_t v___y_1922_; uint8_t v___y_1923_; lean_object* v___y_1927_; uint64_t v___y_1928_; uint32_t v___y_1929_; uint8_t v___y_1930_; uint64_t v___y_1934_; uint32_t v___y_1935_; lean_object* v___y_1936_; uint32_t v___y_1940_; uint8_t v___x_1955_; uint32_t v___x_1956_; uint8_t v___x_1957_; 
v___x_1905_ = lean_expr_data(v_binderType_1892_);
v___x_1906_ = l_Lean_Expr_Data_approxDepth(v___x_1905_);
v___x_1907_ = lean_uint8_to_uint32(v___x_1906_);
v___x_1908_ = lean_expr_data(v_body_1893_);
v___x_1955_ = l_Lean_Expr_Data_approxDepth(v___x_1908_);
v___x_1956_ = lean_uint8_to_uint32(v___x_1955_);
v___x_1957_ = lean_uint32_dec_le(v___x_1907_, v___x_1956_);
if (v___x_1957_ == 0)
{
v___y_1940_ = v___x_1907_;
goto v___jp_1939_;
}
else
{
v___y_1940_ = v___x_1956_;
goto v___jp_1939_;
}
v___jp_1895_:
{
uint64_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_expr_mk_data(v___y_1899_, v___y_1898_, v___y_1901_, v___y_1897_, v___y_1900_, v___y_1896_, v___y_1902_);
v___x_1904_ = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(v___x_1904_, 0, v_binderName_1891_);
lean_ctor_set(v___x_1904_, 1, v_binderType_1892_);
lean_ctor_set(v___x_1904_, 2, v_body_1893_);
lean_ctor_set_uint64(v___x_1904_, sizeof(void*)*3, v___x_1903_);
lean_ctor_set_uint8(v___x_1904_, sizeof(void*)*3 + 8, v_binderInfo_1894_);
return v___x_1904_;
}
v___jp_1909_:
{
uint8_t v___x_1916_; 
v___x_1916_ = l_Lean_Expr_Data_hasLevelParam(v___x_1905_);
if (v___x_1916_ == 0)
{
uint8_t v___x_1917_; 
v___x_1917_ = l_Lean_Expr_Data_hasLevelParam(v___x_1908_);
v___y_1896_ = v___y_1915_;
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v___y_1900_ = v___y_1914_;
v___y_1901_ = v___y_1913_;
v___y_1902_ = v___x_1917_;
goto v___jp_1895_;
}
else
{
v___y_1896_ = v___y_1915_;
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v___y_1900_ = v___y_1914_;
v___y_1901_ = v___y_1913_;
v___y_1902_ = v___x_1916_;
goto v___jp_1895_;
}
}
v___jp_1918_:
{
uint8_t v___x_1924_; 
v___x_1924_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1905_);
if (v___x_1924_ == 0)
{
uint8_t v___x_1925_; 
v___x_1925_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1908_);
v___y_1910_ = v___y_1919_;
v___y_1911_ = v___y_1920_;
v___y_1912_ = v___y_1921_;
v___y_1913_ = v___y_1922_;
v___y_1914_ = v___y_1923_;
v___y_1915_ = v___x_1925_;
goto v___jp_1909_;
}
else
{
v___y_1910_ = v___y_1919_;
v___y_1911_ = v___y_1920_;
v___y_1912_ = v___y_1921_;
v___y_1913_ = v___y_1922_;
v___y_1914_ = v___y_1923_;
v___y_1915_ = v___x_1924_;
goto v___jp_1909_;
}
}
v___jp_1926_:
{
uint8_t v___x_1931_; 
v___x_1931_ = l_Lean_Expr_Data_hasExprMVar(v___x_1905_);
if (v___x_1931_ == 0)
{
uint8_t v___x_1932_; 
v___x_1932_ = l_Lean_Expr_Data_hasExprMVar(v___x_1908_);
v___y_1919_ = v___y_1930_;
v___y_1920_ = v___y_1927_;
v___y_1921_ = v___y_1928_;
v___y_1922_ = v___y_1929_;
v___y_1923_ = v___x_1932_;
goto v___jp_1918_;
}
else
{
v___y_1919_ = v___y_1930_;
v___y_1920_ = v___y_1927_;
v___y_1921_ = v___y_1928_;
v___y_1922_ = v___y_1929_;
v___y_1923_ = v___x_1931_;
goto v___jp_1918_;
}
}
v___jp_1933_:
{
uint8_t v___x_1937_; 
v___x_1937_ = l_Lean_Expr_Data_hasFVar(v___x_1905_);
if (v___x_1937_ == 0)
{
uint8_t v___x_1938_; 
v___x_1938_ = l_Lean_Expr_Data_hasFVar(v___x_1908_);
v___y_1927_ = v___y_1936_;
v___y_1928_ = v___y_1934_;
v___y_1929_ = v___y_1935_;
v___y_1930_ = v___x_1938_;
goto v___jp_1926_;
}
else
{
v___y_1927_ = v___y_1936_;
v___y_1928_ = v___y_1934_;
v___y_1929_ = v___y_1935_;
v___y_1930_ = v___x_1937_;
goto v___jp_1926_;
}
}
v___jp_1939_:
{
lean_object* v___x_1941_; uint32_t v___x_1942_; uint32_t v___x_1943_; uint64_t v___x_1944_; uint64_t v___x_1945_; uint64_t v___x_1946_; uint64_t v___x_1947_; uint64_t v___x_1948_; uint32_t v___x_1949_; lean_object* v___x_1950_; uint32_t v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v___x_1941_ = lean_unsigned_to_nat(1u);
v___x_1942_ = 1;
v___x_1943_ = lean_uint32_add(v___y_1940_, v___x_1942_);
v___x_1944_ = lean_uint32_to_uint64(v___x_1943_);
v___x_1945_ = l_Lean_Expr_Data_hash(v___x_1905_);
v___x_1946_ = l_Lean_Expr_Data_hash(v___x_1908_);
v___x_1947_ = lean_uint64_mix_hash(v___x_1945_, v___x_1946_);
v___x_1948_ = lean_uint64_mix_hash(v___x_1944_, v___x_1947_);
v___x_1949_ = l_Lean_Expr_Data_looseBVarRange(v___x_1905_);
v___x_1950_ = lean_uint32_to_nat(v___x_1949_);
v___x_1951_ = l_Lean_Expr_Data_looseBVarRange(v___x_1908_);
v___x_1952_ = lean_uint32_to_nat(v___x_1951_);
v___x_1953_ = lean_nat_sub(v___x_1952_, v___x_1941_);
lean_dec(v___x_1952_);
v___x_1954_ = lean_nat_dec_le(v___x_1950_, v___x_1953_);
if (v___x_1954_ == 0)
{
lean_dec(v___x_1953_);
v___y_1934_ = v___x_1948_;
v___y_1935_ = v___x_1943_;
v___y_1936_ = v___x_1950_;
goto v___jp_1933_;
}
else
{
lean_dec(v___x_1950_);
v___y_1934_ = v___x_1948_;
v___y_1935_ = v___x_1943_;
v___y_1936_ = v___x_1953_;
goto v___jp_1933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* v_binderName_1958_, lean_object* v_binderType_1959_, lean_object* v_body_1960_, lean_object* v_binderInfo_1961_){
_start:
{
uint8_t v_binderInfo_boxed_1962_; lean_object* v_res_1963_; 
v_binderInfo_boxed_1962_ = lean_unbox(v_binderInfo_1961_);
v_res_1963_ = l_Lean_Expr_forallE___override(v_binderName_1958_, v_binderType_1959_, v_body_1960_, v_binderInfo_boxed_1962_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object* v_declName_1964_, lean_object* v_type_1965_, lean_object* v_value_1966_, lean_object* v_body_1967_, uint8_t v_nondep_1968_){
_start:
{
uint64_t v___y_1970_; uint8_t v___y_1971_; uint8_t v___y_1972_; uint32_t v___y_1973_; lean_object* v___y_1974_; uint8_t v___y_1975_; uint8_t v___y_1976_; uint64_t v___y_1980_; uint8_t v___y_1981_; uint64_t v___y_1982_; uint32_t v___y_1983_; uint8_t v___y_1984_; lean_object* v___y_1985_; uint8_t v___y_1986_; uint8_t v___y_1987_; uint64_t v___x_1989_; uint8_t v___x_1990_; uint32_t v___x_1991_; uint64_t v___x_1992_; uint64_t v___y_1994_; uint64_t v___y_1995_; uint32_t v___y_1996_; uint8_t v___y_1997_; lean_object* v___y_1998_; uint8_t v___y_1999_; uint8_t v___y_2000_; uint64_t v___y_2004_; uint64_t v___y_2005_; uint8_t v___y_2006_; uint32_t v___y_2007_; lean_object* v___y_2008_; uint8_t v___y_2009_; uint8_t v___y_2010_; uint64_t v___y_2013_; uint64_t v___y_2014_; uint32_t v___y_2015_; lean_object* v___y_2016_; uint8_t v___y_2017_; uint8_t v___y_2018_; uint64_t v___y_2022_; uint64_t v___y_2023_; uint32_t v___y_2024_; lean_object* v___y_2025_; uint8_t v___y_2026_; uint8_t v___y_2027_; uint64_t v___y_2030_; uint64_t v___y_2031_; uint32_t v___y_2032_; lean_object* v___y_2033_; uint8_t v___y_2034_; uint64_t v___y_2038_; uint64_t v___y_2039_; uint32_t v___y_2040_; lean_object* v___y_2041_; uint8_t v___y_2042_; uint64_t v___y_2045_; uint64_t v___y_2046_; uint32_t v___y_2047_; lean_object* v___y_2048_; uint64_t v___y_2052_; lean_object* v___y_2053_; uint64_t v___y_2054_; uint32_t v___y_2055_; lean_object* v___y_2056_; uint64_t v___y_2062_; uint32_t v___y_2063_; uint32_t v___y_2080_; uint8_t v___x_2085_; uint32_t v___x_2086_; uint8_t v___x_2087_; 
v___x_1989_ = lean_expr_data(v_type_1965_);
v___x_1990_ = l_Lean_Expr_Data_approxDepth(v___x_1989_);
v___x_1991_ = lean_uint8_to_uint32(v___x_1990_);
v___x_1992_ = lean_expr_data(v_value_1966_);
v___x_2085_ = l_Lean_Expr_Data_approxDepth(v___x_1992_);
v___x_2086_ = lean_uint8_to_uint32(v___x_2085_);
v___x_2087_ = lean_uint32_dec_le(v___x_1991_, v___x_2086_);
if (v___x_2087_ == 0)
{
v___y_2080_ = v___x_1991_;
goto v___jp_2079_;
}
else
{
v___y_2080_ = v___x_2086_;
goto v___jp_2079_;
}
v___jp_1969_:
{
uint64_t v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_expr_mk_data(v___y_1970_, v___y_1974_, v___y_1973_, v___y_1975_, v___y_1972_, v___y_1971_, v___y_1976_);
v___x_1978_ = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(v___x_1978_, 0, v_declName_1964_);
lean_ctor_set(v___x_1978_, 1, v_type_1965_);
lean_ctor_set(v___x_1978_, 2, v_value_1966_);
lean_ctor_set(v___x_1978_, 3, v_body_1967_);
lean_ctor_set_uint64(v___x_1978_, sizeof(void*)*4, v___x_1977_);
lean_ctor_set_uint8(v___x_1978_, sizeof(void*)*4 + 8, v_nondep_1968_);
return v___x_1978_;
}
v___jp_1979_:
{
if (v___y_1987_ == 0)
{
uint8_t v___x_1988_; 
v___x_1988_ = l_Lean_Expr_Data_hasLevelParam(v___y_1982_);
v___y_1970_ = v___y_1980_;
v___y_1971_ = v___y_1981_;
v___y_1972_ = v___y_1984_;
v___y_1973_ = v___y_1983_;
v___y_1974_ = v___y_1985_;
v___y_1975_ = v___y_1986_;
v___y_1976_ = v___x_1988_;
goto v___jp_1969_;
}
else
{
v___y_1970_ = v___y_1980_;
v___y_1971_ = v___y_1981_;
v___y_1972_ = v___y_1984_;
v___y_1973_ = v___y_1983_;
v___y_1974_ = v___y_1985_;
v___y_1975_ = v___y_1986_;
v___y_1976_ = v___y_1987_;
goto v___jp_1969_;
}
}
v___jp_1993_:
{
uint8_t v___x_2001_; 
v___x_2001_ = l_Lean_Expr_Data_hasLevelParam(v___x_1989_);
if (v___x_2001_ == 0)
{
uint8_t v___x_2002_; 
v___x_2002_ = l_Lean_Expr_Data_hasLevelParam(v___x_1992_);
v___y_1980_ = v___y_1994_;
v___y_1981_ = v___y_2000_;
v___y_1982_ = v___y_1995_;
v___y_1983_ = v___y_1996_;
v___y_1984_ = v___y_1997_;
v___y_1985_ = v___y_1998_;
v___y_1986_ = v___y_1999_;
v___y_1987_ = v___x_2002_;
goto v___jp_1979_;
}
else
{
v___y_1980_ = v___y_1994_;
v___y_1981_ = v___y_2000_;
v___y_1982_ = v___y_1995_;
v___y_1983_ = v___y_1996_;
v___y_1984_ = v___y_1997_;
v___y_1985_ = v___y_1998_;
v___y_1986_ = v___y_1999_;
v___y_1987_ = v___x_2001_;
goto v___jp_1979_;
}
}
v___jp_2003_:
{
if (v___y_2010_ == 0)
{
uint8_t v___x_2011_; 
v___x_2011_ = l_Lean_Expr_Data_hasLevelMVar(v___y_2005_);
v___y_1994_ = v___y_2004_;
v___y_1995_ = v___y_2005_;
v___y_1996_ = v___y_2007_;
v___y_1997_ = v___y_2006_;
v___y_1998_ = v___y_2008_;
v___y_1999_ = v___y_2009_;
v___y_2000_ = v___x_2011_;
goto v___jp_1993_;
}
else
{
v___y_1994_ = v___y_2004_;
v___y_1995_ = v___y_2005_;
v___y_1996_ = v___y_2007_;
v___y_1997_ = v___y_2006_;
v___y_1998_ = v___y_2008_;
v___y_1999_ = v___y_2009_;
v___y_2000_ = v___y_2010_;
goto v___jp_1993_;
}
}
v___jp_2012_:
{
uint8_t v___x_2019_; 
v___x_2019_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1989_);
if (v___x_2019_ == 0)
{
uint8_t v___x_2020_; 
v___x_2020_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1992_);
v___y_2004_ = v___y_2013_;
v___y_2005_ = v___y_2014_;
v___y_2006_ = v___y_2018_;
v___y_2007_ = v___y_2015_;
v___y_2008_ = v___y_2016_;
v___y_2009_ = v___y_2017_;
v___y_2010_ = v___x_2020_;
goto v___jp_2003_;
}
else
{
v___y_2004_ = v___y_2013_;
v___y_2005_ = v___y_2014_;
v___y_2006_ = v___y_2018_;
v___y_2007_ = v___y_2015_;
v___y_2008_ = v___y_2016_;
v___y_2009_ = v___y_2017_;
v___y_2010_ = v___x_2019_;
goto v___jp_2003_;
}
}
v___jp_2021_:
{
if (v___y_2027_ == 0)
{
uint8_t v___x_2028_; 
v___x_2028_ = l_Lean_Expr_Data_hasExprMVar(v___y_2023_);
v___y_2013_ = v___y_2022_;
v___y_2014_ = v___y_2023_;
v___y_2015_ = v___y_2024_;
v___y_2016_ = v___y_2025_;
v___y_2017_ = v___y_2026_;
v___y_2018_ = v___x_2028_;
goto v___jp_2012_;
}
else
{
v___y_2013_ = v___y_2022_;
v___y_2014_ = v___y_2023_;
v___y_2015_ = v___y_2024_;
v___y_2016_ = v___y_2025_;
v___y_2017_ = v___y_2026_;
v___y_2018_ = v___y_2027_;
goto v___jp_2012_;
}
}
v___jp_2029_:
{
uint8_t v___x_2035_; 
v___x_2035_ = l_Lean_Expr_Data_hasExprMVar(v___x_1989_);
if (v___x_2035_ == 0)
{
uint8_t v___x_2036_; 
v___x_2036_ = l_Lean_Expr_Data_hasExprMVar(v___x_1992_);
v___y_2022_ = v___y_2030_;
v___y_2023_ = v___y_2031_;
v___y_2024_ = v___y_2032_;
v___y_2025_ = v___y_2033_;
v___y_2026_ = v___y_2034_;
v___y_2027_ = v___x_2036_;
goto v___jp_2021_;
}
else
{
v___y_2022_ = v___y_2030_;
v___y_2023_ = v___y_2031_;
v___y_2024_ = v___y_2032_;
v___y_2025_ = v___y_2033_;
v___y_2026_ = v___y_2034_;
v___y_2027_ = v___x_2035_;
goto v___jp_2021_;
}
}
v___jp_2037_:
{
if (v___y_2042_ == 0)
{
uint8_t v___x_2043_; 
v___x_2043_ = l_Lean_Expr_Data_hasFVar(v___y_2039_);
v___y_2030_ = v___y_2038_;
v___y_2031_ = v___y_2039_;
v___y_2032_ = v___y_2040_;
v___y_2033_ = v___y_2041_;
v___y_2034_ = v___x_2043_;
goto v___jp_2029_;
}
else
{
v___y_2030_ = v___y_2038_;
v___y_2031_ = v___y_2039_;
v___y_2032_ = v___y_2040_;
v___y_2033_ = v___y_2041_;
v___y_2034_ = v___y_2042_;
goto v___jp_2029_;
}
}
v___jp_2044_:
{
uint8_t v___x_2049_; 
v___x_2049_ = l_Lean_Expr_Data_hasFVar(v___x_1989_);
if (v___x_2049_ == 0)
{
uint8_t v___x_2050_; 
v___x_2050_ = l_Lean_Expr_Data_hasFVar(v___x_1992_);
v___y_2038_ = v___y_2045_;
v___y_2039_ = v___y_2046_;
v___y_2040_ = v___y_2047_;
v___y_2041_ = v___y_2048_;
v___y_2042_ = v___x_2050_;
goto v___jp_2037_;
}
else
{
v___y_2038_ = v___y_2045_;
v___y_2039_ = v___y_2046_;
v___y_2040_ = v___y_2047_;
v___y_2041_ = v___y_2048_;
v___y_2042_ = v___x_2049_;
goto v___jp_2037_;
}
}
v___jp_2051_:
{
uint32_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2057_ = l_Lean_Expr_Data_looseBVarRange(v___y_2054_);
v___x_2058_ = lean_uint32_to_nat(v___x_2057_);
v___x_2059_ = lean_nat_sub(v___x_2058_, v___y_2053_);
lean_dec(v___x_2058_);
v___x_2060_ = lean_nat_dec_le(v___y_2056_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_dec(v___x_2059_);
v___y_2045_ = v___y_2052_;
v___y_2046_ = v___y_2054_;
v___y_2047_ = v___y_2055_;
v___y_2048_ = v___y_2056_;
goto v___jp_2044_;
}
else
{
lean_dec(v___y_2056_);
v___y_2045_ = v___y_2052_;
v___y_2046_ = v___y_2054_;
v___y_2047_ = v___y_2055_;
v___y_2048_ = v___x_2059_;
goto v___jp_2044_;
}
}
v___jp_2061_:
{
lean_object* v___x_2064_; uint32_t v___x_2065_; uint32_t v___x_2066_; uint64_t v___x_2067_; uint64_t v___x_2068_; uint64_t v___x_2069_; uint64_t v___x_2070_; uint64_t v___x_2071_; uint64_t v___x_2072_; uint64_t v___x_2073_; uint32_t v___x_2074_; lean_object* v___x_2075_; uint32_t v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2064_ = lean_unsigned_to_nat(1u);
v___x_2065_ = 1;
v___x_2066_ = lean_uint32_add(v___y_2063_, v___x_2065_);
v___x_2067_ = lean_uint32_to_uint64(v___x_2066_);
v___x_2068_ = l_Lean_Expr_Data_hash(v___x_1989_);
v___x_2069_ = l_Lean_Expr_Data_hash(v___x_1992_);
v___x_2070_ = l_Lean_Expr_Data_hash(v___y_2062_);
v___x_2071_ = lean_uint64_mix_hash(v___x_2069_, v___x_2070_);
v___x_2072_ = lean_uint64_mix_hash(v___x_2068_, v___x_2071_);
v___x_2073_ = lean_uint64_mix_hash(v___x_2067_, v___x_2072_);
v___x_2074_ = l_Lean_Expr_Data_looseBVarRange(v___x_1989_);
v___x_2075_ = lean_uint32_to_nat(v___x_2074_);
v___x_2076_ = l_Lean_Expr_Data_looseBVarRange(v___x_1992_);
v___x_2077_ = lean_uint32_to_nat(v___x_2076_);
v___x_2078_ = lean_nat_dec_le(v___x_2075_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_dec(v___x_2077_);
v___y_2052_ = v___x_2073_;
v___y_2053_ = v___x_2064_;
v___y_2054_ = v___y_2062_;
v___y_2055_ = v___x_2066_;
v___y_2056_ = v___x_2075_;
goto v___jp_2051_;
}
else
{
lean_dec(v___x_2075_);
v___y_2052_ = v___x_2073_;
v___y_2053_ = v___x_2064_;
v___y_2054_ = v___y_2062_;
v___y_2055_ = v___x_2066_;
v___y_2056_ = v___x_2077_;
goto v___jp_2051_;
}
}
v___jp_2079_:
{
uint64_t v___x_2081_; uint8_t v___x_2082_; uint32_t v___x_2083_; uint8_t v___x_2084_; 
v___x_2081_ = lean_expr_data(v_body_1967_);
v___x_2082_ = l_Lean_Expr_Data_approxDepth(v___x_2081_);
v___x_2083_ = lean_uint8_to_uint32(v___x_2082_);
v___x_2084_ = lean_uint32_dec_le(v___y_2080_, v___x_2083_);
if (v___x_2084_ == 0)
{
v___y_2062_ = v___x_2081_;
v___y_2063_ = v___y_2080_;
goto v___jp_2061_;
}
else
{
v___y_2062_ = v___x_2081_;
v___y_2063_ = v___x_2083_;
goto v___jp_2061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* v_declName_2088_, lean_object* v_type_2089_, lean_object* v_value_2090_, lean_object* v_body_2091_, lean_object* v_nondep_2092_){
_start:
{
uint8_t v_nondep_boxed_2093_; lean_object* v_res_2094_; 
v_nondep_boxed_2093_ = lean_unbox(v_nondep_2092_);
v_res_2094_ = l_Lean_Expr_letE___override(v_declName_2088_, v_type_2089_, v_value_2090_, v_body_2091_, v_nondep_boxed_2093_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* v_a_2095_){
_start:
{
uint64_t v___x_2096_; uint64_t v___x_2097_; uint64_t v___x_2098_; lean_object* v___x_2099_; uint32_t v___x_2100_; uint8_t v___x_2101_; uint64_t v___x_2102_; lean_object* v___x_2103_; 
v___x_2096_ = 3ULL;
v___x_2097_ = l_Lean_Literal_hash(v_a_2095_);
v___x_2098_ = lean_uint64_mix_hash(v___x_2096_, v___x_2097_);
v___x_2099_ = lean_unsigned_to_nat(0u);
v___x_2100_ = 0;
v___x_2101_ = 0;
v___x_2102_ = lean_expr_mk_data(v___x_2098_, v___x_2099_, v___x_2100_, v___x_2101_, v___x_2101_, v___x_2101_, v___x_2101_);
v___x_2103_ = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(v___x_2103_, 0, v_a_2095_);
lean_ctor_set_uint64(v___x_2103_, sizeof(void*)*1, v___x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* v_data_2104_, lean_object* v_expr_2105_){
_start:
{
uint64_t v___x_2106_; uint8_t v___x_2107_; uint32_t v___x_2108_; uint32_t v___x_2109_; uint32_t v___x_2110_; uint64_t v___x_2111_; uint64_t v___x_2112_; uint64_t v___x_2113_; uint32_t v___x_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; uint8_t v___x_2117_; uint8_t v___x_2118_; uint8_t v___x_2119_; uint64_t v___x_2120_; lean_object* v___x_2121_; 
v___x_2106_ = lean_expr_data(v_expr_2105_);
v___x_2107_ = l_Lean_Expr_Data_approxDepth(v___x_2106_);
v___x_2108_ = lean_uint8_to_uint32(v___x_2107_);
v___x_2109_ = 1;
v___x_2110_ = lean_uint32_add(v___x_2108_, v___x_2109_);
v___x_2111_ = lean_uint32_to_uint64(v___x_2110_);
v___x_2112_ = l_Lean_Expr_Data_hash(v___x_2106_);
v___x_2113_ = lean_uint64_mix_hash(v___x_2111_, v___x_2112_);
v___x_2114_ = l_Lean_Expr_Data_looseBVarRange(v___x_2106_);
v___x_2115_ = lean_uint32_to_nat(v___x_2114_);
v___x_2116_ = l_Lean_Expr_Data_hasFVar(v___x_2106_);
v___x_2117_ = l_Lean_Expr_Data_hasExprMVar(v___x_2106_);
v___x_2118_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2106_);
v___x_2119_ = l_Lean_Expr_Data_hasLevelParam(v___x_2106_);
v___x_2120_ = lean_expr_mk_data(v___x_2113_, v___x_2115_, v___x_2110_, v___x_2116_, v___x_2117_, v___x_2118_, v___x_2119_);
v___x_2121_ = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(v___x_2121_, 0, v_data_2104_);
lean_ctor_set(v___x_2121_, 1, v_expr_2105_);
lean_ctor_set_uint64(v___x_2121_, sizeof(void*)*2, v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* v_typeName_2122_, lean_object* v_idx_2123_, lean_object* v_struct_2124_){
_start:
{
uint64_t v___x_2125_; uint8_t v___x_2126_; uint32_t v___x_2127_; uint32_t v___x_2128_; uint32_t v___x_2129_; uint64_t v___x_2130_; uint64_t v___y_2132_; 
v___x_2125_ = lean_expr_data(v_struct_2124_);
v___x_2126_ = l_Lean_Expr_Data_approxDepth(v___x_2125_);
v___x_2127_ = lean_uint8_to_uint32(v___x_2126_);
v___x_2128_ = 1;
v___x_2129_ = lean_uint32_add(v___x_2127_, v___x_2128_);
v___x_2130_ = lean_uint32_to_uint64(v___x_2129_);
if (lean_obj_tag(v_typeName_2122_) == 0)
{
uint64_t v___x_2146_; 
v___x_2146_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
v___y_2132_ = v___x_2146_;
goto v___jp_2131_;
}
else
{
uint64_t v_hash_2147_; 
v_hash_2147_ = lean_ctor_get_uint64(v_typeName_2122_, sizeof(void*)*2);
v___y_2132_ = v_hash_2147_;
goto v___jp_2131_;
}
v___jp_2131_:
{
uint64_t v___x_2133_; uint64_t v___x_2134_; uint64_t v___x_2135_; uint64_t v___x_2136_; uint64_t v___x_2137_; uint32_t v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; uint8_t v___x_2141_; uint8_t v___x_2142_; uint8_t v___x_2143_; uint64_t v___x_2144_; lean_object* v___x_2145_; 
v___x_2133_ = lean_uint64_of_nat(v_idx_2123_);
v___x_2134_ = l_Lean_Expr_Data_hash(v___x_2125_);
v___x_2135_ = lean_uint64_mix_hash(v___x_2133_, v___x_2134_);
v___x_2136_ = lean_uint64_mix_hash(v___y_2132_, v___x_2135_);
v___x_2137_ = lean_uint64_mix_hash(v___x_2130_, v___x_2136_);
v___x_2138_ = l_Lean_Expr_Data_looseBVarRange(v___x_2125_);
v___x_2139_ = lean_uint32_to_nat(v___x_2138_);
v___x_2140_ = l_Lean_Expr_Data_hasFVar(v___x_2125_);
v___x_2141_ = l_Lean_Expr_Data_hasExprMVar(v___x_2125_);
v___x_2142_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2125_);
v___x_2143_ = l_Lean_Expr_Data_hasLevelParam(v___x_2125_);
v___x_2144_ = lean_expr_mk_data(v___x_2137_, v___x_2139_, v___x_2129_, v___x_2140_, v___x_2141_, v___x_2142_, v___x_2143_);
v___x_2145_ = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(v___x_2145_, 0, v_typeName_2122_);
lean_ctor_set(v___x_2145_, 1, v_idx_2123_);
lean_ctor_set(v___x_2145_, 2, v_struct_2124_);
lean_ctor_set_uint64(v___x_2145_, sizeof(void*)*3, v___x_2144_);
return v___x_2145_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__5(lean_object* v_x_2148_){
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
v___x_2152_ = l_Lean_Level_hasMVar(v_head_2150_);
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
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__5___boxed(lean_object* v_x_2154_){
_start:
{
uint8_t v_res_2155_; lean_object* v_r_2156_; 
v_res_2155_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_x_2154_);
lean_dec(v_x_2154_);
v_r_2156_ = lean_box(v_res_2155_);
return v_r_2156_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__6(lean_object* v_x_2157_){
_start:
{
if (lean_obj_tag(v_x_2157_) == 0)
{
uint8_t v___x_2158_; 
v___x_2158_ = 0;
return v___x_2158_;
}
else
{
lean_object* v_head_2159_; lean_object* v_tail_2160_; uint8_t v___x_2161_; 
v_head_2159_ = lean_ctor_get(v_x_2157_, 0);
v_tail_2160_ = lean_ctor_get(v_x_2157_, 1);
v___x_2161_ = l_Lean_Level_hasParam(v_head_2159_);
if (v___x_2161_ == 0)
{
v_x_2157_ = v_tail_2160_;
goto _start;
}
else
{
return v___x_2161_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__6___boxed(lean_object* v_x_2163_){
_start:
{
uint8_t v_res_2164_; lean_object* v_r_2165_; 
v_res_2164_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_x_2163_);
lean_dec(v_x_2163_);
v_r_2165_ = lean_box(v_res_2164_);
return v_r_2165_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t v_x_2166_, lean_object* v_x_2167_){
_start:
{
if (lean_obj_tag(v_x_2167_) == 0)
{
return v_x_2166_;
}
else
{
lean_object* v_head_2168_; lean_object* v_tail_2169_; uint64_t v___x_2170_; uint64_t v___x_2171_; 
v_head_2168_ = lean_ctor_get(v_x_2167_, 0);
v_tail_2169_ = lean_ctor_get(v_x_2167_, 1);
v___x_2170_ = l_Lean_Level_hash(v_head_2168_);
v___x_2171_ = lean_uint64_mix_hash(v_x_2166_, v___x_2170_);
v_x_2166_ = v___x_2171_;
v_x_2167_ = v_tail_2169_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object* v_x_2173_, lean_object* v_x_2174_){
_start:
{
uint64_t v_x_1734__boxed_2175_; uint64_t v_res_2176_; lean_object* v_r_2177_; 
v_x_1734__boxed_2175_ = lean_unbox_uint64(v_x_2173_);
lean_dec_ref(v_x_2173_);
v_res_2176_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_1734__boxed_2175_, v_x_2174_);
lean_dec(v_x_2174_);
v_r_2177_ = lean_box_uint64(v_res_2176_);
return v_r_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* v_declName_2178_, lean_object* v_us_2179_){
_start:
{
uint64_t v___x_2180_; uint64_t v___y_2182_; 
v___x_2180_ = 5ULL;
if (lean_obj_tag(v_declName_2178_) == 0)
{
uint64_t v___x_2194_; 
v___x_2194_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
v___y_2182_ = v___x_2194_;
goto v___jp_2181_;
}
else
{
uint64_t v_hash_2195_; 
v_hash_2195_ = lean_ctor_get_uint64(v_declName_2178_, sizeof(void*)*2);
v___y_2182_ = v_hash_2195_;
goto v___jp_2181_;
}
v___jp_2181_:
{
uint64_t v___x_2183_; uint64_t v___x_2184_; uint64_t v___x_2185_; uint64_t v___x_2186_; lean_object* v___x_2187_; uint32_t v___x_2188_; uint8_t v___x_2189_; uint8_t v___x_2190_; uint8_t v___x_2191_; uint64_t v___x_2192_; lean_object* v___x_2193_; 
v___x_2183_ = 7ULL;
v___x_2184_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v___x_2183_, v_us_2179_);
v___x_2185_ = lean_uint64_mix_hash(v___y_2182_, v___x_2184_);
v___x_2186_ = lean_uint64_mix_hash(v___x_2180_, v___x_2185_);
v___x_2187_ = lean_unsigned_to_nat(0u);
v___x_2188_ = 0;
v___x_2189_ = 0;
v___x_2190_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_us_2179_);
v___x_2191_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_us_2179_);
v___x_2192_ = lean_expr_mk_data(v___x_2186_, v___x_2187_, v___x_2188_, v___x_2189_, v___x_2189_, v___x_2190_, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(v___x_2193_, 0, v_declName_2178_);
lean_ctor_set(v___x_2193_, 1, v_us_2179_);
lean_ctor_set_uint64(v___x_2193_, sizeof(void*)*2, v___x_2192_);
return v___x_2193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = lean_unsigned_to_nat(0u);
v___x_2198_ = l_Lean_instReprLevel_repr(v___y_2196_, v___x_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2199_, lean_object* v_x_2200_, lean_object* v_x_2201_){
_start:
{
if (lean_obj_tag(v_x_2201_) == 0)
{
lean_dec(v_x_2199_);
return v_x_2200_;
}
else
{
lean_object* v_head_2202_; lean_object* v_tail_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2214_; 
v_head_2202_ = lean_ctor_get(v_x_2201_, 0);
v_tail_2203_ = lean_ctor_get(v_x_2201_, 1);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_x_2201_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2205_ = v_x_2201_;
v_isShared_2206_ = v_isSharedCheck_2214_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_tail_2203_);
lean_inc(v_head_2202_);
lean_dec(v_x_2201_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2214_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
lean_inc(v_x_2199_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set_tag(v___x_2205_, 5);
lean_ctor_set(v___x_2205_, 1, v_x_2199_);
lean_ctor_set(v___x_2205_, 0, v_x_2200_);
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_x_2200_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_x_2199_);
v___x_2208_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = lean_unsigned_to_nat(0u);
v___x_2210_ = l_Lean_instReprLevel_repr(v_head_2202_, v___x_2209_);
v___x_2211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2208_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v_x_2200_ = v___x_2211_;
v_x_2201_ = v_tail_2203_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object* v_x_2215_, lean_object* v_x_2216_, lean_object* v_x_2217_){
_start:
{
if (lean_obj_tag(v_x_2217_) == 0)
{
lean_dec(v_x_2215_);
return v_x_2216_;
}
else
{
lean_object* v_head_2218_; lean_object* v_tail_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2230_; 
v_head_2218_ = lean_ctor_get(v_x_2217_, 0);
v_tail_2219_ = lean_ctor_get(v_x_2217_, 1);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_x_2217_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2221_ = v_x_2217_;
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_tail_2219_);
lean_inc(v_head_2218_);
lean_dec(v_x_2217_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
lean_inc(v_x_2215_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set_tag(v___x_2221_, 5);
lean_ctor_set(v___x_2221_, 1, v_x_2215_);
lean_ctor_set(v___x_2221_, 0, v_x_2216_);
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_x_2216_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_x_2215_);
v___x_2224_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = l_Lean_instReprLevel_repr(v_head_2218_, v___x_2225_);
v___x_2227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2224_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___x_2228_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(v_x_2215_, v___x_2227_, v_tail_2219_);
return v___x_2228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object* v_x_2231_, lean_object* v_x_2232_){
_start:
{
if (lean_obj_tag(v_x_2231_) == 0)
{
lean_object* v___x_2233_; 
lean_dec(v_x_2232_);
v___x_2233_ = lean_box(0);
return v___x_2233_;
}
else
{
lean_object* v_tail_2234_; 
v_tail_2234_ = lean_ctor_get(v_x_2231_, 1);
if (lean_obj_tag(v_tail_2234_) == 0)
{
lean_object* v_head_2235_; lean_object* v___x_2236_; 
lean_dec(v_x_2232_);
v_head_2235_ = lean_ctor_get(v_x_2231_, 0);
lean_inc(v_head_2235_);
lean_dec_ref(v_x_2231_);
v___x_2236_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2235_);
return v___x_2236_;
}
else
{
lean_object* v_head_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_inc(v_tail_2234_);
v_head_2237_ = lean_ctor_get(v_x_2231_, 0);
lean_inc(v_head_2237_);
lean_dec_ref(v_x_2231_);
v___x_2238_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2237_);
v___x_2239_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(v_x_2232_, v___x_2238_, v_tail_2234_);
return v___x_2239_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2));
v___x_2252_ = lean_string_length(v___x_2251_);
return v___x_2252_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7);
v___x_2254_ = lean_nat_to_int(v___x_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object* v_a_2259_){
_start:
{
if (lean_obj_tag(v_a_2259_) == 0)
{
lean_object* v___x_2260_; 
v___x_2260_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1));
return v___x_2260_;
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; 
v___x_2261_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5));
v___x_2262_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(v_a_2259_, v___x_2261_);
v___x_2263_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8);
v___x_2264_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9));
v___x_2265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v___x_2262_);
v___x_2266_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10));
v___x_2267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2265_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
v___x_2268_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2263_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v___x_2269_ = 0;
v___x_2270_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set_uint8(v___x_2270_, sizeof(void*)*1, v___x_2269_);
return v___x_2270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object* v_x_2343_, lean_object* v_prec_2344_){
_start:
{
switch(lean_obj_tag(v_x_2343_))
{
case 0:
{
lean_object* v_deBruijnIndex_2345_; lean_object* v___y_2347_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v_deBruijnIndex_2345_ = lean_ctor_get(v_x_2343_, 0);
lean_inc(v_deBruijnIndex_2345_);
lean_dec_ref(v_x_2343_);
v___x_2356_ = lean_unsigned_to_nat(1024u);
v___x_2357_ = lean_nat_dec_le(v___x_2356_, v_prec_2344_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; 
v___x_2358_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2347_ = v___x_2358_;
goto v___jp_2346_;
}
else
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2347_ = v___x_2359_;
goto v___jp_2346_;
}
v___jp_2346_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2348_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__2));
v___x_2349_ = l_Nat_reprFast(v_deBruijnIndex_2345_);
v___x_2350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
v___x_2351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2348_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
lean_inc(v___y_2347_);
v___x_2352_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___y_2347_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = 0;
v___x_2354_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2354_, 0, v___x_2352_);
lean_ctor_set_uint8(v___x_2354_, sizeof(void*)*1, v___x_2353_);
v___x_2355_ = l_Repr_addAppParen(v___x_2354_, v_prec_2344_);
return v___x_2355_;
}
}
case 1:
{
lean_object* v_fvarId_2360_; lean_object* v___y_2362_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v_fvarId_2360_ = lean_ctor_get(v_x_2343_, 0);
lean_inc(v_fvarId_2360_);
lean_dec_ref(v_x_2343_);
v___x_2371_ = lean_unsigned_to_nat(1024u);
v___x_2372_ = lean_nat_dec_le(v___x_2371_, v_prec_2344_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; 
v___x_2373_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2362_ = v___x_2373_;
goto v___jp_2361_;
}
else
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2362_ = v___x_2374_;
goto v___jp_2361_;
}
v___jp_2361_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2363_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__5));
v___x_2364_ = lean_unsigned_to_nat(1024u);
v___x_2365_ = l_Lean_Name_reprPrec(v_fvarId_2360_, v___x_2364_);
v___x_2366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2363_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
lean_inc(v___y_2362_);
v___x_2367_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___y_2362_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = 0;
v___x_2369_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set_uint8(v___x_2369_, sizeof(void*)*1, v___x_2368_);
v___x_2370_ = l_Repr_addAppParen(v___x_2369_, v_prec_2344_);
return v___x_2370_;
}
}
case 2:
{
lean_object* v_mvarId_2375_; lean_object* v___y_2377_; lean_object* v___x_2386_; uint8_t v___x_2387_; 
v_mvarId_2375_ = lean_ctor_get(v_x_2343_, 0);
lean_inc(v_mvarId_2375_);
lean_dec_ref(v_x_2343_);
v___x_2386_ = lean_unsigned_to_nat(1024u);
v___x_2387_ = lean_nat_dec_le(v___x_2386_, v_prec_2344_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2377_ = v___x_2388_;
goto v___jp_2376_;
}
else
{
lean_object* v___x_2389_; 
v___x_2389_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2377_ = v___x_2389_;
goto v___jp_2376_;
}
v___jp_2376_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2378_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__8));
v___x_2379_ = lean_unsigned_to_nat(1024u);
v___x_2380_ = l_Lean_Name_reprPrec(v_mvarId_2375_, v___x_2379_);
v___x_2381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2378_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
lean_inc(v___y_2377_);
v___x_2382_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___y_2377_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = 0;
v___x_2384_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2384_, 0, v___x_2382_);
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*1, v___x_2383_);
v___x_2385_ = l_Repr_addAppParen(v___x_2384_, v_prec_2344_);
return v___x_2385_;
}
}
case 3:
{
lean_object* v_u_2390_; lean_object* v___y_2392_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
v_u_2390_ = lean_ctor_get(v_x_2343_, 0);
lean_inc(v_u_2390_);
lean_dec_ref(v_x_2343_);
v___x_2401_ = lean_unsigned_to_nat(1024u);
v___x_2402_ = lean_nat_dec_le(v___x_2401_, v_prec_2344_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; 
v___x_2403_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2392_ = v___x_2403_;
goto v___jp_2391_;
}
else
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2392_ = v___x_2404_;
goto v___jp_2391_;
}
v___jp_2391_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2393_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__11));
v___x_2394_ = lean_unsigned_to_nat(1024u);
v___x_2395_ = l_Lean_instReprLevel_repr(v_u_2390_, v___x_2394_);
v___x_2396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2393_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
lean_inc(v___y_2392_);
v___x_2397_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___y_2392_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
v___x_2398_ = 0;
v___x_2399_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set_uint8(v___x_2399_, sizeof(void*)*1, v___x_2398_);
v___x_2400_ = l_Repr_addAppParen(v___x_2399_, v_prec_2344_);
return v___x_2400_;
}
}
case 4:
{
lean_object* v_declName_2405_; lean_object* v_us_2406_; lean_object* v___y_2408_; lean_object* v___x_2421_; uint8_t v___x_2422_; 
v_declName_2405_ = lean_ctor_get(v_x_2343_, 0);
lean_inc(v_declName_2405_);
v_us_2406_ = lean_ctor_get(v_x_2343_, 1);
lean_inc(v_us_2406_);
lean_dec_ref(v_x_2343_);
v___x_2421_ = lean_unsigned_to_nat(1024u);
v___x_2422_ = lean_nat_dec_le(v___x_2421_, v_prec_2344_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; 
v___x_2423_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2408_ = v___x_2423_;
goto v___jp_2407_;
}
else
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2408_ = v___x_2424_;
goto v___jp_2407_;
}
v___jp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2409_ = lean_box(1);
v___x_2410_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__14));
v___x_2411_ = lean_unsigned_to_nat(1024u);
v___x_2412_ = l_Lean_Name_reprPrec(v_declName_2405_, v___x_2411_);
v___x_2413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2410_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
lean_ctor_set(v___x_2414_, 1, v___x_2409_);
v___x_2415_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_us_2406_);
v___x_2416_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
lean_inc(v___y_2408_);
v___x_2417_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___y_2408_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = 0;
v___x_2419_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2419_, 0, v___x_2417_);
lean_ctor_set_uint8(v___x_2419_, sizeof(void*)*1, v___x_2418_);
v___x_2420_ = l_Repr_addAppParen(v___x_2419_, v_prec_2344_);
return v___x_2420_;
}
}
case 5:
{
lean_object* v_fn_2425_; lean_object* v_arg_2426_; lean_object* v___x_2427_; lean_object* v___y_2429_; uint8_t v___x_2441_; 
v_fn_2425_ = lean_ctor_get(v_x_2343_, 0);
lean_inc_ref(v_fn_2425_);
v_arg_2426_ = lean_ctor_get(v_x_2343_, 1);
lean_inc_ref(v_arg_2426_);
lean_dec_ref(v_x_2343_);
v___x_2427_ = lean_unsigned_to_nat(1024u);
v___x_2441_ = lean_nat_dec_le(v___x_2427_, v_prec_2344_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2429_ = v___x_2442_;
goto v___jp_2428_;
}
else
{
lean_object* v___x_2443_; 
v___x_2443_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2429_ = v___x_2443_;
goto v___jp_2428_;
}
v___jp_2428_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2430_ = lean_box(1);
v___x_2431_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__17));
v___x_2432_ = l_Lean_instReprExpr_repr(v_fn_2425_, v___x_2427_);
v___x_2433_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2431_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
lean_ctor_set(v___x_2434_, 1, v___x_2430_);
v___x_2435_ = l_Lean_instReprExpr_repr(v_arg_2426_, v___x_2427_);
v___x_2436_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
lean_inc(v___y_2429_);
v___x_2437_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___y_2429_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = 0;
v___x_2439_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
lean_ctor_set_uint8(v___x_2439_, sizeof(void*)*1, v___x_2438_);
v___x_2440_ = l_Repr_addAppParen(v___x_2439_, v_prec_2344_);
return v___x_2440_;
}
}
case 6:
{
lean_object* v_binderName_2444_; lean_object* v_binderType_2445_; lean_object* v_body_2446_; uint8_t v_binderInfo_2447_; lean_object* v___x_2448_; lean_object* v___y_2450_; uint8_t v___x_2468_; 
v_binderName_2444_ = lean_ctor_get(v_x_2343_, 0);
lean_inc(v_binderName_2444_);
v_binderType_2445_ = lean_ctor_get(v_x_2343_, 1);
lean_inc_ref(v_binderType_2445_);
v_body_2446_ = lean_ctor_get(v_x_2343_, 2);
lean_inc_ref(v_body_2446_);
v_binderInfo_2447_ = lean_ctor_get_uint8(v_x_2343_, sizeof(void*)*3 + 8);
lean_dec_ref(v_x_2343_);
v___x_2448_ = lean_unsigned_to_nat(1024u);
v___x_2468_ = lean_nat_dec_le(v___x_2448_, v_prec_2344_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2450_ = v___x_2469_;
goto v___jp_2449_;
}
else
{
lean_object* v___x_2470_; 
v___x_2470_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2450_ = v___x_2470_;
goto v___jp_2449_;
}
v___jp_2449_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2451_ = lean_box(1);
v___x_2452_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__20));
v___x_2453_ = l_Lean_Name_reprPrec(v_binderName_2444_, v___x_2448_);
v___x_2454_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
lean_ctor_set(v___x_2455_, 1, v___x_2451_);
v___x_2456_ = l_Lean_instReprExpr_repr(v_binderType_2445_, v___x_2448_);
v___x_2457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2455_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
lean_ctor_set(v___x_2458_, 1, v___x_2451_);
v___x_2459_ = l_Lean_instReprExpr_repr(v_body_2446_, v___x_2448_);
v___x_2460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
lean_ctor_set(v___x_2461_, 1, v___x_2451_);
v___x_2462_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2447_, v___x_2448_);
v___x_2463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
lean_inc(v___y_2450_);
v___x_2464_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___y_2450_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = 0;
v___x_2466_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set_uint8(v___x_2466_, sizeof(void*)*1, v___x_2465_);
v___x_2467_ = l_Repr_addAppParen(v___x_2466_, v_prec_2344_);
return v___x_2467_;
}
}
case 7:
{
lean_object* v_binderName_2471_; lean_object* v_binderType_2472_; lean_object* v_body_2473_; uint8_t v_binderInfo_2474_; lean_object* v___x_2475_; lean_object* v___y_2477_; uint8_t v___x_2495_; 
v_binderName_2471_ = lean_ctor_get(v_x_2343_, 0);
lean_inc(v_binderName_2471_);
v_binderType_2472_ = lean_ctor_get(v_x_2343_, 1);
lean_inc_ref(v_binderType_2472_);
v_body_2473_ = lean_ctor_get(v_x_2343_, 2);
lean_inc_ref(v_body_2473_);
v_binderInfo_2474_ = lean_ctor_get_uint8(v_x_2343_, sizeof(void*)*3 + 8);
lean_dec_ref(v_x_2343_);
v___x_2475_ = lean_unsigned_to_nat(1024u);
v___x_2495_ = lean_nat_dec_le(v___x_2475_, v_prec_2344_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; 
v___x_2496_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2477_ = v___x_2496_;
goto v___jp_2476_;
}
else
{
lean_object* v___x_2497_; 
v___x_2497_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2477_ = v___x_2497_;
goto v___jp_2476_;
}
v___jp_2476_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2478_ = lean_box(1);
v___x_2479_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__23));
v___x_2480_ = l_Lean_Name_reprPrec(v_binderName_2471_, v___x_2475_);
v___x_2481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
lean_ctor_set(v___x_2482_, 1, v___x_2478_);
v___x_2483_ = l_Lean_instReprExpr_repr(v_binderType_2472_, v___x_2475_);
v___x_2484_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2482_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
lean_ctor_set(v___x_2485_, 1, v___x_2478_);
v___x_2486_ = l_Lean_instReprExpr_repr(v_body_2473_, v___x_2475_);
v___x_2487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
lean_ctor_set(v___x_2488_, 1, v___x_2478_);
v___x_2489_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2474_, v___x_2475_);
v___x_2490_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2488_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
lean_inc(v___y_2477_);
v___x_2491_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___y_2477_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
v___x_2492_ = 0;
v___x_2493_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2493_, 0, v___x_2491_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*1, v___x_2492_);
v___x_2494_ = l_Repr_addAppParen(v___x_2493_, v_prec_2344_);
return v___x_2494_;
}
}
case 8:
{
lean_object* v_declName_2498_; lean_object* v_type_2499_; lean_object* v_value_2500_; lean_object* v_body_2501_; uint8_t v_nondep_2502_; lean_object* v___x_2503_; lean_object* v___y_2505_; uint8_t v___x_2526_; 
v_declName_2498_ = lean_ctor_get(v_x_2343_, 0);
lean_inc(v_declName_2498_);
v_type_2499_ = lean_ctor_get(v_x_2343_, 1);
lean_inc_ref(v_type_2499_);
v_value_2500_ = lean_ctor_get(v_x_2343_, 2);
lean_inc_ref(v_value_2500_);
v_body_2501_ = lean_ctor_get(v_x_2343_, 3);
lean_inc_ref(v_body_2501_);
v_nondep_2502_ = lean_ctor_get_uint8(v_x_2343_, sizeof(void*)*4 + 8);
lean_dec_ref(v_x_2343_);
v___x_2503_ = lean_unsigned_to_nat(1024u);
v___x_2526_ = lean_nat_dec_le(v___x_2503_, v_prec_2344_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2505_ = v___x_2527_;
goto v___jp_2504_;
}
else
{
lean_object* v___x_2528_; 
v___x_2528_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2505_ = v___x_2528_;
goto v___jp_2504_;
}
v___jp_2504_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2506_ = lean_box(1);
v___x_2507_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__26));
v___x_2508_ = l_Lean_Name_reprPrec(v_declName_2498_, v___x_2503_);
v___x_2509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v___x_2506_);
v___x_2511_ = l_Lean_instReprExpr_repr(v_type_2499_, v___x_2503_);
v___x_2512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
lean_ctor_set(v___x_2513_, 1, v___x_2506_);
v___x_2514_ = l_Lean_instReprExpr_repr(v_value_2500_, v___x_2503_);
v___x_2515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v___x_2516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
lean_ctor_set(v___x_2516_, 1, v___x_2506_);
v___x_2517_ = l_Lean_instReprExpr_repr(v_body_2501_, v___x_2503_);
v___x_2518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
lean_ctor_set(v___x_2519_, 1, v___x_2506_);
v___x_2520_ = l_Bool_repr___redArg(v_nondep_2502_);
v___x_2521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
lean_inc(v___y_2505_);
v___x_2522_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___y_2505_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = 0;
v___x_2524_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2524_, 0, v___x_2522_);
lean_ctor_set_uint8(v___x_2524_, sizeof(void*)*1, v___x_2523_);
v___x_2525_ = l_Repr_addAppParen(v___x_2524_, v_prec_2344_);
return v___x_2525_;
}
}
case 9:
{
lean_object* v_a_2529_; lean_object* v___y_2531_; lean_object* v___x_2540_; uint8_t v___x_2541_; 
v_a_2529_ = lean_ctor_get(v_x_2343_, 0);
lean_inc_ref(v_a_2529_);
lean_dec_ref(v_x_2343_);
v___x_2540_ = lean_unsigned_to_nat(1024u);
v___x_2541_ = lean_nat_dec_le(v___x_2540_, v_prec_2344_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2531_ = v___x_2542_;
goto v___jp_2530_;
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2531_ = v___x_2543_;
goto v___jp_2530_;
}
v___jp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2532_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__29));
v___x_2533_ = lean_unsigned_to_nat(1024u);
v___x_2534_ = l_Lean_instReprLiteral_repr(v_a_2529_, v___x_2533_);
v___x_2535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2532_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
lean_inc(v___y_2531_);
v___x_2536_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___y_2531_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = 0;
v___x_2538_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2538_, 0, v___x_2536_);
lean_ctor_set_uint8(v___x_2538_, sizeof(void*)*1, v___x_2537_);
v___x_2539_ = l_Repr_addAppParen(v___x_2538_, v_prec_2344_);
return v___x_2539_;
}
}
case 10:
{
lean_object* v_data_2544_; lean_object* v_expr_2545_; lean_object* v___x_2546_; lean_object* v___y_2548_; uint8_t v___x_2560_; 
v_data_2544_ = lean_ctor_get(v_x_2343_, 0);
lean_inc(v_data_2544_);
v_expr_2545_ = lean_ctor_get(v_x_2343_, 1);
lean_inc_ref(v_expr_2545_);
lean_dec_ref(v_x_2343_);
v___x_2546_ = lean_unsigned_to_nat(1024u);
v___x_2560_ = lean_nat_dec_le(v___x_2546_, v_prec_2344_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2548_ = v___x_2561_;
goto v___jp_2547_;
}
else
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2548_ = v___x_2562_;
goto v___jp_2547_;
}
v___jp_2547_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2549_ = lean_box(1);
v___x_2550_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__32));
v___x_2551_ = l_Lean_instReprKVMap_repr___redArg(v_data_2544_);
v___x_2552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
lean_ctor_set(v___x_2553_, 1, v___x_2549_);
v___x_2554_ = l_Lean_instReprExpr_repr(v_expr_2545_, v___x_2546_);
v___x_2555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
lean_inc(v___y_2548_);
v___x_2556_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___y_2548_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = 0;
v___x_2558_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2558_, 0, v___x_2556_);
lean_ctor_set_uint8(v___x_2558_, sizeof(void*)*1, v___x_2557_);
v___x_2559_ = l_Repr_addAppParen(v___x_2558_, v_prec_2344_);
return v___x_2559_;
}
}
default: 
{
lean_object* v_typeName_2563_; lean_object* v_idx_2564_; lean_object* v_struct_2565_; lean_object* v___x_2566_; lean_object* v___y_2568_; uint8_t v___x_2584_; 
v_typeName_2563_ = lean_ctor_get(v_x_2343_, 0);
lean_inc(v_typeName_2563_);
v_idx_2564_ = lean_ctor_get(v_x_2343_, 1);
lean_inc(v_idx_2564_);
v_struct_2565_ = lean_ctor_get(v_x_2343_, 2);
lean_inc_ref(v_struct_2565_);
lean_dec_ref(v_x_2343_);
v___x_2566_ = lean_unsigned_to_nat(1024u);
v___x_2584_ = lean_nat_dec_le(v___x_2566_, v_prec_2344_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; 
v___x_2585_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2568_ = v___x_2585_;
goto v___jp_2567_;
}
else
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2568_ = v___x_2586_;
goto v___jp_2567_;
}
v___jp_2567_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2569_ = lean_box(1);
v___x_2570_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__35));
v___x_2571_ = l_Lean_Name_reprPrec(v_typeName_2563_, v___x_2566_);
v___x_2572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2570_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
v___x_2573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
lean_ctor_set(v___x_2573_, 1, v___x_2569_);
v___x_2574_ = l_Nat_reprFast(v_idx_2564_);
v___x_2575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
v___x_2576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2573_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v___x_2569_);
v___x_2578_ = l_Lean_instReprExpr_repr(v_struct_2565_, v___x_2566_);
v___x_2579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
lean_inc(v___y_2568_);
v___x_2580_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___y_2568_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = 0;
v___x_2582_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set_uint8(v___x_2582_, sizeof(void*)*1, v___x_2581_);
v___x_2583_ = l_Repr_addAppParen(v___x_2582_, v_prec_2344_);
return v___x_2583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object* v_x_2587_, lean_object* v_prec_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_instReprExpr_repr(v_x_2587_, v_prec_2588_);
lean_dec(v_prec_2588_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object* v_a_2590_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = lean_nat_to_int(v_a_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object* v_a_2592_, lean_object* v_n_2593_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_a_2592_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object* v_a_2595_, lean_object* v_n_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0(v_a_2595_, v_n_2596_);
lean_dec(v_n_2596_);
return v_res_2597_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__2(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = lean_box(0);
v___x_2604_ = ((lean_object*)(l_Lean_instInhabitedExpr___closed__1));
v___x_2605_ = l_Lean_Expr_const___override(v___x_2604_, v___x_2603_);
return v___x_2605_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr(void){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* v_x_2619_){
_start:
{
switch(lean_obj_tag(v_x_2619_))
{
case 0:
{
lean_object* v___x_2620_; 
v___x_2620_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__0));
return v___x_2620_;
}
case 1:
{
lean_object* v___x_2621_; 
v___x_2621_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__1));
return v___x_2621_;
}
case 2:
{
lean_object* v___x_2622_; 
v___x_2622_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__2));
return v___x_2622_;
}
case 3:
{
lean_object* v___x_2623_; 
v___x_2623_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__3));
return v___x_2623_;
}
case 4:
{
lean_object* v___x_2624_; 
v___x_2624_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__4));
return v___x_2624_;
}
case 5:
{
lean_object* v___x_2625_; 
v___x_2625_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__5));
return v___x_2625_;
}
case 6:
{
lean_object* v___x_2626_; 
v___x_2626_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__6));
return v___x_2626_;
}
case 7:
{
lean_object* v___x_2627_; 
v___x_2627_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__7));
return v___x_2627_;
}
case 8:
{
lean_object* v___x_2628_; 
v___x_2628_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__8));
return v___x_2628_;
}
case 9:
{
lean_object* v___x_2629_; 
v___x_2629_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__9));
return v___x_2629_;
}
case 10:
{
lean_object* v___x_2630_; 
v___x_2630_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__10));
return v___x_2630_;
}
default: 
{
lean_object* v___x_2631_; 
v___x_2631_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__11));
return v___x_2631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* v_x_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_Expr_ctorName(v_x_2632_);
lean_dec_ref(v_x_2632_);
return v_res_2633_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object* v_e_2634_){
_start:
{
uint64_t v___x_2635_; uint64_t v___x_2636_; 
v___x_2635_ = lean_expr_data(v_e_2634_);
v___x_2636_ = l_Lean_Expr_Data_hash(v___x_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* v_e_2637_){
_start:
{
uint64_t v_res_2638_; lean_object* v_r_2639_; 
v_res_2638_ = l_Lean_Expr_hash(v_e_2637_);
lean_dec_ref(v_e_2637_);
v_r_2639_ = lean_box_uint64(v_res_2638_);
return v_r_2639_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object* v_e_2642_){
_start:
{
uint64_t v___x_2643_; uint8_t v___x_2644_; 
v___x_2643_ = lean_expr_data(v_e_2642_);
v___x_2644_ = l_Lean_Expr_Data_hasFVar(v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* v_e_2645_){
_start:
{
uint8_t v_res_2646_; lean_object* v_r_2647_; 
v_res_2646_ = l_Lean_Expr_hasFVar(v_e_2645_);
lean_dec_ref(v_e_2645_);
v_r_2647_ = lean_box(v_res_2646_);
return v_r_2647_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object* v_e_2648_){
_start:
{
uint64_t v___x_2649_; uint8_t v___x_2650_; 
v___x_2649_ = lean_expr_data(v_e_2648_);
v___x_2650_ = l_Lean_Expr_Data_hasExprMVar(v___x_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* v_e_2651_){
_start:
{
uint8_t v_res_2652_; lean_object* v_r_2653_; 
v_res_2652_ = l_Lean_Expr_hasExprMVar(v_e_2651_);
lean_dec_ref(v_e_2651_);
v_r_2653_ = lean_box(v_res_2652_);
return v_r_2653_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object* v_e_2654_){
_start:
{
uint64_t v___x_2655_; uint8_t v___x_2656_; 
v___x_2655_ = lean_expr_data(v_e_2654_);
v___x_2656_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* v_e_2657_){
_start:
{
uint8_t v_res_2658_; lean_object* v_r_2659_; 
v_res_2658_ = l_Lean_Expr_hasLevelMVar(v_e_2657_);
lean_dec_ref(v_e_2657_);
v_r_2659_ = lean_box(v_res_2658_);
return v_r_2659_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object* v_e_2660_){
_start:
{
uint64_t v_d_2661_; uint8_t v___x_2662_; 
v_d_2661_ = lean_expr_data(v_e_2660_);
v___x_2662_ = l_Lean_Expr_Data_hasExprMVar(v_d_2661_);
if (v___x_2662_ == 0)
{
uint8_t v___x_2663_; 
v___x_2663_ = l_Lean_Expr_Data_hasLevelMVar(v_d_2661_);
return v___x_2663_;
}
else
{
return v___x_2662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* v_e_2664_){
_start:
{
uint8_t v_res_2665_; lean_object* v_r_2666_; 
v_res_2665_ = l_Lean_Expr_hasMVar(v_e_2664_);
lean_dec_ref(v_e_2664_);
v_r_2666_ = lean_box(v_res_2665_);
return v_r_2666_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object* v_e_2667_){
_start:
{
uint64_t v___x_2668_; uint8_t v___x_2669_; 
v___x_2668_ = lean_expr_data(v_e_2667_);
v___x_2669_ = l_Lean_Expr_Data_hasLevelParam(v___x_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* v_e_2670_){
_start:
{
uint8_t v_res_2671_; lean_object* v_r_2672_; 
v_res_2671_ = l_Lean_Expr_hasLevelParam(v_e_2670_);
lean_dec_ref(v_e_2670_);
v_r_2672_ = lean_box(v_res_2671_);
return v_r_2672_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object* v_e_2673_){
_start:
{
uint64_t v___x_2674_; uint8_t v___x_2675_; uint32_t v___x_2676_; 
v___x_2674_ = lean_expr_data(v_e_2673_);
v___x_2675_ = l_Lean_Expr_Data_approxDepth(v___x_2674_);
v___x_2676_ = lean_uint8_to_uint32(v___x_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* v_e_2677_){
_start:
{
uint32_t v_res_2678_; lean_object* v_r_2679_; 
v_res_2678_ = l_Lean_Expr_approxDepth(v_e_2677_);
lean_dec_ref(v_e_2677_);
v_r_2679_ = lean_box_uint32(v_res_2678_);
return v_r_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* v_e_2680_){
_start:
{
uint64_t v___x_2681_; uint32_t v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = lean_expr_data(v_e_2680_);
v___x_2682_ = l_Lean_Expr_Data_looseBVarRange(v___x_2681_);
v___x_2683_ = lean_uint32_to_nat(v___x_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* v_e_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_Expr_looseBVarRange(v_e_2684_);
lean_dec_ref(v_e_2684_);
return v_res_2685_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object* v_e_2686_){
_start:
{
switch(lean_obj_tag(v_e_2686_))
{
case 7:
{
uint8_t v_binderInfo_2687_; 
v_binderInfo_2687_ = lean_ctor_get_uint8(v_e_2686_, sizeof(void*)*3 + 8);
return v_binderInfo_2687_;
}
case 6:
{
uint8_t v_binderInfo_2688_; 
v_binderInfo_2688_ = lean_ctor_get_uint8(v_e_2686_, sizeof(void*)*3 + 8);
return v_binderInfo_2688_;
}
default: 
{
uint8_t v___x_2689_; 
v___x_2689_ = 0;
return v___x_2689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* v_e_2690_){
_start:
{
uint8_t v_res_2691_; lean_object* v_r_2692_; 
v_res_2691_ = l_Lean_Expr_binderInfo(v_e_2690_);
lean_dec_ref(v_e_2690_);
v_r_2692_ = lean_box(v_res_2691_);
return v_r_2692_;
}
}
LEAN_EXPORT uint64_t lean_expr_hash(lean_object* v_a_2693_){
_start:
{
uint64_t v___x_2694_; 
v___x_2694_ = l_Lean_Expr_hash(v_a_2693_);
lean_dec_ref(v_a_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* v_a_2695_){
_start:
{
uint64_t v_res_2696_; lean_object* v_r_2697_; 
v_res_2696_ = lean_expr_hash(v_a_2695_);
v_r_2697_ = lean_box_uint64(v_res_2696_);
return v_r_2697_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object* v_e_2698_){
_start:
{
uint8_t v___x_2699_; 
v___x_2699_ = l_Lean_Expr_hasFVar(v_e_2698_);
lean_dec_ref(v_e_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* v_e_2700_){
_start:
{
uint8_t v_res_2701_; lean_object* v_r_2702_; 
v_res_2701_ = lean_expr_has_fvar(v_e_2700_);
v_r_2702_ = lean_box(v_res_2701_);
return v_r_2702_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object* v_e_2703_){
_start:
{
uint8_t v___x_2704_; 
v___x_2704_ = l_Lean_Expr_hasExprMVar(v_e_2703_);
lean_dec_ref(v_e_2703_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* v_e_2705_){
_start:
{
uint8_t v_res_2706_; lean_object* v_r_2707_; 
v_res_2706_ = lean_expr_has_expr_mvar(v_e_2705_);
v_r_2707_ = lean_box(v_res_2706_);
return v_r_2707_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object* v_e_2708_){
_start:
{
uint8_t v___x_2709_; 
v___x_2709_ = l_Lean_Expr_hasLevelMVar(v_e_2708_);
lean_dec_ref(v_e_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* v_e_2710_){
_start:
{
uint8_t v_res_2711_; lean_object* v_r_2712_; 
v_res_2711_ = lean_expr_has_level_mvar(v_e_2710_);
v_r_2712_ = lean_box(v_res_2711_);
return v_r_2712_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_mvar(lean_object* v_e_2713_){
_start:
{
uint8_t v___x_2714_; 
v___x_2714_ = l_Lean_Expr_hasMVar(v_e_2713_);
lean_dec_ref(v_e_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVarEx___boxed(lean_object* v_e_2715_){
_start:
{
uint8_t v_res_2716_; lean_object* v_r_2717_; 
v_res_2716_ = lean_expr_has_mvar(v_e_2715_);
v_r_2717_ = lean_box(v_res_2716_);
return v_r_2717_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* v_e_2718_){
_start:
{
uint8_t v___x_2719_; 
v___x_2719_ = l_Lean_Expr_hasLevelParam(v_e_2718_);
lean_dec_ref(v_e_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* v_e_2720_){
_start:
{
uint8_t v_res_2721_; lean_object* v_r_2722_; 
v_res_2721_ = lean_expr_has_level_param(v_e_2720_);
v_r_2722_ = lean_box(v_res_2721_);
return v_r_2722_;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* v_e_2723_){
_start:
{
uint64_t v___x_2724_; uint32_t v___x_2725_; 
v___x_2724_ = lean_expr_data(v_e_2723_);
lean_dec_ref(v_e_2723_);
v___x_2725_ = l_Lean_Expr_Data_looseBVarRange(v___x_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* v_e_2726_){
_start:
{
uint32_t v_res_2727_; lean_object* v_r_2728_; 
v_res_2727_ = lean_expr_loose_bvar_range(v_e_2726_);
v_r_2728_ = lean_box_uint32(v_res_2727_);
return v_r_2728_;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* v_e_2729_){
_start:
{
uint8_t v___x_2730_; 
v___x_2730_ = l_Lean_Expr_binderInfo(v_e_2729_);
lean_dec_ref(v_e_2729_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* v_e_2731_){
_start:
{
uint8_t v_res_2732_; lean_object* v_r_2733_; 
v_res_2732_ = lean_expr_binder_info(v_e_2731_);
v_r_2733_ = lean_box(v_res_2732_);
return v_r_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* v_declName_2734_, lean_object* v_us_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_Expr_const___override(v_declName_2734_, v_us_2735_);
return v___x_2736_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2(void){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2740_ = lean_box(0);
v___x_2741_ = ((lean_object*)(l_Lean_Literal_type___closed__1));
v___x_2742_ = l_Lean_Expr_const___override(v___x_2741_, v___x_2740_);
return v___x_2742_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5(void){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2746_ = lean_box(0);
v___x_2747_ = ((lean_object*)(l_Lean_Literal_type___closed__4));
v___x_2748_ = l_Lean_Expr_const___override(v___x_2747_, v___x_2746_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* v_x_2749_){
_start:
{
if (lean_obj_tag(v_x_2749_) == 0)
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_2750_;
}
else
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_obj_once(&l_Lean_Literal_type___closed__5, &l_Lean_Literal_type___closed__5_once, _init_l_Lean_Literal_type___closed__5);
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* v_x_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_Literal_type(v_x_2752_);
lean_dec_ref(v_x_2752_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* v_a_2754_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_Literal_type(v_a_2754_);
lean_dec_ref(v_a_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* v_idx_2756_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Lean_Expr_bvar___override(v_idx_2756_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* v_u_2758_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_Expr_sort___override(v_u_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* v_fvarId_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_Expr_fvar___override(v_fvarId_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* v_mvarId_2762_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_Expr_mvar___override(v_mvarId_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* v_m_2764_, lean_object* v_e_2765_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_Expr_mdata___override(v_m_2764_, v_e_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* v_structName_2767_, lean_object* v_idx_2768_, lean_object* v_struct_2769_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l_Lean_Expr_proj___override(v_structName_2767_, v_idx_2768_, v_struct_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* v_f_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_Expr_app___override(v_f_2771_, v_a_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* v_x_2774_, uint8_t v_bi_2775_, lean_object* v_t_2776_, lean_object* v_b_2777_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_Expr_lam___override(v_x_2774_, v_t_2776_, v_b_2777_, v_bi_2775_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* v_x_2779_, lean_object* v_bi_2780_, lean_object* v_t_2781_, lean_object* v_b_2782_){
_start:
{
uint8_t v_bi_boxed_2783_; lean_object* v_res_2784_; 
v_bi_boxed_2783_ = lean_unbox(v_bi_2780_);
v_res_2784_ = l_Lean_mkLambda(v_x_2779_, v_bi_boxed_2783_, v_t_2781_, v_b_2782_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* v_x_2785_, uint8_t v_bi_2786_, lean_object* v_t_2787_, lean_object* v_b_2788_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Lean_Expr_forallE___override(v_x_2785_, v_t_2787_, v_b_2788_, v_bi_2786_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* v_x_2790_, lean_object* v_bi_2791_, lean_object* v_t_2792_, lean_object* v_b_2793_){
_start:
{
uint8_t v_bi_boxed_2794_; lean_object* v_res_2795_; 
v_bi_boxed_2794_ = lean_unbox(v_bi_2791_);
v_res_2795_ = l_Lean_mkForall(v_x_2790_, v_bi_boxed_2794_, v_t_2792_, v_b_2793_);
return v_res_2795_;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__2(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2799_ = lean_box(0);
v___x_2800_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2801_ = l_Lean_Expr_const___override(v___x_2800_, v___x_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* v_type_2802_){
_start:
{
lean_object* v___x_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2803_ = lean_box(0);
v___x_2804_ = 0;
v___x_2805_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__2, &l_Lean_mkSimpleThunkType___closed__2_once, _init_l_Lean_mkSimpleThunkType___closed__2);
v___x_2806_ = l_Lean_Expr_forallE___override(v___x_2803_, v___x_2805_, v_type_2802_, v___x_2804_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* v_type_2810_){
_start:
{
lean_object* v___x_2811_; uint8_t v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2811_ = ((lean_object*)(l_Lean_mkSimpleThunk___closed__1));
v___x_2812_ = 0;
v___x_2813_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__2, &l_Lean_mkSimpleThunkType___closed__2_once, _init_l_Lean_mkSimpleThunkType___closed__2);
v___x_2814_ = l_Lean_Expr_lam___override(v___x_2811_, v___x_2813_, v_type_2810_, v___x_2812_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* v_x_2815_, lean_object* v_t_2816_, lean_object* v_v_2817_, lean_object* v_b_2818_, uint8_t v_nondep_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_Expr_letE___override(v_x_2815_, v_t_2816_, v_v_2817_, v_b_2818_, v_nondep_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* v_x_2821_, lean_object* v_t_2822_, lean_object* v_v_2823_, lean_object* v_b_2824_, lean_object* v_nondep_2825_){
_start:
{
uint8_t v_nondep_boxed_2826_; lean_object* v_res_2827_; 
v_nondep_boxed_2826_ = lean_unbox(v_nondep_2825_);
v_res_2827_ = l_Lean_mkLet(v_x_2821_, v_t_2822_, v_v_2823_, v_b_2824_, v_nondep_boxed_2826_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object* v_x_2828_, lean_object* v_t_2829_, lean_object* v_v_2830_, lean_object* v_b_2831_){
_start:
{
uint8_t v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = 1;
v___x_2833_ = l_Lean_Expr_letE___override(v_x_2828_, v_t_2829_, v_v_2830_, v_b_2831_, v___x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* v_f_2834_, lean_object* v_a_2835_, lean_object* v_b_2836_){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = l_Lean_Expr_app___override(v_f_2834_, v_a_2835_);
v___x_2838_ = l_Lean_Expr_app___override(v___x_2837_, v_b_2836_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* v_f_2839_, lean_object* v_a_2840_, lean_object* v_b_2841_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_mkAppB(v_f_2839_, v_a_2840_, v_b_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* v_f_2843_, lean_object* v_a_2844_, lean_object* v_b_2845_, lean_object* v_c_2846_){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = l_Lean_mkAppB(v_f_2843_, v_a_2844_, v_b_2845_);
v___x_2848_ = l_Lean_Expr_app___override(v___x_2847_, v_c_2846_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* v_f_2849_, lean_object* v_a_2850_, lean_object* v_b_2851_, lean_object* v_c_2852_, lean_object* v_d_2853_){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = l_Lean_mkAppB(v_f_2849_, v_a_2850_, v_b_2851_);
v___x_2855_ = l_Lean_mkAppB(v___x_2854_, v_c_2852_, v_d_2853_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* v_f_2856_, lean_object* v_a_2857_, lean_object* v_b_2858_, lean_object* v_c_2859_, lean_object* v_d_2860_, lean_object* v_e_2861_){
_start:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2862_ = l_Lean_mkApp4(v_f_2856_, v_a_2857_, v_b_2858_, v_c_2859_, v_d_2860_);
v___x_2863_ = l_Lean_Expr_app___override(v___x_2862_, v_e_2861_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* v_f_2864_, lean_object* v_a_2865_, lean_object* v_b_2866_, lean_object* v_c_2867_, lean_object* v_d_2868_, lean_object* v_e_u2081_2869_, lean_object* v_e_u2082_2870_){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = l_Lean_mkApp4(v_f_2864_, v_a_2865_, v_b_2866_, v_c_2867_, v_d_2868_);
v___x_2872_ = l_Lean_mkAppB(v___x_2871_, v_e_u2081_2869_, v_e_u2082_2870_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* v_f_2873_, lean_object* v_a_2874_, lean_object* v_b_2875_, lean_object* v_c_2876_, lean_object* v_d_2877_, lean_object* v_e_u2081_2878_, lean_object* v_e_u2082_2879_, lean_object* v_e_u2083_2880_){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = l_Lean_mkApp4(v_f_2873_, v_a_2874_, v_b_2875_, v_c_2876_, v_d_2877_);
v___x_2882_ = l_Lean_mkApp3(v___x_2881_, v_e_u2081_2878_, v_e_u2082_2879_, v_e_u2083_2880_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* v_f_2883_, lean_object* v_a_2884_, lean_object* v_b_2885_, lean_object* v_c_2886_, lean_object* v_d_2887_, lean_object* v_e_u2081_2888_, lean_object* v_e_u2082_2889_, lean_object* v_e_u2083_2890_, lean_object* v_e_u2084_2891_){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = l_Lean_mkApp4(v_f_2883_, v_a_2884_, v_b_2885_, v_c_2886_, v_d_2887_);
v___x_2893_ = l_Lean_mkApp4(v___x_2892_, v_e_u2081_2888_, v_e_u2082_2889_, v_e_u2083_2890_, v_e_u2084_2891_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* v_f_2894_, lean_object* v_a_2895_, lean_object* v_b_2896_, lean_object* v_c_2897_, lean_object* v_d_2898_, lean_object* v_e_u2081_2899_, lean_object* v_e_u2082_2900_, lean_object* v_e_u2083_2901_, lean_object* v_e_u2084_2902_, lean_object* v_e_u2085_2903_){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = l_Lean_mkApp4(v_f_2894_, v_a_2895_, v_b_2896_, v_c_2897_, v_d_2898_);
v___x_2905_ = l_Lean_mkApp5(v___x_2904_, v_e_u2081_2899_, v_e_u2082_2900_, v_e_u2083_2901_, v_e_u2084_2902_, v_e_u2085_2903_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* v_f_2906_, lean_object* v_a_2907_, lean_object* v_b_2908_, lean_object* v_c_2909_, lean_object* v_d_2910_, lean_object* v_e_u2081_2911_, lean_object* v_e_u2082_2912_, lean_object* v_e_u2083_2913_, lean_object* v_e_u2084_2914_, lean_object* v_e_u2085_2915_, lean_object* v_e_u2086_2916_){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = l_Lean_mkApp4(v_f_2906_, v_a_2907_, v_b_2908_, v_c_2909_, v_d_2910_);
v___x_2918_ = l_Lean_mkApp6(v___x_2917_, v_e_u2081_2911_, v_e_u2082_2912_, v_e_u2083_2913_, v_e_u2084_2914_, v_e_u2085_2915_, v_e_u2086_2916_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* v_l_2919_){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = l_Lean_Expr_lit___override(v_l_2919_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* v_n_2921_){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v_n_2921_);
v___x_2923_ = l_Lean_Expr_lit___override(v___x_2922_);
return v___x_2923_;
}
}
static lean_object* _init_l_Lean_mkInstOfNatNat___closed__2(void){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2927_ = lean_box(0);
v___x_2928_ = ((lean_object*)(l_Lean_mkInstOfNatNat___closed__1));
v___x_2929_ = l_Lean_Expr_const___override(v___x_2928_, v___x_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object* v_n_2930_){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = lean_obj_once(&l_Lean_mkInstOfNatNat___closed__2, &l_Lean_mkInstOfNatNat___closed__2_once, _init_l_Lean_mkInstOfNatNat___closed__2);
v___x_2932_ = l_Lean_Expr_app___override(v___x_2931_, v_n_2930_);
return v___x_2932_;
}
}
static lean_object* _init_l_Lean_mkNatLitCore___closed__4(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2941_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_2942_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_2943_ = l_Lean_Expr_const___override(v___x_2942_, v___x_2941_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object* v_n_2944_){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2945_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_2946_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
lean_inc_ref(v_n_2944_);
v___x_2947_ = l_Lean_mkInstOfNatNat(v_n_2944_);
v___x_2948_ = l_Lean_mkApp3(v___x_2945_, v___x_2946_, v_n_2944_, v___x_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* v_n_2949_){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = l_Lean_mkRawNatLit(v_n_2949_);
v___x_2951_ = l_Lean_mkNatLitCore(v___x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* v_s_2952_){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2953_, 0, v_s_2952_);
v___x_2954_ = l_Lean_Expr_lit___override(v___x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* v_idx_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_Expr_bvar___override(v_idx_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* v_fvarId_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_Expr_fvar___override(v_fvarId_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object* v_mvarId_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_Expr_mvar___override(v_mvarId_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_2961_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_Expr_sort___override(v_u_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_2963_, lean_object* v_lvls_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_Expr_const___override(v_c_2963_, v_lvls_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_2966_, lean_object* v_a_2967_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_Expr_app___override(v_f_2966_, v_a_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* v_n_2969_, lean_object* v_d_2970_, lean_object* v_b_2971_, uint8_t v_bi_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_Lean_Expr_lam___override(v_n_2969_, v_d_2970_, v_b_2971_, v_bi_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_2974_, lean_object* v_d_2975_, lean_object* v_b_2976_, lean_object* v_bi_2977_){
_start:
{
uint8_t v_bi_boxed_2978_; lean_object* v_res_2979_; 
v_bi_boxed_2978_ = lean_unbox(v_bi_2977_);
v_res_2979_ = lean_expr_mk_lambda(v_n_2974_, v_d_2975_, v_b_2976_, v_bi_boxed_2978_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* v_n_2980_, lean_object* v_d_2981_, lean_object* v_b_2982_, uint8_t v_bi_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_Expr_forallE___override(v_n_2980_, v_d_2981_, v_b_2982_, v_bi_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_2985_, lean_object* v_d_2986_, lean_object* v_b_2987_, lean_object* v_bi_2988_){
_start:
{
uint8_t v_bi_boxed_2989_; lean_object* v_res_2990_; 
v_bi_boxed_2989_ = lean_unbox(v_bi_2988_);
v_res_2990_ = lean_expr_mk_forall(v_n_2985_, v_d_2986_, v_b_2987_, v_bi_boxed_2989_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* v_n_2991_, lean_object* v_t_2992_, lean_object* v_v_2993_, lean_object* v_b_2994_, uint8_t v_nondep_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_Expr_letE___override(v_n_2991_, v_t_2992_, v_v_2993_, v_b_2994_, v_nondep_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_2997_, lean_object* v_t_2998_, lean_object* v_v_2999_, lean_object* v_b_3000_, lean_object* v_nondep_3001_){
_start:
{
uint8_t v_nondep_boxed_3002_; lean_object* v_res_3003_; 
v_nondep_boxed_3002_ = lean_unbox(v_nondep_3001_);
v_res_3003_ = lean_expr_mk_let(v_n_2997_, v_t_2998_, v_v_2999_, v_b_3000_, v_nondep_boxed_3002_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_Expr_lit___override(v_l_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_3006_, lean_object* v_e_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_Expr_mdata___override(v_m_3006_, v_e_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_3009_, lean_object* v_idx_3010_, lean_object* v_struct_3011_){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = l_Lean_Expr_proj___override(v_structName_3009_, v_idx_3010_, v_struct_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_3013_, size_t v_i_3014_, size_t v_stop_3015_, lean_object* v_b_3016_){
_start:
{
uint8_t v___x_3017_; 
v___x_3017_ = lean_usize_dec_eq(v_i_3014_, v_stop_3015_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; lean_object* v___x_3019_; size_t v___x_3020_; size_t v___x_3021_; 
v___x_3018_ = lean_array_uget_borrowed(v_as_3013_, v_i_3014_);
lean_inc(v___x_3018_);
v___x_3019_ = l_Lean_Expr_app___override(v_b_3016_, v___x_3018_);
v___x_3020_ = ((size_t)1ULL);
v___x_3021_ = lean_usize_add(v_i_3014_, v___x_3020_);
v_i_3014_ = v___x_3021_;
v_b_3016_ = v___x_3019_;
goto _start;
}
else
{
return v_b_3016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_3023_, lean_object* v_i_3024_, lean_object* v_stop_3025_, lean_object* v_b_3026_){
_start:
{
size_t v_i_boxed_3027_; size_t v_stop_boxed_3028_; lean_object* v_res_3029_; 
v_i_boxed_3027_ = lean_unbox_usize(v_i_3024_);
lean_dec(v_i_3024_);
v_stop_boxed_3028_ = lean_unbox_usize(v_stop_3025_);
lean_dec(v_stop_3025_);
v_res_3029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_3023_, v_i_boxed_3027_, v_stop_boxed_3028_, v_b_3026_);
lean_dec_ref(v_as_3023_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_3030_, lean_object* v_args_3031_){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3032_ = lean_unsigned_to_nat(0u);
v___x_3033_ = lean_array_get_size(v_args_3031_);
v___x_3034_ = lean_nat_dec_lt(v___x_3032_, v___x_3033_);
if (v___x_3034_ == 0)
{
return v_f_3030_;
}
else
{
uint8_t v___x_3035_; 
v___x_3035_ = lean_nat_dec_le(v___x_3033_, v___x_3033_);
if (v___x_3035_ == 0)
{
if (v___x_3034_ == 0)
{
return v_f_3030_;
}
else
{
size_t v___x_3036_; size_t v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = ((size_t)0ULL);
v___x_3037_ = lean_usize_of_nat(v___x_3033_);
v___x_3038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3031_, v___x_3036_, v___x_3037_, v_f_3030_);
return v___x_3038_;
}
}
else
{
size_t v___x_3039_; size_t v___x_3040_; lean_object* v___x_3041_; 
v___x_3039_ = ((size_t)0ULL);
v___x_3040_ = lean_usize_of_nat(v___x_3033_);
v___x_3041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3031_, v___x_3039_, v___x_3040_, v_f_3030_);
return v___x_3041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_3042_, lean_object* v_args_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_mkAppN(v_f_3042_, v_args_3043_);
lean_dec_ref(v_args_3043_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_3045_, lean_object* v_args_3046_, lean_object* v_i_3047_, lean_object* v_e_3048_){
_start:
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_nat_dec_lt(v_i_3047_, v_n_3045_);
if (v___x_3049_ == 0)
{
lean_dec(v_i_3047_);
return v_e_3048_;
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3050_ = lean_unsigned_to_nat(1u);
v___x_3051_ = lean_nat_add(v_i_3047_, v___x_3050_);
v___x_3052_ = l_Lean_instInhabitedExpr;
v___x_3053_ = lean_array_get_borrowed(v___x_3052_, v_args_3046_, v_i_3047_);
lean_dec(v_i_3047_);
lean_inc(v___x_3053_);
v___x_3054_ = l_Lean_Expr_app___override(v_e_3048_, v___x_3053_);
v_i_3047_ = v___x_3051_;
v_e_3048_ = v___x_3054_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_3056_, lean_object* v_args_3057_, lean_object* v_i_3058_, lean_object* v_e_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_3056_, v_args_3057_, v_i_3058_, v_e_3059_);
lean_dec_ref(v_args_3057_);
lean_dec(v_n_3056_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_3061_, lean_object* v_i_3062_, lean_object* v_j_3063_, lean_object* v_args_3064_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_3063_, v_args_3064_, v_i_3062_, v_f_3061_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_3066_, lean_object* v_i_3067_, lean_object* v_j_3068_, lean_object* v_args_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_mkAppRange(v_f_3066_, v_i_3067_, v_j_3068_, v_args_3069_);
lean_dec_ref(v_args_3069_);
lean_dec(v_j_3068_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_3071_, size_t v_i_3072_, size_t v_stop_3073_, lean_object* v_b_3074_){
_start:
{
uint8_t v___x_3075_; 
v___x_3075_ = lean_usize_dec_eq(v_i_3072_, v_stop_3073_);
if (v___x_3075_ == 0)
{
size_t v___x_3076_; size_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3076_ = ((size_t)1ULL);
v___x_3077_ = lean_usize_sub(v_i_3072_, v___x_3076_);
v___x_3078_ = lean_array_uget_borrowed(v_as_3071_, v___x_3077_);
lean_inc(v___x_3078_);
v___x_3079_ = l_Lean_Expr_app___override(v_b_3074_, v___x_3078_);
v_i_3072_ = v___x_3077_;
v_b_3074_ = v___x_3079_;
goto _start;
}
else
{
return v_b_3074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_3081_, lean_object* v_i_3082_, lean_object* v_stop_3083_, lean_object* v_b_3084_){
_start:
{
size_t v_i_boxed_3085_; size_t v_stop_boxed_3086_; lean_object* v_res_3087_; 
v_i_boxed_3085_ = lean_unbox_usize(v_i_3082_);
lean_dec(v_i_3082_);
v_stop_boxed_3086_ = lean_unbox_usize(v_stop_3083_);
lean_dec(v_stop_3083_);
v_res_3087_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3081_, v_i_boxed_3085_, v_stop_boxed_3086_, v_b_3084_);
lean_dec_ref(v_as_3081_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_3088_, lean_object* v_revArgs_3089_){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v___x_3090_ = lean_array_get_size(v_revArgs_3089_);
v___x_3091_ = lean_unsigned_to_nat(0u);
v___x_3092_ = lean_nat_dec_lt(v___x_3091_, v___x_3090_);
if (v___x_3092_ == 0)
{
return v_fn_3088_;
}
else
{
size_t v___x_3093_; size_t v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = lean_usize_of_nat(v___x_3090_);
v___x_3094_ = ((size_t)0ULL);
v___x_3095_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_3089_, v___x_3093_, v___x_3094_, v_fn_3088_);
return v___x_3095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_3096_, lean_object* v_revArgs_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_mkAppRev(v_fn_3096_, v_revArgs_3097_);
lean_dec_ref(v_revArgs_3097_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = lean_expr_dbg_to_string(v_e_3100_);
lean_dec_ref(v_e_3100_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_3104_, lean_object* v_b_3105_){
_start:
{
uint8_t v_res_3106_; lean_object* v_r_3107_; 
v_res_3106_ = lean_expr_quick_lt(v_a_3104_, v_b_3105_);
lean_dec_ref(v_b_3105_);
lean_dec_ref(v_a_3104_);
v_r_3107_ = lean_box(v_res_3106_);
return v_r_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_3110_, lean_object* v_b_3111_){
_start:
{
uint8_t v_res_3112_; lean_object* v_r_3113_; 
v_res_3112_ = lean_expr_lt(v_a_3110_, v_b_3111_);
lean_dec_ref(v_b_3111_);
lean_dec_ref(v_a_3110_);
v_r_3113_ = lean_box(v_res_3112_);
return v_r_3113_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* v_a_3114_, lean_object* v_b_3115_){
_start:
{
uint8_t v___x_3116_; 
v___x_3116_ = lean_expr_quick_lt(v_a_3114_, v_b_3115_);
if (v___x_3116_ == 0)
{
uint8_t v___x_3117_; 
v___x_3117_ = lean_expr_quick_lt(v_b_3115_, v_a_3114_);
if (v___x_3117_ == 0)
{
uint8_t v___x_3118_; 
v___x_3118_ = 1;
return v___x_3118_;
}
else
{
uint8_t v___x_3119_; 
v___x_3119_ = 2;
return v___x_3119_;
}
}
else
{
uint8_t v___x_3120_; 
v___x_3120_ = 0;
return v___x_3120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_3121_, lean_object* v_b_3122_){
_start:
{
uint8_t v_res_3123_; lean_object* v_r_3124_; 
v_res_3123_ = l_Lean_Expr_quickComp(v_a_3121_, v_b_3122_);
lean_dec_ref(v_b_3122_);
lean_dec_ref(v_a_3121_);
v_r_3124_ = lean_box(v_res_3123_);
return v_r_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_3127_, lean_object* v_b_3128_){
_start:
{
uint8_t v_res_3129_; lean_object* v_r_3130_; 
v_res_3129_ = lean_expr_eqv(v_a_3127_, v_b_3128_);
lean_dec_ref(v_b_3128_);
lean_dec_ref(v_a_3127_);
v_r_3130_ = lean_box(v_res_3129_);
return v_r_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3135_, lean_object* v_b_3136_){
_start:
{
uint8_t v_res_3137_; lean_object* v_r_3138_; 
v_res_3137_ = lean_expr_equal(v_a_3135_, v_b_3136_);
lean_dec_ref(v_b_3136_);
lean_dec_ref(v_a_3135_);
v_r_3138_ = lean_box(v_res_3137_);
return v_r_3138_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* v_x_3139_){
_start:
{
if (lean_obj_tag(v_x_3139_) == 3)
{
uint8_t v___x_3140_; 
v___x_3140_ = 1;
return v___x_3140_;
}
else
{
uint8_t v___x_3141_; 
v___x_3141_ = 0;
return v___x_3141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3142_){
_start:
{
uint8_t v_res_3143_; lean_object* v_r_3144_; 
v_res_3143_ = l_Lean_Expr_isSort(v_x_3142_);
lean_dec_ref(v_x_3142_);
v_r_3144_ = lean_box(v_res_3143_);
return v_r_3144_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* v_x_3145_){
_start:
{
if (lean_obj_tag(v_x_3145_) == 3)
{
lean_object* v_u_3146_; 
v_u_3146_ = lean_ctor_get(v_x_3145_, 0);
if (lean_obj_tag(v_u_3146_) == 1)
{
uint8_t v___x_3147_; 
v___x_3147_ = 1;
return v___x_3147_;
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
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3150_){
_start:
{
uint8_t v_res_3151_; lean_object* v_r_3152_; 
v_res_3151_ = l_Lean_Expr_isType(v_x_3150_);
lean_dec_ref(v_x_3150_);
v_r_3152_ = lean_box(v_res_3151_);
return v_r_3152_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* v_x_3153_){
_start:
{
if (lean_obj_tag(v_x_3153_) == 3)
{
lean_object* v_u_3154_; 
v_u_3154_ = lean_ctor_get(v_x_3153_, 0);
if (lean_obj_tag(v_u_3154_) == 1)
{
lean_object* v_a_3155_; 
v_a_3155_ = lean_ctor_get(v_u_3154_, 0);
if (lean_obj_tag(v_a_3155_) == 0)
{
uint8_t v___x_3156_; 
v___x_3156_ = 1;
return v___x_3156_;
}
else
{
uint8_t v___x_3157_; 
v___x_3157_ = 0;
return v___x_3157_;
}
}
else
{
uint8_t v___x_3158_; 
v___x_3158_ = 0;
return v___x_3158_;
}
}
else
{
uint8_t v___x_3159_; 
v___x_3159_ = 0;
return v___x_3159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3160_){
_start:
{
uint8_t v_res_3161_; lean_object* v_r_3162_; 
v_res_3161_ = l_Lean_Expr_isType0(v_x_3160_);
lean_dec_ref(v_x_3160_);
v_r_3162_ = lean_box(v_res_3161_);
return v_r_3162_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* v_x_3163_){
_start:
{
if (lean_obj_tag(v_x_3163_) == 3)
{
lean_object* v_u_3164_; 
v_u_3164_ = lean_ctor_get(v_x_3163_, 0);
if (lean_obj_tag(v_u_3164_) == 0)
{
uint8_t v___x_3165_; 
v___x_3165_ = 1;
return v___x_3165_;
}
else
{
uint8_t v___x_3166_; 
v___x_3166_ = 0;
return v___x_3166_;
}
}
else
{
uint8_t v___x_3167_; 
v___x_3167_ = 0;
return v___x_3167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3168_){
_start:
{
uint8_t v_res_3169_; lean_object* v_r_3170_; 
v_res_3169_ = l_Lean_Expr_isProp(v_x_3168_);
lean_dec_ref(v_x_3168_);
v_r_3170_ = lean_box(v_res_3169_);
return v_r_3170_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3171_){
_start:
{
if (lean_obj_tag(v_x_3171_) == 0)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3174_){
_start:
{
uint8_t v_res_3175_; lean_object* v_r_3176_; 
v_res_3175_ = l_Lean_Expr_isBVar(v_x_3174_);
lean_dec_ref(v_x_3174_);
v_r_3176_ = lean_box(v_res_3175_);
return v_r_3176_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3177_){
_start:
{
if (lean_obj_tag(v_x_3177_) == 2)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3180_){
_start:
{
uint8_t v_res_3181_; lean_object* v_r_3182_; 
v_res_3181_ = l_Lean_Expr_isMVar(v_x_3180_);
lean_dec_ref(v_x_3180_);
v_r_3182_ = lean_box(v_res_3181_);
return v_r_3182_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3183_){
_start:
{
if (lean_obj_tag(v_x_3183_) == 1)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3186_){
_start:
{
uint8_t v_res_3187_; lean_object* v_r_3188_; 
v_res_3187_ = l_Lean_Expr_isFVar(v_x_3186_);
lean_dec_ref(v_x_3186_);
v_r_3188_ = lean_box(v_res_3187_);
return v_r_3188_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* v_x_3189_){
_start:
{
if (lean_obj_tag(v_x_3189_) == 5)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3192_){
_start:
{
uint8_t v_res_3193_; lean_object* v_r_3194_; 
v_res_3193_ = l_Lean_Expr_isApp(v_x_3192_);
lean_dec_ref(v_x_3192_);
v_r_3194_ = lean_box(v_res_3193_);
return v_r_3194_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* v_x_3195_){
_start:
{
if (lean_obj_tag(v_x_3195_) == 11)
{
uint8_t v___x_3196_; 
v___x_3196_ = 1;
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
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3198_){
_start:
{
uint8_t v_res_3199_; lean_object* v_r_3200_; 
v_res_3199_ = l_Lean_Expr_isProj(v_x_3198_);
lean_dec_ref(v_x_3198_);
v_r_3200_ = lean_box(v_res_3199_);
return v_r_3200_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* v_x_3201_){
_start:
{
if (lean_obj_tag(v_x_3201_) == 4)
{
uint8_t v___x_3202_; 
v___x_3202_ = 1;
return v___x_3202_;
}
else
{
uint8_t v___x_3203_; 
v___x_3203_ = 0;
return v___x_3203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3204_){
_start:
{
uint8_t v_res_3205_; lean_object* v_r_3206_; 
v_res_3205_ = l_Lean_Expr_isConst(v_x_3204_);
lean_dec_ref(v_x_3204_);
v_r_3206_ = lean_box(v_res_3205_);
return v_r_3206_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3207_, lean_object* v_x_3208_){
_start:
{
if (lean_obj_tag(v_x_3207_) == 4)
{
lean_object* v_declName_3209_; uint8_t v___x_3210_; 
v_declName_3209_ = lean_ctor_get(v_x_3207_, 0);
v___x_3210_ = lean_name_eq(v_declName_3209_, v_x_3208_);
return v___x_3210_;
}
else
{
uint8_t v___x_3211_; 
v___x_3211_ = 0;
return v___x_3211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3212_, lean_object* v_x_3213_){
_start:
{
uint8_t v_res_3214_; lean_object* v_r_3215_; 
v_res_3214_ = l_Lean_Expr_isConstOf(v_x_3212_, v_x_3213_);
lean_dec(v_x_3213_);
lean_dec_ref(v_x_3212_);
v_r_3215_ = lean_box(v_res_3214_);
return v_r_3215_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3216_, lean_object* v_x_3217_){
_start:
{
if (lean_obj_tag(v_x_3216_) == 1)
{
lean_object* v_fvarId_3218_; uint8_t v___x_3219_; 
v_fvarId_3218_ = lean_ctor_get(v_x_3216_, 0);
v___x_3219_ = lean_name_eq(v_fvarId_3218_, v_x_3217_);
return v___x_3219_;
}
else
{
uint8_t v___x_3220_; 
v___x_3220_ = 0;
return v___x_3220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3221_, lean_object* v_x_3222_){
_start:
{
uint8_t v_res_3223_; lean_object* v_r_3224_; 
v_res_3223_ = l_Lean_Expr_isFVarOf(v_x_3221_, v_x_3222_);
lean_dec(v_x_3222_);
lean_dec_ref(v_x_3221_);
v_r_3224_ = lean_box(v_res_3223_);
return v_r_3224_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* v_x_3225_){
_start:
{
if (lean_obj_tag(v_x_3225_) == 7)
{
uint8_t v___x_3226_; 
v___x_3226_ = 1;
return v___x_3226_;
}
else
{
uint8_t v___x_3227_; 
v___x_3227_ = 0;
return v___x_3227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3228_){
_start:
{
uint8_t v_res_3229_; lean_object* v_r_3230_; 
v_res_3229_ = l_Lean_Expr_isForall(v_x_3228_);
lean_dec_ref(v_x_3228_);
v_r_3230_ = lean_box(v_res_3229_);
return v_r_3230_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3231_){
_start:
{
if (lean_obj_tag(v_x_3231_) == 6)
{
uint8_t v___x_3232_; 
v___x_3232_ = 1;
return v___x_3232_;
}
else
{
uint8_t v___x_3233_; 
v___x_3233_ = 0;
return v___x_3233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3234_){
_start:
{
uint8_t v_res_3235_; lean_object* v_r_3236_; 
v_res_3235_ = l_Lean_Expr_isLambda(v_x_3234_);
lean_dec_ref(v_x_3234_);
v_r_3236_ = lean_box(v_res_3235_);
return v_r_3236_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3237_){
_start:
{
switch(lean_obj_tag(v_x_3237_))
{
case 6:
{
uint8_t v___x_3238_; 
v___x_3238_ = 1;
return v___x_3238_;
}
case 7:
{
uint8_t v___x_3239_; 
v___x_3239_ = 1;
return v___x_3239_;
}
default: 
{
uint8_t v___x_3240_; 
v___x_3240_ = 0;
return v___x_3240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3241_){
_start:
{
uint8_t v_res_3242_; lean_object* v_r_3243_; 
v_res_3242_ = l_Lean_Expr_isBinding(v_x_3241_);
lean_dec_ref(v_x_3241_);
v_r_3243_ = lean_box(v_res_3242_);
return v_r_3243_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* v_x_3244_){
_start:
{
if (lean_obj_tag(v_x_3244_) == 8)
{
uint8_t v___x_3245_; 
v___x_3245_ = 1;
return v___x_3245_;
}
else
{
uint8_t v___x_3246_; 
v___x_3246_ = 0;
return v___x_3246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3247_){
_start:
{
uint8_t v_res_3248_; lean_object* v_r_3249_; 
v_res_3248_ = l_Lean_Expr_isLet(v_x_3247_);
lean_dec_ref(v_x_3247_);
v_r_3249_ = lean_box(v_res_3248_);
return v_r_3249_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object* v_x_3250_){
_start:
{
if (lean_obj_tag(v_x_3250_) == 8)
{
uint8_t v_nondep_3251_; 
v_nondep_3251_ = lean_ctor_get_uint8(v_x_3250_, sizeof(void*)*4 + 8);
return v_nondep_3251_;
}
else
{
uint8_t v___x_3252_; 
v___x_3252_ = 0;
return v___x_3252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3253_){
_start:
{
uint8_t v_res_3254_; lean_object* v_r_3255_; 
v_res_3254_ = l_Lean_Expr_isHave(v_x_3253_);
lean_dec_ref(v_x_3253_);
v_r_3255_ = lean_box(v_res_3254_);
return v_r_3255_;
}
}
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object* v_a_3256_){
_start:
{
uint8_t v___x_3257_; 
v___x_3257_ = l_Lean_Expr_isHave(v_a_3256_);
lean_dec_ref(v_a_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3258_){
_start:
{
uint8_t v_res_3259_; lean_object* v_r_3260_; 
v_res_3259_ = lean_expr_is_have(v_a_3258_);
v_r_3260_ = lean_box(v_res_3259_);
return v_r_3260_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* v_x_3261_){
_start:
{
if (lean_obj_tag(v_x_3261_) == 10)
{
uint8_t v___x_3262_; 
v___x_3262_ = 1;
return v___x_3262_;
}
else
{
uint8_t v___x_3263_; 
v___x_3263_ = 0;
return v___x_3263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3264_){
_start:
{
uint8_t v_res_3265_; lean_object* v_r_3266_; 
v_res_3265_ = l_Lean_Expr_isMData(v_x_3264_);
lean_dec_ref(v_x_3264_);
v_r_3266_ = lean_box(v_res_3265_);
return v_r_3266_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* v_x_3267_){
_start:
{
if (lean_obj_tag(v_x_3267_) == 9)
{
uint8_t v___x_3268_; 
v___x_3268_ = 1;
return v___x_3268_;
}
else
{
uint8_t v___x_3269_; 
v___x_3269_ = 0;
return v___x_3269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3270_){
_start:
{
uint8_t v_res_3271_; lean_object* v_r_3272_; 
v_res_3271_ = l_Lean_Expr_isLit(v_x_3270_);
lean_dec_ref(v_x_3270_);
v_r_3272_ = lean_box(v_res_3271_);
return v_r_3272_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3273_){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = l_Lean_instInhabitedExpr;
v___x_3275_ = lean_panic_fn_borrowed(v___x_3274_, v_msg_3273_);
return v___x_3275_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3279_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3280_ = lean_unsigned_to_nat(15u);
v___x_3281_ = lean_unsigned_to_nat(922u);
v___x_3282_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3283_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3284_ = l_mkPanicMessageWithDecl(v___x_3283_, v___x_3282_, v___x_3281_, v___x_3280_, v___x_3279_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3285_){
_start:
{
if (lean_obj_tag(v_x_3285_) == 5)
{
lean_object* v_fn_3286_; 
v_fn_3286_ = lean_ctor_get(v_x_3285_, 0);
lean_inc_ref(v_fn_3286_);
return v_fn_3286_;
}
else
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3288_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3287_);
return v___x_3288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_Expr_appFn_x21(v_x_3289_);
lean_dec_ref(v_x_3289_);
return v_res_3290_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3292_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3293_ = lean_unsigned_to_nat(15u);
v___x_3294_ = lean_unsigned_to_nat(926u);
v___x_3295_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3296_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3297_ = l_mkPanicMessageWithDecl(v___x_3296_, v___x_3295_, v___x_3294_, v___x_3293_, v___x_3292_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3298_){
_start:
{
if (lean_obj_tag(v_x_3298_) == 5)
{
lean_object* v_arg_3299_; 
v_arg_3299_ = lean_ctor_get(v_x_3298_, 1);
lean_inc_ref(v_arg_3299_);
return v_arg_3299_;
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3301_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3300_);
return v___x_3301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_Expr_appArg_x21(v_x_3302_);
lean_dec_ref(v_x_3302_);
return v_res_3303_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3305_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3306_ = lean_unsigned_to_nat(17u);
v___x_3307_ = lean_unsigned_to_nat(931u);
v___x_3308_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3309_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3310_ = l_mkPanicMessageWithDecl(v___x_3309_, v___x_3308_, v___x_3307_, v___x_3306_, v___x_3305_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3311_){
_start:
{
switch(lean_obj_tag(v_x_3311_))
{
case 10:
{
lean_object* v_expr_3312_; 
v_expr_3312_ = lean_ctor_get(v_x_3311_, 1);
v_x_3311_ = v_expr_3312_;
goto _start;
}
case 5:
{
lean_object* v_fn_3314_; 
v_fn_3314_ = lean_ctor_get(v_x_3311_, 0);
lean_inc_ref(v_fn_3314_);
return v_fn_3314_;
}
default: 
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3316_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3315_);
return v___x_3316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Lean_Expr_appFn_x21_x27(v_x_3317_);
lean_dec_ref(v_x_3317_);
return v_res_3318_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3320_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3321_ = lean_unsigned_to_nat(17u);
v___x_3322_ = lean_unsigned_to_nat(936u);
v___x_3323_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3324_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3325_ = l_mkPanicMessageWithDecl(v___x_3324_, v___x_3323_, v___x_3322_, v___x_3321_, v___x_3320_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3326_){
_start:
{
switch(lean_obj_tag(v_x_3326_))
{
case 10:
{
lean_object* v_expr_3327_; 
v_expr_3327_ = lean_ctor_get(v_x_3326_, 1);
v_x_3326_ = v_expr_3327_;
goto _start;
}
case 5:
{
lean_object* v_arg_3329_; 
v_arg_3329_ = lean_ctor_get(v_x_3326_, 1);
lean_inc_ref(v_arg_3329_);
return v_arg_3329_;
}
default: 
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3331_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3330_);
return v___x_3331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_Expr_appArg_x21_x27(v_x_3332_);
lean_dec_ref(v_x_3332_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3334_){
_start:
{
lean_object* v_arg_3335_; 
v_arg_3335_ = lean_ctor_get(v_e_3334_, 1);
lean_inc_ref(v_arg_3335_);
return v_arg_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Lean_Expr_appArg___redArg(v_e_3336_);
lean_dec_ref(v_e_3336_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3338_, lean_object* v_h_3339_){
_start:
{
lean_object* v_arg_3340_; 
v_arg_3340_ = lean_ctor_get(v_e_3338_, 1);
lean_inc_ref(v_arg_3340_);
return v_arg_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3341_, lean_object* v_h_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_Expr_appArg(v_e_3341_, v_h_3342_);
lean_dec_ref(v_e_3341_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3344_){
_start:
{
lean_object* v_fn_3345_; 
v_fn_3345_ = lean_ctor_get(v_e_3344_, 0);
lean_inc_ref(v_fn_3345_);
return v_fn_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_Expr_appFn___redArg(v_e_3346_);
lean_dec_ref(v_e_3346_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3348_, lean_object* v_h_3349_){
_start:
{
lean_object* v_fn_3350_; 
v_fn_3350_ = lean_ctor_get(v_e_3348_, 0);
lean_inc_ref(v_fn_3350_);
return v_fn_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3351_, lean_object* v_h_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lean_Expr_appFn(v_e_3351_, v_h_3352_);
lean_dec_ref(v_e_3351_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3354_){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3355_ = lean_box(0);
v___x_3356_ = lean_panic_fn_borrowed(v___x_3355_, v_msg_3354_);
return v___x_3356_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3359_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3360_ = lean_unsigned_to_nat(14u);
v___x_3361_ = lean_unsigned_to_nat(948u);
v___x_3362_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3363_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3364_ = l_mkPanicMessageWithDecl(v___x_3363_, v___x_3362_, v___x_3361_, v___x_3360_, v___x_3359_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3365_){
_start:
{
if (lean_obj_tag(v_x_3365_) == 3)
{
lean_object* v_u_3366_; 
v_u_3366_ = lean_ctor_get(v_x_3365_, 0);
lean_inc(v_u_3366_);
return v_u_3366_;
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3368_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3367_);
return v___x_3368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Expr_sortLevel_x21(v_x_3369_);
lean_dec_ref(v_x_3369_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3371_){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3373_ = lean_panic_fn_borrowed(v___x_3372_, v_msg_3371_);
return v___x_3373_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3376_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3377_ = lean_unsigned_to_nat(13u);
v___x_3378_ = lean_unsigned_to_nat(952u);
v___x_3379_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3380_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3381_ = l_mkPanicMessageWithDecl(v___x_3380_, v___x_3379_, v___x_3378_, v___x_3377_, v___x_3376_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3382_){
_start:
{
if (lean_obj_tag(v_x_3382_) == 9)
{
lean_object* v_a_3383_; 
v_a_3383_ = lean_ctor_get(v_x_3382_, 0);
lean_inc_ref(v_a_3383_);
return v_a_3383_;
}
else
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3385_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3384_);
return v___x_3385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_Expr_litValue_x21(v_x_3386_);
lean_dec_ref(v_x_3386_);
return v_res_3387_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3388_){
_start:
{
if (lean_obj_tag(v_x_3388_) == 9)
{
lean_object* v_a_3389_; 
v_a_3389_ = lean_ctor_get(v_x_3388_, 0);
if (lean_obj_tag(v_a_3389_) == 0)
{
uint8_t v___x_3390_; 
v___x_3390_ = 1;
return v___x_3390_;
}
else
{
uint8_t v___x_3391_; 
v___x_3391_ = 0;
return v___x_3391_;
}
}
else
{
uint8_t v___x_3392_; 
v___x_3392_ = 0;
return v___x_3392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3393_){
_start:
{
uint8_t v_res_3394_; lean_object* v_r_3395_; 
v_res_3394_ = l_Lean_Expr_isRawNatLit(v_x_3393_);
lean_dec_ref(v_x_3393_);
v_r_3395_ = lean_box(v_res_3394_);
return v_r_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3396_){
_start:
{
if (lean_obj_tag(v_x_3396_) == 9)
{
lean_object* v_a_3397_; 
v_a_3397_ = lean_ctor_get(v_x_3396_, 0);
lean_inc_ref(v_a_3397_);
lean_dec_ref(v_x_3396_);
if (lean_obj_tag(v_a_3397_) == 0)
{
lean_object* v_val_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
v_val_3398_ = lean_ctor_get(v_a_3397_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v_a_3397_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v_a_3397_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_val_3398_);
lean_dec(v_a_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
lean_ctor_set_tag(v___x_3400_, 1);
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_val_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
else
{
lean_object* v___x_3406_; 
lean_dec_ref(v_a_3397_);
v___x_3406_ = lean_box(0);
return v___x_3406_;
}
}
else
{
lean_object* v___x_3407_; 
lean_dec_ref(v_x_3396_);
v___x_3407_ = lean_box(0);
return v___x_3407_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3408_){
_start:
{
if (lean_obj_tag(v_x_3408_) == 9)
{
lean_object* v_a_3409_; 
v_a_3409_ = lean_ctor_get(v_x_3408_, 0);
if (lean_obj_tag(v_a_3409_) == 1)
{
uint8_t v___x_3410_; 
v___x_3410_ = 1;
return v___x_3410_;
}
else
{
uint8_t v___x_3411_; 
v___x_3411_ = 0;
return v___x_3411_;
}
}
else
{
uint8_t v___x_3412_; 
v___x_3412_ = 0;
return v___x_3412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3413_){
_start:
{
uint8_t v_res_3414_; lean_object* v_r_3415_; 
v_res_3414_ = l_Lean_Expr_isStringLit(v_x_3413_);
lean_dec_ref(v_x_3413_);
v_r_3415_ = lean_box(v_res_3414_);
return v_r_3415_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3420_){
_start:
{
if (lean_obj_tag(v_x_3420_) == 5)
{
lean_object* v_fn_3421_; 
v_fn_3421_ = lean_ctor_get(v_x_3420_, 0);
if (lean_obj_tag(v_fn_3421_) == 4)
{
lean_object* v_arg_3422_; lean_object* v_declName_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v_arg_3422_ = lean_ctor_get(v_x_3420_, 1);
v_declName_3423_ = lean_ctor_get(v_fn_3421_, 0);
v___x_3424_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3425_ = lean_name_eq(v_declName_3423_, v___x_3424_);
if (v___x_3425_ == 0)
{
return v___x_3425_;
}
else
{
uint8_t v___x_3426_; 
v___x_3426_ = l_Lean_Expr_isRawNatLit(v_arg_3422_);
return v___x_3426_;
}
}
else
{
uint8_t v___x_3427_; 
v___x_3427_ = 0;
return v___x_3427_;
}
}
else
{
uint8_t v___x_3428_; 
v___x_3428_ = 0;
return v___x_3428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3429_){
_start:
{
uint8_t v_res_3430_; lean_object* v_r_3431_; 
v_res_3430_ = l_Lean_Expr_isCharLit(v_x_3429_);
lean_dec_ref(v_x_3429_);
v_r_3431_ = lean_box(v_res_3430_);
return v_r_3431_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3432_){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = lean_box(0);
v___x_3434_ = lean_panic_fn_borrowed(v___x_3433_, v_msg_3432_);
return v___x_3434_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3437_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3438_ = lean_unsigned_to_nat(17u);
v___x_3439_ = lean_unsigned_to_nat(976u);
v___x_3440_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3441_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3442_ = l_mkPanicMessageWithDecl(v___x_3441_, v___x_3440_, v___x_3439_, v___x_3438_, v___x_3437_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3443_){
_start:
{
if (lean_obj_tag(v_x_3443_) == 4)
{
lean_object* v_declName_3444_; 
v_declName_3444_ = lean_ctor_get(v_x_3443_, 0);
lean_inc(v_declName_3444_);
return v_declName_3444_;
}
else
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3446_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3445_);
return v___x_3446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Lean_Expr_constName_x21(v_x_3447_);
lean_dec_ref(v_x_3447_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3449_){
_start:
{
if (lean_obj_tag(v_x_3449_) == 4)
{
lean_object* v_declName_3450_; lean_object* v___x_3451_; 
v_declName_3450_ = lean_ctor_get(v_x_3449_, 0);
lean_inc(v_declName_3450_);
v___x_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3451_, 0, v_declName_3450_);
return v___x_3451_;
}
else
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_box(0);
return v___x_3452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_Lean_Expr_constName_x3f(v_x_3453_);
lean_dec_ref(v_x_3453_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3455_){
_start:
{
lean_object* v___x_3456_; 
v___x_3456_ = l_Lean_Expr_constName_x3f(v_e_3455_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v___x_3457_; 
v___x_3457_ = lean_box(0);
return v___x_3457_;
}
else
{
lean_object* v_val_3458_; 
v_val_3458_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_val_3458_);
lean_dec_ref(v___x_3456_);
return v_val_3458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Lean_Expr_constName(v_e_3459_);
lean_dec_ref(v_e_3459_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3461_){
_start:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3462_ = lean_box(0);
v___x_3463_ = lean_panic_fn_borrowed(v___x_3462_, v_msg_3461_);
return v___x_3463_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3465_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3466_ = lean_unsigned_to_nat(18u);
v___x_3467_ = lean_unsigned_to_nat(996u);
v___x_3468_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3469_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3470_ = l_mkPanicMessageWithDecl(v___x_3469_, v___x_3468_, v___x_3467_, v___x_3466_, v___x_3465_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3471_){
_start:
{
if (lean_obj_tag(v_x_3471_) == 4)
{
lean_object* v_us_3472_; 
v_us_3472_ = lean_ctor_get(v_x_3471_, 1);
lean_inc(v_us_3472_);
return v_us_3472_;
}
else
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3473_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3474_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3473_);
return v___x_3474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_Lean_Expr_constLevels_x21(v_x_3475_);
lean_dec_ref(v_x_3475_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3477_){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3478_ = lean_unsigned_to_nat(0u);
v___x_3479_ = lean_panic_fn_borrowed(v___x_3478_, v_msg_3477_);
return v___x_3479_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3482_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3483_ = lean_unsigned_to_nat(16u);
v___x_3484_ = lean_unsigned_to_nat(1000u);
v___x_3485_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3486_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3487_ = l_mkPanicMessageWithDecl(v___x_3486_, v___x_3485_, v___x_3484_, v___x_3483_, v___x_3482_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3488_){
_start:
{
if (lean_obj_tag(v_x_3488_) == 0)
{
lean_object* v_deBruijnIndex_3489_; 
v_deBruijnIndex_3489_ = lean_ctor_get(v_x_3488_, 0);
lean_inc(v_deBruijnIndex_3489_);
return v_deBruijnIndex_3489_;
}
else
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3491_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3490_);
return v___x_3491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l_Lean_Expr_bvarIdx_x21(v_x_3492_);
lean_dec_ref(v_x_3492_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3494_){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = lean_box(0);
v___x_3496_ = lean_panic_fn_borrowed(v___x_3495_, v_msg_3494_);
return v___x_3496_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3499_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3500_ = lean_unsigned_to_nat(14u);
v___x_3501_ = lean_unsigned_to_nat(1004u);
v___x_3502_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3503_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3504_ = l_mkPanicMessageWithDecl(v___x_3503_, v___x_3502_, v___x_3501_, v___x_3500_, v___x_3499_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3505_){
_start:
{
if (lean_obj_tag(v_x_3505_) == 1)
{
lean_object* v_fvarId_3506_; 
v_fvarId_3506_ = lean_ctor_get(v_x_3505_, 0);
lean_inc(v_fvarId_3506_);
return v_fvarId_3506_;
}
else
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3508_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3507_);
return v___x_3508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_Expr_fvarId_x21(v_x_3509_);
lean_dec_ref(v_x_3509_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3511_){
_start:
{
if (lean_obj_tag(v_x_3511_) == 1)
{
lean_object* v_fvarId_3512_; lean_object* v___x_3513_; 
v_fvarId_3512_ = lean_ctor_get(v_x_3511_, 0);
lean_inc(v_fvarId_3512_);
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v_fvarId_3512_);
return v___x_3513_;
}
else
{
lean_object* v___x_3514_; 
v___x_3514_ = lean_box(0);
return v___x_3514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_Lean_Expr_fvarId_x3f(v_x_3515_);
lean_dec_ref(v_x_3515_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3517_){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = lean_box(0);
v___x_3519_ = lean_panic_fn_borrowed(v___x_3518_, v_msg_3517_);
return v___x_3519_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3522_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3523_ = lean_unsigned_to_nat(14u);
v___x_3524_ = lean_unsigned_to_nat(1012u);
v___x_3525_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3526_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3527_ = l_mkPanicMessageWithDecl(v___x_3526_, v___x_3525_, v___x_3524_, v___x_3523_, v___x_3522_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3528_){
_start:
{
if (lean_obj_tag(v_x_3528_) == 2)
{
lean_object* v_mvarId_3529_; 
v_mvarId_3529_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_mvarId_3529_);
return v_mvarId_3529_;
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3531_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3530_);
return v___x_3531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_Expr_mvarId_x21(v_x_3532_);
lean_dec_ref(v_x_3532_);
return v_res_3533_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3536_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3537_ = lean_unsigned_to_nat(23u);
v___x_3538_ = lean_unsigned_to_nat(1017u);
v___x_3539_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3540_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3541_ = l_mkPanicMessageWithDecl(v___x_3540_, v___x_3539_, v___x_3538_, v___x_3537_, v___x_3536_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3542_){
_start:
{
switch(lean_obj_tag(v_x_3542_))
{
case 7:
{
lean_object* v_binderName_3543_; 
v_binderName_3543_ = lean_ctor_get(v_x_3542_, 0);
lean_inc(v_binderName_3543_);
return v_binderName_3543_;
}
case 6:
{
lean_object* v_binderName_3544_; 
v_binderName_3544_ = lean_ctor_get(v_x_3542_, 0);
lean_inc(v_binderName_3544_);
return v_binderName_3544_;
}
default: 
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3546_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3545_);
return v___x_3546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l_Lean_Expr_bindingName_x21(v_x_3547_);
lean_dec_ref(v_x_3547_);
return v_res_3548_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3550_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3551_ = lean_unsigned_to_nat(23u);
v___x_3552_ = lean_unsigned_to_nat(1022u);
v___x_3553_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3554_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3555_ = l_mkPanicMessageWithDecl(v___x_3554_, v___x_3553_, v___x_3552_, v___x_3551_, v___x_3550_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3556_){
_start:
{
switch(lean_obj_tag(v_x_3556_))
{
case 7:
{
lean_object* v_binderType_3557_; 
v_binderType_3557_ = lean_ctor_get(v_x_3556_, 1);
lean_inc_ref(v_binderType_3557_);
return v_binderType_3557_;
}
case 6:
{
lean_object* v_binderType_3558_; 
v_binderType_3558_ = lean_ctor_get(v_x_3556_, 1);
lean_inc_ref(v_binderType_3558_);
return v_binderType_3558_;
}
default: 
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3560_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3559_);
return v___x_3560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lean_Expr_bindingDomain_x21(v_x_3561_);
lean_dec_ref(v_x_3561_);
return v_res_3562_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3564_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3565_ = lean_unsigned_to_nat(23u);
v___x_3566_ = lean_unsigned_to_nat(1027u);
v___x_3567_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3568_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3569_ = l_mkPanicMessageWithDecl(v___x_3568_, v___x_3567_, v___x_3566_, v___x_3565_, v___x_3564_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3570_){
_start:
{
switch(lean_obj_tag(v_x_3570_))
{
case 7:
{
lean_object* v_body_3571_; 
v_body_3571_ = lean_ctor_get(v_x_3570_, 2);
lean_inc_ref(v_body_3571_);
return v_body_3571_;
}
case 6:
{
lean_object* v_body_3572_; 
v_body_3572_ = lean_ctor_get(v_x_3570_, 2);
lean_inc_ref(v_body_3572_);
return v_body_3572_;
}
default: 
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3574_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3573_);
return v___x_3574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_Expr_bindingBody_x21(v_x_3575_);
lean_dec_ref(v_x_3575_);
return v_res_3576_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3577_){
_start:
{
uint8_t v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; 
v___x_3578_ = 0;
v___x_3579_ = lean_box(v___x_3578_);
v___x_3580_ = lean_panic_fn_borrowed(v___x_3579_, v_msg_3577_);
lean_dec(v___x_3579_);
v___x_3581_ = lean_unbox(v___x_3580_);
lean_dec(v___x_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3582_){
_start:
{
uint8_t v_res_3583_; lean_object* v_r_3584_; 
v_res_3583_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3582_);
v_r_3584_ = lean_box(v_res_3583_);
return v_r_3584_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3586_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3587_ = lean_unsigned_to_nat(24u);
v___x_3588_ = lean_unsigned_to_nat(1032u);
v___x_3589_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3590_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3591_ = l_mkPanicMessageWithDecl(v___x_3590_, v___x_3589_, v___x_3588_, v___x_3587_, v___x_3586_);
return v___x_3591_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3592_){
_start:
{
switch(lean_obj_tag(v_x_3592_))
{
case 7:
{
uint8_t v_binderInfo_3593_; 
v_binderInfo_3593_ = lean_ctor_get_uint8(v_x_3592_, sizeof(void*)*3 + 8);
return v_binderInfo_3593_;
}
case 6:
{
uint8_t v_binderInfo_3594_; 
v_binderInfo_3594_ = lean_ctor_get_uint8(v_x_3592_, sizeof(void*)*3 + 8);
return v_binderInfo_3594_;
}
default: 
{
lean_object* v___x_3595_; uint8_t v___x_3596_; 
v___x_3595_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3596_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3595_);
return v___x_3596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3597_){
_start:
{
uint8_t v_res_3598_; lean_object* v_r_3599_; 
v_res_3598_ = l_Lean_Expr_bindingInfo_x21(v_x_3597_);
lean_dec_ref(v_x_3597_);
v_r_3599_ = lean_box(v_res_3598_);
return v_r_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3600_){
_start:
{
lean_object* v_binderName_3601_; 
v_binderName_3601_ = lean_ctor_get(v_x_3600_, 0);
lean_inc(v_binderName_3601_);
return v_binderName_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_Lean_Expr_forallName___redArg(v_x_3602_);
lean_dec_ref(v_x_3602_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3604_, lean_object* v_x_3605_){
_start:
{
lean_object* v_binderName_3606_; 
v_binderName_3606_ = lean_ctor_get(v_x_3604_, 0);
lean_inc(v_binderName_3606_);
return v_binderName_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3607_, lean_object* v_x_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_Expr_forallName(v_x_3607_, v_x_3608_);
lean_dec_ref(v_x_3607_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3610_){
_start:
{
lean_object* v_binderType_3611_; 
v_binderType_3611_ = lean_ctor_get(v_x_3610_, 1);
lean_inc_ref(v_binderType_3611_);
return v_binderType_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_Expr_forallDomain___redArg(v_x_3612_);
lean_dec_ref(v_x_3612_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3614_, lean_object* v_x_3615_){
_start:
{
lean_object* v_binderType_3616_; 
v_binderType_3616_ = lean_ctor_get(v_x_3614_, 1);
lean_inc_ref(v_binderType_3616_);
return v_binderType_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3617_, lean_object* v_x_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_Expr_forallDomain(v_x_3617_, v_x_3618_);
lean_dec_ref(v_x_3617_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3620_){
_start:
{
lean_object* v_body_3621_; 
v_body_3621_ = lean_ctor_get(v_x_3620_, 2);
lean_inc_ref(v_body_3621_);
return v_body_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Lean_Expr_forallBody___redArg(v_x_3622_);
lean_dec_ref(v_x_3622_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3624_, lean_object* v_x_3625_){
_start:
{
lean_object* v_body_3626_; 
v_body_3626_ = lean_ctor_get(v_x_3624_, 2);
lean_inc_ref(v_body_3626_);
return v_body_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3627_, lean_object* v_x_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Lean_Expr_forallBody(v_x_3627_, v_x_3628_);
lean_dec_ref(v_x_3627_);
return v_res_3629_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3630_){
_start:
{
uint8_t v_binderInfo_3631_; 
v_binderInfo_3631_ = lean_ctor_get_uint8(v_x_3630_, sizeof(void*)*3 + 8);
return v_binderInfo_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3632_){
_start:
{
uint8_t v_res_3633_; lean_object* v_r_3634_; 
v_res_3633_ = l_Lean_Expr_forallInfo___redArg(v_x_3632_);
lean_dec_ref(v_x_3632_);
v_r_3634_ = lean_box(v_res_3633_);
return v_r_3634_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3635_, lean_object* v_x_3636_){
_start:
{
uint8_t v_binderInfo_3637_; 
v_binderInfo_3637_ = lean_ctor_get_uint8(v_x_3635_, sizeof(void*)*3 + 8);
return v_binderInfo_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3638_, lean_object* v_x_3639_){
_start:
{
uint8_t v_res_3640_; lean_object* v_r_3641_; 
v_res_3640_ = l_Lean_Expr_forallInfo(v_x_3638_, v_x_3639_);
lean_dec_ref(v_x_3638_);
v_r_3641_ = lean_box(v_res_3640_);
return v_r_3641_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3644_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3645_ = lean_unsigned_to_nat(17u);
v___x_3646_ = lean_unsigned_to_nat(1048u);
v___x_3647_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3648_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3649_ = l_mkPanicMessageWithDecl(v___x_3648_, v___x_3647_, v___x_3646_, v___x_3645_, v___x_3644_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3650_){
_start:
{
if (lean_obj_tag(v_x_3650_) == 8)
{
lean_object* v_declName_3651_; 
v_declName_3651_ = lean_ctor_get(v_x_3650_, 0);
lean_inc(v_declName_3651_);
return v_declName_3651_;
}
else
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3653_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3652_);
return v___x_3653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l_Lean_Expr_letName_x21(v_x_3654_);
lean_dec_ref(v_x_3654_);
return v_res_3655_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3657_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3658_ = lean_unsigned_to_nat(19u);
v___x_3659_ = lean_unsigned_to_nat(1052u);
v___x_3660_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3661_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3662_ = l_mkPanicMessageWithDecl(v___x_3661_, v___x_3660_, v___x_3659_, v___x_3658_, v___x_3657_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3663_){
_start:
{
if (lean_obj_tag(v_x_3663_) == 8)
{
lean_object* v_type_3664_; 
v_type_3664_ = lean_ctor_get(v_x_3663_, 1);
lean_inc_ref(v_type_3664_);
return v_type_3664_;
}
else
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3666_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3665_);
return v___x_3666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_Lean_Expr_letType_x21(v_x_3667_);
lean_dec_ref(v_x_3667_);
return v_res_3668_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3670_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3671_ = lean_unsigned_to_nat(21u);
v___x_3672_ = lean_unsigned_to_nat(1056u);
v___x_3673_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3674_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3675_ = l_mkPanicMessageWithDecl(v___x_3674_, v___x_3673_, v___x_3672_, v___x_3671_, v___x_3670_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3676_){
_start:
{
if (lean_obj_tag(v_x_3676_) == 8)
{
lean_object* v_value_3677_; 
v_value_3677_ = lean_ctor_get(v_x_3676_, 2);
lean_inc_ref(v_value_3677_);
return v_value_3677_;
}
else
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3679_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3678_);
return v___x_3679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l_Lean_Expr_letValue_x21(v_x_3680_);
lean_dec_ref(v_x_3680_);
return v_res_3681_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3683_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3684_ = lean_unsigned_to_nat(23u);
v___x_3685_ = lean_unsigned_to_nat(1060u);
v___x_3686_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3687_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3688_ = l_mkPanicMessageWithDecl(v___x_3687_, v___x_3686_, v___x_3685_, v___x_3684_, v___x_3683_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3689_){
_start:
{
if (lean_obj_tag(v_x_3689_) == 8)
{
lean_object* v_body_3690_; 
v_body_3690_ = lean_ctor_get(v_x_3689_, 3);
lean_inc_ref(v_body_3690_);
return v_body_3690_;
}
else
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3691_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3692_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3691_);
return v___x_3692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l_Lean_Expr_letBody_x21(v_x_3693_);
lean_dec_ref(v_x_3693_);
return v_res_3694_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3695_){
_start:
{
uint8_t v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; uint8_t v___x_3699_; 
v___x_3696_ = 0;
v___x_3697_ = lean_box(v___x_3696_);
v___x_3698_ = lean_panic_fn_borrowed(v___x_3697_, v_msg_3695_);
lean_dec(v___x_3697_);
v___x_3699_ = lean_unbox(v___x_3698_);
lean_dec(v___x_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3700_){
_start:
{
uint8_t v_res_3701_; lean_object* v_r_3702_; 
v_res_3701_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3700_);
v_r_3702_ = lean_box(v_res_3701_);
return v_r_3702_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3704_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3705_ = lean_unsigned_to_nat(27u);
v___x_3706_ = lean_unsigned_to_nat(1064u);
v___x_3707_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3708_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3709_ = l_mkPanicMessageWithDecl(v___x_3708_, v___x_3707_, v___x_3706_, v___x_3705_, v___x_3704_);
return v___x_3709_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3710_){
_start:
{
if (lean_obj_tag(v_x_3710_) == 8)
{
uint8_t v_nondep_3711_; 
v_nondep_3711_ = lean_ctor_get_uint8(v_x_3710_, sizeof(void*)*4 + 8);
return v_nondep_3711_;
}
else
{
lean_object* v___x_3712_; uint8_t v___x_3713_; 
v___x_3712_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3713_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3712_);
return v___x_3713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3714_){
_start:
{
uint8_t v_res_3715_; lean_object* v_r_3716_; 
v_res_3715_ = l_Lean_Expr_letNondep_x21(v_x_3714_);
lean_dec_ref(v_x_3714_);
v_r_3716_ = lean_box(v_res_3715_);
return v_r_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3717_){
_start:
{
if (lean_obj_tag(v_x_3717_) == 10)
{
lean_object* v_expr_3718_; 
v_expr_3718_ = lean_ctor_get(v_x_3717_, 1);
v_x_3717_ = v_expr_3718_;
goto _start;
}
else
{
lean_inc_ref(v_x_3717_);
return v_x_3717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Lean_Expr_consumeMData(v_x_3720_);
lean_dec_ref(v_x_3720_);
return v_res_3721_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3724_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3725_ = lean_unsigned_to_nat(17u);
v___x_3726_ = lean_unsigned_to_nat(1072u);
v___x_3727_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3728_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3729_ = l_mkPanicMessageWithDecl(v___x_3728_, v___x_3727_, v___x_3726_, v___x_3725_, v___x_3724_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3730_){
_start:
{
if (lean_obj_tag(v_x_3730_) == 10)
{
lean_object* v_expr_3731_; 
v_expr_3731_ = lean_ctor_get(v_x_3730_, 1);
lean_inc_ref(v_expr_3731_);
return v_expr_3731_;
}
else
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3733_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3732_);
return v___x_3733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Lean_Expr_mdataExpr_x21(v_x_3734_);
lean_dec_ref(v_x_3734_);
return v_res_3735_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3738_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3739_ = lean_unsigned_to_nat(18u);
v___x_3740_ = lean_unsigned_to_nat(1076u);
v___x_3741_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3742_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3743_ = l_mkPanicMessageWithDecl(v___x_3742_, v___x_3741_, v___x_3740_, v___x_3739_, v___x_3738_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3744_){
_start:
{
if (lean_obj_tag(v_x_3744_) == 11)
{
lean_object* v_struct_3745_; 
v_struct_3745_ = lean_ctor_get(v_x_3744_, 2);
lean_inc_ref(v_struct_3745_);
return v_struct_3745_;
}
else
{
lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3746_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3747_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3746_);
return v___x_3747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l_Lean_Expr_projExpr_x21(v_x_3748_);
lean_dec_ref(v_x_3748_);
return v_res_3749_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3751_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3752_ = lean_unsigned_to_nat(18u);
v___x_3753_ = lean_unsigned_to_nat(1080u);
v___x_3754_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3755_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3756_ = l_mkPanicMessageWithDecl(v___x_3755_, v___x_3754_, v___x_3753_, v___x_3752_, v___x_3751_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3757_){
_start:
{
if (lean_obj_tag(v_x_3757_) == 11)
{
lean_object* v_idx_3758_; 
v_idx_3758_ = lean_ctor_get(v_x_3757_, 1);
lean_inc(v_idx_3758_);
return v_idx_3758_;
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3759_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3760_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3759_);
return v___x_3760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l_Lean_Expr_projIdx_x21(v_x_3761_);
lean_dec_ref(v_x_3761_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3763_){
_start:
{
if (lean_obj_tag(v_x_3763_) == 7)
{
lean_object* v_body_3764_; 
v_body_3764_ = lean_ctor_get(v_x_3763_, 2);
v_x_3763_ = v_body_3764_;
goto _start;
}
else
{
lean_inc_ref(v_x_3763_);
return v_x_3763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_Expr_getForallBody(v_x_3766_);
lean_dec_ref(v_x_3766_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3768_, lean_object* v_x_3769_){
_start:
{
lean_object* v_zero_3770_; uint8_t v_isZero_3771_; 
v_zero_3770_ = lean_unsigned_to_nat(0u);
v_isZero_3771_ = lean_nat_dec_eq(v_x_3768_, v_zero_3770_);
if (v_isZero_3771_ == 1)
{
lean_dec(v_x_3768_);
lean_inc_ref(v_x_3769_);
return v_x_3769_;
}
else
{
if (lean_obj_tag(v_x_3769_) == 7)
{
lean_object* v_body_3772_; lean_object* v_one_3773_; lean_object* v_n_3774_; 
v_body_3772_ = lean_ctor_get(v_x_3769_, 2);
v_one_3773_ = lean_unsigned_to_nat(1u);
v_n_3774_ = lean_nat_sub(v_x_3768_, v_one_3773_);
lean_dec(v_x_3768_);
v_x_3768_ = v_n_3774_;
v_x_3769_ = v_body_3772_;
goto _start;
}
else
{
lean_dec(v_x_3768_);
lean_inc_ref(v_x_3769_);
return v_x_3769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3776_, lean_object* v_x_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3776_, v_x_3777_);
lean_dec_ref(v_x_3777_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3779_){
_start:
{
if (lean_obj_tag(v_x_3779_) == 7)
{
lean_object* v_binderName_3780_; lean_object* v_body_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v_binderName_3780_ = lean_ctor_get(v_x_3779_, 0);
v_body_3781_ = lean_ctor_get(v_x_3779_, 2);
v___x_3782_ = l_Lean_Expr_getForallBinderNames(v_body_3781_);
lean_inc(v_binderName_3780_);
v___x_3783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3783_, 0, v_binderName_3780_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
return v___x_3783_;
}
else
{
lean_object* v___x_3784_; 
v___x_3784_ = lean_box(0);
return v___x_3784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Lean_Expr_getForallBinderNames(v_x_3785_);
lean_dec_ref(v_x_3785_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3787_){
_start:
{
switch(lean_obj_tag(v_x_3787_))
{
case 10:
{
lean_object* v_expr_3788_; 
v_expr_3788_ = lean_ctor_get(v_x_3787_, 1);
v_x_3787_ = v_expr_3788_;
goto _start;
}
case 7:
{
lean_object* v_body_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v_body_3790_ = lean_ctor_get(v_x_3787_, 2);
v___x_3791_ = l_Lean_Expr_getNumHeadForalls(v_body_3790_);
v___x_3792_ = lean_unsigned_to_nat(1u);
v___x_3793_ = lean_nat_add(v___x_3791_, v___x_3792_);
lean_dec(v___x_3791_);
return v___x_3793_;
}
default: 
{
lean_object* v___x_3794_; 
v___x_3794_ = lean_unsigned_to_nat(0u);
return v___x_3794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Lean_Expr_getNumHeadForalls(v_x_3795_);
lean_dec_ref(v_x_3795_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3797_){
_start:
{
if (lean_obj_tag(v_x_3797_) == 5)
{
lean_object* v_fn_3798_; 
v_fn_3798_ = lean_ctor_get(v_x_3797_, 0);
v_x_3797_ = v_fn_3798_;
goto _start;
}
else
{
lean_inc_ref(v_x_3797_);
return v_x_3797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_Expr_getAppFn(v_x_3800_);
lean_dec_ref(v_x_3800_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3802_){
_start:
{
switch(lean_obj_tag(v_x_3802_))
{
case 5:
{
lean_object* v_fn_3803_; 
v_fn_3803_ = lean_ctor_get(v_x_3802_, 0);
v_x_3802_ = v_fn_3803_;
goto _start;
}
case 10:
{
lean_object* v_expr_3805_; 
v_expr_3805_ = lean_ctor_get(v_x_3802_, 1);
v_x_3802_ = v_expr_3805_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3802_);
return v_x_3802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_Lean_Expr_getAppFn_x27(v_x_3807_);
lean_dec_ref(v_x_3807_);
return v_res_3808_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3809_, lean_object* v_n_3810_){
_start:
{
lean_object* v___x_3811_; 
v___x_3811_ = l_Lean_Expr_getAppFn(v_e_3809_);
if (lean_obj_tag(v___x_3811_) == 4)
{
lean_object* v_declName_3812_; uint8_t v___x_3813_; 
v_declName_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_declName_3812_);
lean_dec_ref(v___x_3811_);
v___x_3813_ = lean_name_eq(v_declName_3812_, v_n_3810_);
lean_dec(v_declName_3812_);
return v___x_3813_;
}
else
{
uint8_t v___x_3814_; 
lean_dec_ref(v___x_3811_);
v___x_3814_ = 0;
return v___x_3814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3815_, lean_object* v_n_3816_){
_start:
{
uint8_t v_res_3817_; lean_object* v_r_3818_; 
v_res_3817_ = l_Lean_Expr_isAppOf(v_e_3815_, v_n_3816_);
lean_dec(v_n_3816_);
lean_dec_ref(v_e_3815_);
v_r_3818_ = lean_box(v_res_3817_);
return v_r_3818_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3819_, lean_object* v_x_3820_, lean_object* v_x_3821_){
_start:
{
switch(lean_obj_tag(v_x_3819_))
{
case 4:
{
lean_object* v_declName_3822_; lean_object* v___x_3823_; uint8_t v___x_3824_; 
v_declName_3822_ = lean_ctor_get(v_x_3819_, 0);
v___x_3823_ = lean_unsigned_to_nat(0u);
v___x_3824_ = lean_nat_dec_eq(v_x_3821_, v___x_3823_);
lean_dec(v_x_3821_);
if (v___x_3824_ == 0)
{
return v___x_3824_;
}
else
{
uint8_t v___x_3825_; 
v___x_3825_ = lean_name_eq(v_declName_3822_, v_x_3820_);
return v___x_3825_;
}
}
case 5:
{
lean_object* v_fn_3826_; lean_object* v_zero_3827_; uint8_t v_isZero_3828_; 
v_fn_3826_ = lean_ctor_get(v_x_3819_, 0);
v_zero_3827_ = lean_unsigned_to_nat(0u);
v_isZero_3828_ = lean_nat_dec_eq(v_x_3821_, v_zero_3827_);
if (v_isZero_3828_ == 0)
{
lean_object* v_one_3829_; lean_object* v_n_3830_; 
v_one_3829_ = lean_unsigned_to_nat(1u);
v_n_3830_ = lean_nat_sub(v_x_3821_, v_one_3829_);
lean_dec(v_x_3821_);
v_x_3819_ = v_fn_3826_;
v_x_3821_ = v_n_3830_;
goto _start;
}
else
{
uint8_t v___x_3832_; 
lean_dec(v_x_3821_);
v___x_3832_ = 0;
return v___x_3832_;
}
}
default: 
{
uint8_t v___x_3833_; 
lean_dec(v_x_3821_);
v___x_3833_ = 0;
return v___x_3833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3834_, lean_object* v_x_3835_, lean_object* v_x_3836_){
_start:
{
uint8_t v_res_3837_; lean_object* v_r_3838_; 
v_res_3837_ = l_Lean_Expr_isAppOfArity(v_x_3834_, v_x_3835_, v_x_3836_);
lean_dec(v_x_3835_);
lean_dec_ref(v_x_3834_);
v_r_3838_ = lean_box(v_res_3837_);
return v_r_3838_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3839_, lean_object* v_x_3840_, lean_object* v_x_3841_){
_start:
{
switch(lean_obj_tag(v_x_3839_))
{
case 10:
{
lean_object* v_expr_3842_; 
v_expr_3842_ = lean_ctor_get(v_x_3839_, 1);
v_x_3839_ = v_expr_3842_;
goto _start;
}
case 4:
{
lean_object* v_declName_3844_; lean_object* v___x_3845_; uint8_t v___x_3846_; 
v_declName_3844_ = lean_ctor_get(v_x_3839_, 0);
v___x_3845_ = lean_unsigned_to_nat(0u);
v___x_3846_ = lean_nat_dec_eq(v_x_3841_, v___x_3845_);
lean_dec(v_x_3841_);
if (v___x_3846_ == 0)
{
return v___x_3846_;
}
else
{
uint8_t v___x_3847_; 
v___x_3847_ = lean_name_eq(v_declName_3844_, v_x_3840_);
return v___x_3847_;
}
}
case 5:
{
lean_object* v_fn_3848_; lean_object* v_zero_3849_; uint8_t v_isZero_3850_; 
v_fn_3848_ = lean_ctor_get(v_x_3839_, 0);
v_zero_3849_ = lean_unsigned_to_nat(0u);
v_isZero_3850_ = lean_nat_dec_eq(v_x_3841_, v_zero_3849_);
if (v_isZero_3850_ == 0)
{
lean_object* v_one_3851_; lean_object* v_n_3852_; 
v_one_3851_ = lean_unsigned_to_nat(1u);
v_n_3852_ = lean_nat_sub(v_x_3841_, v_one_3851_);
lean_dec(v_x_3841_);
v_x_3839_ = v_fn_3848_;
v_x_3841_ = v_n_3852_;
goto _start;
}
else
{
uint8_t v___x_3854_; 
lean_dec(v_x_3841_);
v___x_3854_ = 0;
return v___x_3854_;
}
}
default: 
{
uint8_t v___x_3855_; 
lean_dec(v_x_3841_);
v___x_3855_ = 0;
return v___x_3855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3856_, lean_object* v_x_3857_, lean_object* v_x_3858_){
_start:
{
uint8_t v_res_3859_; lean_object* v_r_3860_; 
v_res_3859_ = l_Lean_Expr_isAppOfArity_x27(v_x_3856_, v_x_3857_, v_x_3858_);
lean_dec(v_x_3857_);
lean_dec_ref(v_x_3856_);
v_r_3860_ = lean_box(v_res_3859_);
return v_r_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3861_, lean_object* v_x_3862_){
_start:
{
if (lean_obj_tag(v_x_3861_) == 5)
{
lean_object* v_fn_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v_fn_3863_ = lean_ctor_get(v_x_3861_, 0);
v___x_3864_ = lean_unsigned_to_nat(1u);
v___x_3865_ = lean_nat_add(v_x_3862_, v___x_3864_);
lean_dec(v_x_3862_);
v_x_3861_ = v_fn_3863_;
v_x_3862_ = v___x_3865_;
goto _start;
}
else
{
return v_x_3862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3867_, lean_object* v_x_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3867_, v_x_3868_);
lean_dec_ref(v_x_3867_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3870_){
_start:
{
lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3871_ = lean_unsigned_to_nat(0u);
v___x_3872_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3870_, v___x_3871_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_Expr_getAppNumArgs(v_e_3873_);
lean_dec_ref(v_e_3873_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3875_, lean_object* v_a_3876_){
_start:
{
switch(lean_obj_tag(v_a_3875_))
{
case 10:
{
lean_object* v_expr_3877_; 
v_expr_3877_ = lean_ctor_get(v_a_3875_, 1);
v_a_3875_ = v_expr_3877_;
goto _start;
}
case 5:
{
lean_object* v_fn_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v_fn_3879_ = lean_ctor_get(v_a_3875_, 0);
v___x_3880_ = lean_unsigned_to_nat(1u);
v___x_3881_ = lean_nat_add(v_a_3876_, v___x_3880_);
lean_dec(v_a_3876_);
v_a_3875_ = v_fn_3879_;
v_a_3876_ = v___x_3881_;
goto _start;
}
default: 
{
return v_a_3876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3883_, lean_object* v_a_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3883_, v_a_3884_);
lean_dec_ref(v_a_3883_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3886_){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = lean_unsigned_to_nat(0u);
v___x_3888_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3886_, v___x_3887_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3889_);
lean_dec_ref(v_e_3889_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3891_, lean_object* v_x_3892_){
_start:
{
lean_object* v_zero_3893_; uint8_t v_isZero_3894_; 
v_zero_3893_ = lean_unsigned_to_nat(0u);
v_isZero_3894_ = lean_nat_dec_eq(v_x_3891_, v_zero_3893_);
if (v_isZero_3894_ == 0)
{
if (lean_obj_tag(v_x_3892_) == 5)
{
lean_object* v_fn_3895_; lean_object* v_one_3896_; lean_object* v_n_3897_; 
v_fn_3895_ = lean_ctor_get(v_x_3892_, 0);
v_one_3896_ = lean_unsigned_to_nat(1u);
v_n_3897_ = lean_nat_sub(v_x_3891_, v_one_3896_);
lean_dec(v_x_3891_);
v_x_3891_ = v_n_3897_;
v_x_3892_ = v_fn_3895_;
goto _start;
}
else
{
lean_dec(v_x_3891_);
lean_inc_ref(v_x_3892_);
return v_x_3892_;
}
}
else
{
lean_dec(v_x_3891_);
lean_inc_ref(v_x_3892_);
return v_x_3892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_3899_, lean_object* v_x_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Lean_Expr_getBoundedAppFn(v_x_3899_, v_x_3900_);
lean_dec_ref(v_x_3900_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_3902_, lean_object* v_x_3903_, lean_object* v_x_3904_){
_start:
{
if (lean_obj_tag(v_x_3902_) == 5)
{
lean_object* v_fn_3905_; lean_object* v_arg_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v_fn_3905_ = lean_ctor_get(v_x_3902_, 0);
lean_inc_ref(v_fn_3905_);
v_arg_3906_ = lean_ctor_get(v_x_3902_, 1);
lean_inc_ref(v_arg_3906_);
lean_dec_ref(v_x_3902_);
v___x_3907_ = lean_array_set(v_x_3903_, v_x_3904_, v_arg_3906_);
v___x_3908_ = lean_unsigned_to_nat(1u);
v___x_3909_ = lean_nat_sub(v_x_3904_, v___x_3908_);
lean_dec(v_x_3904_);
v_x_3902_ = v_fn_3905_;
v_x_3903_ = v___x_3907_;
v_x_3904_ = v___x_3909_;
goto _start;
}
else
{
lean_dec(v_x_3904_);
lean_dec_ref(v_x_3902_);
return v_x_3903_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_3911_; lean_object* v_dummy_3912_; 
v___x_3911_ = lean_box(0);
v_dummy_3912_ = l_Lean_Expr_sort___override(v___x_3911_);
return v_dummy_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_3913_){
_start:
{
lean_object* v_dummy_3914_; lean_object* v_nargs_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v_dummy_3914_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3915_ = l_Lean_Expr_getAppNumArgs(v_e_3913_);
lean_inc(v_nargs_3915_);
v___x_3916_ = lean_mk_array(v_nargs_3915_, v_dummy_3914_);
v___x_3917_ = lean_unsigned_to_nat(1u);
v___x_3918_ = lean_nat_sub(v_nargs_3915_, v___x_3917_);
lean_dec(v_nargs_3915_);
v___x_3919_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3913_, v___x_3916_, v___x_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_3920_, lean_object* v_x_3921_, lean_object* v_x_3922_){
_start:
{
if (lean_obj_tag(v_x_3920_) == 5)
{
lean_object* v_fn_3923_; lean_object* v_arg_3924_; lean_object* v_zero_3925_; uint8_t v_isZero_3926_; 
v_fn_3923_ = lean_ctor_get(v_x_3920_, 0);
lean_inc_ref(v_fn_3923_);
v_arg_3924_ = lean_ctor_get(v_x_3920_, 1);
lean_inc_ref(v_arg_3924_);
lean_dec_ref(v_x_3920_);
v_zero_3925_ = lean_unsigned_to_nat(0u);
v_isZero_3926_ = lean_nat_dec_eq(v_x_3922_, v_zero_3925_);
if (v_isZero_3926_ == 0)
{
lean_object* v_one_3927_; lean_object* v_n_3928_; lean_object* v___x_3929_; 
v_one_3927_ = lean_unsigned_to_nat(1u);
v_n_3928_ = lean_nat_sub(v_x_3922_, v_one_3927_);
lean_dec(v_x_3922_);
v___x_3929_ = lean_array_set(v_x_3921_, v_n_3928_, v_arg_3924_);
v_x_3920_ = v_fn_3923_;
v_x_3921_ = v___x_3929_;
v_x_3922_ = v_n_3928_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3924_);
lean_dec_ref(v_fn_3923_);
lean_dec(v_x_3922_);
return v_x_3921_;
}
}
else
{
lean_dec(v_x_3922_);
lean_dec_ref(v_x_3920_);
return v_x_3921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_3931_, lean_object* v_e_3932_){
_start:
{
lean_object* v_dummy_3933_; lean_object* v___y_3935_; lean_object* v___x_3938_; uint8_t v___x_3939_; 
v_dummy_3933_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_3938_ = l_Lean_Expr_getAppNumArgs(v_e_3932_);
v___x_3939_ = lean_nat_dec_le(v_maxArgs_3931_, v___x_3938_);
if (v___x_3939_ == 0)
{
lean_dec(v_maxArgs_3931_);
v___y_3935_ = v___x_3938_;
goto v___jp_3934_;
}
else
{
lean_dec(v___x_3938_);
v___y_3935_ = v_maxArgs_3931_;
goto v___jp_3934_;
}
v___jp_3934_:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
lean_inc(v___y_3935_);
v___x_3936_ = lean_mk_array(v___y_3935_, v_dummy_3933_);
v___x_3937_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_3932_, v___x_3936_, v___y_3935_);
return v___x_3937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_3940_, lean_object* v_x_3941_){
_start:
{
if (lean_obj_tag(v_x_3940_) == 5)
{
lean_object* v_fn_3942_; lean_object* v_arg_3943_; lean_object* v___x_3944_; 
v_fn_3942_ = lean_ctor_get(v_x_3940_, 0);
lean_inc_ref(v_fn_3942_);
v_arg_3943_ = lean_ctor_get(v_x_3940_, 1);
lean_inc_ref(v_arg_3943_);
lean_dec_ref(v_x_3940_);
v___x_3944_ = lean_array_push(v_x_3941_, v_arg_3943_);
v_x_3940_ = v_fn_3942_;
v_x_3941_ = v___x_3944_;
goto _start;
}
else
{
lean_dec_ref(v_x_3940_);
return v_x_3941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_3946_){
_start:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3947_ = l_Lean_Expr_getAppNumArgs(v_e_3946_);
v___x_3948_ = lean_mk_empty_array_with_capacity(v___x_3947_);
lean_dec(v___x_3947_);
v___x_3949_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3946_, v___x_3948_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_3950_, lean_object* v_x_3951_, lean_object* v_x_3952_, lean_object* v_x_3953_){
_start:
{
if (lean_obj_tag(v_x_3951_) == 5)
{
lean_object* v_fn_3954_; lean_object* v_arg_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v_fn_3954_ = lean_ctor_get(v_x_3951_, 0);
lean_inc_ref(v_fn_3954_);
v_arg_3955_ = lean_ctor_get(v_x_3951_, 1);
lean_inc_ref(v_arg_3955_);
lean_dec_ref(v_x_3951_);
v___x_3956_ = lean_array_set(v_x_3952_, v_x_3953_, v_arg_3955_);
v___x_3957_ = lean_unsigned_to_nat(1u);
v___x_3958_ = lean_nat_sub(v_x_3953_, v___x_3957_);
lean_dec(v_x_3953_);
v_x_3951_ = v_fn_3954_;
v_x_3952_ = v___x_3956_;
v_x_3953_ = v___x_3958_;
goto _start;
}
else
{
lean_object* v___x_3960_; 
lean_dec(v_x_3953_);
v___x_3960_ = lean_apply_2(v_k_3950_, v_x_3951_, v_x_3952_);
return v___x_3960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_3961_, lean_object* v_k_3962_, lean_object* v_x_3963_, lean_object* v_x_3964_, lean_object* v_x_3965_){
_start:
{
lean_object* v___x_3966_; 
v___x_3966_ = l_Lean_Expr_withAppAux___redArg(v_k_3962_, v_x_3963_, v_x_3964_, v_x_3965_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_3967_, lean_object* v_k_3968_){
_start:
{
lean_object* v_dummy_3969_; lean_object* v_nargs_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v_dummy_3969_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3970_ = l_Lean_Expr_getAppNumArgs(v_e_3967_);
lean_inc(v_nargs_3970_);
v___x_3971_ = lean_mk_array(v_nargs_3970_, v_dummy_3969_);
v___x_3972_ = lean_unsigned_to_nat(1u);
v___x_3973_ = lean_nat_sub(v_nargs_3970_, v___x_3972_);
lean_dec(v_nargs_3970_);
v___x_3974_ = l_Lean_Expr_withAppAux___redArg(v_k_3968_, v_e_3967_, v___x_3971_, v___x_3973_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_3975_, lean_object* v_e_3976_, lean_object* v_k_3977_){
_start:
{
lean_object* v_dummy_3978_; lean_object* v_nargs_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v_dummy_3978_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3979_ = l_Lean_Expr_getAppNumArgs(v_e_3976_);
lean_inc(v_nargs_3979_);
v___x_3980_ = lean_mk_array(v_nargs_3979_, v_dummy_3978_);
v___x_3981_ = lean_unsigned_to_nat(1u);
v___x_3982_ = lean_nat_sub(v_nargs_3979_, v___x_3981_);
lean_dec(v_nargs_3979_);
v___x_3983_ = l_Lean_Expr_withAppAux___redArg(v_k_3977_, v_e_3976_, v___x_3980_, v___x_3982_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_3984_, lean_object* v_x_3985_, lean_object* v_x_3986_){
_start:
{
if (lean_obj_tag(v_x_3984_) == 5)
{
lean_object* v_fn_3987_; lean_object* v_arg_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v_fn_3987_ = lean_ctor_get(v_x_3984_, 0);
lean_inc_ref(v_fn_3987_);
v_arg_3988_ = lean_ctor_get(v_x_3984_, 1);
lean_inc_ref(v_arg_3988_);
lean_dec_ref(v_x_3984_);
v___x_3989_ = lean_array_set(v_x_3985_, v_x_3986_, v_arg_3988_);
v___x_3990_ = lean_unsigned_to_nat(1u);
v___x_3991_ = lean_nat_sub(v_x_3986_, v___x_3990_);
lean_dec(v_x_3986_);
v_x_3984_ = v_fn_3987_;
v_x_3985_ = v___x_3989_;
v_x_3986_ = v___x_3991_;
goto _start;
}
else
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec(v_x_3986_);
v___x_3993_ = l_Lean_Expr_constName(v_x_3984_);
lean_dec_ref(v_x_3984_);
v___x_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
lean_ctor_set(v___x_3994_, 1, v_x_3985_);
return v___x_3994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_3995_){
_start:
{
lean_object* v_dummy_3996_; lean_object* v_nargs_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v_dummy_3996_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3997_ = l_Lean_Expr_getAppNumArgs(v_e_3995_);
lean_inc(v_nargs_3997_);
v___x_3998_ = lean_mk_array(v_nargs_3997_, v_dummy_3996_);
v___x_3999_ = lean_unsigned_to_nat(1u);
v___x_4000_ = lean_nat_sub(v_nargs_3997_, v___x_3999_);
lean_dec(v_nargs_3997_);
v___x_4001_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_3995_, v___x_3998_, v___x_4000_);
return v___x_4001_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4002_; 
v___x_4002_ = l_Array_instInhabited(lean_box(0));
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_4003_){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4004_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_4005_ = lean_panic_fn_borrowed(v___x_4004_, v_msg_4003_);
return v___x_4005_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4008_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_4009_ = lean_unsigned_to_nat(27u);
v___x_4010_ = lean_unsigned_to_nat(1237u);
v___x_4011_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_4012_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4013_ = l_mkPanicMessageWithDecl(v___x_4012_, v___x_4011_, v___x_4010_, v___x_4009_, v___x_4008_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_){
_start:
{
lean_object* v_zero_4017_; uint8_t v_isZero_4018_; 
v_zero_4017_ = lean_unsigned_to_nat(0u);
v_isZero_4018_ = lean_nat_dec_eq(v_a_4014_, v_zero_4017_);
if (v_isZero_4018_ == 1)
{
lean_dec_ref(v_a_4015_);
lean_dec(v_a_4014_);
return v_a_4016_;
}
else
{
if (lean_obj_tag(v_a_4015_) == 5)
{
lean_object* v_fn_4019_; lean_object* v_arg_4020_; lean_object* v_one_4021_; lean_object* v_n_4022_; lean_object* v___x_4023_; 
v_fn_4019_ = lean_ctor_get(v_a_4015_, 0);
lean_inc_ref(v_fn_4019_);
v_arg_4020_ = lean_ctor_get(v_a_4015_, 1);
lean_inc_ref(v_arg_4020_);
lean_dec_ref(v_a_4015_);
v_one_4021_ = lean_unsigned_to_nat(1u);
v_n_4022_ = lean_nat_sub(v_a_4014_, v_one_4021_);
lean_dec(v_a_4014_);
v___x_4023_ = lean_array_set(v_a_4016_, v_n_4022_, v_arg_4020_);
v_a_4014_ = v_n_4022_;
v_a_4015_ = v_fn_4019_;
v_a_4016_ = v___x_4023_;
goto _start;
}
else
{
lean_object* v___x_4025_; lean_object* v___x_4026_; 
lean_dec_ref(v_a_4016_);
lean_dec_ref(v_a_4015_);
lean_dec(v_a_4014_);
v___x_4025_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_4026_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_4025_);
return v___x_4026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_4027_, lean_object* v_n_4028_){
_start:
{
lean_object* v_dummy_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v_dummy_4029_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_4028_);
v___x_4030_ = lean_mk_array(v_n_4028_, v_dummy_4029_);
v___x_4031_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_4028_, v_e_4027_, v___x_4030_);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_4032_, lean_object* v_n_4033_){
_start:
{
lean_object* v_zero_4034_; uint8_t v_isZero_4035_; 
v_zero_4034_ = lean_unsigned_to_nat(0u);
v_isZero_4035_ = lean_nat_dec_eq(v_n_4033_, v_zero_4034_);
if (v_isZero_4035_ == 1)
{
lean_dec(v_n_4033_);
lean_inc_ref(v_e_4032_);
return v_e_4032_;
}
else
{
if (lean_obj_tag(v_e_4032_) == 5)
{
lean_object* v_fn_4036_; lean_object* v_one_4037_; lean_object* v_n_4038_; 
v_fn_4036_ = lean_ctor_get(v_e_4032_, 0);
v_one_4037_ = lean_unsigned_to_nat(1u);
v_n_4038_ = lean_nat_sub(v_n_4033_, v_one_4037_);
lean_dec(v_n_4033_);
v_e_4032_ = v_fn_4036_;
v_n_4033_ = v_n_4038_;
goto _start;
}
else
{
lean_dec(v_n_4033_);
lean_inc_ref(v_e_4032_);
return v_e_4032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_4040_, lean_object* v_n_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l_Lean_Expr_stripArgsN(v_e_4040_, v_n_4041_);
lean_dec_ref(v_e_4040_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_4043_, lean_object* v_n_4044_){
_start:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4045_ = l_Lean_Expr_getAppNumArgs(v_e_4043_);
v___x_4046_ = lean_nat_sub(v___x_4045_, v_n_4044_);
lean_dec(v___x_4045_);
v___x_4047_ = l_Lean_Expr_stripArgsN(v_e_4043_, v___x_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_4048_, lean_object* v_n_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_Expr_getAppPrefix(v_e_4048_, v_n_4049_);
lean_dec(v_n_4049_);
lean_dec_ref(v_e_4048_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_4051_, lean_object* v_inst_4052_, lean_object* v_f_4053_, lean_object* v_x_4054_){
_start:
{
size_t v_sz_4055_; size_t v___x_4056_; lean_object* v___x_4057_; 
v_sz_4055_ = lean_array_size(v_args_4051_);
v___x_4056_ = ((size_t)0ULL);
v___x_4057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4052_, v_f_4053_, v_sz_4055_, v___x_4056_, v_args_4051_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_4059_, lean_object* v_inst_4060_, lean_object* v_f_4061_, lean_object* v_toSeq_4062_, lean_object* v_fn_4063_, lean_object* v_args_4064_){
_start:
{
lean_object* v_map_4065_; lean_object* v___f_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v_map_4065_ = lean_ctor_get(v_toFunctor_4059_, 0);
lean_inc(v_map_4065_);
lean_dec_ref(v_toFunctor_4059_);
lean_inc(v_f_4061_);
v___f_4066_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4066_, 0, v_args_4064_);
lean_closure_set(v___f_4066_, 1, v_inst_4060_);
lean_closure_set(v___f_4066_, 2, v_f_4061_);
v___x_4067_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_4068_ = lean_apply_1(v_f_4061_, v_fn_4063_);
v___x_4069_ = lean_apply_4(v_map_4065_, lean_box(0), lean_box(0), v___x_4067_, v___x_4068_);
v___x_4070_ = lean_apply_4(v_toSeq_4062_, lean_box(0), lean_box(0), v___x_4069_, v___f_4066_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_4071_, lean_object* v_f_4072_, lean_object* v_e_4073_){
_start:
{
lean_object* v_toApplicative_4074_; lean_object* v_toFunctor_4075_; lean_object* v_toSeq_4076_; lean_object* v___f_4077_; lean_object* v_dummy_4078_; lean_object* v_nargs_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v_toApplicative_4074_ = lean_ctor_get(v_inst_4071_, 0);
v_toFunctor_4075_ = lean_ctor_get(v_toApplicative_4074_, 0);
lean_inc_ref(v_toFunctor_4075_);
v_toSeq_4076_ = lean_ctor_get(v_toApplicative_4074_, 2);
lean_inc(v_toSeq_4076_);
v___f_4077_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_4077_, 0, v_toFunctor_4075_);
lean_closure_set(v___f_4077_, 1, v_inst_4071_);
lean_closure_set(v___f_4077_, 2, v_f_4072_);
lean_closure_set(v___f_4077_, 3, v_toSeq_4076_);
v_dummy_4078_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4079_ = l_Lean_Expr_getAppNumArgs(v_e_4073_);
lean_inc(v_nargs_4079_);
v___x_4080_ = lean_mk_array(v_nargs_4079_, v_dummy_4078_);
v___x_4081_ = lean_unsigned_to_nat(1u);
v___x_4082_ = lean_nat_sub(v_nargs_4079_, v___x_4081_);
lean_dec(v_nargs_4079_);
v___x_4083_ = l_Lean_Expr_withAppAux___redArg(v___f_4077_, v_e_4073_, v___x_4080_, v___x_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_4084_, lean_object* v_inst_4085_, lean_object* v_f_4086_, lean_object* v_e_4087_){
_start:
{
lean_object* v___x_4088_; 
v___x_4088_ = l_Lean_Expr_traverseApp___redArg(v_inst_4085_, v_f_4086_, v_e_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_4089_, lean_object* v_x_4090_, lean_object* v_x_4091_){
_start:
{
if (lean_obj_tag(v_x_4090_) == 5)
{
lean_object* v_fn_4092_; lean_object* v_arg_4093_; lean_object* v___x_4094_; 
v_fn_4092_ = lean_ctor_get(v_x_4090_, 0);
lean_inc_ref(v_fn_4092_);
v_arg_4093_ = lean_ctor_get(v_x_4090_, 1);
lean_inc_ref(v_arg_4093_);
lean_dec_ref(v_x_4090_);
v___x_4094_ = lean_array_push(v_x_4091_, v_arg_4093_);
v_x_4090_ = v_fn_4092_;
v_x_4091_ = v___x_4094_;
goto _start;
}
else
{
lean_object* v___x_4096_; 
v___x_4096_ = lean_apply_2(v_k_4089_, v_x_4090_, v_x_4091_);
return v___x_4096_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_4097_, lean_object* v_k_4098_, lean_object* v_x_4099_, lean_object* v_x_4100_){
_start:
{
lean_object* v___x_4101_; 
v___x_4101_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4098_, v_x_4099_, v_x_4100_);
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_4102_, lean_object* v_k_4103_){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4104_ = l_Lean_Expr_getAppNumArgs(v_e_4102_);
v___x_4105_ = lean_mk_empty_array_with_capacity(v___x_4104_);
lean_dec(v___x_4104_);
v___x_4106_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4103_, v_e_4102_, v___x_4105_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_4107_, lean_object* v_e_4108_, lean_object* v_k_4109_){
_start:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4110_ = l_Lean_Expr_getAppNumArgs(v_e_4108_);
v___x_4111_ = lean_mk_empty_array_with_capacity(v___x_4110_);
lean_dec(v___x_4110_);
v___x_4112_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4109_, v_e_4108_, v___x_4111_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_4113_, lean_object* v_x_4114_, lean_object* v_x_4115_){
_start:
{
if (lean_obj_tag(v_x_4113_) == 5)
{
lean_object* v_fn_4116_; lean_object* v_arg_4117_; lean_object* v_zero_4118_; uint8_t v_isZero_4119_; 
v_fn_4116_ = lean_ctor_get(v_x_4113_, 0);
v_arg_4117_ = lean_ctor_get(v_x_4113_, 1);
v_zero_4118_ = lean_unsigned_to_nat(0u);
v_isZero_4119_ = lean_nat_dec_eq(v_x_4114_, v_zero_4118_);
if (v_isZero_4119_ == 1)
{
lean_dec(v_x_4114_);
lean_inc_ref(v_arg_4117_);
return v_arg_4117_;
}
else
{
lean_object* v_one_4120_; lean_object* v_n_4121_; 
v_one_4120_ = lean_unsigned_to_nat(1u);
v_n_4121_ = lean_nat_sub(v_x_4114_, v_one_4120_);
lean_dec(v_x_4114_);
v_x_4113_ = v_fn_4116_;
v_x_4114_ = v_n_4121_;
goto _start;
}
}
else
{
lean_dec(v_x_4114_);
lean_inc_ref(v_x_4115_);
return v_x_4115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_4123_, lean_object* v_x_4124_, lean_object* v_x_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_Expr_getRevArgD(v_x_4123_, v_x_4124_, v_x_4125_);
lean_dec_ref(v_x_4125_);
lean_dec_ref(v_x_4123_);
return v_res_4126_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4129_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4130_ = lean_unsigned_to_nat(20u);
v___x_4131_ = lean_unsigned_to_nat(1278u);
v___x_4132_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4133_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4134_ = l_mkPanicMessageWithDecl(v___x_4133_, v___x_4132_, v___x_4131_, v___x_4130_, v___x_4129_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4135_, lean_object* v_x_4136_){
_start:
{
if (lean_obj_tag(v_x_4135_) == 5)
{
lean_object* v_fn_4137_; lean_object* v_arg_4138_; lean_object* v_zero_4139_; uint8_t v_isZero_4140_; 
v_fn_4137_ = lean_ctor_get(v_x_4135_, 0);
v_arg_4138_ = lean_ctor_get(v_x_4135_, 1);
v_zero_4139_ = lean_unsigned_to_nat(0u);
v_isZero_4140_ = lean_nat_dec_eq(v_x_4136_, v_zero_4139_);
if (v_isZero_4140_ == 1)
{
lean_dec(v_x_4136_);
lean_inc_ref(v_arg_4138_);
return v_arg_4138_;
}
else
{
lean_object* v_one_4141_; lean_object* v_n_4142_; 
v_one_4141_ = lean_unsigned_to_nat(1u);
v_n_4142_ = lean_nat_sub(v_x_4136_, v_one_4141_);
lean_dec(v_x_4136_);
v_x_4135_ = v_fn_4137_;
v_x_4136_ = v_n_4142_;
goto _start;
}
}
else
{
lean_object* v___x_4144_; lean_object* v___x_4145_; 
lean_dec(v_x_4136_);
v___x_4144_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4145_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4144_);
return v___x_4145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4146_, lean_object* v_x_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Lean_Expr_getRevArg_x21(v_x_4146_, v_x_4147_);
lean_dec_ref(v_x_4146_);
return v_res_4148_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4150_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4151_ = lean_unsigned_to_nat(20u);
v___x_4152_ = lean_unsigned_to_nat(1285u);
v___x_4153_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4154_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4155_ = l_mkPanicMessageWithDecl(v___x_4154_, v___x_4153_, v___x_4152_, v___x_4151_, v___x_4150_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4156_, lean_object* v_x_4157_){
_start:
{
switch(lean_obj_tag(v_x_4156_))
{
case 10:
{
lean_object* v_expr_4158_; 
v_expr_4158_ = lean_ctor_get(v_x_4156_, 1);
v_x_4156_ = v_expr_4158_;
goto _start;
}
case 5:
{
lean_object* v_fn_4160_; lean_object* v_arg_4161_; lean_object* v_zero_4162_; uint8_t v_isZero_4163_; 
v_fn_4160_ = lean_ctor_get(v_x_4156_, 0);
v_arg_4161_ = lean_ctor_get(v_x_4156_, 1);
v_zero_4162_ = lean_unsigned_to_nat(0u);
v_isZero_4163_ = lean_nat_dec_eq(v_x_4157_, v_zero_4162_);
if (v_isZero_4163_ == 1)
{
lean_dec(v_x_4157_);
lean_inc_ref(v_arg_4161_);
return v_arg_4161_;
}
else
{
lean_object* v_one_4164_; lean_object* v_n_4165_; 
v_one_4164_ = lean_unsigned_to_nat(1u);
v_n_4165_ = lean_nat_sub(v_x_4157_, v_one_4164_);
lean_dec(v_x_4157_);
v_x_4156_ = v_fn_4160_;
v_x_4157_ = v_n_4165_;
goto _start;
}
}
default: 
{
lean_object* v___x_4167_; lean_object* v___x_4168_; 
lean_dec(v_x_4157_);
v___x_4167_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4168_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4167_);
return v___x_4168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4169_, lean_object* v_x_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4169_, v_x_4170_);
lean_dec_ref(v_x_4169_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4172_, lean_object* v_i_4173_, lean_object* v_n_4174_){
_start:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4175_ = lean_nat_sub(v_n_4174_, v_i_4173_);
v___x_4176_ = lean_unsigned_to_nat(1u);
v___x_4177_ = lean_nat_sub(v___x_4175_, v___x_4176_);
lean_dec(v___x_4175_);
v___x_4178_ = l_Lean_Expr_getRevArg_x21(v_e_4172_, v___x_4177_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4179_, lean_object* v_i_4180_, lean_object* v_n_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l_Lean_Expr_getArg_x21(v_e_4179_, v_i_4180_, v_n_4181_);
lean_dec(v_n_4181_);
lean_dec(v_i_4180_);
lean_dec_ref(v_e_4179_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4183_, lean_object* v_i_4184_, lean_object* v_n_4185_){
_start:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4186_ = lean_nat_sub(v_n_4185_, v_i_4184_);
v___x_4187_ = lean_unsigned_to_nat(1u);
v___x_4188_ = lean_nat_sub(v___x_4186_, v___x_4187_);
lean_dec(v___x_4186_);
v___x_4189_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4183_, v___x_4188_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4190_, lean_object* v_i_4191_, lean_object* v_n_4192_){
_start:
{
lean_object* v_res_4193_; 
v_res_4193_ = l_Lean_Expr_getArg_x21_x27(v_e_4190_, v_i_4191_, v_n_4192_);
lean_dec(v_n_4192_);
lean_dec(v_i_4191_);
lean_dec_ref(v_e_4190_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4194_, lean_object* v_i_4195_, lean_object* v_v_u2080_4196_, lean_object* v_n_4197_){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4198_ = lean_nat_sub(v_n_4197_, v_i_4195_);
v___x_4199_ = lean_unsigned_to_nat(1u);
v___x_4200_ = lean_nat_sub(v___x_4198_, v___x_4199_);
lean_dec(v___x_4198_);
v___x_4201_ = l_Lean_Expr_getRevArgD(v_e_4194_, v___x_4200_, v_v_u2080_4196_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4202_, lean_object* v_i_4203_, lean_object* v_v_u2080_4204_, lean_object* v_n_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l_Lean_Expr_getArgD(v_e_4202_, v_i_4203_, v_v_u2080_4204_, v_n_4205_);
lean_dec(v_n_4205_);
lean_dec_ref(v_v_u2080_4204_);
lean_dec(v_i_4203_);
lean_dec_ref(v_e_4202_);
return v_res_4206_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4207_){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; 
v___x_4208_ = lean_unsigned_to_nat(0u);
v___x_4209_ = l_Lean_Expr_looseBVarRange(v_e_4207_);
v___x_4210_ = lean_nat_dec_lt(v___x_4208_, v___x_4209_);
lean_dec(v___x_4209_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4211_){
_start:
{
uint8_t v_res_4212_; lean_object* v_r_4213_; 
v_res_4212_ = l_Lean_Expr_hasLooseBVars(v_e_4211_);
lean_dec_ref(v_e_4211_);
v_r_4213_ = lean_box(v_res_4212_);
return v_r_4213_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4214_){
_start:
{
if (lean_obj_tag(v_e_4214_) == 7)
{
lean_object* v_body_4215_; uint8_t v___x_4216_; 
v_body_4215_ = lean_ctor_get(v_e_4214_, 2);
v___x_4216_ = l_Lean_Expr_hasLooseBVars(v_body_4215_);
if (v___x_4216_ == 0)
{
uint8_t v___x_4217_; 
v___x_4217_ = 1;
return v___x_4217_;
}
else
{
uint8_t v___x_4218_; 
v___x_4218_ = 0;
return v___x_4218_;
}
}
else
{
uint8_t v___x_4219_; 
v___x_4219_ = 0;
return v___x_4219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4220_){
_start:
{
uint8_t v_res_4221_; lean_object* v_r_4222_; 
v_res_4221_ = l_Lean_Expr_isArrow(v_e_4220_);
lean_dec_ref(v_e_4220_);
v_r_4222_ = lean_box(v_res_4221_);
return v_r_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4225_, lean_object* v_bvarIdx_4226_){
_start:
{
uint8_t v_res_4227_; lean_object* v_r_4228_; 
v_res_4227_ = lean_expr_has_loose_bvar(v_e_4225_, v_bvarIdx_4226_);
lean_dec(v_bvarIdx_4226_);
lean_dec_ref(v_e_4225_);
v_r_4228_ = lean_box(v_res_4227_);
return v_r_4228_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4229_, lean_object* v_bvarIdx_4230_, uint8_t v_considerRange_4231_){
_start:
{
if (lean_obj_tag(v_e_4229_) == 7)
{
lean_object* v_binderType_4232_; lean_object* v_body_4233_; uint8_t v_binderInfo_4234_; uint8_t v___y_4236_; uint8_t v___x_4240_; 
v_binderType_4232_ = lean_ctor_get(v_e_4229_, 1);
v_body_4233_ = lean_ctor_get(v_e_4229_, 2);
v_binderInfo_4234_ = lean_ctor_get_uint8(v_e_4229_, sizeof(void*)*3 + 8);
v___x_4240_ = lean_expr_has_loose_bvar(v_binderType_4232_, v_bvarIdx_4230_);
if (v___x_4240_ == 0)
{
v___y_4236_ = v___x_4240_;
goto v___jp_4235_;
}
else
{
uint8_t v___x_4241_; 
v___x_4241_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4234_);
if (v___x_4241_ == 0)
{
lean_object* v___x_4242_; uint8_t v___x_4243_; 
v___x_4242_ = lean_unsigned_to_nat(0u);
v___x_4243_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4233_, v___x_4242_, v_considerRange_4231_);
v___y_4236_ = v___x_4243_;
goto v___jp_4235_;
}
else
{
v___y_4236_ = v___x_4241_;
goto v___jp_4235_;
}
}
v___jp_4235_:
{
if (v___y_4236_ == 0)
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4237_ = lean_unsigned_to_nat(1u);
v___x_4238_ = lean_nat_add(v_bvarIdx_4230_, v___x_4237_);
lean_dec(v_bvarIdx_4230_);
v_e_4229_ = v_body_4233_;
v_bvarIdx_4230_ = v___x_4238_;
goto _start;
}
else
{
lean_dec(v_bvarIdx_4230_);
return v___y_4236_;
}
}
}
else
{
if (v_considerRange_4231_ == 0)
{
lean_dec(v_bvarIdx_4230_);
return v_considerRange_4231_;
}
else
{
uint8_t v___x_4244_; 
v___x_4244_ = lean_expr_has_loose_bvar(v_e_4229_, v_bvarIdx_4230_);
lean_dec(v_bvarIdx_4230_);
return v___x_4244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4245_, lean_object* v_bvarIdx_4246_, lean_object* v_considerRange_4247_){
_start:
{
uint8_t v_considerRange_boxed_4248_; uint8_t v_res_4249_; lean_object* v_r_4250_; 
v_considerRange_boxed_4248_ = lean_unbox(v_considerRange_4247_);
v_res_4249_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4245_, v_bvarIdx_4246_, v_considerRange_boxed_4248_);
lean_dec_ref(v_e_4245_);
v_r_4250_ = lean_box(v_res_4249_);
return v_r_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4254_, lean_object* v_s_4255_, lean_object* v_d_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = lean_expr_lower_loose_bvars(v_e_4254_, v_s_4255_, v_d_4256_);
lean_dec(v_d_4256_);
lean_dec(v_s_4255_);
lean_dec_ref(v_e_4254_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4261_, lean_object* v_s_4262_, lean_object* v_d_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = lean_expr_lift_loose_bvars(v_e_4261_, v_s_4262_, v_d_4263_);
lean_dec(v_d_4263_);
lean_dec(v_s_4262_);
lean_dec_ref(v_e_4261_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4265_, lean_object* v_numParams_4266_, uint8_t v_considerRange_4267_){
_start:
{
if (lean_obj_tag(v_e_4265_) == 7)
{
lean_object* v_binderName_4268_; lean_object* v_binderType_4269_; lean_object* v_body_4270_; uint8_t v_binderInfo_4271_; lean_object* v_zero_4272_; uint8_t v_isZero_4273_; 
v_binderName_4268_ = lean_ctor_get(v_e_4265_, 0);
v_binderType_4269_ = lean_ctor_get(v_e_4265_, 1);
v_body_4270_ = lean_ctor_get(v_e_4265_, 2);
v_binderInfo_4271_ = lean_ctor_get_uint8(v_e_4265_, sizeof(void*)*3 + 8);
v_zero_4272_ = lean_unsigned_to_nat(0u);
v_isZero_4273_ = lean_nat_dec_eq(v_numParams_4266_, v_zero_4272_);
if (v_isZero_4273_ == 0)
{
lean_object* v_one_4274_; lean_object* v_n_4275_; lean_object* v_b_4276_; uint8_t v___y_4278_; uint8_t v___x_4282_; 
lean_inc_ref(v_body_4270_);
lean_inc_ref(v_binderType_4269_);
lean_inc(v_binderName_4268_);
lean_dec_ref(v_e_4265_);
v_one_4274_ = lean_unsigned_to_nat(1u);
v_n_4275_ = lean_nat_sub(v_numParams_4266_, v_one_4274_);
v_b_4276_ = l_Lean_Expr_inferImplicit(v_body_4270_, v_n_4275_, v_considerRange_4267_);
lean_dec(v_n_4275_);
v___x_4282_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4271_);
if (v___x_4282_ == 0)
{
v___y_4278_ = v___x_4282_;
goto v___jp_4277_;
}
else
{
uint8_t v___x_4283_; 
v___x_4283_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4276_, v_zero_4272_, v_considerRange_4267_);
v___y_4278_ = v___x_4283_;
goto v___jp_4277_;
}
v___jp_4277_:
{
if (v___y_4278_ == 0)
{
lean_object* v___x_4279_; 
v___x_4279_ = l_Lean_Expr_forallE___override(v_binderName_4268_, v_binderType_4269_, v_b_4276_, v_binderInfo_4271_);
return v___x_4279_;
}
else
{
uint8_t v___x_4280_; lean_object* v___x_4281_; 
v___x_4280_ = 1;
v___x_4281_ = l_Lean_Expr_forallE___override(v_binderName_4268_, v_binderType_4269_, v_b_4276_, v___x_4280_);
return v___x_4281_;
}
}
}
else
{
return v_e_4265_;
}
}
else
{
return v_e_4265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4284_, lean_object* v_numParams_4285_, lean_object* v_considerRange_4286_){
_start:
{
uint8_t v_considerRange_boxed_4287_; lean_object* v_res_4288_; 
v_considerRange_boxed_4287_ = lean_unbox(v_considerRange_4286_);
v_res_4288_ = l_Lean_Expr_inferImplicit(v_e_4284_, v_numParams_4285_, v_considerRange_boxed_4287_);
lean_dec(v_numParams_4285_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4289_, lean_object* v_binderInfos_x3f_4290_){
_start:
{
if (lean_obj_tag(v_e_4289_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4290_) == 1)
{
lean_object* v_binderName_4291_; lean_object* v_binderType_4292_; lean_object* v_body_4293_; uint8_t v_binderInfo_4294_; lean_object* v_head_4295_; lean_object* v_tail_4296_; lean_object* v_b_4297_; 
v_binderName_4291_ = lean_ctor_get(v_e_4289_, 0);
lean_inc(v_binderName_4291_);
v_binderType_4292_ = lean_ctor_get(v_e_4289_, 1);
lean_inc_ref(v_binderType_4292_);
v_body_4293_ = lean_ctor_get(v_e_4289_, 2);
lean_inc_ref(v_body_4293_);
v_binderInfo_4294_ = lean_ctor_get_uint8(v_e_4289_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_4289_);
v_head_4295_ = lean_ctor_get(v_binderInfos_x3f_4290_, 0);
v_tail_4296_ = lean_ctor_get(v_binderInfos_x3f_4290_, 1);
v_b_4297_ = l_Lean_Expr_updateForallBinderInfos(v_body_4293_, v_tail_4296_);
if (lean_obj_tag(v_head_4295_) == 0)
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Lean_Expr_forallE___override(v_binderName_4291_, v_binderType_4292_, v_b_4297_, v_binderInfo_4294_);
return v___x_4298_;
}
else
{
lean_object* v_val_4299_; uint8_t v___x_4300_; lean_object* v___x_4301_; 
v_val_4299_ = lean_ctor_get(v_head_4295_, 0);
v___x_4300_ = lean_unbox(v_val_4299_);
v___x_4301_ = l_Lean_Expr_forallE___override(v_binderName_4291_, v_binderType_4292_, v_b_4297_, v___x_4300_);
return v___x_4301_;
}
}
else
{
return v_e_4289_;
}
}
else
{
return v_e_4289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4302_, lean_object* v_binderInfos_x3f_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = l_Lean_Expr_updateForallBinderInfos(v_e_4302_, v_binderInfos_x3f_4303_);
lean_dec(v_binderInfos_x3f_4303_);
return v_res_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4305_, lean_object* v_binderNames_x3f_4306_){
_start:
{
switch(lean_obj_tag(v_e_4305_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4306_) == 1)
{
lean_object* v_binderName_4307_; lean_object* v_binderType_4308_; lean_object* v_body_4309_; uint8_t v_binderInfo_4310_; lean_object* v_head_4311_; lean_object* v_tail_4312_; lean_object* v_b_4313_; 
v_binderName_4307_ = lean_ctor_get(v_e_4305_, 0);
lean_inc(v_binderName_4307_);
v_binderType_4308_ = lean_ctor_get(v_e_4305_, 1);
lean_inc_ref(v_binderType_4308_);
v_body_4309_ = lean_ctor_get(v_e_4305_, 2);
lean_inc_ref(v_body_4309_);
v_binderInfo_4310_ = lean_ctor_get_uint8(v_e_4305_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_4305_);
v_head_4311_ = lean_ctor_get(v_binderNames_x3f_4306_, 0);
lean_inc(v_head_4311_);
v_tail_4312_ = lean_ctor_get(v_binderNames_x3f_4306_, 1);
lean_inc(v_tail_4312_);
lean_dec_ref(v_binderNames_x3f_4306_);
v_b_4313_ = l_Lean_Expr_updateBinderNames(v_body_4309_, v_tail_4312_);
if (lean_obj_tag(v_head_4311_) == 0)
{
lean_object* v___x_4314_; 
v___x_4314_ = l_Lean_Expr_forallE___override(v_binderName_4307_, v_binderType_4308_, v_b_4313_, v_binderInfo_4310_);
return v___x_4314_;
}
else
{
lean_object* v_val_4315_; lean_object* v___x_4316_; 
lean_dec(v_binderName_4307_);
v_val_4315_ = lean_ctor_get(v_head_4311_, 0);
lean_inc(v_val_4315_);
lean_dec_ref(v_head_4311_);
v___x_4316_ = l_Lean_Expr_forallE___override(v_val_4315_, v_binderType_4308_, v_b_4313_, v_binderInfo_4310_);
return v___x_4316_;
}
}
else
{
lean_dec(v_binderNames_x3f_4306_);
return v_e_4305_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4306_) == 1)
{
lean_object* v_binderName_4317_; lean_object* v_binderType_4318_; lean_object* v_body_4319_; uint8_t v_binderInfo_4320_; lean_object* v_head_4321_; lean_object* v_tail_4322_; lean_object* v_b_4323_; 
v_binderName_4317_ = lean_ctor_get(v_e_4305_, 0);
lean_inc(v_binderName_4317_);
v_binderType_4318_ = lean_ctor_get(v_e_4305_, 1);
lean_inc_ref(v_binderType_4318_);
v_body_4319_ = lean_ctor_get(v_e_4305_, 2);
lean_inc_ref(v_body_4319_);
v_binderInfo_4320_ = lean_ctor_get_uint8(v_e_4305_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_4305_);
v_head_4321_ = lean_ctor_get(v_binderNames_x3f_4306_, 0);
lean_inc(v_head_4321_);
v_tail_4322_ = lean_ctor_get(v_binderNames_x3f_4306_, 1);
lean_inc(v_tail_4322_);
lean_dec_ref(v_binderNames_x3f_4306_);
v_b_4323_ = l_Lean_Expr_updateBinderNames(v_body_4319_, v_tail_4322_);
if (lean_obj_tag(v_head_4321_) == 0)
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Lean_Expr_lam___override(v_binderName_4317_, v_binderType_4318_, v_b_4323_, v_binderInfo_4320_);
return v___x_4324_;
}
else
{
lean_object* v_val_4325_; lean_object* v___x_4326_; 
lean_dec(v_binderName_4317_);
v_val_4325_ = lean_ctor_get(v_head_4321_, 0);
lean_inc(v_val_4325_);
lean_dec_ref(v_head_4321_);
v___x_4326_ = l_Lean_Expr_lam___override(v_val_4325_, v_binderType_4318_, v_b_4323_, v_binderInfo_4320_);
return v___x_4326_;
}
}
else
{
lean_dec(v_binderNames_x3f_4306_);
return v_e_4305_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4306_);
return v_e_4305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4329_, lean_object* v_subst_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = lean_expr_instantiate(v_e_4329_, v_subst_4330_);
lean_dec_ref(v_subst_4330_);
lean_dec_ref(v_e_4329_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4334_, lean_object* v_subst_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = lean_expr_instantiate1(v_e_4334_, v_subst_4335_);
lean_dec_ref(v_subst_4335_);
lean_dec_ref(v_e_4334_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4339_, lean_object* v_subst_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = lean_expr_instantiate_rev(v_e_4339_, v_subst_4340_);
lean_dec_ref(v_subst_4340_);
lean_dec_ref(v_e_4339_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4346_, lean_object* v_beginIdx_4347_, lean_object* v_endIdx_4348_, lean_object* v_subst_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = lean_expr_instantiate_range(v_e_4346_, v_beginIdx_4347_, v_endIdx_4348_, v_subst_4349_);
lean_dec_ref(v_subst_4349_);
lean_dec(v_endIdx_4348_);
lean_dec(v_beginIdx_4347_);
lean_dec_ref(v_e_4346_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4355_, lean_object* v_beginIdx_4356_, lean_object* v_endIdx_4357_, lean_object* v_subst_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = lean_expr_instantiate_rev_range(v_e_4355_, v_beginIdx_4356_, v_endIdx_4357_, v_subst_4358_);
lean_dec_ref(v_subst_4358_);
lean_dec(v_endIdx_4357_);
lean_dec(v_beginIdx_4356_);
lean_dec_ref(v_e_4355_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4362_, lean_object* v_xs_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = lean_expr_abstract(v_e_4362_, v_xs_4363_);
lean_dec_ref(v_xs_4363_);
lean_dec_ref(v_e_4362_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4368_, lean_object* v_n_4369_, lean_object* v_xs_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = lean_expr_abstract_range(v_e_4368_, v_n_4369_, v_xs_4370_);
lean_dec_ref(v_xs_4370_);
lean_dec(v_n_4369_);
lean_dec_ref(v_e_4368_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4372_, lean_object* v_fvar_4373_, lean_object* v_v_4374_){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4375_ = lean_unsigned_to_nat(1u);
v___x_4376_ = lean_mk_empty_array_with_capacity(v___x_4375_);
v___x_4377_ = lean_array_push(v___x_4376_, v_fvar_4373_);
v___x_4378_ = lean_expr_abstract(v_e_4372_, v___x_4377_);
lean_dec_ref(v___x_4377_);
v___x_4379_ = lean_expr_instantiate1(v___x_4378_, v_v_4374_);
lean_dec_ref(v___x_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4380_, lean_object* v_fvar_4381_, lean_object* v_v_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_Lean_Expr_replaceFVar(v_e_4380_, v_fvar_4381_, v_v_4382_);
lean_dec_ref(v_v_4382_);
lean_dec_ref(v_e_4380_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4384_, lean_object* v_fvarId_4385_, lean_object* v_v_4386_){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4387_ = l_Lean_Expr_fvar___override(v_fvarId_4385_);
v___x_4388_ = l_Lean_Expr_replaceFVar(v_e_4384_, v___x_4387_, v_v_4386_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4389_, lean_object* v_fvarId_4390_, lean_object* v_v_4391_){
_start:
{
lean_object* v_res_4392_; 
v_res_4392_ = l_Lean_Expr_replaceFVarId(v_e_4389_, v_fvarId_4390_, v_v_4391_);
lean_dec_ref(v_v_4391_);
lean_dec_ref(v_e_4389_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4393_, lean_object* v_fvars_4394_, lean_object* v_vs_4395_){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4396_ = lean_expr_abstract(v_e_4393_, v_fvars_4394_);
v___x_4397_ = lean_expr_instantiate_rev(v___x_4396_, v_vs_4395_);
lean_dec_ref(v___x_4396_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4398_, lean_object* v_fvars_4399_, lean_object* v_vs_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_Lean_Expr_replaceFVars(v_e_4398_, v_fvars_4399_, v_vs_4400_);
lean_dec_ref(v_vs_4400_);
lean_dec_ref(v_fvars_4399_);
lean_dec_ref(v_e_4398_);
return v_res_4401_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4404_){
_start:
{
switch(lean_obj_tag(v_x_4404_))
{
case 4:
{
uint8_t v___x_4405_; 
v___x_4405_ = 1;
return v___x_4405_;
}
case 3:
{
uint8_t v___x_4406_; 
v___x_4406_ = 1;
return v___x_4406_;
}
case 0:
{
uint8_t v___x_4407_; 
v___x_4407_ = 1;
return v___x_4407_;
}
case 9:
{
uint8_t v___x_4408_; 
v___x_4408_ = 1;
return v___x_4408_;
}
case 2:
{
uint8_t v___x_4409_; 
v___x_4409_ = 1;
return v___x_4409_;
}
case 1:
{
uint8_t v___x_4410_; 
v___x_4410_ = 1;
return v___x_4410_;
}
default: 
{
uint8_t v___x_4411_; 
v___x_4411_ = 0;
return v___x_4411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4412_){
_start:
{
uint8_t v_res_4413_; lean_object* v_r_4414_; 
v_res_4413_ = l_Lean_Expr_isAtomic(v_x_4412_);
lean_dec_ref(v_x_4412_);
v_r_4414_ = lean_box(v_res_4413_);
return v_r_4414_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4420_ = lean_box(0);
v___x_4421_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4422_ = l_Lean_Expr_const___override(v___x_4421_, v___x_4420_);
return v___x_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4423_, lean_object* v_proof_4424_){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4425_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4426_ = l_Lean_mkAppB(v___x_4425_, v_pred_4423_, v_proof_4424_);
return v___x_4426_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4431_ = lean_box(0);
v___x_4432_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4433_ = l_Lean_Expr_const___override(v___x_4432_, v___x_4431_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4434_, lean_object* v_proof_4435_){
_start:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4436_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4437_ = l_Lean_mkAppB(v___x_4436_, v_pred_4434_, v_proof_4435_);
return v___x_4437_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4438_; 
v___x_4438_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4438_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4440_){
_start:
{
lean_inc_ref(v_val_4440_);
return v_val_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4441_);
lean_dec_ref(v_val_4441_);
return v_res_4442_;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4445_, lean_object* v_x_4446_){
_start:
{
uint8_t v___x_4447_; 
v___x_4447_ = lean_expr_equal(v_x_4445_, v_x_4446_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4448_, lean_object* v_x_4449_){
_start:
{
uint8_t v_res_4450_; lean_object* v_r_4451_; 
v_res_4450_ = l_Lean_ExprStructEq_beq(v_x_4448_, v_x_4449_);
lean_dec_ref(v_x_4449_);
lean_dec_ref(v_x_4448_);
v_r_4451_ = lean_box(v_res_4450_);
return v_r_4451_;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4452_){
_start:
{
uint64_t v___x_4453_; 
v___x_4453_ = l_Lean_Expr_hash(v_x_4452_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4454_){
_start:
{
uint64_t v_res_4455_; lean_object* v_r_4456_; 
v_res_4455_ = l_Lean_ExprStructEq_hash(v_x_4454_);
lean_dec_ref(v_x_4454_);
v_r_4456_ = lean_box_uint64(v_res_4455_);
return v_r_4456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4463_, lean_object* v_start_4464_, lean_object* v_b_4465_, lean_object* v_i_4466_){
_start:
{
uint8_t v___x_4467_; 
v___x_4467_ = lean_nat_dec_le(v_i_4466_, v_start_4464_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4468_; lean_object* v_i_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4468_ = lean_unsigned_to_nat(1u);
v_i_4469_ = lean_nat_sub(v_i_4466_, v___x_4468_);
lean_dec(v_i_4466_);
v___x_4470_ = l_Lean_instInhabitedExpr;
v___x_4471_ = lean_array_get_borrowed(v___x_4470_, v_revArgs_4463_, v_i_4469_);
lean_inc(v___x_4471_);
v___x_4472_ = l_Lean_Expr_app___override(v_b_4465_, v___x_4471_);
v_b_4465_ = v___x_4472_;
v_i_4466_ = v_i_4469_;
goto _start;
}
else
{
lean_dec(v_i_4466_);
return v_b_4465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4474_, lean_object* v_start_4475_, lean_object* v_b_4476_, lean_object* v_i_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4474_, v_start_4475_, v_b_4476_, v_i_4477_);
lean_dec(v_start_4475_);
lean_dec_ref(v_revArgs_4474_);
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4479_, lean_object* v_beginIdx_4480_, lean_object* v_endIdx_4481_, lean_object* v_revArgs_4482_){
_start:
{
lean_object* v___x_4483_; 
v___x_4483_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4482_, v_beginIdx_4480_, v_f_4479_, v_endIdx_4481_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4484_, lean_object* v_beginIdx_4485_, lean_object* v_endIdx_4486_, lean_object* v_revArgs_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l_Lean_Expr_mkAppRevRange(v_f_4484_, v_beginIdx_4485_, v_endIdx_4486_, v_revArgs_4487_);
lean_dec_ref(v_revArgs_4487_);
lean_dec(v_beginIdx_4485_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4489_, uint8_t v_useZeta_4490_, uint8_t v_preserveMData_4491_, lean_object* v_sz_4492_, lean_object* v_e_4493_, lean_object* v_i_4494_){
_start:
{
switch(lean_obj_tag(v_e_4493_))
{
case 6:
{
lean_object* v_body_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; uint8_t v___x_4503_; 
v_body_4500_ = lean_ctor_get(v_e_4493_, 2);
lean_inc_ref(v_body_4500_);
lean_dec_ref(v_e_4493_);
v___x_4501_ = lean_unsigned_to_nat(1u);
v___x_4502_ = lean_nat_add(v_i_4494_, v___x_4501_);
lean_dec(v_i_4494_);
v___x_4503_ = lean_nat_dec_lt(v___x_4502_, v_sz_4492_);
if (v___x_4503_ == 0)
{
lean_object* v___x_4504_; 
lean_dec(v___x_4502_);
v___x_4504_ = lean_expr_instantiate(v_body_4500_, v_revArgs_4489_);
lean_dec_ref(v_body_4500_);
return v___x_4504_;
}
else
{
v_e_4493_ = v_body_4500_;
v_i_4494_ = v___x_4502_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4490_ == 0)
{
goto v___jp_4495_;
}
else
{
lean_object* v_value_4506_; lean_object* v_body_4507_; uint8_t v___x_4508_; 
v_value_4506_ = lean_ctor_get(v_e_4493_, 2);
v_body_4507_ = lean_ctor_get(v_e_4493_, 3);
v___x_4508_ = lean_nat_dec_lt(v_i_4494_, v_sz_4492_);
if (v___x_4508_ == 0)
{
goto v___jp_4495_;
}
else
{
lean_object* v___x_4509_; 
lean_inc_ref(v_body_4507_);
lean_inc_ref(v_value_4506_);
lean_dec_ref(v_e_4493_);
v___x_4509_ = lean_expr_instantiate1(v_body_4507_, v_value_4506_);
lean_dec_ref(v_value_4506_);
lean_dec_ref(v_body_4507_);
v_e_4493_ = v___x_4509_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4491_ == 0)
{
lean_object* v_expr_4511_; 
v_expr_4511_ = lean_ctor_get(v_e_4493_, 1);
lean_inc_ref(v_expr_4511_);
lean_dec_ref(v_e_4493_);
v_e_4493_ = v_expr_4511_;
goto _start;
}
else
{
goto v___jp_4495_;
}
}
default: 
{
goto v___jp_4495_;
}
}
v___jp_4495_:
{
lean_object* v_n_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v_n_4496_ = lean_nat_sub(v_sz_4492_, v_i_4494_);
lean_dec(v_i_4494_);
v___x_4497_ = lean_expr_instantiate_range(v_e_4493_, v_n_4496_, v_sz_4492_, v_revArgs_4489_);
lean_dec_ref(v_e_4493_);
v___x_4498_ = lean_unsigned_to_nat(0u);
v___x_4499_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4489_, v___x_4498_, v___x_4497_, v_n_4496_);
return v___x_4499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4513_, lean_object* v_useZeta_4514_, lean_object* v_preserveMData_4515_, lean_object* v_sz_4516_, lean_object* v_e_4517_, lean_object* v_i_4518_){
_start:
{
uint8_t v_useZeta_boxed_4519_; uint8_t v_preserveMData_boxed_4520_; lean_object* v_res_4521_; 
v_useZeta_boxed_4519_ = lean_unbox(v_useZeta_4514_);
v_preserveMData_boxed_4520_ = lean_unbox(v_preserveMData_4515_);
v_res_4521_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4513_, v_useZeta_boxed_4519_, v_preserveMData_boxed_4520_, v_sz_4516_, v_e_4517_, v_i_4518_);
lean_dec(v_sz_4516_);
lean_dec_ref(v_revArgs_4513_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4522_, lean_object* v_revArgs_4523_, uint8_t v_useZeta_4524_, uint8_t v_preserveMData_4525_){
_start:
{
lean_object* v_sz_4526_; lean_object* v___x_4527_; uint8_t v___x_4528_; 
v_sz_4526_ = lean_array_get_size(v_revArgs_4523_);
v___x_4527_ = lean_unsigned_to_nat(0u);
v___x_4528_ = lean_nat_dec_eq(v_sz_4526_, v___x_4527_);
if (v___x_4528_ == 0)
{
lean_object* v___x_4529_; 
v___x_4529_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4523_, v_useZeta_4524_, v_preserveMData_4525_, v_sz_4526_, v_f_4522_, v___x_4527_);
return v___x_4529_;
}
else
{
return v_f_4522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4530_, lean_object* v_revArgs_4531_, lean_object* v_useZeta_4532_, lean_object* v_preserveMData_4533_){
_start:
{
uint8_t v_useZeta_boxed_4534_; uint8_t v_preserveMData_boxed_4535_; lean_object* v_res_4536_; 
v_useZeta_boxed_4534_ = lean_unbox(v_useZeta_4532_);
v_preserveMData_boxed_4535_ = lean_unbox(v_preserveMData_4533_);
v_res_4536_ = l_Lean_Expr_betaRev(v_f_4530_, v_revArgs_4531_, v_useZeta_boxed_4534_, v_preserveMData_boxed_4535_);
lean_dec_ref(v_revArgs_4531_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4537_, lean_object* v_args_4538_){
_start:
{
lean_object* v___x_4539_; uint8_t v___x_4540_; lean_object* v___x_4541_; 
v___x_4539_ = l_Array_reverse___redArg(v_args_4538_);
v___x_4540_ = 0;
v___x_4541_ = l_Lean_Expr_betaRev(v_f_4537_, v___x_4539_, v___x_4540_, v___x_4540_);
lean_dec_ref(v___x_4539_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4542_){
_start:
{
switch(lean_obj_tag(v_x_4542_))
{
case 6:
{
lean_object* v_body_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; 
v_body_4543_ = lean_ctor_get(v_x_4542_, 2);
v___x_4544_ = l_Lean_Expr_getNumHeadLambdas(v_body_4543_);
v___x_4545_ = lean_unsigned_to_nat(1u);
v___x_4546_ = lean_nat_add(v___x_4544_, v___x_4545_);
lean_dec(v___x_4544_);
return v___x_4546_;
}
case 10:
{
lean_object* v_expr_4547_; 
v_expr_4547_ = lean_ctor_get(v_x_4542_, 1);
v_x_4542_ = v_expr_4547_;
goto _start;
}
default: 
{
lean_object* v___x_4549_; 
v___x_4549_ = lean_unsigned_to_nat(0u);
return v___x_4549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l_Lean_Expr_getNumHeadLambdas(v_x_4550_);
lean_dec_ref(v_x_4550_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object* v_x_4552_){
_start:
{
switch(lean_obj_tag(v_x_4552_))
{
case 6:
{
lean_object* v_body_4553_; 
v_body_4553_ = lean_ctor_get(v_x_4552_, 2);
v_x_4552_ = v_body_4553_;
goto _start;
}
case 10:
{
lean_object* v_expr_4555_; 
v_expr_4555_ = lean_ctor_get(v_x_4552_, 1);
v_x_4552_ = v_expr_4555_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_4552_);
return v_x_4552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object* v_x_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_Expr_getLambdaBody(v_x_4557_);
lean_dec_ref(v_x_4557_);
return v_res_4558_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4559_, lean_object* v_x_4560_){
_start:
{
switch(lean_obj_tag(v_x_4560_))
{
case 6:
{
uint8_t v___x_4561_; 
v___x_4561_ = 1;
return v___x_4561_;
}
case 8:
{
if (v_useZeta_4559_ == 0)
{
return v_useZeta_4559_;
}
else
{
lean_object* v_body_4562_; 
v_body_4562_ = lean_ctor_get(v_x_4560_, 3);
v_x_4560_ = v_body_4562_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4564_; 
v_expr_4564_ = lean_ctor_get(v_x_4560_, 1);
v_x_4560_ = v_expr_4564_;
goto _start;
}
default: 
{
uint8_t v___x_4566_; 
v___x_4566_ = 0;
return v___x_4566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4567_, lean_object* v_x_4568_){
_start:
{
uint8_t v_useZeta_boxed_4569_; uint8_t v_res_4570_; lean_object* v_r_4571_; 
v_useZeta_boxed_4569_ = lean_unbox(v_useZeta_4567_);
v_res_4570_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4569_, v_x_4568_);
lean_dec_ref(v_x_4568_);
v_r_4571_ = lean_box(v_res_4570_);
return v_r_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4572_){
_start:
{
lean_object* v_f_4573_; uint8_t v___x_4574_; uint8_t v___x_4575_; 
v_f_4573_ = l_Lean_Expr_getAppFn(v_e_4572_);
v___x_4574_ = 0;
v___x_4575_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4574_, v_f_4573_);
if (v___x_4575_ == 0)
{
lean_dec_ref(v_f_4573_);
return v_e_4572_;
}
else
{
lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4576_ = l_Lean_Expr_getAppNumArgs(v_e_4572_);
v___x_4577_ = lean_mk_empty_array_with_capacity(v___x_4576_);
lean_dec(v___x_4576_);
v___x_4578_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4572_, v___x_4577_);
v___x_4579_ = l_Lean_Expr_betaRev(v_f_4573_, v___x_4578_, v___x_4574_, v___x_4574_);
lean_dec_ref(v___x_4578_);
return v___x_4579_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4580_, uint8_t v_useZeta_4581_){
_start:
{
uint8_t v___x_4582_; 
v___x_4582_ = l_Lean_Expr_isApp(v_e_4580_);
if (v___x_4582_ == 0)
{
return v___x_4582_;
}
else
{
lean_object* v___x_4583_; uint8_t v___x_4584_; 
v___x_4583_ = l_Lean_Expr_getAppFn(v_e_4580_);
v___x_4584_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4581_, v___x_4583_);
lean_dec_ref(v___x_4583_);
return v___x_4584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4585_, lean_object* v_useZeta_4586_){
_start:
{
uint8_t v_useZeta_boxed_4587_; uint8_t v_res_4588_; lean_object* v_r_4589_; 
v_useZeta_boxed_4587_ = lean_unbox(v_useZeta_4586_);
v_res_4588_ = l_Lean_Expr_isHeadBetaTarget(v_e_4585_, v_useZeta_boxed_4587_);
lean_dec_ref(v_e_4585_);
v_r_4589_ = lean_box(v_res_4588_);
return v_r_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4590_, lean_object* v_x_4591_, lean_object* v_x_4592_){
_start:
{
lean_object* v_f_4594_; 
if (lean_obj_tag(v_x_4590_) == 5)
{
lean_object* v_arg_4598_; 
v_arg_4598_ = lean_ctor_get(v_x_4590_, 1);
if (lean_obj_tag(v_arg_4598_) == 0)
{
lean_object* v_fn_4599_; lean_object* v_deBruijnIndex_4600_; lean_object* v_zero_4601_; uint8_t v_isZero_4602_; 
v_fn_4599_ = lean_ctor_get(v_x_4590_, 0);
v_deBruijnIndex_4600_ = lean_ctor_get(v_arg_4598_, 0);
v_zero_4601_ = lean_unsigned_to_nat(0u);
v_isZero_4602_ = lean_nat_dec_eq(v_x_4591_, v_zero_4601_);
if (v_isZero_4602_ == 1)
{
lean_dec(v_x_4592_);
lean_dec(v_x_4591_);
v_f_4594_ = v_x_4590_;
goto v___jp_4593_;
}
else
{
uint8_t v___x_4603_; 
lean_inc(v_deBruijnIndex_4600_);
lean_inc_ref(v_fn_4599_);
lean_dec_ref(v_x_4590_);
v___x_4603_ = lean_nat_dec_eq(v_deBruijnIndex_4600_, v_x_4592_);
lean_dec(v_deBruijnIndex_4600_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4604_; 
lean_dec_ref(v_fn_4599_);
lean_dec(v_x_4592_);
lean_dec(v_x_4591_);
v___x_4604_ = lean_box(0);
return v___x_4604_;
}
else
{
lean_object* v_one_4605_; lean_object* v_n_4606_; lean_object* v___x_4607_; 
v_one_4605_ = lean_unsigned_to_nat(1u);
v_n_4606_ = lean_nat_sub(v_x_4591_, v_one_4605_);
lean_dec(v_x_4591_);
v___x_4607_ = lean_nat_add(v_x_4592_, v_one_4605_);
lean_dec(v_x_4592_);
v_x_4590_ = v_fn_4599_;
v_x_4591_ = v_n_4606_;
v_x_4592_ = v___x_4607_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4609_; uint8_t v_isZero_4610_; 
lean_dec(v_x_4592_);
v_zero_4609_ = lean_unsigned_to_nat(0u);
v_isZero_4610_ = lean_nat_dec_eq(v_x_4591_, v_zero_4609_);
lean_dec(v_x_4591_);
if (v_isZero_4610_ == 1)
{
v_f_4594_ = v_x_4590_;
goto v___jp_4593_;
}
else
{
lean_object* v___x_4611_; 
lean_dec_ref(v_x_4590_);
v___x_4611_ = lean_box(0);
return v___x_4611_;
}
}
}
else
{
lean_object* v_zero_4612_; uint8_t v_isZero_4613_; 
lean_dec(v_x_4592_);
v_zero_4612_ = lean_unsigned_to_nat(0u);
v_isZero_4613_ = lean_nat_dec_eq(v_x_4591_, v_zero_4612_);
lean_dec(v_x_4591_);
if (v_isZero_4613_ == 1)
{
v_f_4594_ = v_x_4590_;
goto v___jp_4593_;
}
else
{
lean_object* v___x_4614_; 
lean_dec_ref(v_x_4590_);
v___x_4614_ = lean_box(0);
return v___x_4614_;
}
}
v___jp_4593_:
{
uint8_t v___x_4595_; 
v___x_4595_ = l_Lean_Expr_hasLooseBVars(v_f_4594_);
if (v___x_4595_ == 0)
{
lean_object* v___x_4596_; 
v___x_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4596_, 0, v_f_4594_);
return v___x_4596_;
}
else
{
lean_object* v___x_4597_; 
lean_dec_ref(v_f_4594_);
v___x_4597_ = lean_box(0);
return v___x_4597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4615_, lean_object* v_x_4616_){
_start:
{
if (lean_obj_tag(v_x_4615_) == 6)
{
lean_object* v_body_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
v_body_4617_ = lean_ctor_get(v_x_4615_, 2);
lean_inc_ref(v_body_4617_);
lean_dec_ref(v_x_4615_);
v___x_4618_ = lean_unsigned_to_nat(1u);
v___x_4619_ = lean_nat_add(v_x_4616_, v___x_4618_);
lean_dec(v_x_4616_);
v_x_4615_ = v_body_4617_;
v_x_4616_ = v___x_4619_;
goto _start;
}
else
{
lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4621_ = lean_unsigned_to_nat(0u);
v___x_4622_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4615_, v_x_4616_, v___x_4621_);
return v___x_4622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4623_){
_start:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4624_ = lean_unsigned_to_nat(0u);
v___x_4625_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4623_, v___x_4624_);
return v___x_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4626_){
_start:
{
if (lean_obj_tag(v_x_4626_) == 6)
{
lean_object* v_body_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
v_body_4627_ = lean_ctor_get(v_x_4626_, 2);
lean_inc_ref(v_body_4627_);
lean_dec_ref(v_x_4626_);
v___x_4628_ = lean_unsigned_to_nat(1u);
v___x_4629_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4627_, v___x_4628_);
return v___x_4629_;
}
else
{
lean_object* v___x_4630_; 
lean_dec_ref(v_x_4626_);
v___x_4630_ = lean_box(0);
return v___x_4630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4634_){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; uint8_t v___x_4637_; 
v___x_4635_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4641_);
lean_dec_ref(v_e_4641_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4646_){
_start:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; uint8_t v___x_4649_; 
v___x_4647_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4648_ = lean_unsigned_to_nat(2u);
v___x_4649_ = l_Lean_Expr_isAppOfArity(v_e_4646_, v___x_4647_, v___x_4648_);
if (v___x_4649_ == 0)
{
lean_object* v___x_4650_; 
v___x_4650_ = lean_box(0);
return v___x_4650_;
}
else
{
lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4651_ = l_Lean_Expr_appArg_x21(v_e_4646_);
v___x_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4652_, 0, v___x_4651_);
return v___x_4652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4653_);
lean_dec_ref(v_e_4653_);
return v_res_4654_;
}
}
LEAN_EXPORT uint8_t lean_is_out_param(lean_object* v_e_4658_){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; uint8_t v___x_4661_; 
v___x_4659_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4660_ = lean_unsigned_to_nat(1u);
v___x_4661_ = l_Lean_Expr_isAppOfArity(v_e_4658_, v___x_4659_, v___x_4660_);
lean_dec_ref(v_e_4658_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4662_){
_start:
{
uint8_t v_res_4663_; lean_object* v_r_4664_; 
v_res_4663_ = lean_is_out_param(v_e_4662_);
v_r_4664_ = lean_box(v_res_4663_);
return v_r_4664_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4668_){
_start:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; uint8_t v___x_4671_; 
v___x_4669_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4670_ = lean_unsigned_to_nat(1u);
v___x_4671_ = l_Lean_Expr_isAppOfArity(v_e_4668_, v___x_4669_, v___x_4670_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4672_){
_start:
{
uint8_t v_res_4673_; lean_object* v_r_4674_; 
v_res_4673_ = l_Lean_Expr_isSemiOutParam(v_e_4672_);
lean_dec_ref(v_e_4672_);
v_r_4674_ = lean_box(v_res_4673_);
return v_r_4674_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4675_){
_start:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; uint8_t v___x_4678_; 
v___x_4676_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4677_ = lean_unsigned_to_nat(2u);
v___x_4678_ = l_Lean_Expr_isAppOfArity(v_e_4675_, v___x_4676_, v___x_4677_);
return v___x_4678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4679_){
_start:
{
uint8_t v_res_4680_; lean_object* v_r_4681_; 
v_res_4680_ = l_Lean_Expr_isOptParam(v_e_4679_);
lean_dec_ref(v_e_4679_);
v_r_4681_ = lean_box(v_res_4680_);
return v_r_4681_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4682_){
_start:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; uint8_t v___x_4685_; 
v___x_4683_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4684_ = lean_unsigned_to_nat(2u);
v___x_4685_ = l_Lean_Expr_isAppOfArity(v_e_4682_, v___x_4683_, v___x_4684_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4686_){
_start:
{
uint8_t v_res_4687_; lean_object* v_r_4688_; 
v_res_4687_ = l_Lean_Expr_isAutoParam(v_e_4686_);
lean_dec_ref(v_e_4686_);
v_r_4688_ = lean_box(v_res_4687_);
return v_r_4688_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4689_){
_start:
{
lean_object* v___x_4690_; 
v___x_4690_ = l_Lean_Expr_getAppFn(v_e_4689_);
if (lean_obj_tag(v___x_4690_) == 4)
{
lean_object* v_declName_4691_; uint8_t v___y_4693_; lean_object* v___x_4698_; uint8_t v___x_4699_; 
v_declName_4691_ = lean_ctor_get(v___x_4690_, 0);
lean_inc(v_declName_4691_);
lean_dec_ref(v___x_4690_);
v___x_4698_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4699_ = lean_name_eq(v_declName_4691_, v___x_4698_);
if (v___x_4699_ == 0)
{
lean_object* v___x_4700_; uint8_t v___x_4701_; 
v___x_4700_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4701_ = lean_name_eq(v_declName_4691_, v___x_4700_);
v___y_4693_ = v___x_4701_;
goto v___jp_4692_;
}
else
{
v___y_4693_ = v___x_4699_;
goto v___jp_4692_;
}
v___jp_4692_:
{
if (v___y_4693_ == 0)
{
lean_object* v___x_4694_; uint8_t v___x_4695_; 
v___x_4694_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4695_ = lean_name_eq(v_declName_4691_, v___x_4694_);
if (v___x_4695_ == 0)
{
lean_object* v___x_4696_; uint8_t v___x_4697_; 
v___x_4696_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4697_ = lean_name_eq(v_declName_4691_, v___x_4696_);
lean_dec(v_declName_4691_);
return v___x_4697_;
}
else
{
lean_dec(v_declName_4691_);
return v___x_4695_;
}
}
else
{
lean_dec(v_declName_4691_);
return v___y_4693_;
}
}
}
else
{
uint8_t v___x_4702_; 
lean_dec_ref(v___x_4690_);
v___x_4702_ = 0;
return v___x_4702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4703_){
_start:
{
uint8_t v_res_4704_; lean_object* v_r_4705_; 
v_res_4704_ = l_Lean_Expr_isTypeAnnotation(v_e_4703_);
lean_dec_ref(v_e_4703_);
v_r_4705_ = lean_box(v_res_4704_);
return v_r_4705_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4706_){
_start:
{
uint8_t v___y_4708_; uint8_t v___y_4712_; uint8_t v___x_4718_; 
v___x_4718_ = l_Lean_Expr_isOptParam(v_e_4706_);
if (v___x_4718_ == 0)
{
uint8_t v___x_4719_; 
v___x_4719_ = l_Lean_Expr_isAutoParam(v_e_4706_);
v___y_4712_ = v___x_4719_;
goto v___jp_4711_;
}
else
{
v___y_4712_ = v___x_4718_;
goto v___jp_4711_;
}
v___jp_4707_:
{
if (v___y_4708_ == 0)
{
return v_e_4706_;
}
else
{
lean_object* v___x_4709_; 
v___x_4709_ = l_Lean_Expr_appArg_x21(v_e_4706_);
lean_dec_ref(v_e_4706_);
v_e_4706_ = v___x_4709_;
goto _start;
}
}
v___jp_4711_:
{
if (v___y_4712_ == 0)
{
uint8_t v___x_4713_; 
lean_inc_ref(v_e_4706_);
v___x_4713_ = lean_is_out_param(v_e_4706_);
if (v___x_4713_ == 0)
{
uint8_t v___x_4714_; 
v___x_4714_ = l_Lean_Expr_isSemiOutParam(v_e_4706_);
v___y_4708_ = v___x_4714_;
goto v___jp_4707_;
}
else
{
v___y_4708_ = v___x_4713_;
goto v___jp_4707_;
}
}
else
{
lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4715_ = l_Lean_Expr_appFn_x21(v_e_4706_);
lean_dec_ref(v_e_4706_);
v___x_4716_ = l_Lean_Expr_appArg_x21(v___x_4715_);
lean_dec_ref(v___x_4715_);
v_e_4706_ = v___x_4716_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4720_){
_start:
{
lean_object* v___x_4721_; lean_object* v_e_x27_4722_; uint8_t v___x_4723_; 
v___x_4721_ = l_Lean_Expr_consumeMData(v_e_4720_);
v_e_x27_4722_ = lean_expr_consume_type_annotations(v___x_4721_);
v___x_4723_ = lean_expr_eqv(v_e_x27_4722_, v_e_4720_);
if (v___x_4723_ == 0)
{
lean_dec_ref(v_e_4720_);
v_e_4720_ = v_e_x27_4722_;
goto _start;
}
else
{
lean_dec_ref(v_e_x27_4722_);
return v_e_4720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4725_){
_start:
{
lean_object* v_fn_4726_; lean_object* v___x_4727_; 
v_fn_4726_ = lean_ctor_get(v_e_4725_, 0);
lean_inc_ref(v_fn_4726_);
lean_dec_ref(v_e_4725_);
v___x_4727_ = l_Lean_Expr_cleanupAnnotations(v_fn_4726_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* v_e_4728_, lean_object* v_h_4729_){
_start:
{
lean_object* v___x_4730_; 
v___x_4730_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4728_);
return v___x_4730_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4734_){
_start:
{
lean_object* v___x_4735_; lean_object* v___x_4736_; uint8_t v___x_4737_; 
v___x_4735_ = l_Lean_Expr_cleanupAnnotations(v_e_4734_);
v___x_4736_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4737_ = l_Lean_Expr_isConstOf(v___x_4735_, v___x_4736_);
lean_dec_ref(v___x_4735_);
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4738_){
_start:
{
uint8_t v_res_4739_; lean_object* v_r_4740_; 
v_res_4739_ = l_Lean_Expr_isFalse(v_e_4738_);
v_r_4740_ = lean_box(v_res_4739_);
return v_r_4740_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4744_){
_start:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; uint8_t v___x_4747_; 
v___x_4745_ = l_Lean_Expr_cleanupAnnotations(v_e_4744_);
v___x_4746_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4747_ = l_Lean_Expr_isConstOf(v___x_4745_, v___x_4746_);
lean_dec_ref(v___x_4745_);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4748_){
_start:
{
uint8_t v_res_4749_; lean_object* v_r_4750_; 
v_res_4749_ = l_Lean_Expr_isTrue(v_e_4748_);
v_r_4750_ = lean_box(v_res_4749_);
return v_r_4750_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object* v_e_4755_){
_start:
{
lean_object* v___x_4756_; lean_object* v___x_4757_; uint8_t v___x_4758_; 
v___x_4756_ = l_Lean_Expr_cleanupAnnotations(v_e_4755_);
v___x_4757_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_4758_ = l_Lean_Expr_isConstOf(v___x_4756_, v___x_4757_);
lean_dec_ref(v___x_4756_);
return v___x_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object* v_e_4759_){
_start:
{
uint8_t v_res_4760_; lean_object* v_r_4761_; 
v_res_4760_ = l_Lean_Expr_isBoolFalse(v_e_4759_);
v_r_4761_ = lean_box(v_res_4760_);
return v_r_4761_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object* v_e_4765_){
_start:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; uint8_t v___x_4768_; 
v___x_4766_ = l_Lean_Expr_cleanupAnnotations(v_e_4765_);
v___x_4767_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_4768_ = l_Lean_Expr_isConstOf(v___x_4766_, v___x_4767_);
lean_dec_ref(v___x_4766_);
return v___x_4768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object* v_e_4769_){
_start:
{
uint8_t v_res_4770_; lean_object* v_r_4771_; 
v_res_4770_ = l_Lean_Expr_isBoolTrue(v_e_4769_);
v_r_4771_ = lean_box(v_res_4770_);
return v_r_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* v_x_4772_){
_start:
{
switch(lean_obj_tag(v_x_4772_))
{
case 10:
{
lean_object* v_expr_4773_; 
v_expr_4773_ = lean_ctor_get(v_x_4772_, 1);
lean_inc_ref(v_expr_4773_);
lean_dec_ref(v_x_4772_);
v_x_4772_ = v_expr_4773_;
goto _start;
}
case 7:
{
lean_object* v_body_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v_body_4775_ = lean_ctor_get(v_x_4772_, 2);
lean_inc_ref(v_body_4775_);
lean_dec_ref(v_x_4772_);
v___x_4776_ = l_Lean_Expr_getForallArity(v_body_4775_);
v___x_4777_ = lean_unsigned_to_nat(1u);
v___x_4778_ = lean_nat_add(v___x_4776_, v___x_4777_);
lean_dec(v___x_4776_);
return v___x_4778_;
}
default: 
{
uint8_t v___x_4779_; uint8_t v___x_4780_; 
v___x_4779_ = 0;
v___x_4780_ = l_Lean_Expr_isHeadBetaTarget(v_x_4772_, v___x_4779_);
if (v___x_4780_ == 0)
{
lean_object* v_e_x27_4781_; uint8_t v___x_4782_; 
lean_inc_ref(v_x_4772_);
v_e_x27_4781_ = l_Lean_Expr_cleanupAnnotations(v_x_4772_);
v___x_4782_ = lean_expr_eqv(v_x_4772_, v_e_x27_4781_);
lean_dec_ref(v_x_4772_);
if (v___x_4782_ == 0)
{
v_x_4772_ = v_e_x27_4781_;
goto _start;
}
else
{
lean_object* v___x_4784_; 
lean_dec_ref(v_e_x27_4781_);
v___x_4784_ = lean_unsigned_to_nat(0u);
return v___x_4784_;
}
}
else
{
lean_object* v___x_4785_; 
v___x_4785_ = l_Lean_Expr_headBeta(v_x_4772_);
v_x_4772_ = v___x_4785_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4787_){
_start:
{
lean_object* v___x_4788_; uint8_t v___x_4789_; 
v___x_4788_ = l_Lean_Expr_cleanupAnnotations(v_e_4787_);
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
lean_object* v___x_4791_; uint8_t v___x_4792_; 
v___x_4791_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4788_);
v___x_4792_ = l_Lean_Expr_isApp(v___x_4791_);
if (v___x_4792_ == 0)
{
lean_object* v___x_4793_; 
lean_dec_ref(v___x_4791_);
v___x_4793_ = lean_box(0);
return v___x_4793_;
}
else
{
lean_object* v_arg_4794_; lean_object* v___x_4795_; uint8_t v___x_4796_; 
v_arg_4794_ = lean_ctor_get(v___x_4791_, 1);
lean_inc_ref(v_arg_4794_);
v___x_4795_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4791_);
v___x_4796_ = l_Lean_Expr_isApp(v___x_4795_);
if (v___x_4796_ == 0)
{
lean_object* v___x_4797_; 
lean_dec_ref(v___x_4795_);
lean_dec_ref(v_arg_4794_);
v___x_4797_ = lean_box(0);
return v___x_4797_;
}
else
{
lean_object* v___x_4798_; lean_object* v___x_4799_; uint8_t v___x_4800_; 
v___x_4798_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4795_);
v___x_4799_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4800_ = l_Lean_Expr_isConstOf(v___x_4798_, v___x_4799_);
lean_dec_ref(v___x_4798_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; 
lean_dec_ref(v_arg_4794_);
v___x_4801_ = lean_box(0);
return v___x_4801_;
}
else
{
if (lean_obj_tag(v_arg_4794_) == 9)
{
lean_object* v_a_4802_; 
v_a_4802_ = lean_ctor_get(v_arg_4794_, 0);
lean_inc_ref(v_a_4802_);
lean_dec_ref(v_arg_4794_);
if (lean_obj_tag(v_a_4802_) == 0)
{
lean_object* v_val_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4810_; 
v_val_4803_ = lean_ctor_get(v_a_4802_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v_a_4802_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4805_ = v_a_4802_;
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_val_4803_);
lean_dec(v_a_4802_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4808_; 
if (v_isShared_4806_ == 0)
{
lean_ctor_set_tag(v___x_4805_, 1);
v___x_4808_ = v___x_4805_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_val_4803_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
else
{
lean_object* v___x_4811_; 
lean_dec_ref(v_a_4802_);
v___x_4811_ = lean_box(0);
return v___x_4811_;
}
}
else
{
lean_object* v___x_4812_; 
lean_dec_ref(v_arg_4794_);
v___x_4812_ = lean_box(0);
return v___x_4812_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4818_){
_start:
{
lean_object* v___x_4831_; uint8_t v___x_4832_; 
lean_inc_ref(v_e_4818_);
v___x_4831_ = l_Lean_Expr_cleanupAnnotations(v_e_4818_);
v___x_4832_ = l_Lean_Expr_isApp(v___x_4831_);
if (v___x_4832_ == 0)
{
lean_dec_ref(v___x_4831_);
goto v___jp_4819_;
}
else
{
lean_object* v_arg_4833_; lean_object* v___x_4834_; uint8_t v___x_4835_; 
v_arg_4833_ = lean_ctor_get(v___x_4831_, 1);
lean_inc_ref(v_arg_4833_);
v___x_4834_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4831_);
v___x_4835_ = l_Lean_Expr_isApp(v___x_4834_);
if (v___x_4835_ == 0)
{
lean_dec_ref(v___x_4834_);
lean_dec_ref(v_arg_4833_);
goto v___jp_4819_;
}
else
{
lean_object* v___x_4836_; uint8_t v___x_4837_; 
v___x_4836_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4834_);
v___x_4837_ = l_Lean_Expr_isApp(v___x_4836_);
if (v___x_4837_ == 0)
{
lean_dec_ref(v___x_4836_);
lean_dec_ref(v_arg_4833_);
goto v___jp_4819_;
}
else
{
lean_object* v___x_4838_; lean_object* v___x_4839_; uint8_t v___x_4840_; 
v___x_4838_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4836_);
v___x_4839_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4840_ = l_Lean_Expr_isConstOf(v___x_4838_, v___x_4839_);
lean_dec_ref(v___x_4838_);
if (v___x_4840_ == 0)
{
lean_dec_ref(v_arg_4833_);
goto v___jp_4819_;
}
else
{
lean_object* v___x_4841_; 
lean_dec_ref(v_e_4818_);
v___x_4841_ = l_Lean_Expr_nat_x3f(v_arg_4833_);
if (lean_obj_tag(v___x_4841_) == 0)
{
lean_object* v___x_4842_; 
v___x_4842_ = lean_box(0);
return v___x_4842_;
}
else
{
lean_object* v_val_4843_; lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4855_; 
v_val_4843_ = lean_ctor_get(v___x_4841_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4845_ = v___x_4841_;
v_isShared_4846_ = v_isSharedCheck_4855_;
goto v_resetjp_4844_;
}
else
{
lean_inc(v_val_4843_);
lean_dec(v___x_4841_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4855_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v___x_4847_; uint8_t v___x_4848_; 
v___x_4847_ = lean_unsigned_to_nat(0u);
v___x_4848_ = lean_nat_dec_eq(v_val_4843_, v___x_4847_);
if (v___x_4848_ == 0)
{
lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4852_; 
v___x_4849_ = lean_nat_to_int(v_val_4843_);
v___x_4850_ = lean_int_neg(v___x_4849_);
lean_dec(v___x_4849_);
if (v_isShared_4846_ == 0)
{
lean_ctor_set(v___x_4845_, 0, v___x_4850_);
v___x_4852_ = v___x_4845_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v___x_4850_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
else
{
lean_object* v___x_4854_; 
lean_del_object(v___x_4845_);
lean_dec(v_val_4843_);
v___x_4854_ = lean_box(0);
return v___x_4854_;
}
}
}
}
}
}
}
v___jp_4819_:
{
lean_object* v___x_4820_; 
v___x_4820_ = l_Lean_Expr_nat_x3f(v_e_4818_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v___x_4821_; 
v___x_4821_ = lean_box(0);
return v___x_4821_;
}
else
{
lean_object* v_val_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4830_; 
v_val_4822_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4824_ = v___x_4820_;
v_isShared_4825_ = v_isSharedCheck_4830_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_val_4822_);
lean_dec(v___x_4820_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4830_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4826_; lean_object* v___x_4828_; 
v___x_4826_ = lean_nat_to_int(v_val_4822_);
if (v_isShared_4825_ == 0)
{
lean_ctor_set(v___x_4824_, 0, v___x_4826_);
v___x_4828_ = v___x_4824_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4826_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4856_, lean_object* v_e_4857_){
_start:
{
uint8_t v___x_4858_; lean_object* v_d_4860_; lean_object* v_b_4861_; 
v___x_4858_ = l_Lean_Expr_hasFVar(v_e_4857_);
if (v___x_4858_ == 0)
{
lean_dec_ref(v_e_4857_);
lean_dec_ref(v_p_4856_);
return v___x_4858_;
}
else
{
switch(lean_obj_tag(v_e_4857_))
{
case 7:
{
lean_object* v_binderType_4864_; lean_object* v_body_4865_; 
v_binderType_4864_ = lean_ctor_get(v_e_4857_, 1);
lean_inc_ref(v_binderType_4864_);
v_body_4865_ = lean_ctor_get(v_e_4857_, 2);
lean_inc_ref(v_body_4865_);
lean_dec_ref(v_e_4857_);
v_d_4860_ = v_binderType_4864_;
v_b_4861_ = v_body_4865_;
goto v___jp_4859_;
}
case 6:
{
lean_object* v_binderType_4866_; lean_object* v_body_4867_; 
v_binderType_4866_ = lean_ctor_get(v_e_4857_, 1);
lean_inc_ref(v_binderType_4866_);
v_body_4867_ = lean_ctor_get(v_e_4857_, 2);
lean_inc_ref(v_body_4867_);
lean_dec_ref(v_e_4857_);
v_d_4860_ = v_binderType_4866_;
v_b_4861_ = v_body_4867_;
goto v___jp_4859_;
}
case 10:
{
lean_object* v_expr_4868_; 
v_expr_4868_ = lean_ctor_get(v_e_4857_, 1);
lean_inc_ref(v_expr_4868_);
lean_dec_ref(v_e_4857_);
v_e_4857_ = v_expr_4868_;
goto _start;
}
case 8:
{
lean_object* v_type_4870_; lean_object* v_value_4871_; lean_object* v_body_4872_; uint8_t v___x_4873_; 
v_type_4870_ = lean_ctor_get(v_e_4857_, 1);
lean_inc_ref(v_type_4870_);
v_value_4871_ = lean_ctor_get(v_e_4857_, 2);
lean_inc_ref(v_value_4871_);
v_body_4872_ = lean_ctor_get(v_e_4857_, 3);
lean_inc_ref(v_body_4872_);
lean_dec_ref(v_e_4857_);
lean_inc_ref(v_p_4856_);
v___x_4873_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4856_, v_type_4870_);
if (v___x_4873_ == 0)
{
uint8_t v___x_4874_; 
lean_inc_ref(v_p_4856_);
v___x_4874_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4856_, v_value_4871_);
if (v___x_4874_ == 0)
{
v_e_4857_ = v_body_4872_;
goto _start;
}
else
{
lean_dec_ref(v_body_4872_);
lean_dec_ref(v_p_4856_);
return v___x_4858_;
}
}
else
{
lean_dec_ref(v_body_4872_);
lean_dec_ref(v_value_4871_);
lean_dec_ref(v_p_4856_);
return v___x_4858_;
}
}
case 5:
{
lean_object* v_fn_4876_; lean_object* v_arg_4877_; uint8_t v___x_4878_; 
v_fn_4876_ = lean_ctor_get(v_e_4857_, 0);
lean_inc_ref(v_fn_4876_);
v_arg_4877_ = lean_ctor_get(v_e_4857_, 1);
lean_inc_ref(v_arg_4877_);
lean_dec_ref(v_e_4857_);
lean_inc_ref(v_p_4856_);
v___x_4878_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4856_, v_fn_4876_);
if (v___x_4878_ == 0)
{
v_e_4857_ = v_arg_4877_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4877_);
lean_dec_ref(v_p_4856_);
return v___x_4858_;
}
}
case 11:
{
lean_object* v_struct_4880_; 
v_struct_4880_ = lean_ctor_get(v_e_4857_, 2);
lean_inc_ref(v_struct_4880_);
lean_dec_ref(v_e_4857_);
v_e_4857_ = v_struct_4880_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4882_; lean_object* v___x_4883_; uint8_t v___x_4884_; 
v_fvarId_4882_ = lean_ctor_get(v_e_4857_, 0);
lean_inc(v_fvarId_4882_);
lean_dec_ref(v_e_4857_);
v___x_4883_ = lean_apply_1(v_p_4856_, v_fvarId_4882_);
v___x_4884_ = lean_unbox(v___x_4883_);
return v___x_4884_;
}
default: 
{
uint8_t v___x_4885_; 
lean_dec_ref(v_e_4857_);
lean_dec_ref(v_p_4856_);
v___x_4885_ = 0;
return v___x_4885_;
}
}
}
v___jp_4859_:
{
uint8_t v___x_4862_; 
lean_inc_ref(v_p_4856_);
v___x_4862_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4856_, v_d_4860_);
if (v___x_4862_ == 0)
{
v_e_4857_ = v_b_4861_;
goto _start;
}
else
{
lean_dec_ref(v_b_4861_);
lean_dec_ref(v_p_4856_);
return v___x_4858_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_4886_, lean_object* v_e_4887_){
_start:
{
uint8_t v_res_4888_; lean_object* v_r_4889_; 
v_res_4888_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4886_, v_e_4887_);
v_r_4889_ = lean_box(v_res_4888_);
return v_r_4889_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_4890_, lean_object* v_p_4891_){
_start:
{
uint8_t v___x_4892_; 
v___x_4892_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4891_, v_e_4890_);
return v___x_4892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_4893_, lean_object* v_p_4894_){
_start:
{
uint8_t v_res_4895_; lean_object* v_r_4896_; 
v_res_4895_ = l_Lean_Expr_hasAnyFVar(v_e_4893_, v_p_4894_);
v_r_4896_ = lean_box(v_res_4895_);
return v_r_4896_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_4897_, lean_object* v_e_4898_){
_start:
{
uint8_t v___x_4899_; lean_object* v_d_4901_; lean_object* v_b_4902_; 
v___x_4899_ = l_Lean_Expr_hasFVar(v_e_4898_);
if (v___x_4899_ == 0)
{
return v___x_4899_;
}
else
{
switch(lean_obj_tag(v_e_4898_))
{
case 7:
{
lean_object* v_binderType_4905_; lean_object* v_body_4906_; 
v_binderType_4905_ = lean_ctor_get(v_e_4898_, 1);
v_body_4906_ = lean_ctor_get(v_e_4898_, 2);
v_d_4901_ = v_binderType_4905_;
v_b_4902_ = v_body_4906_;
goto v___jp_4900_;
}
case 6:
{
lean_object* v_binderType_4907_; lean_object* v_body_4908_; 
v_binderType_4907_ = lean_ctor_get(v_e_4898_, 1);
v_body_4908_ = lean_ctor_get(v_e_4898_, 2);
v_d_4901_ = v_binderType_4907_;
v_b_4902_ = v_body_4908_;
goto v___jp_4900_;
}
case 10:
{
lean_object* v_expr_4909_; 
v_expr_4909_ = lean_ctor_get(v_e_4898_, 1);
v_e_4898_ = v_expr_4909_;
goto _start;
}
case 8:
{
lean_object* v_type_4911_; lean_object* v_value_4912_; lean_object* v_body_4913_; uint8_t v___x_4914_; 
v_type_4911_ = lean_ctor_get(v_e_4898_, 1);
v_value_4912_ = lean_ctor_get(v_e_4898_, 2);
v_body_4913_ = lean_ctor_get(v_e_4898_, 3);
v___x_4914_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4897_, v_type_4911_);
if (v___x_4914_ == 0)
{
uint8_t v___x_4915_; 
v___x_4915_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4897_, v_value_4912_);
if (v___x_4915_ == 0)
{
v_e_4898_ = v_body_4913_;
goto _start;
}
else
{
return v___x_4899_;
}
}
else
{
return v___x_4899_;
}
}
case 5:
{
lean_object* v_fn_4917_; lean_object* v_arg_4918_; uint8_t v___x_4919_; 
v_fn_4917_ = lean_ctor_get(v_e_4898_, 0);
v_arg_4918_ = lean_ctor_get(v_e_4898_, 1);
v___x_4919_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4897_, v_fn_4917_);
if (v___x_4919_ == 0)
{
v_e_4898_ = v_arg_4918_;
goto _start;
}
else
{
return v___x_4899_;
}
}
case 11:
{
lean_object* v_struct_4921_; 
v_struct_4921_ = lean_ctor_get(v_e_4898_, 2);
v_e_4898_ = v_struct_4921_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4923_; uint8_t v___x_4924_; 
v_fvarId_4923_ = lean_ctor_get(v_e_4898_, 0);
v___x_4924_ = lean_name_eq(v_fvarId_4923_, v_fvarId_4897_);
return v___x_4924_;
}
default: 
{
uint8_t v___x_4925_; 
v___x_4925_ = 0;
return v___x_4925_;
}
}
}
v___jp_4900_:
{
uint8_t v___x_4903_; 
v___x_4903_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4897_, v_d_4901_);
if (v___x_4903_ == 0)
{
v_e_4898_ = v_b_4902_;
goto _start;
}
else
{
return v___x_4899_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_4926_, lean_object* v_e_4927_){
_start:
{
uint8_t v_res_4928_; lean_object* v_r_4929_; 
v_res_4928_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4926_, v_e_4927_);
lean_dec_ref(v_e_4927_);
lean_dec(v_fvarId_4926_);
v_r_4929_ = lean_box(v_res_4928_);
return v_r_4929_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_4930_, lean_object* v_fvarId_4931_){
_start:
{
uint8_t v___x_4932_; 
v___x_4932_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4931_, v_e_4930_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_4933_, lean_object* v_fvarId_4934_){
_start:
{
uint8_t v_res_4935_; lean_object* v_r_4936_; 
v_res_4935_ = l_Lean_Expr_containsFVar(v_e_4933_, v_fvarId_4934_);
lean_dec(v_fvarId_4934_);
lean_dec_ref(v_e_4933_);
v_r_4936_ = lean_box(v_res_4935_);
return v_r_4936_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___x_4938_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_4939_ = lean_unsigned_to_nat(18u);
v___x_4940_ = lean_unsigned_to_nat(1838u);
v___x_4941_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_4942_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4943_ = l_mkPanicMessageWithDecl(v___x_4942_, v___x_4941_, v___x_4940_, v___x_4939_, v___x_4938_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_4944_, lean_object* v_newFn_4945_, lean_object* v_newArg_4946_){
_start:
{
uint8_t v___y_4948_; 
if (lean_obj_tag(v_e_4944_) == 5)
{
lean_object* v_fn_4950_; lean_object* v_arg_4951_; size_t v___x_4952_; size_t v___x_4953_; uint8_t v___x_4954_; 
v_fn_4950_ = lean_ctor_get(v_e_4944_, 0);
v_arg_4951_ = lean_ctor_get(v_e_4944_, 1);
v___x_4952_ = lean_ptr_addr(v_fn_4950_);
v___x_4953_ = lean_ptr_addr(v_newFn_4945_);
v___x_4954_ = lean_usize_dec_eq(v___x_4952_, v___x_4953_);
if (v___x_4954_ == 0)
{
v___y_4948_ = v___x_4954_;
goto v___jp_4947_;
}
else
{
size_t v___x_4955_; size_t v___x_4956_; uint8_t v___x_4957_; 
v___x_4955_ = lean_ptr_addr(v_arg_4951_);
v___x_4956_ = lean_ptr_addr(v_newArg_4946_);
v___x_4957_ = lean_usize_dec_eq(v___x_4955_, v___x_4956_);
v___y_4948_ = v___x_4957_;
goto v___jp_4947_;
}
}
else
{
lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; 
lean_dec_ref(v_newArg_4946_);
lean_dec_ref(v_newFn_4945_);
v___x_4958_ = l_Lean_instInhabitedExpr;
v___x_4959_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_4960_ = l_panic___redArg(v___x_4958_, v___x_4959_);
return v___x_4960_;
}
v___jp_4947_:
{
if (v___y_4948_ == 0)
{
lean_object* v___x_4949_; 
v___x_4949_ = l_Lean_Expr_app___override(v_newFn_4945_, v_newArg_4946_);
return v___x_4949_;
}
else
{
lean_dec_ref(v_newArg_4946_);
lean_dec_ref(v_newFn_4945_);
lean_inc_ref(v_e_4944_);
return v_e_4944_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_4961_, lean_object* v_newFn_4962_, lean_object* v_newArg_4963_){
_start:
{
lean_object* v_res_4964_; 
v_res_4964_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_4961_, v_newFn_4962_, v_newArg_4963_);
lean_dec_ref(v_e_4961_);
return v_res_4964_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4966_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_4967_ = lean_unsigned_to_nat(20u);
v___x_4968_ = lean_unsigned_to_nat(1849u);
v___x_4969_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_4970_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4971_ = l_mkPanicMessageWithDecl(v___x_4970_, v___x_4969_, v___x_4968_, v___x_4967_, v___x_4966_);
return v___x_4971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_4972_, lean_object* v_fvarIdNew_4973_){
_start:
{
if (lean_obj_tag(v_e_4972_) == 1)
{
lean_object* v_fvarId_4974_; uint8_t v___x_4975_; 
v_fvarId_4974_ = lean_ctor_get(v_e_4972_, 0);
v___x_4975_ = lean_name_eq(v_fvarId_4974_, v_fvarIdNew_4973_);
if (v___x_4975_ == 0)
{
lean_object* v___x_4976_; 
v___x_4976_ = l_Lean_Expr_fvar___override(v_fvarIdNew_4973_);
return v___x_4976_;
}
else
{
lean_dec(v_fvarIdNew_4973_);
lean_inc_ref(v_e_4972_);
return v_e_4972_;
}
}
else
{
lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
lean_dec(v_fvarIdNew_4973_);
v___x_4977_ = l_Lean_instInhabitedExpr;
v___x_4978_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_4979_ = l_panic___redArg(v___x_4977_, v___x_4978_);
return v___x_4979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_4980_, lean_object* v_fvarIdNew_4981_){
_start:
{
lean_object* v_res_4982_; 
v_res_4982_ = l_Lean_Expr_updateFVar_x21(v_e_4980_, v_fvarIdNew_4981_);
lean_dec_ref(v_e_4980_);
return v_res_4982_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4984_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_4985_ = lean_unsigned_to_nat(18u);
v___x_4986_ = lean_unsigned_to_nat(1854u);
v___x_4987_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_4988_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4989_ = l_mkPanicMessageWithDecl(v___x_4988_, v___x_4987_, v___x_4986_, v___x_4985_, v___x_4984_);
return v___x_4989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_4990_, lean_object* v_newLevels_4991_){
_start:
{
if (lean_obj_tag(v_e_4990_) == 4)
{
lean_object* v_declName_4992_; lean_object* v_us_4993_; uint8_t v___x_4994_; 
v_declName_4992_ = lean_ctor_get(v_e_4990_, 0);
v_us_4993_ = lean_ctor_get(v_e_4990_, 1);
v___x_4994_ = l_ptrEqList___redArg(v_us_4993_, v_newLevels_4991_);
if (v___x_4994_ == 0)
{
lean_object* v___x_4995_; 
lean_inc(v_declName_4992_);
lean_dec_ref(v_e_4990_);
v___x_4995_ = l_Lean_Expr_const___override(v_declName_4992_, v_newLevels_4991_);
return v___x_4995_;
}
else
{
lean_dec(v_newLevels_4991_);
return v_e_4990_;
}
}
else
{
lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
lean_dec(v_newLevels_4991_);
lean_dec_ref(v_e_4990_);
v___x_4996_ = l_Lean_instInhabitedExpr;
v___x_4997_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_4998_ = l_panic___redArg(v___x_4996_, v___x_4997_);
return v___x_4998_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5001_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_5002_ = lean_unsigned_to_nat(14u);
v___x_5003_ = lean_unsigned_to_nat(1865u);
v___x_5004_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_5005_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5006_ = l_mkPanicMessageWithDecl(v___x_5005_, v___x_5004_, v___x_5003_, v___x_5002_, v___x_5001_);
return v___x_5006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_5007_, lean_object* v_u_x27_5008_){
_start:
{
if (lean_obj_tag(v_e_5007_) == 3)
{
lean_object* v_u_5009_; size_t v___x_5010_; size_t v___x_5011_; uint8_t v___x_5012_; 
v_u_5009_ = lean_ctor_get(v_e_5007_, 0);
v___x_5010_ = lean_ptr_addr(v_u_5009_);
v___x_5011_ = lean_ptr_addr(v_u_x27_5008_);
v___x_5012_ = lean_usize_dec_eq(v___x_5010_, v___x_5011_);
if (v___x_5012_ == 0)
{
lean_object* v___x_5013_; 
v___x_5013_ = l_Lean_Expr_sort___override(v_u_x27_5008_);
return v___x_5013_;
}
else
{
lean_dec(v_u_x27_5008_);
lean_inc_ref(v_e_5007_);
return v_e_5007_;
}
}
else
{
lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
lean_dec(v_u_x27_5008_);
v___x_5014_ = l_Lean_instInhabitedExpr;
v___x_5015_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_5016_ = l_panic___redArg(v___x_5014_, v___x_5015_);
return v___x_5016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_5017_, lean_object* v_u_x27_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_5017_, v_u_x27_5018_);
lean_dec_ref(v_e_5017_);
return v_res_5019_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5022_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_5023_ = lean_unsigned_to_nat(17u);
v___x_5024_ = lean_unsigned_to_nat(1876u);
v___x_5025_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_5026_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5027_ = l_mkPanicMessageWithDecl(v___x_5026_, v___x_5025_, v___x_5024_, v___x_5023_, v___x_5022_);
return v___x_5027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_5028_, lean_object* v_newExpr_5029_){
_start:
{
if (lean_obj_tag(v_e_5028_) == 10)
{
lean_object* v_data_5030_; lean_object* v_expr_5031_; size_t v___x_5032_; size_t v___x_5033_; uint8_t v___x_5034_; 
v_data_5030_ = lean_ctor_get(v_e_5028_, 0);
v_expr_5031_ = lean_ctor_get(v_e_5028_, 1);
v___x_5032_ = lean_ptr_addr(v_expr_5031_);
v___x_5033_ = lean_ptr_addr(v_newExpr_5029_);
v___x_5034_ = lean_usize_dec_eq(v___x_5032_, v___x_5033_);
if (v___x_5034_ == 0)
{
lean_object* v___x_5035_; 
lean_inc(v_data_5030_);
lean_dec_ref(v_e_5028_);
v___x_5035_ = l_Lean_Expr_mdata___override(v_data_5030_, v_newExpr_5029_);
return v___x_5035_;
}
else
{
lean_dec_ref(v_newExpr_5029_);
return v_e_5028_;
}
}
else
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
lean_dec_ref(v_newExpr_5029_);
lean_dec_ref(v_e_5028_);
v___x_5036_ = l_Lean_instInhabitedExpr;
v___x_5037_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_5038_ = l_panic___redArg(v___x_5036_, v___x_5037_);
return v___x_5038_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
v___x_5041_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_5042_ = lean_unsigned_to_nat(18u);
v___x_5043_ = lean_unsigned_to_nat(1887u);
v___x_5044_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_5045_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5046_ = l_mkPanicMessageWithDecl(v___x_5045_, v___x_5044_, v___x_5043_, v___x_5042_, v___x_5041_);
return v___x_5046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_5047_, lean_object* v_newExpr_5048_){
_start:
{
if (lean_obj_tag(v_e_5047_) == 11)
{
lean_object* v_typeName_5049_; lean_object* v_idx_5050_; lean_object* v_struct_5051_; size_t v___x_5052_; size_t v___x_5053_; uint8_t v___x_5054_; 
v_typeName_5049_ = lean_ctor_get(v_e_5047_, 0);
v_idx_5050_ = lean_ctor_get(v_e_5047_, 1);
v_struct_5051_ = lean_ctor_get(v_e_5047_, 2);
v___x_5052_ = lean_ptr_addr(v_struct_5051_);
v___x_5053_ = lean_ptr_addr(v_newExpr_5048_);
v___x_5054_ = lean_usize_dec_eq(v___x_5052_, v___x_5053_);
if (v___x_5054_ == 0)
{
lean_object* v___x_5055_; 
lean_inc(v_idx_5050_);
lean_inc(v_typeName_5049_);
lean_dec_ref(v_e_5047_);
v___x_5055_ = l_Lean_Expr_proj___override(v_typeName_5049_, v_idx_5050_, v_newExpr_5048_);
return v___x_5055_;
}
else
{
lean_dec_ref(v_newExpr_5048_);
return v_e_5047_;
}
}
else
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
lean_dec_ref(v_newExpr_5048_);
lean_dec_ref(v_e_5047_);
v___x_5056_ = l_Lean_instInhabitedExpr;
v___x_5057_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_5058_ = l_panic___redArg(v___x_5056_, v___x_5057_);
return v___x_5058_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5061_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5062_ = lean_unsigned_to_nat(23u);
v___x_5063_ = lean_unsigned_to_nat(1902u);
v___x_5064_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_5065_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5066_ = l_mkPanicMessageWithDecl(v___x_5065_, v___x_5064_, v___x_5063_, v___x_5062_, v___x_5061_);
return v___x_5066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_5067_, uint8_t v_newBinfo_5068_, lean_object* v_newDomain_5069_, lean_object* v_newBody_5070_){
_start:
{
if (lean_obj_tag(v_e_5067_) == 7)
{
lean_object* v_binderName_5071_; lean_object* v_binderType_5072_; lean_object* v_body_5073_; uint8_t v_binderInfo_5074_; uint8_t v___y_5076_; size_t v___x_5080_; size_t v___x_5081_; uint8_t v___x_5082_; 
v_binderName_5071_ = lean_ctor_get(v_e_5067_, 0);
v_binderType_5072_ = lean_ctor_get(v_e_5067_, 1);
v_body_5073_ = lean_ctor_get(v_e_5067_, 2);
v_binderInfo_5074_ = lean_ctor_get_uint8(v_e_5067_, sizeof(void*)*3 + 8);
v___x_5080_ = lean_ptr_addr(v_binderType_5072_);
v___x_5081_ = lean_ptr_addr(v_newDomain_5069_);
v___x_5082_ = lean_usize_dec_eq(v___x_5080_, v___x_5081_);
if (v___x_5082_ == 0)
{
v___y_5076_ = v___x_5082_;
goto v___jp_5075_;
}
else
{
size_t v___x_5083_; size_t v___x_5084_; uint8_t v___x_5085_; 
v___x_5083_ = lean_ptr_addr(v_body_5073_);
v___x_5084_ = lean_ptr_addr(v_newBody_5070_);
v___x_5085_ = lean_usize_dec_eq(v___x_5083_, v___x_5084_);
v___y_5076_ = v___x_5085_;
goto v___jp_5075_;
}
v___jp_5075_:
{
if (v___y_5076_ == 0)
{
lean_object* v___x_5077_; 
lean_inc(v_binderName_5071_);
lean_dec_ref(v_e_5067_);
v___x_5077_ = l_Lean_Expr_forallE___override(v_binderName_5071_, v_newDomain_5069_, v_newBody_5070_, v_newBinfo_5068_);
return v___x_5077_;
}
else
{
uint8_t v___x_5078_; 
v___x_5078_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5074_, v_newBinfo_5068_);
if (v___x_5078_ == 0)
{
lean_object* v___x_5079_; 
lean_inc(v_binderName_5071_);
lean_dec_ref(v_e_5067_);
v___x_5079_ = l_Lean_Expr_forallE___override(v_binderName_5071_, v_newDomain_5069_, v_newBody_5070_, v_newBinfo_5068_);
return v___x_5079_;
}
else
{
lean_dec_ref(v_newBody_5070_);
lean_dec_ref(v_newDomain_5069_);
return v_e_5067_;
}
}
}
}
else
{
lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; 
lean_dec_ref(v_newBody_5070_);
lean_dec_ref(v_newDomain_5069_);
lean_dec_ref(v_e_5067_);
v___x_5086_ = l_Lean_instInhabitedExpr;
v___x_5087_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_5088_ = l_panic___redArg(v___x_5086_, v___x_5087_);
return v___x_5088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_5089_, lean_object* v_newBinfo_5090_, lean_object* v_newDomain_5091_, lean_object* v_newBody_5092_){
_start:
{
uint8_t v_newBinfo_boxed_5093_; lean_object* v_res_5094_; 
v_newBinfo_boxed_5093_ = lean_unbox(v_newBinfo_5090_);
v_res_5094_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5089_, v_newBinfo_boxed_5093_, v_newDomain_5091_, v_newBody_5092_);
return v_res_5094_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; 
v___x_5096_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5097_ = lean_unsigned_to_nat(24u);
v___x_5098_ = lean_unsigned_to_nat(1913u);
v___x_5099_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_5100_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5101_ = l_mkPanicMessageWithDecl(v___x_5100_, v___x_5099_, v___x_5098_, v___x_5097_, v___x_5096_);
return v___x_5101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_5102_, lean_object* v_newDomain_5103_, lean_object* v_newBody_5104_){
_start:
{
if (lean_obj_tag(v_e_5102_) == 7)
{
lean_object* v_binderName_5105_; lean_object* v_binderType_5106_; lean_object* v_body_5107_; uint8_t v_binderInfo_5108_; uint8_t v___y_5110_; size_t v___x_5114_; size_t v___x_5115_; uint8_t v___x_5116_; 
v_binderName_5105_ = lean_ctor_get(v_e_5102_, 0);
v_binderType_5106_ = lean_ctor_get(v_e_5102_, 1);
v_body_5107_ = lean_ctor_get(v_e_5102_, 2);
v_binderInfo_5108_ = lean_ctor_get_uint8(v_e_5102_, sizeof(void*)*3 + 8);
v___x_5114_ = lean_ptr_addr(v_binderType_5106_);
v___x_5115_ = lean_ptr_addr(v_newDomain_5103_);
v___x_5116_ = lean_usize_dec_eq(v___x_5114_, v___x_5115_);
if (v___x_5116_ == 0)
{
v___y_5110_ = v___x_5116_;
goto v___jp_5109_;
}
else
{
size_t v___x_5117_; size_t v___x_5118_; uint8_t v___x_5119_; 
v___x_5117_ = lean_ptr_addr(v_body_5107_);
v___x_5118_ = lean_ptr_addr(v_newBody_5104_);
v___x_5119_ = lean_usize_dec_eq(v___x_5117_, v___x_5118_);
v___y_5110_ = v___x_5119_;
goto v___jp_5109_;
}
v___jp_5109_:
{
if (v___y_5110_ == 0)
{
lean_object* v___x_5111_; 
lean_inc(v_binderName_5105_);
lean_dec_ref(v_e_5102_);
v___x_5111_ = l_Lean_Expr_forallE___override(v_binderName_5105_, v_newDomain_5103_, v_newBody_5104_, v_binderInfo_5108_);
return v___x_5111_;
}
else
{
uint8_t v___x_5112_; 
v___x_5112_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5108_, v_binderInfo_5108_);
if (v___x_5112_ == 0)
{
lean_object* v___x_5113_; 
lean_inc(v_binderName_5105_);
lean_dec_ref(v_e_5102_);
v___x_5113_ = l_Lean_Expr_forallE___override(v_binderName_5105_, v_newDomain_5103_, v_newBody_5104_, v_binderInfo_5108_);
return v___x_5113_;
}
else
{
lean_dec_ref(v_newBody_5104_);
lean_dec_ref(v_newDomain_5103_);
return v_e_5102_;
}
}
}
}
else
{
lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
lean_dec_ref(v_newBody_5104_);
lean_dec_ref(v_newDomain_5103_);
lean_dec_ref(v_e_5102_);
v___x_5120_ = l_Lean_instInhabitedExpr;
v___x_5121_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_5122_ = l_panic___redArg(v___x_5120_, v___x_5121_);
return v___x_5122_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; 
v___x_5125_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5126_ = lean_unsigned_to_nat(19u);
v___x_5127_ = lean_unsigned_to_nat(1922u);
v___x_5128_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_5129_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5130_ = l_mkPanicMessageWithDecl(v___x_5129_, v___x_5128_, v___x_5127_, v___x_5126_, v___x_5125_);
return v___x_5130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_5131_, uint8_t v_newBinfo_5132_, lean_object* v_newDomain_5133_, lean_object* v_newBody_5134_){
_start:
{
if (lean_obj_tag(v_e_5131_) == 6)
{
lean_object* v_binderName_5135_; lean_object* v_binderType_5136_; lean_object* v_body_5137_; uint8_t v_binderInfo_5138_; uint8_t v___y_5140_; size_t v___x_5144_; size_t v___x_5145_; uint8_t v___x_5146_; 
v_binderName_5135_ = lean_ctor_get(v_e_5131_, 0);
v_binderType_5136_ = lean_ctor_get(v_e_5131_, 1);
v_body_5137_ = lean_ctor_get(v_e_5131_, 2);
v_binderInfo_5138_ = lean_ctor_get_uint8(v_e_5131_, sizeof(void*)*3 + 8);
v___x_5144_ = lean_ptr_addr(v_binderType_5136_);
v___x_5145_ = lean_ptr_addr(v_newDomain_5133_);
v___x_5146_ = lean_usize_dec_eq(v___x_5144_, v___x_5145_);
if (v___x_5146_ == 0)
{
v___y_5140_ = v___x_5146_;
goto v___jp_5139_;
}
else
{
size_t v___x_5147_; size_t v___x_5148_; uint8_t v___x_5149_; 
v___x_5147_ = lean_ptr_addr(v_body_5137_);
v___x_5148_ = lean_ptr_addr(v_newBody_5134_);
v___x_5149_ = lean_usize_dec_eq(v___x_5147_, v___x_5148_);
v___y_5140_ = v___x_5149_;
goto v___jp_5139_;
}
v___jp_5139_:
{
if (v___y_5140_ == 0)
{
lean_object* v___x_5141_; 
lean_inc(v_binderName_5135_);
lean_dec_ref(v_e_5131_);
v___x_5141_ = l_Lean_Expr_lam___override(v_binderName_5135_, v_newDomain_5133_, v_newBody_5134_, v_newBinfo_5132_);
return v___x_5141_;
}
else
{
uint8_t v___x_5142_; 
v___x_5142_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5138_, v_newBinfo_5132_);
if (v___x_5142_ == 0)
{
lean_object* v___x_5143_; 
lean_inc(v_binderName_5135_);
lean_dec_ref(v_e_5131_);
v___x_5143_ = l_Lean_Expr_lam___override(v_binderName_5135_, v_newDomain_5133_, v_newBody_5134_, v_newBinfo_5132_);
return v___x_5143_;
}
else
{
lean_dec_ref(v_newBody_5134_);
lean_dec_ref(v_newDomain_5133_);
return v_e_5131_;
}
}
}
}
else
{
lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; 
lean_dec_ref(v_newBody_5134_);
lean_dec_ref(v_newDomain_5133_);
lean_dec_ref(v_e_5131_);
v___x_5150_ = l_Lean_instInhabitedExpr;
v___x_5151_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_5152_ = l_panic___redArg(v___x_5150_, v___x_5151_);
return v___x_5152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_5153_, lean_object* v_newBinfo_5154_, lean_object* v_newDomain_5155_, lean_object* v_newBody_5156_){
_start:
{
uint8_t v_newBinfo_boxed_5157_; lean_object* v_res_5158_; 
v_newBinfo_boxed_5157_ = lean_unbox(v_newBinfo_5154_);
v_res_5158_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5153_, v_newBinfo_boxed_5157_, v_newDomain_5155_, v_newBody_5156_);
return v_res_5158_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; 
v___x_5160_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5161_ = lean_unsigned_to_nat(20u);
v___x_5162_ = lean_unsigned_to_nat(1933u);
v___x_5163_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5164_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5165_ = l_mkPanicMessageWithDecl(v___x_5164_, v___x_5163_, v___x_5162_, v___x_5161_, v___x_5160_);
return v___x_5165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5166_, lean_object* v_newDomain_5167_, lean_object* v_newBody_5168_){
_start:
{
if (lean_obj_tag(v_e_5166_) == 6)
{
lean_object* v_binderName_5169_; lean_object* v_binderType_5170_; lean_object* v_body_5171_; uint8_t v_binderInfo_5172_; uint8_t v___y_5174_; size_t v___x_5178_; size_t v___x_5179_; uint8_t v___x_5180_; 
v_binderName_5169_ = lean_ctor_get(v_e_5166_, 0);
v_binderType_5170_ = lean_ctor_get(v_e_5166_, 1);
v_body_5171_ = lean_ctor_get(v_e_5166_, 2);
v_binderInfo_5172_ = lean_ctor_get_uint8(v_e_5166_, sizeof(void*)*3 + 8);
v___x_5178_ = lean_ptr_addr(v_binderType_5170_);
v___x_5179_ = lean_ptr_addr(v_newDomain_5167_);
v___x_5180_ = lean_usize_dec_eq(v___x_5178_, v___x_5179_);
if (v___x_5180_ == 0)
{
v___y_5174_ = v___x_5180_;
goto v___jp_5173_;
}
else
{
size_t v___x_5181_; size_t v___x_5182_; uint8_t v___x_5183_; 
v___x_5181_ = lean_ptr_addr(v_body_5171_);
v___x_5182_ = lean_ptr_addr(v_newBody_5168_);
v___x_5183_ = lean_usize_dec_eq(v___x_5181_, v___x_5182_);
v___y_5174_ = v___x_5183_;
goto v___jp_5173_;
}
v___jp_5173_:
{
if (v___y_5174_ == 0)
{
lean_object* v___x_5175_; 
lean_inc(v_binderName_5169_);
lean_dec_ref(v_e_5166_);
v___x_5175_ = l_Lean_Expr_lam___override(v_binderName_5169_, v_newDomain_5167_, v_newBody_5168_, v_binderInfo_5172_);
return v___x_5175_;
}
else
{
uint8_t v___x_5176_; 
v___x_5176_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5172_, v_binderInfo_5172_);
if (v___x_5176_ == 0)
{
lean_object* v___x_5177_; 
lean_inc(v_binderName_5169_);
lean_dec_ref(v_e_5166_);
v___x_5177_ = l_Lean_Expr_lam___override(v_binderName_5169_, v_newDomain_5167_, v_newBody_5168_, v_binderInfo_5172_);
return v___x_5177_;
}
else
{
lean_dec_ref(v_newBody_5168_);
lean_dec_ref(v_newDomain_5167_);
return v_e_5166_;
}
}
}
}
else
{
lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; 
lean_dec_ref(v_newBody_5168_);
lean_dec_ref(v_newDomain_5167_);
lean_dec_ref(v_e_5166_);
v___x_5184_ = l_Lean_instInhabitedExpr;
v___x_5185_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5186_ = l_panic___redArg(v___x_5184_, v___x_5185_);
return v___x_5186_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; 
v___x_5188_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5189_ = lean_unsigned_to_nat(22u);
v___x_5190_ = lean_unsigned_to_nat(1942u);
v___x_5191_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5192_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5193_ = l_mkPanicMessageWithDecl(v___x_5192_, v___x_5191_, v___x_5190_, v___x_5189_, v___x_5188_);
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5194_, lean_object* v_newType_5195_, lean_object* v_newVal_5196_, lean_object* v_newBody_5197_, uint8_t v_newNondep_5198_){
_start:
{
if (lean_obj_tag(v_e_5194_) == 8)
{
lean_object* v_declName_5199_; lean_object* v_type_5200_; lean_object* v_value_5201_; lean_object* v_body_5202_; uint8_t v_nondep_5203_; uint8_t v___y_5205_; size_t v___x_5213_; size_t v___x_5214_; uint8_t v___x_5215_; 
v_declName_5199_ = lean_ctor_get(v_e_5194_, 0);
v_type_5200_ = lean_ctor_get(v_e_5194_, 1);
v_value_5201_ = lean_ctor_get(v_e_5194_, 2);
v_body_5202_ = lean_ctor_get(v_e_5194_, 3);
v_nondep_5203_ = lean_ctor_get_uint8(v_e_5194_, sizeof(void*)*4 + 8);
v___x_5213_ = lean_ptr_addr(v_type_5200_);
v___x_5214_ = lean_ptr_addr(v_newType_5195_);
v___x_5215_ = lean_usize_dec_eq(v___x_5213_, v___x_5214_);
if (v___x_5215_ == 0)
{
v___y_5205_ = v___x_5215_;
goto v___jp_5204_;
}
else
{
size_t v___x_5216_; size_t v___x_5217_; uint8_t v___x_5218_; 
v___x_5216_ = lean_ptr_addr(v_value_5201_);
v___x_5217_ = lean_ptr_addr(v_newVal_5196_);
v___x_5218_ = lean_usize_dec_eq(v___x_5216_, v___x_5217_);
v___y_5205_ = v___x_5218_;
goto v___jp_5204_;
}
v___jp_5204_:
{
if (v___y_5205_ == 0)
{
lean_object* v___x_5206_; 
lean_inc(v_declName_5199_);
lean_dec_ref(v_e_5194_);
v___x_5206_ = l_Lean_Expr_letE___override(v_declName_5199_, v_newType_5195_, v_newVal_5196_, v_newBody_5197_, v_newNondep_5198_);
return v___x_5206_;
}
else
{
size_t v___x_5207_; size_t v___x_5208_; uint8_t v___x_5209_; 
v___x_5207_ = lean_ptr_addr(v_body_5202_);
v___x_5208_ = lean_ptr_addr(v_newBody_5197_);
v___x_5209_ = lean_usize_dec_eq(v___x_5207_, v___x_5208_);
if (v___x_5209_ == 0)
{
lean_object* v___x_5210_; 
lean_inc(v_declName_5199_);
lean_dec_ref(v_e_5194_);
v___x_5210_ = l_Lean_Expr_letE___override(v_declName_5199_, v_newType_5195_, v_newVal_5196_, v_newBody_5197_, v_newNondep_5198_);
return v___x_5210_;
}
else
{
if (v_nondep_5203_ == 0)
{
if (v_newNondep_5198_ == 0)
{
lean_dec_ref(v_newBody_5197_);
lean_dec_ref(v_newVal_5196_);
lean_dec_ref(v_newType_5195_);
return v_e_5194_;
}
else
{
lean_object* v___x_5211_; 
lean_inc(v_declName_5199_);
lean_dec_ref(v_e_5194_);
v___x_5211_ = l_Lean_Expr_letE___override(v_declName_5199_, v_newType_5195_, v_newVal_5196_, v_newBody_5197_, v_newNondep_5198_);
return v___x_5211_;
}
}
else
{
if (v_newNondep_5198_ == 0)
{
lean_object* v___x_5212_; 
lean_inc(v_declName_5199_);
lean_dec_ref(v_e_5194_);
v___x_5212_ = l_Lean_Expr_letE___override(v_declName_5199_, v_newType_5195_, v_newVal_5196_, v_newBody_5197_, v_newNondep_5198_);
return v___x_5212_;
}
else
{
lean_dec_ref(v_newBody_5197_);
lean_dec_ref(v_newVal_5196_);
lean_dec_ref(v_newType_5195_);
return v_e_5194_;
}
}
}
}
}
}
else
{
lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; 
lean_dec_ref(v_newBody_5197_);
lean_dec_ref(v_newVal_5196_);
lean_dec_ref(v_newType_5195_);
lean_dec_ref(v_e_5194_);
v___x_5219_ = l_Lean_instInhabitedExpr;
v___x_5220_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5221_ = l_panic___redArg(v___x_5219_, v___x_5220_);
return v___x_5221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5222_, lean_object* v_newType_5223_, lean_object* v_newVal_5224_, lean_object* v_newBody_5225_, lean_object* v_newNondep_5226_){
_start:
{
uint8_t v_newNondep_boxed_5227_; lean_object* v_res_5228_; 
v_newNondep_boxed_5227_ = lean_unbox(v_newNondep_5226_);
v_res_5228_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5222_, v_newType_5223_, v_newVal_5224_, v_newBody_5225_, v_newNondep_boxed_5227_);
return v_res_5228_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; 
v___x_5230_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5231_ = lean_unsigned_to_nat(27u);
v___x_5232_ = lean_unsigned_to_nat(1955u);
v___x_5233_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5234_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5235_ = l_mkPanicMessageWithDecl(v___x_5234_, v___x_5233_, v___x_5232_, v___x_5231_, v___x_5230_);
return v___x_5235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5236_, lean_object* v_newType_5237_, lean_object* v_newVal_5238_, lean_object* v_newBody_5239_){
_start:
{
if (lean_obj_tag(v_e_5236_) == 8)
{
lean_object* v_declName_5240_; lean_object* v_type_5241_; lean_object* v_value_5242_; lean_object* v_body_5243_; uint8_t v_nondep_5244_; uint8_t v___y_5246_; size_t v___x_5252_; size_t v___x_5253_; uint8_t v___x_5254_; 
v_declName_5240_ = lean_ctor_get(v_e_5236_, 0);
v_type_5241_ = lean_ctor_get(v_e_5236_, 1);
v_value_5242_ = lean_ctor_get(v_e_5236_, 2);
v_body_5243_ = lean_ctor_get(v_e_5236_, 3);
v_nondep_5244_ = lean_ctor_get_uint8(v_e_5236_, sizeof(void*)*4 + 8);
v___x_5252_ = lean_ptr_addr(v_type_5241_);
v___x_5253_ = lean_ptr_addr(v_newType_5237_);
v___x_5254_ = lean_usize_dec_eq(v___x_5252_, v___x_5253_);
if (v___x_5254_ == 0)
{
v___y_5246_ = v___x_5254_;
goto v___jp_5245_;
}
else
{
size_t v___x_5255_; size_t v___x_5256_; uint8_t v___x_5257_; 
v___x_5255_ = lean_ptr_addr(v_value_5242_);
v___x_5256_ = lean_ptr_addr(v_newVal_5238_);
v___x_5257_ = lean_usize_dec_eq(v___x_5255_, v___x_5256_);
v___y_5246_ = v___x_5257_;
goto v___jp_5245_;
}
v___jp_5245_:
{
if (v___y_5246_ == 0)
{
lean_object* v___x_5247_; 
lean_inc(v_declName_5240_);
lean_dec_ref(v_e_5236_);
v___x_5247_ = l_Lean_Expr_letE___override(v_declName_5240_, v_newType_5237_, v_newVal_5238_, v_newBody_5239_, v_nondep_5244_);
return v___x_5247_;
}
else
{
size_t v___x_5248_; size_t v___x_5249_; uint8_t v___x_5250_; 
v___x_5248_ = lean_ptr_addr(v_body_5243_);
v___x_5249_ = lean_ptr_addr(v_newBody_5239_);
v___x_5250_ = lean_usize_dec_eq(v___x_5248_, v___x_5249_);
if (v___x_5250_ == 0)
{
lean_object* v___x_5251_; 
lean_inc(v_declName_5240_);
lean_dec_ref(v_e_5236_);
v___x_5251_ = l_Lean_Expr_letE___override(v_declName_5240_, v_newType_5237_, v_newVal_5238_, v_newBody_5239_, v_nondep_5244_);
return v___x_5251_;
}
else
{
lean_dec_ref(v_newBody_5239_);
lean_dec_ref(v_newVal_5238_);
lean_dec_ref(v_newType_5237_);
return v_e_5236_;
}
}
}
}
else
{
lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; 
lean_dec_ref(v_newBody_5239_);
lean_dec_ref(v_newVal_5238_);
lean_dec_ref(v_newType_5237_);
lean_dec_ref(v_e_5236_);
v___x_5258_ = l_Lean_instInhabitedExpr;
v___x_5259_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5260_ = l_panic___redArg(v___x_5258_, v___x_5259_);
return v___x_5260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5261_, lean_object* v_x_5262_){
_start:
{
if (lean_obj_tag(v_x_5261_) == 5)
{
lean_object* v_fn_5263_; lean_object* v_arg_5264_; lean_object* v___x_5265_; uint8_t v___y_5267_; size_t v___x_5269_; size_t v___x_5270_; uint8_t v___x_5271_; 
v_fn_5263_ = lean_ctor_get(v_x_5261_, 0);
v_arg_5264_ = lean_ctor_get(v_x_5261_, 1);
lean_inc_ref(v_fn_5263_);
v___x_5265_ = l_Lean_Expr_updateFn(v_fn_5263_, v_x_5262_);
v___x_5269_ = lean_ptr_addr(v_fn_5263_);
v___x_5270_ = lean_ptr_addr(v___x_5265_);
v___x_5271_ = lean_usize_dec_eq(v___x_5269_, v___x_5270_);
if (v___x_5271_ == 0)
{
v___y_5267_ = v___x_5271_;
goto v___jp_5266_;
}
else
{
size_t v___x_5272_; uint8_t v___x_5273_; 
v___x_5272_ = lean_ptr_addr(v_arg_5264_);
v___x_5273_ = lean_usize_dec_eq(v___x_5272_, v___x_5272_);
v___y_5267_ = v___x_5273_;
goto v___jp_5266_;
}
v___jp_5266_:
{
if (v___y_5267_ == 0)
{
lean_object* v___x_5268_; 
lean_inc_ref(v_arg_5264_);
lean_dec_ref(v_x_5261_);
v___x_5268_ = l_Lean_Expr_app___override(v___x_5265_, v_arg_5264_);
return v___x_5268_;
}
else
{
lean_dec_ref(v___x_5265_);
return v_x_5261_;
}
}
}
else
{
lean_dec_ref(v_x_5261_);
lean_inc_ref(v_x_5262_);
return v_x_5262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5274_, lean_object* v_x_5275_){
_start:
{
lean_object* v_res_5276_; 
v_res_5276_ = l_Lean_Expr_updateFn(v_x_5274_, v_x_5275_);
lean_dec_ref(v_x_5275_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5277_){
_start:
{
if (lean_obj_tag(v_e_5277_) == 6)
{
lean_object* v_binderName_5278_; lean_object* v_binderType_5279_; lean_object* v_body_5280_; uint8_t v_binderInfo_5281_; lean_object* v_b_x27_5282_; uint8_t v___y_5284_; uint8_t v___y_5289_; 
v_binderName_5278_ = lean_ctor_get(v_e_5277_, 0);
v_binderType_5279_ = lean_ctor_get(v_e_5277_, 1);
v_body_5280_ = lean_ctor_get(v_e_5277_, 2);
v_binderInfo_5281_ = lean_ctor_get_uint8(v_e_5277_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5280_);
v_b_x27_5282_ = l_Lean_Expr_eta(v_body_5280_);
if (lean_obj_tag(v_b_x27_5282_) == 5)
{
lean_object* v_arg_5299_; 
v_arg_5299_ = lean_ctor_get(v_b_x27_5282_, 1);
lean_inc_ref(v_arg_5299_);
if (lean_obj_tag(v_arg_5299_) == 0)
{
lean_object* v_fn_5300_; lean_object* v_deBruijnIndex_5301_; lean_object* v___x_5302_; uint8_t v___x_5303_; 
v_fn_5300_ = lean_ctor_get(v_b_x27_5282_, 0);
lean_inc_ref(v_fn_5300_);
v_deBruijnIndex_5301_ = lean_ctor_get(v_arg_5299_, 0);
lean_inc(v_deBruijnIndex_5301_);
lean_dec_ref(v_arg_5299_);
v___x_5302_ = lean_unsigned_to_nat(0u);
v___x_5303_ = lean_nat_dec_eq(v_deBruijnIndex_5301_, v___x_5302_);
lean_dec(v_deBruijnIndex_5301_);
if (v___x_5303_ == 0)
{
lean_dec_ref(v_fn_5300_);
goto v___jp_5293_;
}
else
{
uint8_t v___x_5304_; 
v___x_5304_ = lean_expr_has_loose_bvar(v_fn_5300_, v___x_5302_);
if (v___x_5304_ == 0)
{
lean_object* v___x_5305_; lean_object* v___x_5306_; 
lean_dec_ref(v_b_x27_5282_);
lean_dec_ref(v_e_5277_);
v___x_5305_ = lean_unsigned_to_nat(1u);
v___x_5306_ = lean_expr_lower_loose_bvars(v_fn_5300_, v___x_5305_, v___x_5305_);
lean_dec_ref(v_fn_5300_);
return v___x_5306_;
}
else
{
size_t v___x_5307_; uint8_t v___x_5308_; 
lean_dec_ref(v_fn_5300_);
v___x_5307_ = lean_ptr_addr(v_binderType_5279_);
v___x_5308_ = lean_usize_dec_eq(v___x_5307_, v___x_5307_);
if (v___x_5308_ == 0)
{
v___y_5284_ = v___x_5308_;
goto v___jp_5283_;
}
else
{
size_t v___x_5309_; size_t v___x_5310_; uint8_t v___x_5311_; 
v___x_5309_ = lean_ptr_addr(v_body_5280_);
v___x_5310_ = lean_ptr_addr(v_b_x27_5282_);
v___x_5311_ = lean_usize_dec_eq(v___x_5309_, v___x_5310_);
v___y_5284_ = v___x_5311_;
goto v___jp_5283_;
}
}
}
}
else
{
lean_dec_ref(v_arg_5299_);
goto v___jp_5293_;
}
}
else
{
goto v___jp_5293_;
}
v___jp_5283_:
{
if (v___y_5284_ == 0)
{
lean_object* v___x_5285_; 
lean_inc_ref(v_binderType_5279_);
lean_inc(v_binderName_5278_);
lean_dec_ref(v_e_5277_);
v___x_5285_ = l_Lean_Expr_lam___override(v_binderName_5278_, v_binderType_5279_, v_b_x27_5282_, v_binderInfo_5281_);
return v___x_5285_;
}
else
{
uint8_t v___x_5286_; 
v___x_5286_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5281_, v_binderInfo_5281_);
if (v___x_5286_ == 0)
{
lean_object* v___x_5287_; 
lean_inc_ref(v_binderType_5279_);
lean_inc(v_binderName_5278_);
lean_dec_ref(v_e_5277_);
v___x_5287_ = l_Lean_Expr_lam___override(v_binderName_5278_, v_binderType_5279_, v_b_x27_5282_, v_binderInfo_5281_);
return v___x_5287_;
}
else
{
lean_dec_ref(v_b_x27_5282_);
return v_e_5277_;
}
}
}
v___jp_5288_:
{
if (v___y_5289_ == 0)
{
lean_object* v___x_5290_; 
lean_inc_ref(v_binderType_5279_);
lean_inc(v_binderName_5278_);
lean_dec_ref(v_e_5277_);
v___x_5290_ = l_Lean_Expr_lam___override(v_binderName_5278_, v_binderType_5279_, v_b_x27_5282_, v_binderInfo_5281_);
return v___x_5290_;
}
else
{
uint8_t v___x_5291_; 
v___x_5291_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5281_, v_binderInfo_5281_);
if (v___x_5291_ == 0)
{
lean_object* v___x_5292_; 
lean_inc_ref(v_binderType_5279_);
lean_inc(v_binderName_5278_);
lean_dec_ref(v_e_5277_);
v___x_5292_ = l_Lean_Expr_lam___override(v_binderName_5278_, v_binderType_5279_, v_b_x27_5282_, v_binderInfo_5281_);
return v___x_5292_;
}
else
{
lean_dec_ref(v_b_x27_5282_);
return v_e_5277_;
}
}
}
v___jp_5293_:
{
size_t v___x_5294_; uint8_t v___x_5295_; 
v___x_5294_ = lean_ptr_addr(v_binderType_5279_);
v___x_5295_ = lean_usize_dec_eq(v___x_5294_, v___x_5294_);
if (v___x_5295_ == 0)
{
v___y_5289_ = v___x_5295_;
goto v___jp_5288_;
}
else
{
size_t v___x_5296_; size_t v___x_5297_; uint8_t v___x_5298_; 
v___x_5296_ = lean_ptr_addr(v_body_5280_);
v___x_5297_ = lean_ptr_addr(v_b_x27_5282_);
v___x_5298_ = lean_usize_dec_eq(v___x_5296_, v___x_5297_);
v___y_5289_ = v___x_5298_;
goto v___jp_5288_;
}
}
}
else
{
return v_e_5277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5312_, lean_object* v_optionName_5313_, lean_object* v_inst_5314_, lean_object* v_val_5315_){
_start:
{
lean_object* v_toDataValue_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; 
v_toDataValue_5316_ = lean_ctor_get(v_inst_5314_, 0);
lean_inc_ref(v_toDataValue_5316_);
lean_dec_ref(v_inst_5314_);
v___x_5317_ = lean_box(0);
v___x_5318_ = lean_apply_1(v_toDataValue_5316_, v_val_5315_);
v___x_5319_ = l_Lean_KVMap_insert(v___x_5317_, v_optionName_5313_, v___x_5318_);
v___x_5320_ = l_Lean_Expr_mdata___override(v___x_5319_, v_e_5312_);
return v___x_5320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5321_, lean_object* v_e_5322_, lean_object* v_optionName_5323_, lean_object* v_inst_5324_, lean_object* v_val_5325_){
_start:
{
lean_object* v___x_5326_; 
v___x_5326_ = l_Lean_Expr_setOption___redArg(v_e_5322_, v_optionName_5323_, v_inst_5324_, v_val_5325_);
return v___x_5326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5327_, lean_object* v_optionName_5328_, uint8_t v_val_5329_){
_start:
{
lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; 
v___x_5330_ = lean_box(0);
v___x_5331_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5331_, 0, v_val_5329_);
v___x_5332_ = l_Lean_KVMap_insert(v___x_5330_, v_optionName_5328_, v___x_5331_);
v___x_5333_ = l_Lean_Expr_mdata___override(v___x_5332_, v_e_5327_);
return v___x_5333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5334_, lean_object* v_optionName_5335_, lean_object* v_val_5336_){
_start:
{
uint8_t v_val_boxed_5337_; lean_object* v_res_5338_; 
v_val_boxed_5337_ = lean_unbox(v_val_5336_);
v_res_5338_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5334_, v_optionName_5335_, v_val_boxed_5337_);
return v_res_5338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5344_, uint8_t v_flag_5345_){
_start:
{
lean_object* v___x_5346_; lean_object* v___x_5347_; 
v___x_5346_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5347_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5344_, v___x_5346_, v_flag_5345_);
return v___x_5347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5348_, lean_object* v_flag_5349_){
_start:
{
uint8_t v_flag_boxed_5350_; lean_object* v_res_5351_; 
v_flag_boxed_5350_ = lean_unbox(v_flag_5349_);
v_res_5351_ = l_Lean_Expr_setPPExplicit(v_e_5348_, v_flag_boxed_5350_);
return v_res_5351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5356_, uint8_t v_flag_5357_){
_start:
{
lean_object* v___x_5358_; lean_object* v___x_5359_; 
v___x_5358_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5359_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5356_, v___x_5358_, v_flag_5357_);
return v___x_5359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5360_, lean_object* v_flag_5361_){
_start:
{
uint8_t v_flag_boxed_5362_; lean_object* v_res_5363_; 
v_flag_boxed_5362_ = lean_unbox(v_flag_5361_);
v_res_5363_ = l_Lean_Expr_setPPUniverses(v_e_5360_, v_flag_boxed_5362_);
return v_res_5363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5368_, uint8_t v_flag_5369_){
_start:
{
lean_object* v___x_5370_; lean_object* v___x_5371_; 
v___x_5370_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5371_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5368_, v___x_5370_, v_flag_5369_);
return v___x_5371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5372_, lean_object* v_flag_5373_){
_start:
{
uint8_t v_flag_boxed_5374_; lean_object* v_res_5375_; 
v_flag_boxed_5374_ = lean_unbox(v_flag_5373_);
v_res_5375_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5372_, v_flag_boxed_5374_);
return v_res_5375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5380_, uint8_t v_flag_5381_){
_start:
{
lean_object* v___x_5382_; lean_object* v___x_5383_; 
v___x_5382_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5383_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5380_, v___x_5382_, v_flag_5381_);
return v___x_5383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5384_, lean_object* v_flag_5385_){
_start:
{
uint8_t v_flag_boxed_5386_; lean_object* v_res_5387_; 
v_flag_boxed_5386_ = lean_unbox(v_flag_5385_);
v_res_5387_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5384_, v_flag_boxed_5386_);
return v_res_5387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5392_, uint8_t v_flag_5393_){
_start:
{
lean_object* v___x_5394_; lean_object* v___x_5395_; 
v___x_5394_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5395_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5392_, v___x_5394_, v_flag_5393_);
return v___x_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5396_, lean_object* v_flag_5397_){
_start:
{
uint8_t v_flag_boxed_5398_; lean_object* v_res_5399_; 
v_flag_boxed_5398_ = lean_unbox(v_flag_5397_);
v_res_5399_ = l_Lean_Expr_setPPNumericTypes(v_e_5396_, v_flag_boxed_5398_);
return v_res_5399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5400_, size_t v_i_5401_, lean_object* v_bs_5402_){
_start:
{
uint8_t v___x_5403_; 
v___x_5403_ = lean_usize_dec_lt(v_i_5401_, v_sz_5400_);
if (v___x_5403_ == 0)
{
return v_bs_5402_;
}
else
{
uint8_t v___x_5404_; lean_object* v_v_5405_; lean_object* v___x_5406_; lean_object* v_bs_x27_5407_; lean_object* v___x_5408_; size_t v___x_5409_; size_t v___x_5410_; lean_object* v___x_5411_; 
v___x_5404_ = 0;
v_v_5405_ = lean_array_uget(v_bs_5402_, v_i_5401_);
v___x_5406_ = lean_unsigned_to_nat(0u);
v_bs_x27_5407_ = lean_array_uset(v_bs_5402_, v_i_5401_, v___x_5406_);
v___x_5408_ = l_Lean_Expr_setPPExplicit(v_v_5405_, v___x_5404_);
v___x_5409_ = ((size_t)1ULL);
v___x_5410_ = lean_usize_add(v_i_5401_, v___x_5409_);
v___x_5411_ = lean_array_uset(v_bs_x27_5407_, v_i_5401_, v___x_5408_);
v_i_5401_ = v___x_5410_;
v_bs_5402_ = v___x_5411_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5413_, lean_object* v_i_5414_, lean_object* v_bs_5415_){
_start:
{
size_t v_sz_boxed_5416_; size_t v_i_boxed_5417_; lean_object* v_res_5418_; 
v_sz_boxed_5416_ = lean_unbox_usize(v_sz_5413_);
lean_dec(v_sz_5413_);
v_i_boxed_5417_ = lean_unbox_usize(v_i_5414_);
lean_dec(v_i_5414_);
v_res_5418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5416_, v_i_boxed_5417_, v_bs_5415_);
return v_res_5418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5419_){
_start:
{
if (lean_obj_tag(v_e_5419_) == 5)
{
lean_object* v___x_5420_; uint8_t v___x_5421_; lean_object* v_f_5422_; lean_object* v_dummy_5423_; lean_object* v_nargs_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; size_t v_sz_5429_; size_t v___x_5430_; lean_object* v_args_5431_; lean_object* v___x_5432_; uint8_t v___x_5433_; lean_object* v___x_5434_; 
v___x_5420_ = l_Lean_Expr_getAppFn(v_e_5419_);
v___x_5421_ = 0;
v_f_5422_ = l_Lean_Expr_setPPExplicit(v___x_5420_, v___x_5421_);
v_dummy_5423_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5424_ = l_Lean_Expr_getAppNumArgs(v_e_5419_);
lean_inc(v_nargs_5424_);
v___x_5425_ = lean_mk_array(v_nargs_5424_, v_dummy_5423_);
v___x_5426_ = lean_unsigned_to_nat(1u);
v___x_5427_ = lean_nat_sub(v_nargs_5424_, v___x_5426_);
lean_dec(v_nargs_5424_);
v___x_5428_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5419_, v___x_5425_, v___x_5427_);
v_sz_5429_ = lean_array_size(v___x_5428_);
v___x_5430_ = ((size_t)0ULL);
v_args_5431_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5429_, v___x_5430_, v___x_5428_);
v___x_5432_ = l_Lean_mkAppN(v_f_5422_, v_args_5431_);
lean_dec_ref(v_args_5431_);
v___x_5433_ = 1;
v___x_5434_ = l_Lean_Expr_setPPExplicit(v___x_5432_, v___x_5433_);
return v___x_5434_;
}
else
{
return v_e_5419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5435_, size_t v_i_5436_, lean_object* v_bs_5437_){
_start:
{
uint8_t v___x_5438_; 
v___x_5438_ = lean_usize_dec_lt(v_i_5436_, v_sz_5435_);
if (v___x_5438_ == 0)
{
return v_bs_5437_;
}
else
{
lean_object* v_v_5439_; lean_object* v___x_5440_; lean_object* v_bs_x27_5441_; lean_object* v___y_5443_; uint8_t v___x_5448_; 
v_v_5439_ = lean_array_uget(v_bs_5437_, v_i_5436_);
v___x_5440_ = lean_unsigned_to_nat(0u);
v_bs_x27_5441_ = lean_array_uset(v_bs_5437_, v_i_5436_, v___x_5440_);
v___x_5448_ = l_Lean_Expr_hasMVar(v_v_5439_);
if (v___x_5448_ == 0)
{
lean_object* v___x_5449_; 
v___x_5449_ = l_Lean_Expr_setPPExplicit(v_v_5439_, v___x_5448_);
v___y_5443_ = v___x_5449_;
goto v___jp_5442_;
}
else
{
v___y_5443_ = v_v_5439_;
goto v___jp_5442_;
}
v___jp_5442_:
{
size_t v___x_5444_; size_t v___x_5445_; lean_object* v___x_5446_; 
v___x_5444_ = ((size_t)1ULL);
v___x_5445_ = lean_usize_add(v_i_5436_, v___x_5444_);
v___x_5446_ = lean_array_uset(v_bs_x27_5441_, v_i_5436_, v___y_5443_);
v_i_5436_ = v___x_5445_;
v_bs_5437_ = v___x_5446_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5450_, lean_object* v_i_5451_, lean_object* v_bs_5452_){
_start:
{
size_t v_sz_boxed_5453_; size_t v_i_boxed_5454_; lean_object* v_res_5455_; 
v_sz_boxed_5453_ = lean_unbox_usize(v_sz_5450_);
lean_dec(v_sz_5450_);
v_i_boxed_5454_ = lean_unbox_usize(v_i_5451_);
lean_dec(v_i_5451_);
v_res_5455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5453_, v_i_boxed_5454_, v_bs_5452_);
return v_res_5455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5456_){
_start:
{
if (lean_obj_tag(v_e_5456_) == 5)
{
lean_object* v___x_5457_; uint8_t v___x_5458_; lean_object* v_f_5459_; lean_object* v_dummy_5460_; lean_object* v_nargs_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; size_t v_sz_5466_; size_t v___x_5467_; lean_object* v_args_5468_; lean_object* v___x_5469_; uint8_t v___x_5470_; lean_object* v___x_5471_; 
v___x_5457_ = l_Lean_Expr_getAppFn(v_e_5456_);
v___x_5458_ = 0;
v_f_5459_ = l_Lean_Expr_setPPExplicit(v___x_5457_, v___x_5458_);
v_dummy_5460_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5461_ = l_Lean_Expr_getAppNumArgs(v_e_5456_);
lean_inc(v_nargs_5461_);
v___x_5462_ = lean_mk_array(v_nargs_5461_, v_dummy_5460_);
v___x_5463_ = lean_unsigned_to_nat(1u);
v___x_5464_ = lean_nat_sub(v_nargs_5461_, v___x_5463_);
lean_dec(v_nargs_5461_);
v___x_5465_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5456_, v___x_5462_, v___x_5464_);
v_sz_5466_ = lean_array_size(v___x_5465_);
v___x_5467_ = ((size_t)0ULL);
v_args_5468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5466_, v___x_5467_, v___x_5465_);
v___x_5469_ = l_Lean_mkAppN(v_f_5459_, v_args_5468_);
lean_dec_ref(v_args_5468_);
v___x_5470_ = 1;
v___x_5471_ = l_Lean_Expr_setPPExplicit(v___x_5469_, v___x_5470_);
return v___x_5471_;
}
else
{
return v_e_5456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5472_, lean_object* v_body_5473_, lean_object* v_x_5474_){
_start:
{
lean_object* v___x_5475_; 
v___x_5475_ = lean_apply_1(v_f_5472_, v_body_5473_);
return v___x_5475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5476_, lean_object* v_binderType_5477_, lean_object* v_x_5478_){
_start:
{
lean_object* v___x_5479_; 
v___x_5479_ = lean_apply_1(v_f_5476_, v_binderType_5477_);
return v___x_5479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5480_, lean_object* v_value_5481_, lean_object* v_x_5482_){
_start:
{
lean_object* v___x_5483_; 
v___x_5483_ = lean_apply_1(v_f_5480_, v_value_5481_);
return v___x_5483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5484_, lean_object* v_type_5485_, lean_object* v_x_5486_){
_start:
{
lean_object* v___x_5487_; 
v___x_5487_ = lean_apply_1(v_f_5484_, v_type_5485_);
return v___x_5487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5488_, lean_object* v_arg_5489_, lean_object* v_x_5490_){
_start:
{
lean_object* v___x_5491_; 
v___x_5491_ = lean_apply_1(v_f_5488_, v_arg_5489_);
return v___x_5491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5492_, lean_object* v_fn_5493_, lean_object* v_x_5494_){
_start:
{
lean_object* v___x_5495_; 
v___x_5495_ = lean_apply_1(v_f_5492_, v_fn_5493_);
return v___x_5495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5496_, lean_object* v_f_5497_, lean_object* v_x_5498_){
_start:
{
switch(lean_obj_tag(v_x_5498_))
{
case 7:
{
lean_object* v_toPure_5499_; lean_object* v_toSeq_5500_; lean_object* v_binderType_5501_; lean_object* v_body_5502_; lean_object* v___f_5503_; lean_object* v___f_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; 
v_toPure_5499_ = lean_ctor_get(v_inst_5496_, 1);
lean_inc(v_toPure_5499_);
v_toSeq_5500_ = lean_ctor_get(v_inst_5496_, 2);
lean_inc_n(v_toSeq_5500_, 2);
lean_dec_ref(v_inst_5496_);
v_binderType_5501_ = lean_ctor_get(v_x_5498_, 1);
v_body_5502_ = lean_ctor_get(v_x_5498_, 2);
lean_inc_ref(v_body_5502_);
lean_inc(v_f_5497_);
v___f_5503_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5503_, 0, v_f_5497_);
lean_closure_set(v___f_5503_, 1, v_body_5502_);
lean_inc_ref(v_binderType_5501_);
v___f_5504_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5504_, 0, v_f_5497_);
lean_closure_set(v___f_5504_, 1, v_binderType_5501_);
v___x_5505_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5505_, 0, v_x_5498_);
v___x_5506_ = lean_apply_2(v_toPure_5499_, lean_box(0), v___x_5505_);
v___x_5507_ = lean_apply_4(v_toSeq_5500_, lean_box(0), lean_box(0), v___x_5506_, v___f_5504_);
v___x_5508_ = lean_apply_4(v_toSeq_5500_, lean_box(0), lean_box(0), v___x_5507_, v___f_5503_);
return v___x_5508_;
}
case 6:
{
lean_object* v_toPure_5509_; lean_object* v_toSeq_5510_; lean_object* v_binderType_5511_; lean_object* v_body_5512_; lean_object* v___f_5513_; lean_object* v___f_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; 
v_toPure_5509_ = lean_ctor_get(v_inst_5496_, 1);
lean_inc(v_toPure_5509_);
v_toSeq_5510_ = lean_ctor_get(v_inst_5496_, 2);
lean_inc_n(v_toSeq_5510_, 2);
lean_dec_ref(v_inst_5496_);
v_binderType_5511_ = lean_ctor_get(v_x_5498_, 1);
v_body_5512_ = lean_ctor_get(v_x_5498_, 2);
lean_inc_ref(v_body_5512_);
lean_inc(v_f_5497_);
v___f_5513_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5513_, 0, v_f_5497_);
lean_closure_set(v___f_5513_, 1, v_body_5512_);
lean_inc_ref(v_binderType_5511_);
v___f_5514_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5514_, 0, v_f_5497_);
lean_closure_set(v___f_5514_, 1, v_binderType_5511_);
v___x_5515_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5515_, 0, v_x_5498_);
v___x_5516_ = lean_apply_2(v_toPure_5509_, lean_box(0), v___x_5515_);
v___x_5517_ = lean_apply_4(v_toSeq_5510_, lean_box(0), lean_box(0), v___x_5516_, v___f_5514_);
v___x_5518_ = lean_apply_4(v_toSeq_5510_, lean_box(0), lean_box(0), v___x_5517_, v___f_5513_);
return v___x_5518_;
}
case 10:
{
lean_object* v_toFunctor_5519_; lean_object* v_expr_5520_; lean_object* v_map_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; 
v_toFunctor_5519_ = lean_ctor_get(v_inst_5496_, 0);
lean_inc_ref(v_toFunctor_5519_);
lean_dec_ref(v_inst_5496_);
v_expr_5520_ = lean_ctor_get(v_x_5498_, 1);
lean_inc_ref(v_expr_5520_);
v_map_5521_ = lean_ctor_get(v_toFunctor_5519_, 0);
lean_inc(v_map_5521_);
lean_dec_ref(v_toFunctor_5519_);
v___x_5522_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5522_, 0, v_x_5498_);
v___x_5523_ = lean_apply_1(v_f_5497_, v_expr_5520_);
v___x_5524_ = lean_apply_4(v_map_5521_, lean_box(0), lean_box(0), v___x_5522_, v___x_5523_);
return v___x_5524_;
}
case 8:
{
lean_object* v_toPure_5525_; lean_object* v_toSeq_5526_; lean_object* v_type_5527_; lean_object* v_value_5528_; lean_object* v_body_5529_; lean_object* v___f_5530_; lean_object* v___f_5531_; lean_object* v___f_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; 
v_toPure_5525_ = lean_ctor_get(v_inst_5496_, 1);
lean_inc(v_toPure_5525_);
v_toSeq_5526_ = lean_ctor_get(v_inst_5496_, 2);
lean_inc_n(v_toSeq_5526_, 3);
lean_dec_ref(v_inst_5496_);
v_type_5527_ = lean_ctor_get(v_x_5498_, 1);
v_value_5528_ = lean_ctor_get(v_x_5498_, 2);
v_body_5529_ = lean_ctor_get(v_x_5498_, 3);
lean_inc_ref(v_body_5529_);
lean_inc_n(v_f_5497_, 2);
v___f_5530_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5530_, 0, v_f_5497_);
lean_closure_set(v___f_5530_, 1, v_body_5529_);
lean_inc_ref(v_value_5528_);
v___f_5531_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5531_, 0, v_f_5497_);
lean_closure_set(v___f_5531_, 1, v_value_5528_);
lean_inc_ref(v_type_5527_);
v___f_5532_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5532_, 0, v_f_5497_);
lean_closure_set(v___f_5532_, 1, v_type_5527_);
v___x_5533_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5533_, 0, v_x_5498_);
v___x_5534_ = lean_apply_2(v_toPure_5525_, lean_box(0), v___x_5533_);
v___x_5535_ = lean_apply_4(v_toSeq_5526_, lean_box(0), lean_box(0), v___x_5534_, v___f_5532_);
v___x_5536_ = lean_apply_4(v_toSeq_5526_, lean_box(0), lean_box(0), v___x_5535_, v___f_5531_);
v___x_5537_ = lean_apply_4(v_toSeq_5526_, lean_box(0), lean_box(0), v___x_5536_, v___f_5530_);
return v___x_5537_;
}
case 5:
{
lean_object* v_toPure_5538_; lean_object* v_toSeq_5539_; lean_object* v_fn_5540_; lean_object* v_arg_5541_; lean_object* v___f_5542_; lean_object* v___f_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; 
v_toPure_5538_ = lean_ctor_get(v_inst_5496_, 1);
lean_inc(v_toPure_5538_);
v_toSeq_5539_ = lean_ctor_get(v_inst_5496_, 2);
lean_inc_n(v_toSeq_5539_, 2);
lean_dec_ref(v_inst_5496_);
v_fn_5540_ = lean_ctor_get(v_x_5498_, 0);
v_arg_5541_ = lean_ctor_get(v_x_5498_, 1);
lean_inc_ref(v_arg_5541_);
lean_inc(v_f_5497_);
v___f_5542_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5542_, 0, v_f_5497_);
lean_closure_set(v___f_5542_, 1, v_arg_5541_);
lean_inc_ref(v_fn_5540_);
v___f_5543_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5543_, 0, v_f_5497_);
lean_closure_set(v___f_5543_, 1, v_fn_5540_);
v___x_5544_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5544_, 0, v_x_5498_);
v___x_5545_ = lean_apply_2(v_toPure_5538_, lean_box(0), v___x_5544_);
v___x_5546_ = lean_apply_4(v_toSeq_5539_, lean_box(0), lean_box(0), v___x_5545_, v___f_5543_);
v___x_5547_ = lean_apply_4(v_toSeq_5539_, lean_box(0), lean_box(0), v___x_5546_, v___f_5542_);
return v___x_5547_;
}
case 11:
{
lean_object* v_toFunctor_5548_; lean_object* v_struct_5549_; lean_object* v_map_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; 
v_toFunctor_5548_ = lean_ctor_get(v_inst_5496_, 0);
lean_inc_ref(v_toFunctor_5548_);
lean_dec_ref(v_inst_5496_);
v_struct_5549_ = lean_ctor_get(v_x_5498_, 2);
lean_inc_ref(v_struct_5549_);
v_map_5550_ = lean_ctor_get(v_toFunctor_5548_, 0);
lean_inc(v_map_5550_);
lean_dec_ref(v_toFunctor_5548_);
v___x_5551_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5551_, 0, v_x_5498_);
v___x_5552_ = lean_apply_1(v_f_5497_, v_struct_5549_);
v___x_5553_ = lean_apply_4(v_map_5550_, lean_box(0), lean_box(0), v___x_5551_, v___x_5552_);
return v___x_5553_;
}
default: 
{
lean_object* v_toPure_5554_; lean_object* v___x_5555_; 
lean_dec(v_f_5497_);
v_toPure_5554_ = lean_ctor_get(v_inst_5496_, 1);
lean_inc(v_toPure_5554_);
lean_dec_ref(v_inst_5496_);
v___x_5555_ = lean_apply_2(v_toPure_5554_, lean_box(0), v_x_5498_);
return v___x_5555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5556_, lean_object* v_inst_5557_, lean_object* v_f_5558_, lean_object* v_x_5559_){
_start:
{
lean_object* v___x_5560_; 
v___x_5560_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5557_, v_f_5558_, v_x_5559_);
return v___x_5560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5561_){
_start:
{
lean_object* v_snd_5562_; 
v_snd_5562_ = lean_ctor_get(v_self_5561_, 1);
lean_inc(v_snd_5562_);
return v_snd_5562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5563_){
_start:
{
lean_object* v_res_5564_; 
v_res_5564_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5563_);
lean_dec_ref(v_self_5563_);
return v_res_5564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5565_, lean_object* v_snd_5566_){
_start:
{
lean_object* v___x_5567_; 
v___x_5567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5567_, 0, v_e_x27_5565_);
lean_ctor_set(v___x_5567_, 1, v_snd_5566_);
return v___x_5567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5568_, lean_object* v_map_5569_, lean_object* v_e_x27_5570_, lean_object* v_a_5571_){
_start:
{
lean_object* v___f_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; 
lean_inc_ref(v_e_x27_5570_);
v___f_5572_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5572_, 0, v_e_x27_5570_);
v___x_5573_ = lean_apply_2(v_f_5568_, v_a_5571_, v_e_x27_5570_);
v___x_5574_ = lean_apply_4(v_map_5569_, lean_box(0), lean_box(0), v___f_5572_, v___x_5573_);
return v___x_5574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5576_, lean_object* v_f_5577_, lean_object* v_init_5578_, lean_object* v_e_5579_){
_start:
{
lean_object* v_toApplicative_5580_; lean_object* v_toFunctor_5581_; lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5608_; 
v_toApplicative_5580_ = lean_ctor_get(v_inst_5576_, 0);
lean_inc_ref(v_toApplicative_5580_);
v_toFunctor_5581_ = lean_ctor_get(v_toApplicative_5580_, 0);
v_isSharedCheck_5608_ = !lean_is_exclusive(v_toApplicative_5580_);
if (v_isSharedCheck_5608_ == 0)
{
lean_object* v_unused_5609_; lean_object* v_unused_5610_; lean_object* v_unused_5611_; lean_object* v_unused_5612_; 
v_unused_5609_ = lean_ctor_get(v_toApplicative_5580_, 4);
lean_dec(v_unused_5609_);
v_unused_5610_ = lean_ctor_get(v_toApplicative_5580_, 3);
lean_dec(v_unused_5610_);
v_unused_5611_ = lean_ctor_get(v_toApplicative_5580_, 2);
lean_dec(v_unused_5611_);
v_unused_5612_ = lean_ctor_get(v_toApplicative_5580_, 1);
lean_dec(v_unused_5612_);
v___x_5583_ = v_toApplicative_5580_;
v_isShared_5584_ = v_isSharedCheck_5608_;
goto v_resetjp_5582_;
}
else
{
lean_inc(v_toFunctor_5581_);
lean_dec(v_toApplicative_5580_);
v___x_5583_ = lean_box(0);
v_isShared_5584_ = v_isSharedCheck_5608_;
goto v_resetjp_5582_;
}
v_resetjp_5582_:
{
lean_object* v_map_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5606_; 
v_map_5585_ = lean_ctor_get(v_toFunctor_5581_, 0);
v_isSharedCheck_5606_ = !lean_is_exclusive(v_toFunctor_5581_);
if (v_isSharedCheck_5606_ == 0)
{
lean_object* v_unused_5607_; 
v_unused_5607_ = lean_ctor_get(v_toFunctor_5581_, 1);
lean_dec(v_unused_5607_);
v___x_5587_ = v_toFunctor_5581_;
v_isShared_5588_ = v_isSharedCheck_5606_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_map_5585_);
lean_dec(v_toFunctor_5581_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5606_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___f_5589_; lean_object* v___f_5590_; lean_object* v___f_5591_; lean_object* v___f_5592_; lean_object* v___f_5593_; lean_object* v___f_5594_; lean_object* v___x_5595_; lean_object* v___x_5597_; 
v___f_5589_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5585_);
v___f_5590_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5590_, 0, v_f_5577_);
lean_closure_set(v___f_5590_, 1, v_map_5585_);
lean_inc_ref_n(v_inst_5576_, 5);
v___f_5591_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5591_, 0, v_inst_5576_);
v___f_5592_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5592_, 0, v_inst_5576_);
v___f_5593_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5593_, 0, v_inst_5576_);
v___f_5594_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5594_, 0, v_inst_5576_);
v___x_5595_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5595_, 0, lean_box(0));
lean_closure_set(v___x_5595_, 1, lean_box(0));
lean_closure_set(v___x_5595_, 2, v_inst_5576_);
if (v_isShared_5588_ == 0)
{
lean_ctor_set(v___x_5587_, 1, v___f_5591_);
lean_ctor_set(v___x_5587_, 0, v___x_5595_);
v___x_5597_ = v___x_5587_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5595_);
lean_ctor_set(v_reuseFailAlloc_5605_, 1, v___f_5591_);
v___x_5597_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
lean_object* v___x_5598_; lean_object* v___x_5600_; 
v___x_5598_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5598_, 0, lean_box(0));
lean_closure_set(v___x_5598_, 1, lean_box(0));
lean_closure_set(v___x_5598_, 2, v_inst_5576_);
if (v_isShared_5584_ == 0)
{
lean_ctor_set(v___x_5583_, 4, v___f_5594_);
lean_ctor_set(v___x_5583_, 3, v___f_5593_);
lean_ctor_set(v___x_5583_, 2, v___f_5592_);
lean_ctor_set(v___x_5583_, 1, v___x_5598_);
lean_ctor_set(v___x_5583_, 0, v___x_5597_);
v___x_5600_ = v___x_5583_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v___x_5597_);
lean_ctor_set(v_reuseFailAlloc_5604_, 1, v___x_5598_);
lean_ctor_set(v_reuseFailAlloc_5604_, 2, v___f_5592_);
lean_ctor_set(v_reuseFailAlloc_5604_, 3, v___f_5593_);
lean_ctor_set(v_reuseFailAlloc_5604_, 4, v___f_5594_);
v___x_5600_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
lean_object* v___x_18__overap_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; 
v___x_18__overap_5601_ = l_Lean_Expr_traverseChildren___redArg(v___x_5600_, v___f_5590_, v_e_5579_);
v___x_5602_ = lean_apply_1(v___x_18__overap_5601_, v_init_5578_);
v___x_5603_ = lean_apply_4(v_map_5585_, lean_box(0), lean_box(0), v___f_5589_, v___x_5602_);
return v___x_5603_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5613_, lean_object* v_m_5614_, lean_object* v_inst_5615_, lean_object* v_f_5616_, lean_object* v_init_5617_, lean_object* v_e_5618_){
_start:
{
lean_object* v___x_5619_; 
v___x_5619_ = l_Lean_Expr_foldlM___redArg(v_inst_5615_, v_f_5616_, v_init_5617_, v_e_5618_);
return v___x_5619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5620_){
_start:
{
lean_object* v_d_5622_; lean_object* v_b_5623_; 
switch(lean_obj_tag(v_x_5620_))
{
case 5:
{
lean_object* v_fn_5629_; lean_object* v_arg_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; 
v_fn_5629_ = lean_ctor_get(v_x_5620_, 0);
v_arg_5630_ = lean_ctor_get(v_x_5620_, 1);
v___x_5631_ = lean_unsigned_to_nat(1u);
v___x_5632_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5629_);
v___x_5633_ = lean_nat_add(v___x_5631_, v___x_5632_);
lean_dec(v___x_5632_);
v___x_5634_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5630_);
v___x_5635_ = lean_nat_add(v___x_5633_, v___x_5634_);
lean_dec(v___x_5634_);
lean_dec(v___x_5633_);
return v___x_5635_;
}
case 6:
{
lean_object* v_binderType_5636_; lean_object* v_body_5637_; 
v_binderType_5636_ = lean_ctor_get(v_x_5620_, 1);
v_body_5637_ = lean_ctor_get(v_x_5620_, 2);
v_d_5622_ = v_binderType_5636_;
v_b_5623_ = v_body_5637_;
goto v___jp_5621_;
}
case 7:
{
lean_object* v_binderType_5638_; lean_object* v_body_5639_; 
v_binderType_5638_ = lean_ctor_get(v_x_5620_, 1);
v_body_5639_ = lean_ctor_get(v_x_5620_, 2);
v_d_5622_ = v_binderType_5638_;
v_b_5623_ = v_body_5639_;
goto v___jp_5621_;
}
case 8:
{
lean_object* v_type_5640_; lean_object* v_value_5641_; lean_object* v_body_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; 
v_type_5640_ = lean_ctor_get(v_x_5620_, 1);
v_value_5641_ = lean_ctor_get(v_x_5620_, 2);
v_body_5642_ = lean_ctor_get(v_x_5620_, 3);
v___x_5643_ = lean_unsigned_to_nat(1u);
v___x_5644_ = l_Lean_Expr_sizeWithoutSharing(v_type_5640_);
v___x_5645_ = lean_nat_add(v___x_5643_, v___x_5644_);
lean_dec(v___x_5644_);
v___x_5646_ = l_Lean_Expr_sizeWithoutSharing(v_value_5641_);
v___x_5647_ = lean_nat_add(v___x_5645_, v___x_5646_);
lean_dec(v___x_5646_);
lean_dec(v___x_5645_);
v___x_5648_ = l_Lean_Expr_sizeWithoutSharing(v_body_5642_);
v___x_5649_ = lean_nat_add(v___x_5647_, v___x_5648_);
lean_dec(v___x_5648_);
lean_dec(v___x_5647_);
return v___x_5649_;
}
case 10:
{
lean_object* v_expr_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; 
v_expr_5650_ = lean_ctor_get(v_x_5620_, 1);
v___x_5651_ = lean_unsigned_to_nat(1u);
v___x_5652_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5650_);
v___x_5653_ = lean_nat_add(v___x_5651_, v___x_5652_);
lean_dec(v___x_5652_);
return v___x_5653_;
}
case 11:
{
lean_object* v_struct_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; 
v_struct_5654_ = lean_ctor_get(v_x_5620_, 2);
v___x_5655_ = lean_unsigned_to_nat(1u);
v___x_5656_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5654_);
v___x_5657_ = lean_nat_add(v___x_5655_, v___x_5656_);
lean_dec(v___x_5656_);
return v___x_5657_;
}
default: 
{
lean_object* v___x_5658_; 
v___x_5658_ = lean_unsigned_to_nat(1u);
return v___x_5658_;
}
}
v___jp_5621_:
{
lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; 
v___x_5624_ = lean_unsigned_to_nat(1u);
v___x_5625_ = l_Lean_Expr_sizeWithoutSharing(v_d_5622_);
v___x_5626_ = lean_nat_add(v___x_5624_, v___x_5625_);
lean_dec(v___x_5625_);
v___x_5627_ = l_Lean_Expr_sizeWithoutSharing(v_b_5623_);
v___x_5628_ = lean_nat_add(v___x_5626_, v___x_5627_);
lean_dec(v___x_5627_);
lean_dec(v___x_5626_);
return v___x_5628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5659_){
_start:
{
lean_object* v_res_5660_; 
v_res_5660_ = l_Lean_Expr_sizeWithoutSharing(v_x_5659_);
lean_dec_ref(v_x_5659_);
return v_res_5660_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5663_, lean_object* v_e_5664_){
_start:
{
lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; 
v___x_5665_ = l_Lean_KVMap_empty;
v___x_5666_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5667_ = l_Lean_KVMap_insert(v___x_5665_, v_kind_5663_, v___x_5666_);
v___x_5668_ = l_Lean_Expr_mdata___override(v___x_5667_, v_e_5664_);
return v___x_5668_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5669_, lean_object* v_e_5670_){
_start:
{
if (lean_obj_tag(v_e_5670_) == 10)
{
lean_object* v_data_5671_; lean_object* v_expr_5672_; uint8_t v___y_5674_; lean_object* v___x_5677_; lean_object* v___x_5678_; uint8_t v___x_5679_; 
v_data_5671_ = lean_ctor_get(v_e_5670_, 0);
v_expr_5672_ = lean_ctor_get(v_e_5670_, 1);
v___x_5677_ = l_Lean_KVMap_size(v_data_5671_);
v___x_5678_ = lean_unsigned_to_nat(1u);
v___x_5679_ = lean_nat_dec_eq(v___x_5677_, v___x_5678_);
lean_dec(v___x_5677_);
if (v___x_5679_ == 0)
{
v___y_5674_ = v___x_5679_;
goto v___jp_5673_;
}
else
{
uint8_t v___x_5680_; uint8_t v___x_5681_; 
v___x_5680_ = 0;
v___x_5681_ = l_Lean_KVMap_getBool(v_data_5671_, v_kind_5669_, v___x_5680_);
v___y_5674_ = v___x_5681_;
goto v___jp_5673_;
}
v___jp_5673_:
{
if (v___y_5674_ == 0)
{
lean_object* v___x_5675_; 
v___x_5675_ = lean_box(0);
return v___x_5675_;
}
else
{
lean_object* v___x_5676_; 
lean_inc_ref(v_expr_5672_);
v___x_5676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5676_, 0, v_expr_5672_);
return v___x_5676_;
}
}
}
else
{
lean_object* v___x_5682_; 
v___x_5682_ = lean_box(0);
return v___x_5682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* v_kind_5683_, lean_object* v_e_5684_){
_start:
{
lean_object* v_res_5685_; 
v_res_5685_ = l_Lean_annotation_x3f(v_kind_5683_, v_e_5684_);
lean_dec_ref(v_e_5684_);
lean_dec(v_kind_5683_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* v_e_5689_){
_start:
{
lean_object* v___x_5690_; lean_object* v___x_5691_; 
v___x_5690_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5691_ = l_Lean_mkAnnotation(v___x_5690_, v_e_5689_);
return v___x_5691_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* v_e_5692_){
_start:
{
lean_object* v___x_5693_; lean_object* v___x_5694_; 
v___x_5693_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5694_ = l_Lean_annotation_x3f(v___x_5693_, v_e_5692_);
return v___x_5694_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* v_e_5695_){
_start:
{
lean_object* v_res_5696_; 
v_res_5696_ = l_Lean_inaccessible_x3f(v_e_5695_);
lean_dec_ref(v_e_5695_);
return v_res_5696_;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* v_p_5701_){
_start:
{
if (lean_obj_tag(v_p_5701_) == 10)
{
lean_object* v_data_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; 
v_data_5702_ = lean_ctor_get(v_p_5701_, 0);
v___x_5703_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5704_ = l_Lean_KVMap_find(v_data_5702_, v___x_5703_);
if (lean_obj_tag(v___x_5704_) == 1)
{
lean_object* v_val_5705_; lean_object* v___x_5707_; uint8_t v_isShared_5708_; uint8_t v_isSharedCheck_5716_; 
v_val_5705_ = lean_ctor_get(v___x_5704_, 0);
v_isSharedCheck_5716_ = !lean_is_exclusive(v___x_5704_);
if (v_isSharedCheck_5716_ == 0)
{
v___x_5707_ = v___x_5704_;
v_isShared_5708_ = v_isSharedCheck_5716_;
goto v_resetjp_5706_;
}
else
{
lean_inc(v_val_5705_);
lean_dec(v___x_5704_);
v___x_5707_ = lean_box(0);
v_isShared_5708_ = v_isSharedCheck_5716_;
goto v_resetjp_5706_;
}
v_resetjp_5706_:
{
if (lean_obj_tag(v_val_5705_) == 5)
{
lean_object* v_v_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5713_; 
v_v_5709_ = lean_ctor_get(v_val_5705_, 0);
lean_inc(v_v_5709_);
lean_dec_ref(v_val_5705_);
v___x_5710_ = l_Lean_Expr_mdataExpr_x21(v_p_5701_);
v___x_5711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5711_, 0, v_v_5709_);
lean_ctor_set(v___x_5711_, 1, v___x_5710_);
if (v_isShared_5708_ == 0)
{
lean_ctor_set(v___x_5707_, 0, v___x_5711_);
v___x_5713_ = v___x_5707_;
goto v_reusejp_5712_;
}
else
{
lean_object* v_reuseFailAlloc_5714_; 
v_reuseFailAlloc_5714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5714_, 0, v___x_5711_);
v___x_5713_ = v_reuseFailAlloc_5714_;
goto v_reusejp_5712_;
}
v_reusejp_5712_:
{
return v___x_5713_;
}
}
else
{
lean_object* v___x_5715_; 
lean_del_object(v___x_5707_);
lean_dec(v_val_5705_);
v___x_5715_ = lean_box(0);
return v___x_5715_;
}
}
}
else
{
lean_object* v___x_5717_; 
lean_dec(v___x_5704_);
v___x_5717_ = lean_box(0);
return v___x_5717_;
}
}
else
{
lean_object* v___x_5718_; 
v___x_5718_ = lean_box(0);
return v___x_5718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* v_p_5719_){
_start:
{
lean_object* v_res_5720_; 
v_res_5720_ = l_Lean_patternWithRef_x3f(v_p_5719_);
lean_dec_ref(v_p_5719_);
return v_res_5720_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object* v_p_5721_){
_start:
{
lean_object* v___x_5722_; 
v___x_5722_ = l_Lean_patternWithRef_x3f(v_p_5721_);
if (lean_obj_tag(v___x_5722_) == 0)
{
uint8_t v___x_5723_; 
v___x_5723_ = 0;
return v___x_5723_;
}
else
{
uint8_t v___x_5724_; 
lean_dec_ref(v___x_5722_);
v___x_5724_ = 1;
return v___x_5724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* v_p_5725_){
_start:
{
uint8_t v_res_5726_; lean_object* v_r_5727_; 
v_res_5726_ = l_Lean_isPatternWithRef(v_p_5725_);
lean_dec_ref(v_p_5725_);
v_r_5727_ = lean_box(v_res_5726_);
return v_r_5727_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* v_p_5728_, lean_object* v_stx_5729_){
_start:
{
lean_object* v___x_5730_; 
v___x_5730_ = l_Lean_patternWithRef_x3f(v_p_5728_);
if (lean_obj_tag(v___x_5730_) == 0)
{
lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; 
v___x_5731_ = l_Lean_KVMap_empty;
v___x_5732_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5733_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_5733_, 0, v_stx_5729_);
v___x_5734_ = l_Lean_KVMap_insert(v___x_5731_, v___x_5732_, v___x_5733_);
v___x_5735_ = l_Lean_Expr_mdata___override(v___x_5734_, v_p_5728_);
return v___x_5735_;
}
else
{
lean_dec_ref(v___x_5730_);
lean_dec(v_stx_5729_);
return v_p_5728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* v_e_5736_){
_start:
{
lean_object* v___x_5737_; 
v___x_5737_ = l_Lean_inaccessible_x3f(v_e_5736_);
if (lean_obj_tag(v___x_5737_) == 1)
{
return v___x_5737_;
}
else
{
lean_object* v___x_5738_; 
lean_dec(v___x_5737_);
v___x_5738_ = l_Lean_patternWithRef_x3f(v_e_5736_);
if (lean_obj_tag(v___x_5738_) == 1)
{
lean_object* v_val_5739_; lean_object* v___x_5741_; uint8_t v_isShared_5742_; uint8_t v_isSharedCheck_5747_; 
v_val_5739_ = lean_ctor_get(v___x_5738_, 0);
v_isSharedCheck_5747_ = !lean_is_exclusive(v___x_5738_);
if (v_isSharedCheck_5747_ == 0)
{
v___x_5741_ = v___x_5738_;
v_isShared_5742_ = v_isSharedCheck_5747_;
goto v_resetjp_5740_;
}
else
{
lean_inc(v_val_5739_);
lean_dec(v___x_5738_);
v___x_5741_ = lean_box(0);
v_isShared_5742_ = v_isSharedCheck_5747_;
goto v_resetjp_5740_;
}
v_resetjp_5740_:
{
lean_object* v_snd_5743_; lean_object* v___x_5745_; 
v_snd_5743_ = lean_ctor_get(v_val_5739_, 1);
lean_inc(v_snd_5743_);
lean_dec(v_val_5739_);
if (v_isShared_5742_ == 0)
{
lean_ctor_set(v___x_5741_, 0, v_snd_5743_);
v___x_5745_ = v___x_5741_;
goto v_reusejp_5744_;
}
else
{
lean_object* v_reuseFailAlloc_5746_; 
v_reuseFailAlloc_5746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5746_, 0, v_snd_5743_);
v___x_5745_ = v_reuseFailAlloc_5746_;
goto v_reusejp_5744_;
}
v_reusejp_5744_:
{
return v___x_5745_;
}
}
}
else
{
lean_object* v___x_5748_; 
lean_dec(v___x_5738_);
v___x_5748_ = lean_box(0);
return v___x_5748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* v_e_5749_){
_start:
{
lean_object* v_res_5750_; 
v_res_5750_ = l_Lean_patternAnnotation_x3f(v_e_5749_);
lean_dec_ref(v_e_5749_);
return v_res_5750_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* v_e_5754_){
_start:
{
lean_object* v___x_5755_; lean_object* v___x_5756_; 
v___x_5755_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5756_ = l_Lean_mkAnnotation(v___x_5755_, v_e_5754_);
return v___x_5756_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* v_e_5760_){
_start:
{
lean_object* v___x_5761_; lean_object* v___x_5762_; 
v___x_5761_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5762_ = l_Lean_annotation_x3f(v___x_5761_, v_e_5760_);
if (lean_obj_tag(v___x_5762_) == 0)
{
return v___x_5762_;
}
else
{
lean_object* v_val_5763_; lean_object* v___x_5765_; uint8_t v_isShared_5766_; uint8_t v_isSharedCheck_5776_; 
v_val_5763_ = lean_ctor_get(v___x_5762_, 0);
v_isSharedCheck_5776_ = !lean_is_exclusive(v___x_5762_);
if (v_isSharedCheck_5776_ == 0)
{
v___x_5765_ = v___x_5762_;
v_isShared_5766_ = v_isSharedCheck_5776_;
goto v_resetjp_5764_;
}
else
{
lean_inc(v_val_5763_);
lean_dec(v___x_5762_);
v___x_5765_ = lean_box(0);
v_isShared_5766_ = v_isSharedCheck_5776_;
goto v_resetjp_5764_;
}
v_resetjp_5764_:
{
lean_object* v___x_5767_; lean_object* v___x_5768_; uint8_t v___x_5769_; 
v___x_5767_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5768_ = lean_unsigned_to_nat(3u);
v___x_5769_ = l_Lean_Expr_isAppOfArity(v_val_5763_, v___x_5767_, v___x_5768_);
if (v___x_5769_ == 0)
{
lean_object* v___x_5770_; 
lean_del_object(v___x_5765_);
lean_dec(v_val_5763_);
v___x_5770_ = lean_box(0);
return v___x_5770_;
}
else
{
lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5774_; 
v___x_5771_ = l_Lean_Expr_appFn_x21(v_val_5763_);
lean_dec(v_val_5763_);
v___x_5772_ = l_Lean_Expr_appArg_x21(v___x_5771_);
lean_dec_ref(v___x_5771_);
if (v_isShared_5766_ == 0)
{
lean_ctor_set(v___x_5765_, 0, v___x_5772_);
v___x_5774_ = v___x_5765_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v___x_5772_);
v___x_5774_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
return v___x_5774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* v_e_5777_){
_start:
{
lean_object* v_res_5778_; 
v_res_5778_ = l_Lean_isLHSGoal_x3f(v_e_5777_);
lean_dec_ref(v_e_5777_);
return v_res_5778_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* v_toPure_5779_, lean_object* v_____do__lift_5780_){
_start:
{
lean_object* v___x_5781_; 
v___x_5781_ = lean_apply_2(v_toPure_5779_, lean_box(0), v_____do__lift_5780_);
return v___x_5781_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* v_inst_5782_, lean_object* v_inst_5783_){
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* v_m_5790_, lean_object* v_inst_5791_, lean_object* v_inst_5792_){
_start:
{
lean_object* v___x_5793_; 
v___x_5793_ = l_Lean_mkFreshFVarId___redArg(v_inst_5791_, v_inst_5792_);
return v___x_5793_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* v_inst_5794_, lean_object* v_inst_5795_){
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
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* v_m_5802_, lean_object* v_inst_5803_, lean_object* v_inst_5804_){
_start:
{
lean_object* v___x_5805_; 
v___x_5805_ = l_Lean_mkFreshMVarId___redArg(v_inst_5803_, v_inst_5804_);
return v___x_5805_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* v_inst_5806_, lean_object* v_inst_5807_){
_start:
{
lean_object* v_toApplicative_5808_; lean_object* v_toBind_5809_; lean_object* v_toPure_5810_; lean_object* v___x_5811_; lean_object* v___f_5812_; lean_object* v___x_5813_; 
v_toApplicative_5808_ = lean_ctor_get(v_inst_5806_, 0);
v_toBind_5809_ = lean_ctor_get(v_inst_5806_, 1);
lean_inc(v_toBind_5809_);
v_toPure_5810_ = lean_ctor_get(v_toApplicative_5808_, 1);
lean_inc(v_toPure_5810_);
v___x_5811_ = l_Lean_mkFreshId___redArg(v_inst_5806_, v_inst_5807_);
v___f_5812_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5812_, 0, v_toPure_5810_);
v___x_5813_ = lean_apply_4(v_toBind_5809_, lean_box(0), lean_box(0), v___x_5811_, v___f_5812_);
return v___x_5813_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* v_m_5814_, lean_object* v_inst_5815_, lean_object* v_inst_5816_){
_start:
{
lean_object* v___x_5817_; 
v___x_5817_ = l_Lean_mkFreshLMVarId___redArg(v_inst_5815_, v_inst_5816_);
return v___x_5817_;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2(void){
_start:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; 
v___x_5821_ = lean_box(0);
v___x_5822_ = ((lean_object*)(l_Lean_mkNot___closed__1));
v___x_5823_ = l_Lean_Expr_const___override(v___x_5822_, v___x_5821_);
return v___x_5823_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* v_p_5824_){
_start:
{
lean_object* v___x_5825_; lean_object* v___x_5826_; 
v___x_5825_ = lean_obj_once(&l_Lean_mkNot___closed__2, &l_Lean_mkNot___closed__2_once, _init_l_Lean_mkNot___closed__2);
v___x_5826_ = l_Lean_Expr_app___override(v___x_5825_, v_p_5824_);
return v___x_5826_;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2(void){
_start:
{
lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; 
v___x_5830_ = lean_box(0);
v___x_5831_ = ((lean_object*)(l_Lean_mkOr___closed__1));
v___x_5832_ = l_Lean_Expr_const___override(v___x_5831_, v___x_5830_);
return v___x_5832_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* v_p_5833_, lean_object* v_q_5834_){
_start:
{
lean_object* v___x_5835_; lean_object* v___x_5836_; 
v___x_5835_ = lean_obj_once(&l_Lean_mkOr___closed__2, &l_Lean_mkOr___closed__2_once, _init_l_Lean_mkOr___closed__2);
v___x_5836_ = l_Lean_mkAppB(v___x_5835_, v_p_5833_, v_q_5834_);
return v___x_5836_;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2(void){
_start:
{
lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; 
v___x_5840_ = lean_box(0);
v___x_5841_ = ((lean_object*)(l_Lean_mkAnd___closed__1));
v___x_5842_ = l_Lean_Expr_const___override(v___x_5841_, v___x_5840_);
return v___x_5842_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* v_p_5843_, lean_object* v_q_5844_){
_start:
{
lean_object* v___x_5845_; lean_object* v___x_5846_; 
v___x_5845_ = lean_obj_once(&l_Lean_mkAnd___closed__2, &l_Lean_mkAnd___closed__2_once, _init_l_Lean_mkAnd___closed__2);
v___x_5846_ = l_Lean_mkAppB(v___x_5845_, v_p_5843_, v_q_5844_);
return v___x_5846_;
}
}
static lean_object* _init_l_Lean_mkAndN___closed__0(void){
_start:
{
lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; 
v___x_5847_ = lean_box(0);
v___x_5848_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_5849_ = l_Lean_Expr_const___override(v___x_5848_, v___x_5847_);
return v___x_5849_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* v_x_5850_){
_start:
{
if (lean_obj_tag(v_x_5850_) == 0)
{
lean_object* v___x_5851_; 
v___x_5851_ = lean_obj_once(&l_Lean_mkAndN___closed__0, &l_Lean_mkAndN___closed__0_once, _init_l_Lean_mkAndN___closed__0);
return v___x_5851_;
}
else
{
lean_object* v_tail_5852_; 
v_tail_5852_ = lean_ctor_get(v_x_5850_, 1);
if (lean_obj_tag(v_tail_5852_) == 0)
{
lean_object* v_head_5853_; 
v_head_5853_ = lean_ctor_get(v_x_5850_, 0);
lean_inc(v_head_5853_);
lean_dec_ref(v_x_5850_);
return v_head_5853_;
}
else
{
lean_object* v_head_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; 
lean_inc(v_tail_5852_);
v_head_5854_ = lean_ctor_get(v_x_5850_, 0);
lean_inc(v_head_5854_);
lean_dec_ref(v_x_5850_);
v___x_5855_ = l_Lean_mkAndN(v_tail_5852_);
v___x_5856_ = l_Lean_mkAnd(v_head_5854_, v___x_5855_);
return v___x_5856_;
}
}
}
}
static lean_object* _init_l_Lean_mkEM___closed__3(void){
_start:
{
lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; 
v___x_5862_ = lean_box(0);
v___x_5863_ = ((lean_object*)(l_Lean_mkEM___closed__2));
v___x_5864_ = l_Lean_Expr_const___override(v___x_5863_, v___x_5862_);
return v___x_5864_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* v_p_5865_){
_start:
{
lean_object* v___x_5866_; lean_object* v___x_5867_; 
v___x_5866_ = lean_obj_once(&l_Lean_mkEM___closed__3, &l_Lean_mkEM___closed__3_once, _init_l_Lean_mkEM___closed__3);
v___x_5867_ = l_Lean_Expr_app___override(v___x_5866_, v_p_5865_);
return v___x_5867_;
}
}
static lean_object* _init_l_Lean_mkIff___closed__2(void){
_start:
{
lean_object* v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; 
v___x_5871_ = lean_box(0);
v___x_5872_ = ((lean_object*)(l_Lean_mkIff___closed__1));
v___x_5873_ = l_Lean_Expr_const___override(v___x_5872_, v___x_5871_);
return v___x_5873_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* v_p_5874_, lean_object* v_q_5875_){
_start:
{
lean_object* v___x_5876_; lean_object* v___x_5877_; 
v___x_5876_ = lean_obj_once(&l_Lean_mkIff___closed__2, &l_Lean_mkIff___closed__2_once, _init_l_Lean_mkIff___closed__2);
v___x_5877_ = l_Lean_mkAppB(v___x_5876_, v_p_5874_, v_q_5875_);
return v___x_5877_;
}
}
static lean_object* _init_l_Lean_Nat_mkType(void){
_start:
{
lean_object* v___x_5878_; 
v___x_5878_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_5878_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; 
v___x_5882_ = lean_box(0);
v___x_5883_ = ((lean_object*)(l_Lean_Nat_mkInstAdd___closed__1));
v___x_5884_ = l_Lean_Expr_const___override(v___x_5883_, v___x_5882_);
return v___x_5884_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd(void){
_start:
{
lean_object* v___x_5885_; 
v___x_5885_ = lean_obj_once(&l_Lean_Nat_mkInstAdd___closed__2, &l_Lean_Nat_mkInstAdd___closed__2_once, _init_l_Lean_Nat_mkInstAdd___closed__2);
return v___x_5885_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__2(void){
_start:
{
lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; 
v___x_5889_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5890_ = ((lean_object*)(l_Lean_Nat_mkInstHAdd___closed__1));
v___x_5891_ = l_Lean_Expr_const___override(v___x_5890_, v___x_5889_);
return v___x_5891_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__3(void){
_start:
{
lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; 
v___x_5892_ = l_Lean_Nat_mkInstAdd;
v___x_5893_ = l_Lean_Nat_mkType;
v___x_5894_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_5895_ = l_Lean_mkAppB(v___x_5894_, v___x_5893_, v___x_5892_);
return v___x_5895_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd(void){
_start:
{
lean_object* v___x_5896_; 
v___x_5896_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__3, &l_Lean_Nat_mkInstHAdd___closed__3_once, _init_l_Lean_Nat_mkInstHAdd___closed__3);
return v___x_5896_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; 
v___x_5900_ = lean_box(0);
v___x_5901_ = ((lean_object*)(l_Lean_Nat_mkInstSub___closed__1));
v___x_5902_ = l_Lean_Expr_const___override(v___x_5901_, v___x_5900_);
return v___x_5902_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub(void){
_start:
{
lean_object* v___x_5903_; 
v___x_5903_ = lean_obj_once(&l_Lean_Nat_mkInstSub___closed__2, &l_Lean_Nat_mkInstSub___closed__2_once, _init_l_Lean_Nat_mkInstSub___closed__2);
return v___x_5903_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__2(void){
_start:
{
lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; 
v___x_5907_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5908_ = ((lean_object*)(l_Lean_Nat_mkInstHSub___closed__1));
v___x_5909_ = l_Lean_Expr_const___override(v___x_5908_, v___x_5907_);
return v___x_5909_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__3(void){
_start:
{
lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; 
v___x_5910_ = l_Lean_Nat_mkInstSub;
v___x_5911_ = l_Lean_Nat_mkType;
v___x_5912_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_5913_ = l_Lean_mkAppB(v___x_5912_, v___x_5911_, v___x_5910_);
return v___x_5913_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub(void){
_start:
{
lean_object* v___x_5914_; 
v___x_5914_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__3, &l_Lean_Nat_mkInstHSub___closed__3_once, _init_l_Lean_Nat_mkInstHSub___closed__3);
return v___x_5914_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; 
v___x_5918_ = lean_box(0);
v___x_5919_ = ((lean_object*)(l_Lean_Nat_mkInstMul___closed__1));
v___x_5920_ = l_Lean_Expr_const___override(v___x_5919_, v___x_5918_);
return v___x_5920_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul(void){
_start:
{
lean_object* v___x_5921_; 
v___x_5921_ = lean_obj_once(&l_Lean_Nat_mkInstMul___closed__2, &l_Lean_Nat_mkInstMul___closed__2_once, _init_l_Lean_Nat_mkInstMul___closed__2);
return v___x_5921_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__2(void){
_start:
{
lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; 
v___x_5925_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5926_ = ((lean_object*)(l_Lean_Nat_mkInstHMul___closed__1));
v___x_5927_ = l_Lean_Expr_const___override(v___x_5926_, v___x_5925_);
return v___x_5927_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; 
v___x_5928_ = l_Lean_Nat_mkInstMul;
v___x_5929_ = l_Lean_Nat_mkType;
v___x_5930_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_5931_ = l_Lean_mkAppB(v___x_5930_, v___x_5929_, v___x_5928_);
return v___x_5931_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul(void){
_start:
{
lean_object* v___x_5932_; 
v___x_5932_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__3, &l_Lean_Nat_mkInstHMul___closed__3_once, _init_l_Lean_Nat_mkInstHMul___closed__3);
return v___x_5932_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv___closed__2(void){
_start:
{
lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; 
v___x_5937_ = lean_box(0);
v___x_5938_ = ((lean_object*)(l_Lean_Nat_mkInstDiv___closed__1));
v___x_5939_ = l_Lean_Expr_const___override(v___x_5938_, v___x_5937_);
return v___x_5939_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv(void){
_start:
{
lean_object* v___x_5940_; 
v___x_5940_ = lean_obj_once(&l_Lean_Nat_mkInstDiv___closed__2, &l_Lean_Nat_mkInstDiv___closed__2_once, _init_l_Lean_Nat_mkInstDiv___closed__2);
return v___x_5940_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__2(void){
_start:
{
lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; 
v___x_5944_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5945_ = ((lean_object*)(l_Lean_Nat_mkInstHDiv___closed__1));
v___x_5946_ = l_Lean_Expr_const___override(v___x_5945_, v___x_5944_);
return v___x_5946_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__3(void){
_start:
{
lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; 
v___x_5947_ = l_Lean_Nat_mkInstDiv;
v___x_5948_ = l_Lean_Nat_mkType;
v___x_5949_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_5950_ = l_Lean_mkAppB(v___x_5949_, v___x_5948_, v___x_5947_);
return v___x_5950_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv(void){
_start:
{
lean_object* v___x_5951_; 
v___x_5951_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__3, &l_Lean_Nat_mkInstHDiv___closed__3_once, _init_l_Lean_Nat_mkInstHDiv___closed__3);
return v___x_5951_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod___closed__2(void){
_start:
{
lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; 
v___x_5956_ = lean_box(0);
v___x_5957_ = ((lean_object*)(l_Lean_Nat_mkInstMod___closed__1));
v___x_5958_ = l_Lean_Expr_const___override(v___x_5957_, v___x_5956_);
return v___x_5958_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod(void){
_start:
{
lean_object* v___x_5959_; 
v___x_5959_ = lean_obj_once(&l_Lean_Nat_mkInstMod___closed__2, &l_Lean_Nat_mkInstMod___closed__2_once, _init_l_Lean_Nat_mkInstMod___closed__2);
return v___x_5959_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__2(void){
_start:
{
lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; 
v___x_5963_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5964_ = ((lean_object*)(l_Lean_Nat_mkInstHMod___closed__1));
v___x_5965_ = l_Lean_Expr_const___override(v___x_5964_, v___x_5963_);
return v___x_5965_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__3(void){
_start:
{
lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; 
v___x_5966_ = l_Lean_Nat_mkInstMod;
v___x_5967_ = l_Lean_Nat_mkType;
v___x_5968_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_5969_ = l_Lean_mkAppB(v___x_5968_, v___x_5967_, v___x_5966_);
return v___x_5969_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod(void){
_start:
{
lean_object* v___x_5970_; 
v___x_5970_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__3, &l_Lean_Nat_mkInstHMod___closed__3_once, _init_l_Lean_Nat_mkInstHMod___closed__3);
return v___x_5970_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow___closed__2(void){
_start:
{
lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; 
v___x_5974_ = lean_box(0);
v___x_5975_ = ((lean_object*)(l_Lean_Nat_mkInstNatPow___closed__1));
v___x_5976_ = l_Lean_Expr_const___override(v___x_5975_, v___x_5974_);
return v___x_5976_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow(void){
_start:
{
lean_object* v___x_5977_; 
v___x_5977_ = lean_obj_once(&l_Lean_Nat_mkInstNatPow___closed__2, &l_Lean_Nat_mkInstNatPow___closed__2_once, _init_l_Lean_Nat_mkInstNatPow___closed__2);
return v___x_5977_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; 
v___x_5981_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5982_ = ((lean_object*)(l_Lean_Nat_mkInstPow___closed__1));
v___x_5983_ = l_Lean_Expr_const___override(v___x_5982_, v___x_5981_);
return v___x_5983_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__3(void){
_start:
{
lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; 
v___x_5984_ = l_Lean_Nat_mkInstNatPow;
v___x_5985_ = l_Lean_Nat_mkType;
v___x_5986_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_5987_ = l_Lean_mkAppB(v___x_5986_, v___x_5985_, v___x_5984_);
return v___x_5987_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow(void){
_start:
{
lean_object* v___x_5988_; 
v___x_5988_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__3, &l_Lean_Nat_mkInstPow___closed__3_once, _init_l_Lean_Nat_mkInstPow___closed__3);
return v___x_5988_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__3(void){
_start:
{
lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; 
v___x_5995_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__2));
v___x_5996_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__1));
v___x_5997_ = l_Lean_Expr_const___override(v___x_5996_, v___x_5995_);
return v___x_5997_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__4(void){
_start:
{
lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; 
v___x_5998_ = l_Lean_Nat_mkInstPow;
v___x_5999_ = l_Lean_Nat_mkType;
v___x_6000_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6001_ = l_Lean_mkApp3(v___x_6000_, v___x_5999_, v___x_5999_, v___x_5998_);
return v___x_6001_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow(void){
_start:
{
lean_object* v___x_6002_; 
v___x_6002_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__4, &l_Lean_Nat_mkInstHPow___closed__4_once, _init_l_Lean_Nat_mkInstHPow___closed__4);
return v___x_6002_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; 
v___x_6006_ = lean_box(0);
v___x_6007_ = ((lean_object*)(l_Lean_Nat_mkInstLT___closed__1));
v___x_6008_ = l_Lean_Expr_const___override(v___x_6007_, v___x_6006_);
return v___x_6008_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT(void){
_start:
{
lean_object* v___x_6009_; 
v___x_6009_ = lean_obj_once(&l_Lean_Nat_mkInstLT___closed__2, &l_Lean_Nat_mkInstLT___closed__2_once, _init_l_Lean_Nat_mkInstLT___closed__2);
return v___x_6009_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; 
v___x_6013_ = lean_box(0);
v___x_6014_ = ((lean_object*)(l_Lean_Nat_mkInstLE___closed__1));
v___x_6015_ = l_Lean_Expr_const___override(v___x_6014_, v___x_6013_);
return v___x_6015_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE(void){
_start:
{
lean_object* v___x_6016_; 
v___x_6016_ = lean_obj_once(&l_Lean_Nat_mkInstLE___closed__2, &l_Lean_Nat_mkInstLE___closed__2_once, _init_l_Lean_Nat_mkInstLE___closed__2);
return v___x_6016_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3(void){
_start:
{
lean_object* v___x_6022_; lean_object* v___x_6023_; 
v___x_6022_ = lean_unsigned_to_nat(0u);
v___x_6023_ = l_Lean_Level_ofNat(v___x_6022_);
return v___x_6023_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4(void){
_start:
{
lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; 
v___x_6024_ = lean_box(0);
v___x_6025_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6025_);
lean_ctor_set(v___x_6026_, 1, v___x_6024_);
return v___x_6026_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5(void){
_start:
{
lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; 
v___x_6027_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6028_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6029_, 0, v___x_6028_);
lean_ctor_set(v___x_6029_, 1, v___x_6027_);
return v___x_6029_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6(void){
_start:
{
lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; 
v___x_6030_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__5, &l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5);
v___x_6031_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6032_, 0, v___x_6031_);
lean_ctor_set(v___x_6032_, 1, v___x_6030_);
return v___x_6032_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7(void){
_start:
{
lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; 
v___x_6033_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6034_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natAddFn___closed__2));
v___x_6035_ = l_Lean_Expr_const___override(v___x_6034_, v___x_6033_);
return v___x_6035_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8(void){
_start:
{
lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; 
v___x_6036_ = l_Lean_Nat_mkInstHAdd;
v___x_6037_ = l_Lean_Nat_mkType;
v___x_6038_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6039_ = l_Lean_mkApp4(v___x_6038_, v___x_6037_, v___x_6037_, v___x_6037_, v___x_6036_);
return v___x_6039_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn(void){
_start:
{
lean_object* v___x_6040_; 
v___x_6040_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__8, &l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8);
return v___x_6040_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3(void){
_start:
{
lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; 
v___x_6046_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6047_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natSubFn___closed__2));
v___x_6048_ = l_Lean_Expr_const___override(v___x_6047_, v___x_6046_);
return v___x_6048_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4(void){
_start:
{
lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; 
v___x_6049_ = l_Lean_Nat_mkInstHSub;
v___x_6050_ = l_Lean_Nat_mkType;
v___x_6051_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6052_ = l_Lean_mkApp4(v___x_6051_, v___x_6050_, v___x_6050_, v___x_6050_, v___x_6049_);
return v___x_6052_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn(void){
_start:
{
lean_object* v___x_6053_; 
v___x_6053_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__4, &l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4);
return v___x_6053_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3(void){
_start:
{
lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; 
v___x_6059_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6060_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natMulFn___closed__2));
v___x_6061_ = l_Lean_Expr_const___override(v___x_6060_, v___x_6059_);
return v___x_6061_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4(void){
_start:
{
lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; 
v___x_6062_ = l_Lean_Nat_mkInstHMul;
v___x_6063_ = l_Lean_Nat_mkType;
v___x_6064_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6065_ = l_Lean_mkApp4(v___x_6064_, v___x_6063_, v___x_6063_, v___x_6063_, v___x_6062_);
return v___x_6065_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn(void){
_start:
{
lean_object* v___x_6066_; 
v___x_6066_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__4, &l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4);
return v___x_6066_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3(void){
_start:
{
lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; 
v___x_6072_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6073_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natPowFn___closed__2));
v___x_6074_ = l_Lean_Expr_const___override(v___x_6073_, v___x_6072_);
return v___x_6074_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4(void){
_start:
{
lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; 
v___x_6075_ = l_Lean_Nat_mkInstHPow;
v___x_6076_ = l_Lean_Nat_mkType;
v___x_6077_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6078_ = l_Lean_mkApp4(v___x_6077_, v___x_6076_, v___x_6076_, v___x_6076_, v___x_6075_);
return v___x_6078_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn(void){
_start:
{
lean_object* v___x_6079_; 
v___x_6079_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__4, &l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4);
return v___x_6079_;
}
}
static lean_object* _init_l_Lean_mkNatSucc___closed__2(void){
_start:
{
lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; 
v___x_6084_ = lean_box(0);
v___x_6085_ = ((lean_object*)(l_Lean_mkNatSucc___closed__1));
v___x_6086_ = l_Lean_Expr_const___override(v___x_6085_, v___x_6084_);
return v___x_6086_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* v_a_6087_){
_start:
{
lean_object* v___x_6088_; lean_object* v___x_6089_; 
v___x_6088_ = lean_obj_once(&l_Lean_mkNatSucc___closed__2, &l_Lean_mkNatSucc___closed__2_once, _init_l_Lean_mkNatSucc___closed__2);
v___x_6089_ = l_Lean_Expr_app___override(v___x_6088_, v_a_6087_);
return v___x_6089_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* v_a_6090_, lean_object* v_b_6091_){
_start:
{
lean_object* v___x_6092_; lean_object* v___x_6093_; 
v___x_6092_ = l___private_Lean_Expr_0__Lean_natAddFn;
v___x_6093_ = l_Lean_mkAppB(v___x_6092_, v_a_6090_, v_b_6091_);
return v___x_6093_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* v_a_6094_, lean_object* v_b_6095_){
_start:
{
lean_object* v___x_6096_; lean_object* v___x_6097_; 
v___x_6096_ = l___private_Lean_Expr_0__Lean_natSubFn;
v___x_6097_ = l_Lean_mkAppB(v___x_6096_, v_a_6094_, v_b_6095_);
return v___x_6097_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* v_a_6098_, lean_object* v_b_6099_){
_start:
{
lean_object* v___x_6100_; lean_object* v___x_6101_; 
v___x_6100_ = l___private_Lean_Expr_0__Lean_natMulFn;
v___x_6101_ = l_Lean_mkAppB(v___x_6100_, v_a_6098_, v_b_6099_);
return v___x_6101_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object* v_a_6102_, lean_object* v_b_6103_){
_start:
{
lean_object* v___x_6104_; lean_object* v___x_6105_; 
v___x_6104_ = l___private_Lean_Expr_0__Lean_natPowFn;
v___x_6105_ = l_Lean_mkAppB(v___x_6104_, v_a_6102_, v_b_6103_);
return v___x_6105_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3(void){
_start:
{
lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; 
v___x_6111_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6112_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natLEPred___closed__2));
v___x_6113_ = l_Lean_Expr_const___override(v___x_6112_, v___x_6111_);
return v___x_6113_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4(void){
_start:
{
lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; 
v___x_6114_ = l_Lean_Nat_mkInstLE;
v___x_6115_ = l_Lean_Nat_mkType;
v___x_6116_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6117_ = l_Lean_mkAppB(v___x_6116_, v___x_6115_, v___x_6114_);
return v___x_6117_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred(void){
_start:
{
lean_object* v___x_6118_; 
v___x_6118_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__4, &l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4);
return v___x_6118_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* v_a_6119_, lean_object* v_b_6120_){
_start:
{
lean_object* v___x_6121_; lean_object* v___x_6122_; 
v___x_6121_ = l___private_Lean_Expr_0__Lean_natLEPred;
v___x_6122_ = l_Lean_mkAppB(v___x_6121_, v_a_6119_, v_b_6120_);
return v___x_6122_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0(void){
_start:
{
lean_object* v___x_6123_; lean_object* v___x_6124_; 
v___x_6123_ = lean_unsigned_to_nat(1u);
v___x_6124_ = l_Lean_Level_ofNat(v___x_6123_);
return v___x_6124_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1(void){
_start:
{
lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; 
v___x_6125_ = lean_box(0);
v___x_6126_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__0, &l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0);
v___x_6127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6127_, 0, v___x_6126_);
lean_ctor_set(v___x_6127_, 1, v___x_6125_);
return v___x_6127_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2(void){
_start:
{
lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; 
v___x_6128_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__1, &l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1);
v___x_6129_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_6130_ = l_Lean_Expr_const___override(v___x_6129_, v___x_6128_);
return v___x_6130_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3(void){
_start:
{
lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; 
v___x_6131_ = l_Lean_Nat_mkType;
v___x_6132_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6133_ = l_Lean_Expr_app___override(v___x_6132_, v___x_6131_);
return v___x_6133_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred(void){
_start:
{
lean_object* v___x_6134_; 
v___x_6134_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__3, &l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3);
return v___x_6134_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* v_a_6135_, lean_object* v_b_6136_){
_start:
{
lean_object* v___x_6137_; lean_object* v___x_6138_; 
v___x_6137_ = l___private_Lean_Expr_0__Lean_natEqPred;
v___x_6138_ = l_Lean_mkAppB(v___x_6137_, v_a_6135_, v_b_6136_);
return v___x_6138_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__0(void){
_start:
{
lean_object* v___x_6139_; lean_object* v___x_6140_; 
v___x_6139_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6140_ = l_Lean_Expr_sort___override(v___x_6139_);
return v___x_6140_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__1(void){
_start:
{
lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; 
v___x_6141_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__0, &l___private_Lean_Expr_0__Lean_propEq___closed__0_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__0);
v___x_6142_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6143_ = l_Lean_Expr_app___override(v___x_6142_, v___x_6141_);
return v___x_6143_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq(void){
_start:
{
lean_object* v___x_6144_; 
v___x_6144_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__1, &l___private_Lean_Expr_0__Lean_propEq___closed__1_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__1);
return v___x_6144_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* v_a_6145_, lean_object* v_b_6146_){
_start:
{
lean_object* v___x_6147_; lean_object* v___x_6148_; 
v___x_6147_ = l___private_Lean_Expr_0__Lean_propEq;
v___x_6148_ = l_Lean_mkAppB(v___x_6147_, v_a_6145_, v_b_6146_);
return v___x_6148_;
}
}
static lean_object* _init_l_Lean_Int_mkType___closed__2(void){
_start:
{
lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; 
v___x_6152_ = lean_box(0);
v___x_6153_ = ((lean_object*)(l_Lean_Int_mkType___closed__1));
v___x_6154_ = l_Lean_Expr_const___override(v___x_6153_, v___x_6152_);
return v___x_6154_;
}
}
static lean_object* _init_l_Lean_Int_mkType(void){
_start:
{
lean_object* v___x_6155_; 
v___x_6155_ = lean_obj_once(&l_Lean_Int_mkType___closed__2, &l_Lean_Int_mkType___closed__2_once, _init_l_Lean_Int_mkType___closed__2);
return v___x_6155_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg___closed__2(void){
_start:
{
lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; 
v___x_6160_ = lean_box(0);
v___x_6161_ = ((lean_object*)(l_Lean_Int_mkInstNeg___closed__1));
v___x_6162_ = l_Lean_Expr_const___override(v___x_6161_, v___x_6160_);
return v___x_6162_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg(void){
_start:
{
lean_object* v___x_6163_; 
v___x_6163_ = lean_obj_once(&l_Lean_Int_mkInstNeg___closed__2, &l_Lean_Int_mkInstNeg___closed__2_once, _init_l_Lean_Int_mkInstNeg___closed__2);
return v___x_6163_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; 
v___x_6168_ = lean_box(0);
v___x_6169_ = ((lean_object*)(l_Lean_Int_mkInstAdd___closed__1));
v___x_6170_ = l_Lean_Expr_const___override(v___x_6169_, v___x_6168_);
return v___x_6170_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd(void){
_start:
{
lean_object* v___x_6171_; 
v___x_6171_ = lean_obj_once(&l_Lean_Int_mkInstAdd___closed__2, &l_Lean_Int_mkInstAdd___closed__2_once, _init_l_Lean_Int_mkInstAdd___closed__2);
return v___x_6171_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd___closed__0(void){
_start:
{
lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; 
v___x_6172_ = l_Lean_Int_mkInstAdd;
v___x_6173_ = l_Lean_Int_mkType;
v___x_6174_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6175_ = l_Lean_mkAppB(v___x_6174_, v___x_6173_, v___x_6172_);
return v___x_6175_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd(void){
_start:
{
lean_object* v___x_6176_; 
v___x_6176_ = lean_obj_once(&l_Lean_Int_mkInstHAdd___closed__0, &l_Lean_Int_mkInstHAdd___closed__0_once, _init_l_Lean_Int_mkInstHAdd___closed__0);
return v___x_6176_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; 
v___x_6181_ = lean_box(0);
v___x_6182_ = ((lean_object*)(l_Lean_Int_mkInstSub___closed__1));
v___x_6183_ = l_Lean_Expr_const___override(v___x_6182_, v___x_6181_);
return v___x_6183_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub(void){
_start:
{
lean_object* v___x_6184_; 
v___x_6184_ = lean_obj_once(&l_Lean_Int_mkInstSub___closed__2, &l_Lean_Int_mkInstSub___closed__2_once, _init_l_Lean_Int_mkInstSub___closed__2);
return v___x_6184_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub___closed__0(void){
_start:
{
lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; 
v___x_6185_ = l_Lean_Int_mkInstSub;
v___x_6186_ = l_Lean_Int_mkType;
v___x_6187_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6188_ = l_Lean_mkAppB(v___x_6187_, v___x_6186_, v___x_6185_);
return v___x_6188_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub(void){
_start:
{
lean_object* v___x_6189_; 
v___x_6189_ = lean_obj_once(&l_Lean_Int_mkInstHSub___closed__0, &l_Lean_Int_mkInstHSub___closed__0_once, _init_l_Lean_Int_mkInstHSub___closed__0);
return v___x_6189_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; 
v___x_6194_ = lean_box(0);
v___x_6195_ = ((lean_object*)(l_Lean_Int_mkInstMul___closed__1));
v___x_6196_ = l_Lean_Expr_const___override(v___x_6195_, v___x_6194_);
return v___x_6196_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul(void){
_start:
{
lean_object* v___x_6197_; 
v___x_6197_ = lean_obj_once(&l_Lean_Int_mkInstMul___closed__2, &l_Lean_Int_mkInstMul___closed__2_once, _init_l_Lean_Int_mkInstMul___closed__2);
return v___x_6197_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul___closed__0(void){
_start:
{
lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; 
v___x_6198_ = l_Lean_Int_mkInstMul;
v___x_6199_ = l_Lean_Int_mkType;
v___x_6200_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6201_ = l_Lean_mkAppB(v___x_6200_, v___x_6199_, v___x_6198_);
return v___x_6201_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul(void){
_start:
{
lean_object* v___x_6202_; 
v___x_6202_ = lean_obj_once(&l_Lean_Int_mkInstHMul___closed__0, &l_Lean_Int_mkInstHMul___closed__0_once, _init_l_Lean_Int_mkInstHMul___closed__0);
return v___x_6202_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv___closed__1(void){
_start:
{
lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; 
v___x_6206_ = lean_box(0);
v___x_6207_ = ((lean_object*)(l_Lean_Int_mkInstDiv___closed__0));
v___x_6208_ = l_Lean_Expr_const___override(v___x_6207_, v___x_6206_);
return v___x_6208_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv(void){
_start:
{
lean_object* v___x_6209_; 
v___x_6209_ = lean_obj_once(&l_Lean_Int_mkInstDiv___closed__1, &l_Lean_Int_mkInstDiv___closed__1_once, _init_l_Lean_Int_mkInstDiv___closed__1);
return v___x_6209_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv___closed__0(void){
_start:
{
lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; 
v___x_6210_ = l_Lean_Int_mkInstDiv;
v___x_6211_ = l_Lean_Int_mkType;
v___x_6212_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6213_ = l_Lean_mkAppB(v___x_6212_, v___x_6211_, v___x_6210_);
return v___x_6213_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv(void){
_start:
{
lean_object* v___x_6214_; 
v___x_6214_ = lean_obj_once(&l_Lean_Int_mkInstHDiv___closed__0, &l_Lean_Int_mkInstHDiv___closed__0_once, _init_l_Lean_Int_mkInstHDiv___closed__0);
return v___x_6214_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod___closed__1(void){
_start:
{
lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; 
v___x_6218_ = lean_box(0);
v___x_6219_ = ((lean_object*)(l_Lean_Int_mkInstMod___closed__0));
v___x_6220_ = l_Lean_Expr_const___override(v___x_6219_, v___x_6218_);
return v___x_6220_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod(void){
_start:
{
lean_object* v___x_6221_; 
v___x_6221_ = lean_obj_once(&l_Lean_Int_mkInstMod___closed__1, &l_Lean_Int_mkInstMod___closed__1_once, _init_l_Lean_Int_mkInstMod___closed__1);
return v___x_6221_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod___closed__0(void){
_start:
{
lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; 
v___x_6222_ = l_Lean_Int_mkInstMod;
v___x_6223_ = l_Lean_Int_mkType;
v___x_6224_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6225_ = l_Lean_mkAppB(v___x_6224_, v___x_6223_, v___x_6222_);
return v___x_6225_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod(void){
_start:
{
lean_object* v___x_6226_; 
v___x_6226_ = lean_obj_once(&l_Lean_Int_mkInstHMod___closed__0, &l_Lean_Int_mkInstHMod___closed__0_once, _init_l_Lean_Int_mkInstHMod___closed__0);
return v___x_6226_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; 
v___x_6231_ = lean_box(0);
v___x_6232_ = ((lean_object*)(l_Lean_Int_mkInstPow___closed__1));
v___x_6233_ = l_Lean_Expr_const___override(v___x_6232_, v___x_6231_);
return v___x_6233_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow(void){
_start:
{
lean_object* v___x_6234_; 
v___x_6234_ = lean_obj_once(&l_Lean_Int_mkInstPow___closed__2, &l_Lean_Int_mkInstPow___closed__2_once, _init_l_Lean_Int_mkInstPow___closed__2);
return v___x_6234_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat___closed__0(void){
_start:
{
lean_object* v___x_6235_; lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; 
v___x_6235_ = l_Lean_Int_mkInstPow;
v___x_6236_ = l_Lean_Int_mkType;
v___x_6237_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6238_ = l_Lean_mkAppB(v___x_6237_, v___x_6236_, v___x_6235_);
return v___x_6238_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat(void){
_start:
{
lean_object* v___x_6239_; 
v___x_6239_ = lean_obj_once(&l_Lean_Int_mkInstPowNat___closed__0, &l_Lean_Int_mkInstPowNat___closed__0_once, _init_l_Lean_Int_mkInstPowNat___closed__0);
return v___x_6239_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow___closed__0(void){
_start:
{
lean_object* v___x_6240_; lean_object* v___x_6241_; lean_object* v___x_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; 
v___x_6240_ = l_Lean_Int_mkInstPowNat;
v___x_6241_ = l_Lean_Nat_mkType;
v___x_6242_ = l_Lean_Int_mkType;
v___x_6243_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6244_ = l_Lean_mkApp3(v___x_6243_, v___x_6242_, v___x_6241_, v___x_6240_);
return v___x_6244_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow(void){
_start:
{
lean_object* v___x_6245_; 
v___x_6245_ = lean_obj_once(&l_Lean_Int_mkInstHPow___closed__0, &l_Lean_Int_mkInstHPow___closed__0_once, _init_l_Lean_Int_mkInstHPow___closed__0);
return v___x_6245_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6250_; lean_object* v___x_6251_; lean_object* v___x_6252_; 
v___x_6250_ = lean_box(0);
v___x_6251_ = ((lean_object*)(l_Lean_Int_mkInstLT___closed__1));
v___x_6252_ = l_Lean_Expr_const___override(v___x_6251_, v___x_6250_);
return v___x_6252_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT(void){
_start:
{
lean_object* v___x_6253_; 
v___x_6253_ = lean_obj_once(&l_Lean_Int_mkInstLT___closed__2, &l_Lean_Int_mkInstLT___closed__2_once, _init_l_Lean_Int_mkInstLT___closed__2);
return v___x_6253_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6258_; lean_object* v___x_6259_; lean_object* v___x_6260_; 
v___x_6258_ = lean_box(0);
v___x_6259_ = ((lean_object*)(l_Lean_Int_mkInstLE___closed__1));
v___x_6260_ = l_Lean_Expr_const___override(v___x_6259_, v___x_6258_);
return v___x_6260_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE(void){
_start:
{
lean_object* v___x_6261_; 
v___x_6261_ = lean_obj_once(&l_Lean_Int_mkInstLE___closed__2, &l_Lean_Int_mkInstLE___closed__2_once, _init_l_Lean_Int_mkInstLE___closed__2);
return v___x_6261_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast___closed__2(void){
_start:
{
lean_object* v___x_6265_; lean_object* v___x_6266_; lean_object* v___x_6267_; 
v___x_6265_ = lean_box(0);
v___x_6266_ = ((lean_object*)(l_Lean_Int_mkInstNatCast___closed__1));
v___x_6267_ = l_Lean_Expr_const___override(v___x_6266_, v___x_6265_);
return v___x_6267_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast(void){
_start:
{
lean_object* v___x_6268_; 
v___x_6268_ = lean_obj_once(&l_Lean_Int_mkInstNatCast___closed__2, &l_Lean_Int_mkInstNatCast___closed__2_once, _init_l_Lean_Int_mkInstNatCast___closed__2);
return v___x_6268_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0(void){
_start:
{
lean_object* v___x_6269_; lean_object* v___x_6270_; lean_object* v___x_6271_; 
v___x_6269_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6270_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_6271_ = l_Lean_Expr_const___override(v___x_6270_, v___x_6269_);
return v___x_6271_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1(void){
_start:
{
lean_object* v___x_6272_; lean_object* v___x_6273_; lean_object* v___x_6274_; lean_object* v___x_6275_; 
v___x_6272_ = l_Lean_Int_mkInstNeg;
v___x_6273_ = l_Lean_Int_mkType;
v___x_6274_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__0, &l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0);
v___x_6275_ = l_Lean_mkAppB(v___x_6274_, v___x_6273_, v___x_6272_);
return v___x_6275_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn(void){
_start:
{
lean_object* v___x_6276_; 
v___x_6276_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__1, &l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1);
return v___x_6276_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0(void){
_start:
{
lean_object* v___x_6277_; lean_object* v___x_6278_; lean_object* v___x_6279_; lean_object* v___x_6280_; 
v___x_6277_ = l_Lean_Int_mkInstHAdd;
v___x_6278_ = l_Lean_Int_mkType;
v___x_6279_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6280_ = l_Lean_mkApp4(v___x_6279_, v___x_6278_, v___x_6278_, v___x_6278_, v___x_6277_);
return v___x_6280_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn(void){
_start:
{
lean_object* v___x_6281_; 
v___x_6281_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intAddFn___closed__0, &l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0);
return v___x_6281_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0(void){
_start:
{
lean_object* v___x_6282_; lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; 
v___x_6282_ = l_Lean_Int_mkInstHSub;
v___x_6283_ = l_Lean_Int_mkType;
v___x_6284_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6285_ = l_Lean_mkApp4(v___x_6284_, v___x_6283_, v___x_6283_, v___x_6283_, v___x_6282_);
return v___x_6285_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn(void){
_start:
{
lean_object* v___x_6286_; 
v___x_6286_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intSubFn___closed__0, &l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0);
return v___x_6286_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0(void){
_start:
{
lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; 
v___x_6287_ = l_Lean_Int_mkInstHMul;
v___x_6288_ = l_Lean_Int_mkType;
v___x_6289_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6290_ = l_Lean_mkApp4(v___x_6289_, v___x_6288_, v___x_6288_, v___x_6288_, v___x_6287_);
return v___x_6290_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn(void){
_start:
{
lean_object* v___x_6291_; 
v___x_6291_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intMulFn___closed__0, &l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0);
return v___x_6291_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3(void){
_start:
{
lean_object* v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; 
v___x_6297_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6298_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intDivFn___closed__2));
v___x_6299_ = l_Lean_Expr_const___override(v___x_6298_, v___x_6297_);
return v___x_6299_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4(void){
_start:
{
lean_object* v___x_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; 
v___x_6300_ = l_Lean_Int_mkInstHDiv;
v___x_6301_ = l_Lean_Int_mkType;
v___x_6302_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__3, &l___private_Lean_Expr_0__Lean_intDivFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3);
v___x_6303_ = l_Lean_mkApp4(v___x_6302_, v___x_6301_, v___x_6301_, v___x_6301_, v___x_6300_);
return v___x_6303_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn(void){
_start:
{
lean_object* v___x_6304_; 
v___x_6304_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__4, &l___private_Lean_Expr_0__Lean_intDivFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4);
return v___x_6304_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3(void){
_start:
{
lean_object* v___x_6310_; lean_object* v___x_6311_; lean_object* v___x_6312_; 
v___x_6310_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6311_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intModFn___closed__2));
v___x_6312_ = l_Lean_Expr_const___override(v___x_6311_, v___x_6310_);
return v___x_6312_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4(void){
_start:
{
lean_object* v___x_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; lean_object* v___x_6316_; 
v___x_6313_ = l_Lean_Int_mkInstHMod;
v___x_6314_ = l_Lean_Int_mkType;
v___x_6315_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__3, &l___private_Lean_Expr_0__Lean_intModFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3);
v___x_6316_ = l_Lean_mkApp4(v___x_6315_, v___x_6314_, v___x_6314_, v___x_6314_, v___x_6313_);
return v___x_6316_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn(void){
_start:
{
lean_object* v___x_6317_; 
v___x_6317_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__4, &l___private_Lean_Expr_0__Lean_intModFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4);
return v___x_6317_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0(void){
_start:
{
lean_object* v___x_6318_; lean_object* v___x_6319_; lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v___x_6322_; 
v___x_6318_ = l_Lean_Int_mkInstHPow;
v___x_6319_ = l_Lean_Nat_mkType;
v___x_6320_ = l_Lean_Int_mkType;
v___x_6321_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6322_ = l_Lean_mkApp4(v___x_6321_, v___x_6320_, v___x_6319_, v___x_6320_, v___x_6318_);
return v___x_6322_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn(void){
_start:
{
lean_object* v___x_6323_; 
v___x_6323_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0, &l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0);
return v___x_6323_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3(void){
_start:
{
lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; 
v___x_6329_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6330_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2));
v___x_6331_ = l_Lean_Expr_const___override(v___x_6330_, v___x_6329_);
return v___x_6331_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4(void){
_start:
{
lean_object* v___x_6332_; lean_object* v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; 
v___x_6332_ = l_Lean_Int_mkInstNatCast;
v___x_6333_ = l_Lean_Int_mkType;
v___x_6334_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3);
v___x_6335_ = l_Lean_mkAppB(v___x_6334_, v___x_6333_, v___x_6332_);
return v___x_6335_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn(void){
_start:
{
lean_object* v___x_6336_; 
v___x_6336_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4);
return v___x_6336_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* v_a_6337_){
_start:
{
lean_object* v___x_6338_; lean_object* v___x_6339_; 
v___x_6338_ = l___private_Lean_Expr_0__Lean_intNegFn;
v___x_6339_ = l_Lean_Expr_app___override(v___x_6338_, v_a_6337_);
return v___x_6339_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* v_a_6340_, lean_object* v_b_6341_){
_start:
{
lean_object* v___x_6342_; lean_object* v___x_6343_; 
v___x_6342_ = l___private_Lean_Expr_0__Lean_intAddFn;
v___x_6343_ = l_Lean_mkAppB(v___x_6342_, v_a_6340_, v_b_6341_);
return v___x_6343_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* v_a_6344_, lean_object* v_b_6345_){
_start:
{
lean_object* v___x_6346_; lean_object* v___x_6347_; 
v___x_6346_ = l___private_Lean_Expr_0__Lean_intSubFn;
v___x_6347_ = l_Lean_mkAppB(v___x_6346_, v_a_6344_, v_b_6345_);
return v___x_6347_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* v_a_6348_, lean_object* v_b_6349_){
_start:
{
lean_object* v___x_6350_; lean_object* v___x_6351_; 
v___x_6350_ = l___private_Lean_Expr_0__Lean_intMulFn;
v___x_6351_ = l_Lean_mkAppB(v___x_6350_, v_a_6348_, v_b_6349_);
return v___x_6351_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* v_a_6352_, lean_object* v_b_6353_){
_start:
{
lean_object* v___x_6354_; lean_object* v___x_6355_; 
v___x_6354_ = l___private_Lean_Expr_0__Lean_intDivFn;
v___x_6355_ = l_Lean_mkAppB(v___x_6354_, v_a_6352_, v_b_6353_);
return v___x_6355_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* v_a_6356_, lean_object* v_b_6357_){
_start:
{
lean_object* v___x_6358_; lean_object* v___x_6359_; 
v___x_6358_ = l___private_Lean_Expr_0__Lean_intModFn;
v___x_6359_ = l_Lean_mkAppB(v___x_6358_, v_a_6356_, v_b_6357_);
return v___x_6359_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* v_a_6360_){
_start:
{
lean_object* v___x_6361_; lean_object* v___x_6362_; 
v___x_6361_ = l___private_Lean_Expr_0__Lean_intNatCastFn;
v___x_6362_ = l_Lean_Expr_app___override(v___x_6361_, v_a_6360_);
return v___x_6362_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object* v_a_6363_, lean_object* v_b_6364_){
_start:
{
lean_object* v___x_6365_; lean_object* v___x_6366_; 
v___x_6365_ = l___private_Lean_Expr_0__Lean_intPowNatFn;
v___x_6366_ = l_Lean_mkAppB(v___x_6365_, v_a_6363_, v_b_6364_);
return v___x_6366_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0(void){
_start:
{
lean_object* v___x_6367_; lean_object* v___x_6368_; lean_object* v___x_6369_; lean_object* v___x_6370_; 
v___x_6367_ = l_Lean_Int_mkInstLE;
v___x_6368_ = l_Lean_Int_mkType;
v___x_6369_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6370_ = l_Lean_mkAppB(v___x_6369_, v___x_6368_, v___x_6367_);
return v___x_6370_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred(void){
_start:
{
lean_object* v___x_6371_; 
v___x_6371_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLEPred___closed__0, &l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0);
return v___x_6371_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* v_a_6372_, lean_object* v_b_6373_){
_start:
{
lean_object* v___x_6374_; lean_object* v___x_6375_; 
v___x_6374_ = l___private_Lean_Expr_0__Lean_intLEPred;
v___x_6375_ = l_Lean_mkAppB(v___x_6374_, v_a_6372_, v_b_6373_);
return v___x_6375_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3(void){
_start:
{
lean_object* v___x_6381_; lean_object* v___x_6382_; lean_object* v___x_6383_; 
v___x_6381_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6382_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intLTPred___closed__2));
v___x_6383_ = l_Lean_Expr_const___override(v___x_6382_, v___x_6381_);
return v___x_6383_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4(void){
_start:
{
lean_object* v___x_6384_; lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; 
v___x_6384_ = l_Lean_Int_mkInstLT;
v___x_6385_ = l_Lean_Int_mkType;
v___x_6386_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__3, &l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3);
v___x_6387_ = l_Lean_mkAppB(v___x_6386_, v___x_6385_, v___x_6384_);
return v___x_6387_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred(void){
_start:
{
lean_object* v___x_6388_; 
v___x_6388_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__4, &l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4);
return v___x_6388_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object* v_a_6389_, lean_object* v_b_6390_){
_start:
{
lean_object* v___x_6391_; lean_object* v___x_6392_; 
v___x_6391_ = l___private_Lean_Expr_0__Lean_intLTPred;
v___x_6392_ = l_Lean_mkAppB(v___x_6391_, v_a_6389_, v_b_6390_);
return v___x_6392_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0(void){
_start:
{
lean_object* v___x_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; 
v___x_6393_ = l_Lean_Int_mkType;
v___x_6394_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6395_ = l_Lean_Expr_app___override(v___x_6394_, v___x_6393_);
return v___x_6395_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred(void){
_start:
{
lean_object* v___x_6396_; 
v___x_6396_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intEqPred___closed__0, &l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0);
return v___x_6396_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* v_a_6397_, lean_object* v_b_6398_){
_start:
{
lean_object* v___x_6399_; lean_object* v___x_6400_; 
v___x_6399_ = l___private_Lean_Expr_0__Lean_intEqPred;
v___x_6400_ = l_Lean_mkAppB(v___x_6399_, v_a_6397_, v_b_6398_);
return v___x_6400_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__3(void){
_start:
{
lean_object* v___x_6406_; lean_object* v___x_6407_; lean_object* v___x_6408_; 
v___x_6406_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6407_ = ((lean_object*)(l_Lean_mkIntDvd___closed__2));
v___x_6408_ = l_Lean_Expr_const___override(v___x_6407_, v___x_6406_);
return v___x_6408_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__6(void){
_start:
{
lean_object* v___x_6413_; lean_object* v___x_6414_; lean_object* v___x_6415_; 
v___x_6413_ = lean_box(0);
v___x_6414_ = ((lean_object*)(l_Lean_mkIntDvd___closed__5));
v___x_6415_ = l_Lean_Expr_const___override(v___x_6414_, v___x_6413_);
return v___x_6415_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* v_a_6416_, lean_object* v_b_6417_){
_start:
{
lean_object* v___x_6418_; lean_object* v___x_6419_; lean_object* v___x_6420_; lean_object* v___x_6421_; 
v___x_6418_ = lean_obj_once(&l_Lean_mkIntDvd___closed__3, &l_Lean_mkIntDvd___closed__3_once, _init_l_Lean_mkIntDvd___closed__3);
v___x_6419_ = l_Lean_Int_mkType;
v___x_6420_ = lean_obj_once(&l_Lean_mkIntDvd___closed__6, &l_Lean_mkIntDvd___closed__6_once, _init_l_Lean_mkIntDvd___closed__6);
v___x_6421_ = l_Lean_mkApp4(v___x_6418_, v___x_6419_, v___x_6420_, v_a_6416_, v_b_6417_);
return v___x_6421_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__2(void){
_start:
{
lean_object* v___x_6425_; lean_object* v___x_6426_; lean_object* v___x_6427_; 
v___x_6425_ = lean_box(0);
v___x_6426_ = ((lean_object*)(l_Lean_mkIntLit___closed__1));
v___x_6427_ = l_Lean_Expr_const___override(v___x_6426_, v___x_6425_);
return v___x_6427_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__3(void){
_start:
{
lean_object* v___x_6428_; lean_object* v___x_6429_; 
v___x_6428_ = lean_unsigned_to_nat(0u);
v___x_6429_ = lean_nat_to_int(v___x_6428_);
return v___x_6429_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* v_n_6430_){
_start:
{
lean_object* v___x_6431_; lean_object* v_r_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; lean_object* v___x_6435_; lean_object* v___x_6436_; lean_object* v_r_6437_; lean_object* v___x_6438_; uint8_t v___x_6439_; 
v___x_6431_ = lean_nat_abs(v_n_6430_);
v_r_6432_ = l_Lean_mkRawNatLit(v___x_6431_);
v___x_6433_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_6434_ = l_Lean_Int_mkType;
v___x_6435_ = lean_obj_once(&l_Lean_mkIntLit___closed__2, &l_Lean_mkIntLit___closed__2_once, _init_l_Lean_mkIntLit___closed__2);
lean_inc_ref(v_r_6432_);
v___x_6436_ = l_Lean_Expr_app___override(v___x_6435_, v_r_6432_);
v_r_6437_ = l_Lean_mkApp3(v___x_6433_, v___x_6434_, v_r_6432_, v___x_6436_);
v___x_6438_ = lean_obj_once(&l_Lean_mkIntLit___closed__3, &l_Lean_mkIntLit___closed__3_once, _init_l_Lean_mkIntLit___closed__3);
v___x_6439_ = lean_int_dec_lt(v_n_6430_, v___x_6438_);
if (v___x_6439_ == 0)
{
return v_r_6437_;
}
else
{
lean_object* v___x_6440_; 
v___x_6440_ = l_Lean_mkIntNeg(v_r_6437_);
return v___x_6440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* v_n_6441_){
_start:
{
lean_object* v_res_6442_; 
v_res_6442_ = l_Lean_mkIntLit(v_n_6441_);
lean_dec(v_n_6441_);
return v_res_6442_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6447_; lean_object* v___x_6448_; 
v___x_6447_ = lean_box(0);
v___x_6448_ = l_Lean_Level_succ___override(v___x_6447_);
return v___x_6448_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; 
v___x_6449_ = lean_box(0);
v___x_6450_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__2, &l_Lean_reflBoolTrue___closed__2_once, _init_l_Lean_reflBoolTrue___closed__2);
v___x_6451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6451_, 0, v___x_6450_);
lean_ctor_set(v___x_6451_, 1, v___x_6449_);
return v___x_6451_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6452_; lean_object* v___x_6453_; lean_object* v___x_6454_; 
v___x_6452_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__3, &l_Lean_reflBoolTrue___closed__3_once, _init_l_Lean_reflBoolTrue___closed__3);
v___x_6453_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__1));
v___x_6454_ = l_Lean_Expr_const___override(v___x_6453_, v___x_6452_);
return v___x_6454_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__6(void){
_start:
{
lean_object* v___x_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; 
v___x_6457_ = lean_box(0);
v___x_6458_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__5));
v___x_6459_ = l_Lean_Expr_const___override(v___x_6458_, v___x_6457_);
return v___x_6459_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__7(void){
_start:
{
lean_object* v___x_6460_; lean_object* v___x_6461_; lean_object* v___x_6462_; 
v___x_6460_ = lean_box(0);
v___x_6461_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_6462_ = l_Lean_Expr_const___override(v___x_6461_, v___x_6460_);
return v___x_6462_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__8(void){
_start:
{
lean_object* v___x_6463_; lean_object* v___x_6464_; lean_object* v___x_6465_; lean_object* v___x_6466_; 
v___x_6463_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6464_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6465_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6466_ = l_Lean_mkAppB(v___x_6465_, v___x_6464_, v___x_6463_);
return v___x_6466_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue(void){
_start:
{
lean_object* v___x_6467_; 
v___x_6467_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__8, &l_Lean_reflBoolTrue___closed__8_once, _init_l_Lean_reflBoolTrue___closed__8);
return v___x_6467_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6468_; lean_object* v___x_6469_; lean_object* v___x_6470_; 
v___x_6468_ = lean_box(0);
v___x_6469_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_6470_ = l_Lean_Expr_const___override(v___x_6469_, v___x_6468_);
return v___x_6470_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6471_; lean_object* v___x_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; 
v___x_6471_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6472_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6473_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6474_ = l_Lean_mkAppB(v___x_6473_, v___x_6472_, v___x_6471_);
return v___x_6474_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse(void){
_start:
{
lean_object* v___x_6475_; 
v___x_6475_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
return v___x_6475_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; 
v___x_6479_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6480_ = ((lean_object*)(l_Lean_eagerReflBoolTrue___closed__1));
v___x_6481_ = l_Lean_Expr_const___override(v___x_6480_, v___x_6479_);
return v___x_6481_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; lean_object* v___x_6485_; 
v___x_6482_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6483_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6484_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6485_ = l_Lean_mkApp3(v___x_6484_, v___x_6483_, v___x_6482_, v___x_6482_);
return v___x_6485_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; 
v___x_6486_ = l_Lean_reflBoolTrue;
v___x_6487_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__3, &l_Lean_eagerReflBoolTrue___closed__3_once, _init_l_Lean_eagerReflBoolTrue___closed__3);
v___x_6488_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6489_ = l_Lean_mkAppB(v___x_6488_, v___x_6487_, v___x_6486_);
return v___x_6489_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue(void){
_start:
{
lean_object* v___x_6490_; 
v___x_6490_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__4, &l_Lean_eagerReflBoolTrue___closed__4_once, _init_l_Lean_eagerReflBoolTrue___closed__4);
return v___x_6490_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; 
v___x_6491_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6492_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6493_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6494_ = l_Lean_mkApp3(v___x_6493_, v___x_6492_, v___x_6491_, v___x_6491_);
return v___x_6494_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6495_; lean_object* v___x_6496_; lean_object* v___x_6497_; lean_object* v___x_6498_; 
v___x_6495_ = l_Lean_reflBoolFalse;
v___x_6496_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__0, &l_Lean_eagerReflBoolFalse___closed__0_once, _init_l_Lean_eagerReflBoolFalse___closed__0);
v___x_6497_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6498_ = l_Lean_mkAppB(v___x_6497_, v___x_6496_, v___x_6495_);
return v___x_6498_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse(void){
_start:
{
lean_object* v___x_6499_; 
v___x_6499_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__1, &l_Lean_eagerReflBoolFalse___closed__1_once, _init_l_Lean_eagerReflBoolFalse___closed__1);
return v___x_6499_;
}
}
static lean_object* _init_l_Lean_Expr_replaceFn___closed__2(void){
_start:
{
lean_object* v___x_6502_; lean_object* v___x_6503_; lean_object* v___x_6504_; lean_object* v___x_6505_; lean_object* v___x_6506_; lean_object* v___x_6507_; 
v___x_6502_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__1));
v___x_6503_ = lean_unsigned_to_nat(9u);
v___x_6504_ = lean_unsigned_to_nat(2432u);
v___x_6505_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__0));
v___x_6506_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_6507_ = l_mkPanicMessageWithDecl(v___x_6506_, v___x_6505_, v___x_6504_, v___x_6503_, v___x_6502_);
return v___x_6507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object* v_e_6508_, lean_object* v_declName_6509_){
_start:
{
switch(lean_obj_tag(v_e_6508_))
{
case 5:
{
lean_object* v_fn_6510_; lean_object* v_arg_6511_; lean_object* v___x_6512_; lean_object* v___x_6513_; 
v_fn_6510_ = lean_ctor_get(v_e_6508_, 0);
lean_inc_ref(v_fn_6510_);
v_arg_6511_ = lean_ctor_get(v_e_6508_, 1);
lean_inc_ref(v_arg_6511_);
lean_dec_ref(v_e_6508_);
v___x_6512_ = l_Lean_Expr_replaceFn(v_fn_6510_, v_declName_6509_);
v___x_6513_ = l_Lean_Expr_app___override(v___x_6512_, v_arg_6511_);
return v___x_6513_;
}
case 4:
{
lean_object* v_us_6514_; lean_object* v___x_6515_; 
v_us_6514_ = lean_ctor_get(v_e_6508_, 1);
lean_inc(v_us_6514_);
lean_dec_ref(v_e_6508_);
v___x_6515_ = l_Lean_Expr_const___override(v_declName_6509_, v_us_6514_);
return v___x_6515_;
}
default: 
{
lean_object* v___x_6516_; lean_object* v___x_6517_; 
lean_dec(v_declName_6509_);
lean_dec_ref(v_e_6508_);
v___x_6516_ = lean_obj_once(&l_Lean_Expr_replaceFn___closed__2, &l_Lean_Expr_replaceFn___closed__2_once, _init_l_Lean_Expr_replaceFn___closed__2);
v___x_6517_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_6516_);
return v___x_6517_;
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
