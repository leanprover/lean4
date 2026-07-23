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
v___x_825_ = lean_nat_add(v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec(v___y_823_);
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
lean_ctor_set(v___x_805_, 3, v___y_822_);
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
lean_ctor_set(v_reuseFailAlloc_830_, 3, v___y_822_);
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
v___y_822_ = v___x_836_;
v___y_823_ = v___x_837_;
v___y_824_ = v_size_838_;
goto v___jp_821_;
}
else
{
lean_object* v___x_839_; 
v___x_839_ = lean_unsigned_to_nat(0u);
v___y_822_ = v___x_836_;
v___y_823_ = v___x_837_;
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
lean_dec_ref_known(v_x_1006_, 5);
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
lean_dec_ref_known(v_t_1510_, 2);
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
lean_dec_ref_known(v_t_1510_, 2);
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
lean_dec_ref_known(v_t_1510_, 3);
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
lean_dec_ref_known(v_t_1510_, 3);
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
lean_dec_ref_known(v_t_1510_, 4);
v___x_1535_ = lean_box(v_nondep_1534_);
v___x_1536_ = lean_apply_5(v_k_1511_, v_declName_1530_, v_type_1531_, v_value_1532_, v_body_1533_, v___x_1535_);
return v___x_1536_;
}
case 9:
{
lean_object* v_a_1537_; lean_object* v___x_1538_; 
v_a_1537_ = lean_ctor_get(v_t_1510_, 0);
lean_inc_ref(v_a_1537_);
lean_dec_ref_known(v_t_1510_, 1);
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
lean_dec_ref_known(v_t_1510_, 2);
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
lean_dec_ref_known(v_t_1510_, 3);
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
lean_dec_ref_known(v_t_1660_, 1);
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
lean_dec_ref_known(v_t_1660_, 1);
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
lean_dec_ref_known(v_t_1660_, 1);
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
lean_dec_ref_known(v_t_1660_, 1);
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
lean_dec_ref_known(v_t_1660_, 2);
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
lean_dec_ref_known(v_t_1660_, 2);
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
lean_dec_ref_known(v_t_1660_, 3);
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
lean_dec_ref_known(v_t_1660_, 3);
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
lean_dec_ref_known(v_t_1660_, 4);
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
lean_dec_ref_known(v_t_1660_, 1);
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
lean_dec_ref_known(v_t_1660_, 2);
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
lean_dec_ref_known(v_t_1660_, 3);
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
lean_dec_ref_known(v_t_1716_, 1);
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
lean_dec_ref_known(v_t_1716_, 1);
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
lean_dec_ref_known(v_t_1716_, 1);
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
lean_dec_ref_known(v_t_1716_, 1);
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
lean_dec_ref_known(v_t_1716_, 2);
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
lean_dec_ref_known(v_t_1716_, 2);
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
lean_dec_ref_known(v_t_1716_, 3);
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
lean_dec_ref_known(v_t_1716_, 3);
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
lean_dec_ref_known(v_t_1716_, 4);
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
lean_dec_ref_known(v_t_1716_, 1);
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
lean_dec_ref_known(v_t_1716_, 2);
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
lean_dec_ref_known(v_t_1716_, 3);
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
uint8_t v___y_1823_; uint8_t v___y_1824_; lean_object* v___y_1825_; uint32_t v___y_1826_; uint8_t v___y_1827_; uint64_t v___y_1828_; uint8_t v___y_1829_; uint64_t v___x_1832_; uint8_t v___x_1833_; uint32_t v___x_1834_; uint64_t v___x_1835_; lean_object* v___y_1837_; uint8_t v___y_1838_; uint32_t v___y_1839_; uint8_t v___y_1840_; uint64_t v___y_1841_; uint8_t v___y_1842_; lean_object* v___y_1846_; uint32_t v___y_1847_; uint8_t v___y_1848_; uint64_t v___y_1849_; uint8_t v___y_1850_; lean_object* v___y_1854_; uint32_t v___y_1855_; uint64_t v___y_1856_; uint8_t v___y_1857_; uint32_t v___y_1861_; uint64_t v___y_1862_; lean_object* v___y_1863_; uint32_t v___y_1867_; uint8_t v___x_1882_; uint32_t v___x_1883_; uint8_t v___x_1884_; 
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
v___x_1830_ = lean_expr_mk_data(v___y_1828_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1824_, v___y_1823_, v___y_1829_);
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
v___y_1823_ = v___y_1842_;
v___y_1824_ = v___y_1838_;
v___y_1825_ = v___y_1837_;
v___y_1826_ = v___y_1839_;
v___y_1827_ = v___y_1840_;
v___y_1828_ = v___y_1841_;
v___y_1829_ = v___x_1844_;
goto v___jp_1822_;
}
else
{
v___y_1823_ = v___y_1842_;
v___y_1824_ = v___y_1838_;
v___y_1825_ = v___y_1837_;
v___y_1826_ = v___y_1839_;
v___y_1827_ = v___y_1840_;
v___y_1828_ = v___y_1841_;
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
v___y_1838_ = v___y_1850_;
v___y_1839_ = v___y_1847_;
v___y_1840_ = v___y_1848_;
v___y_1841_ = v___y_1849_;
v___y_1842_ = v___x_1852_;
goto v___jp_1836_;
}
else
{
v___y_1837_ = v___y_1846_;
v___y_1838_ = v___y_1850_;
v___y_1839_ = v___y_1847_;
v___y_1840_ = v___y_1848_;
v___y_1841_ = v___y_1849_;
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
v___y_1847_ = v___y_1855_;
v___y_1848_ = v___y_1857_;
v___y_1849_ = v___y_1856_;
v___y_1850_ = v___x_1859_;
goto v___jp_1845_;
}
else
{
v___y_1846_ = v___y_1854_;
v___y_1847_ = v___y_1855_;
v___y_1848_ = v___y_1857_;
v___y_1849_ = v___y_1856_;
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
v___y_1854_ = v___y_1863_;
v___y_1855_ = v___y_1861_;
v___y_1856_ = v___y_1862_;
v___y_1857_ = v___x_1865_;
goto v___jp_1853_;
}
else
{
v___y_1854_ = v___y_1863_;
v___y_1855_ = v___y_1861_;
v___y_1856_ = v___y_1862_;
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
uint8_t v___y_1896_; uint64_t v___y_1897_; uint8_t v___y_1898_; uint8_t v___y_1899_; uint32_t v___y_1900_; lean_object* v___y_1901_; uint8_t v___y_1902_; uint64_t v___x_1905_; uint8_t v___x_1906_; uint32_t v___x_1907_; uint64_t v___x_1908_; uint64_t v___y_1910_; uint8_t v___y_1911_; uint8_t v___y_1912_; uint32_t v___y_1913_; lean_object* v___y_1914_; uint8_t v___y_1915_; uint8_t v___y_1919_; uint64_t v___y_1920_; uint32_t v___y_1921_; lean_object* v___y_1922_; uint8_t v___y_1923_; uint64_t v___y_1927_; uint32_t v___y_1928_; lean_object* v___y_1929_; uint8_t v___y_1930_; uint64_t v___y_1934_; uint32_t v___y_1935_; lean_object* v___y_1936_; uint32_t v___y_1940_; uint8_t v___x_1955_; uint32_t v___x_1956_; uint8_t v___x_1957_; 
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
v___x_1903_ = lean_expr_mk_data(v___y_1897_, v___y_1901_, v___y_1900_, v___y_1896_, v___y_1898_, v___y_1899_, v___y_1902_);
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
v___y_1896_ = v___y_1911_;
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___y_1912_;
v___y_1899_ = v___y_1915_;
v___y_1900_ = v___y_1913_;
v___y_1901_ = v___y_1914_;
v___y_1902_ = v___x_1917_;
goto v___jp_1895_;
}
else
{
v___y_1896_ = v___y_1911_;
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___y_1912_;
v___y_1899_ = v___y_1915_;
v___y_1900_ = v___y_1913_;
v___y_1901_ = v___y_1914_;
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
v___y_1910_ = v___y_1920_;
v___y_1911_ = v___y_1919_;
v___y_1912_ = v___y_1923_;
v___y_1913_ = v___y_1921_;
v___y_1914_ = v___y_1922_;
v___y_1915_ = v___x_1925_;
goto v___jp_1909_;
}
else
{
v___y_1910_ = v___y_1920_;
v___y_1911_ = v___y_1919_;
v___y_1912_ = v___y_1923_;
v___y_1913_ = v___y_1921_;
v___y_1914_ = v___y_1922_;
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
v___y_1927_ = v___y_1934_;
v___y_1928_ = v___y_1935_;
v___y_1929_ = v___y_1936_;
v___y_1930_ = v___x_1938_;
goto v___jp_1926_;
}
else
{
v___y_1927_ = v___y_1934_;
v___y_1928_ = v___y_1935_;
v___y_1929_ = v___y_1936_;
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
lean_object* v___y_1970_; uint64_t v___y_1971_; uint8_t v___y_1972_; uint8_t v___y_1973_; uint32_t v___y_1974_; uint8_t v___y_1975_; uint8_t v___y_1976_; lean_object* v___y_1980_; uint64_t v___y_1981_; uint64_t v___y_1982_; uint8_t v___y_1983_; uint8_t v___y_1984_; uint32_t v___y_1985_; uint8_t v___y_1986_; uint8_t v___y_1987_; uint64_t v___x_1989_; uint8_t v___x_1990_; uint32_t v___x_1991_; uint64_t v___x_1992_; uint64_t v___y_1994_; lean_object* v___y_1995_; uint64_t v___y_1996_; uint8_t v___y_1997_; uint8_t v___y_1998_; uint32_t v___y_1999_; uint8_t v___y_2000_; lean_object* v___y_2004_; uint64_t v___y_2005_; uint64_t v___y_2006_; uint8_t v___y_2007_; uint8_t v___y_2008_; uint32_t v___y_2009_; uint8_t v___y_2010_; lean_object* v___y_2013_; uint64_t v___y_2014_; uint64_t v___y_2015_; uint8_t v___y_2016_; uint32_t v___y_2017_; uint8_t v___y_2018_; lean_object* v___y_2022_; uint64_t v___y_2023_; uint64_t v___y_2024_; uint8_t v___y_2025_; uint32_t v___y_2026_; uint8_t v___y_2027_; uint64_t v___y_2030_; lean_object* v___y_2031_; uint64_t v___y_2032_; uint32_t v___y_2033_; uint8_t v___y_2034_; lean_object* v___y_2038_; uint64_t v___y_2039_; uint64_t v___y_2040_; uint32_t v___y_2041_; uint8_t v___y_2042_; uint64_t v___y_2045_; uint64_t v___y_2046_; uint32_t v___y_2047_; lean_object* v___y_2048_; uint64_t v___y_2052_; uint64_t v___y_2053_; uint32_t v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; uint64_t v___y_2062_; uint32_t v___y_2063_; uint32_t v___y_2080_; uint8_t v___x_2085_; uint32_t v___x_2086_; uint8_t v___x_2087_; 
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
v___x_1977_ = lean_expr_mk_data(v___y_1971_, v___y_1970_, v___y_1974_, v___y_1972_, v___y_1973_, v___y_1975_, v___y_1976_);
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
v___x_1988_ = l_Lean_Expr_Data_hasLevelParam(v___y_1981_);
v___y_1970_ = v___y_1980_;
v___y_1971_ = v___y_1982_;
v___y_1972_ = v___y_1983_;
v___y_1973_ = v___y_1984_;
v___y_1974_ = v___y_1985_;
v___y_1975_ = v___y_1986_;
v___y_1976_ = v___x_1988_;
goto v___jp_1969_;
}
else
{
v___y_1970_ = v___y_1980_;
v___y_1971_ = v___y_1982_;
v___y_1972_ = v___y_1983_;
v___y_1973_ = v___y_1984_;
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
v___y_1980_ = v___y_1995_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1997_;
v___y_1984_ = v___y_1998_;
v___y_1985_ = v___y_1999_;
v___y_1986_ = v___y_2000_;
v___y_1987_ = v___x_2002_;
goto v___jp_1979_;
}
else
{
v___y_1980_ = v___y_1995_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1997_;
v___y_1984_ = v___y_1998_;
v___y_1985_ = v___y_1999_;
v___y_1986_ = v___y_2000_;
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
v___y_1994_ = v___y_2005_;
v___y_1995_ = v___y_2004_;
v___y_1996_ = v___y_2006_;
v___y_1997_ = v___y_2007_;
v___y_1998_ = v___y_2008_;
v___y_1999_ = v___y_2009_;
v___y_2000_ = v___x_2011_;
goto v___jp_1993_;
}
else
{
v___y_1994_ = v___y_2005_;
v___y_1995_ = v___y_2004_;
v___y_1996_ = v___y_2006_;
v___y_1997_ = v___y_2007_;
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
v___y_2006_ = v___y_2015_;
v___y_2007_ = v___y_2016_;
v___y_2008_ = v___y_2018_;
v___y_2009_ = v___y_2017_;
v___y_2010_ = v___x_2020_;
goto v___jp_2003_;
}
else
{
v___y_2004_ = v___y_2013_;
v___y_2005_ = v___y_2014_;
v___y_2006_ = v___y_2015_;
v___y_2007_ = v___y_2016_;
v___y_2008_ = v___y_2018_;
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
v___y_2022_ = v___y_2031_;
v___y_2023_ = v___y_2030_;
v___y_2024_ = v___y_2032_;
v___y_2025_ = v___y_2034_;
v___y_2026_ = v___y_2033_;
v___y_2027_ = v___x_2036_;
goto v___jp_2021_;
}
else
{
v___y_2022_ = v___y_2031_;
v___y_2023_ = v___y_2030_;
v___y_2024_ = v___y_2032_;
v___y_2025_ = v___y_2034_;
v___y_2026_ = v___y_2033_;
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
v___y_2030_ = v___y_2039_;
v___y_2031_ = v___y_2038_;
v___y_2032_ = v___y_2040_;
v___y_2033_ = v___y_2041_;
v___y_2034_ = v___x_2043_;
goto v___jp_2029_;
}
else
{
v___y_2030_ = v___y_2039_;
v___y_2031_ = v___y_2038_;
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
v___y_2038_ = v___y_2048_;
v___y_2039_ = v___y_2045_;
v___y_2040_ = v___y_2046_;
v___y_2041_ = v___y_2047_;
v___y_2042_ = v___x_2050_;
goto v___jp_2037_;
}
else
{
v___y_2038_ = v___y_2048_;
v___y_2039_ = v___y_2045_;
v___y_2040_ = v___y_2046_;
v___y_2041_ = v___y_2047_;
v___y_2042_ = v___x_2049_;
goto v___jp_2037_;
}
}
v___jp_2051_:
{
uint32_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2057_ = l_Lean_Expr_Data_looseBVarRange(v___y_2052_);
v___x_2058_ = lean_uint32_to_nat(v___x_2057_);
v___x_2059_ = lean_nat_sub(v___x_2058_, v___y_2055_);
lean_dec(v___x_2058_);
v___x_2060_ = lean_nat_dec_le(v___y_2056_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_dec(v___x_2059_);
v___y_2045_ = v___y_2052_;
v___y_2046_ = v___y_2053_;
v___y_2047_ = v___y_2054_;
v___y_2048_ = v___y_2056_;
goto v___jp_2044_;
}
else
{
lean_dec(v___y_2056_);
v___y_2045_ = v___y_2052_;
v___y_2046_ = v___y_2053_;
v___y_2047_ = v___y_2054_;
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
v___y_2052_ = v___y_2062_;
v___y_2053_ = v___x_2073_;
v___y_2054_ = v___x_2066_;
v___y_2055_ = v___x_2064_;
v___y_2056_ = v___x_2075_;
goto v___jp_2051_;
}
else
{
lean_dec(v___x_2075_);
v___y_2052_ = v___y_2062_;
v___y_2053_ = v___x_2073_;
v___y_2054_ = v___x_2066_;
v___y_2055_ = v___x_2064_;
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
lean_dec_ref_known(v_x_2231_, 2);
v___x_2236_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2235_);
return v___x_2236_;
}
else
{
lean_object* v_head_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_inc(v_tail_2234_);
v_head_2237_ = lean_ctor_get(v_x_2231_, 0);
lean_inc(v_head_2237_);
lean_dec_ref_known(v_x_2231_, 2);
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
lean_dec_ref_known(v_x_2343_, 1);
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
lean_dec_ref_known(v_x_2343_, 1);
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
lean_dec_ref_known(v_x_2343_, 1);
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
lean_dec_ref_known(v_x_2343_, 1);
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
lean_dec_ref_known(v_x_2343_, 2);
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
lean_dec_ref_known(v_x_2343_, 2);
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
lean_dec_ref_known(v_x_2343_, 3);
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
lean_dec_ref_known(v_x_2343_, 3);
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
lean_dec_ref_known(v_x_2343_, 4);
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
lean_dec_ref_known(v_x_2343_, 1);
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
lean_dec_ref_known(v_x_2343_, 2);
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
lean_dec_ref_known(v_x_2343_, 3);
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
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* v_e_2713_){
_start:
{
uint8_t v___x_2714_; 
v___x_2714_ = l_Lean_Expr_hasLevelParam(v_e_2713_);
lean_dec_ref(v_e_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* v_e_2715_){
_start:
{
uint8_t v_res_2716_; lean_object* v_r_2717_; 
v_res_2716_ = lean_expr_has_level_param(v_e_2715_);
v_r_2717_ = lean_box(v_res_2716_);
return v_r_2717_;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* v_e_2718_){
_start:
{
uint64_t v___x_2719_; uint32_t v___x_2720_; 
v___x_2719_ = lean_expr_data(v_e_2718_);
lean_dec_ref(v_e_2718_);
v___x_2720_ = l_Lean_Expr_Data_looseBVarRange(v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* v_e_2721_){
_start:
{
uint32_t v_res_2722_; lean_object* v_r_2723_; 
v_res_2722_ = lean_expr_loose_bvar_range(v_e_2721_);
v_r_2723_ = lean_box_uint32(v_res_2722_);
return v_r_2723_;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* v_e_2724_){
_start:
{
uint8_t v___x_2725_; 
v___x_2725_ = l_Lean_Expr_binderInfo(v_e_2724_);
lean_dec_ref(v_e_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* v_e_2726_){
_start:
{
uint8_t v_res_2727_; lean_object* v_r_2728_; 
v_res_2727_ = lean_expr_binder_info(v_e_2726_);
v_r_2728_ = lean_box(v_res_2727_);
return v_r_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* v_declName_2729_, lean_object* v_us_2730_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_Expr_const___override(v_declName_2729_, v_us_2730_);
return v___x_2731_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2(void){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2735_ = lean_box(0);
v___x_2736_ = ((lean_object*)(l_Lean_Literal_type___closed__1));
v___x_2737_ = l_Lean_Expr_const___override(v___x_2736_, v___x_2735_);
return v___x_2737_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5(void){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2741_ = lean_box(0);
v___x_2742_ = ((lean_object*)(l_Lean_Literal_type___closed__4));
v___x_2743_ = l_Lean_Expr_const___override(v___x_2742_, v___x_2741_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* v_x_2744_){
_start:
{
if (lean_obj_tag(v_x_2744_) == 0)
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_2745_;
}
else
{
lean_object* v___x_2746_; 
v___x_2746_ = lean_obj_once(&l_Lean_Literal_type___closed__5, &l_Lean_Literal_type___closed__5_once, _init_l_Lean_Literal_type___closed__5);
return v___x_2746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* v_x_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_Literal_type(v_x_2747_);
lean_dec_ref(v_x_2747_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* v_a_2749_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_Literal_type(v_a_2749_);
lean_dec_ref(v_a_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* v_idx_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Lean_Expr_bvar___override(v_idx_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* v_u_2753_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_Expr_sort___override(v_u_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* v_fvarId_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Lean_Expr_fvar___override(v_fvarId_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* v_mvarId_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_Expr_mvar___override(v_mvarId_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* v_m_2759_, lean_object* v_e_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_Expr_mdata___override(v_m_2759_, v_e_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* v_structName_2762_, lean_object* v_idx_2763_, lean_object* v_struct_2764_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_Expr_proj___override(v_structName_2762_, v_idx_2763_, v_struct_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* v_f_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Lean_Expr_app___override(v_f_2766_, v_a_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* v_x_2769_, uint8_t v_bi_2770_, lean_object* v_t_2771_, lean_object* v_b_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_Expr_lam___override(v_x_2769_, v_t_2771_, v_b_2772_, v_bi_2770_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* v_x_2774_, lean_object* v_bi_2775_, lean_object* v_t_2776_, lean_object* v_b_2777_){
_start:
{
uint8_t v_bi_boxed_2778_; lean_object* v_res_2779_; 
v_bi_boxed_2778_ = lean_unbox(v_bi_2775_);
v_res_2779_ = l_Lean_mkLambda(v_x_2774_, v_bi_boxed_2778_, v_t_2776_, v_b_2777_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* v_x_2780_, uint8_t v_bi_2781_, lean_object* v_t_2782_, lean_object* v_b_2783_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Lean_Expr_forallE___override(v_x_2780_, v_t_2782_, v_b_2783_, v_bi_2781_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* v_x_2785_, lean_object* v_bi_2786_, lean_object* v_t_2787_, lean_object* v_b_2788_){
_start:
{
uint8_t v_bi_boxed_2789_; lean_object* v_res_2790_; 
v_bi_boxed_2789_ = lean_unbox(v_bi_2786_);
v_res_2790_ = l_Lean_mkForall(v_x_2785_, v_bi_boxed_2789_, v_t_2787_, v_b_2788_);
return v_res_2790_;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__4(void){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2797_ = lean_box(0);
v___x_2798_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__3));
v___x_2799_ = l_Lean_Expr_const___override(v___x_2798_, v___x_2797_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* v_type_2800_){
_start:
{
lean_object* v___x_2801_; uint8_t v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2801_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2802_ = 0;
v___x_2803_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2804_ = l_Lean_Expr_forallE___override(v___x_2801_, v___x_2803_, v_type_2800_, v___x_2802_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* v_type_2805_){
_start:
{
lean_object* v___x_2806_; uint8_t v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2806_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2807_ = 0;
v___x_2808_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2809_ = l_Lean_Expr_lam___override(v___x_2806_, v___x_2808_, v_type_2805_, v___x_2807_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* v_x_2810_, lean_object* v_t_2811_, lean_object* v_v_2812_, lean_object* v_b_2813_, uint8_t v_nondep_2814_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_Expr_letE___override(v_x_2810_, v_t_2811_, v_v_2812_, v_b_2813_, v_nondep_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* v_x_2816_, lean_object* v_t_2817_, lean_object* v_v_2818_, lean_object* v_b_2819_, lean_object* v_nondep_2820_){
_start:
{
uint8_t v_nondep_boxed_2821_; lean_object* v_res_2822_; 
v_nondep_boxed_2821_ = lean_unbox(v_nondep_2820_);
v_res_2822_ = l_Lean_mkLet(v_x_2816_, v_t_2817_, v_v_2818_, v_b_2819_, v_nondep_boxed_2821_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object* v_x_2823_, lean_object* v_t_2824_, lean_object* v_v_2825_, lean_object* v_b_2826_){
_start:
{
uint8_t v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = 1;
v___x_2828_ = l_Lean_Expr_letE___override(v_x_2823_, v_t_2824_, v_v_2825_, v_b_2826_, v___x_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* v_f_2829_, lean_object* v_a_2830_, lean_object* v_b_2831_){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = l_Lean_Expr_app___override(v_f_2829_, v_a_2830_);
v___x_2833_ = l_Lean_Expr_app___override(v___x_2832_, v_b_2831_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* v_f_2834_, lean_object* v_a_2835_, lean_object* v_b_2836_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l_Lean_mkAppB(v_f_2834_, v_a_2835_, v_b_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* v_f_2838_, lean_object* v_a_2839_, lean_object* v_b_2840_, lean_object* v_c_2841_){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = l_Lean_mkAppB(v_f_2838_, v_a_2839_, v_b_2840_);
v___x_2843_ = l_Lean_Expr_app___override(v___x_2842_, v_c_2841_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* v_f_2844_, lean_object* v_a_2845_, lean_object* v_b_2846_, lean_object* v_c_2847_, lean_object* v_d_2848_){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = l_Lean_mkAppB(v_f_2844_, v_a_2845_, v_b_2846_);
v___x_2850_ = l_Lean_mkAppB(v___x_2849_, v_c_2847_, v_d_2848_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* v_f_2851_, lean_object* v_a_2852_, lean_object* v_b_2853_, lean_object* v_c_2854_, lean_object* v_d_2855_, lean_object* v_e_2856_){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = l_Lean_mkApp4(v_f_2851_, v_a_2852_, v_b_2853_, v_c_2854_, v_d_2855_);
v___x_2858_ = l_Lean_Expr_app___override(v___x_2857_, v_e_2856_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* v_f_2859_, lean_object* v_a_2860_, lean_object* v_b_2861_, lean_object* v_c_2862_, lean_object* v_d_2863_, lean_object* v_e_u2081_2864_, lean_object* v_e_u2082_2865_){
_start:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = l_Lean_mkApp4(v_f_2859_, v_a_2860_, v_b_2861_, v_c_2862_, v_d_2863_);
v___x_2867_ = l_Lean_mkAppB(v___x_2866_, v_e_u2081_2864_, v_e_u2082_2865_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* v_f_2868_, lean_object* v_a_2869_, lean_object* v_b_2870_, lean_object* v_c_2871_, lean_object* v_d_2872_, lean_object* v_e_u2081_2873_, lean_object* v_e_u2082_2874_, lean_object* v_e_u2083_2875_){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2876_ = l_Lean_mkApp4(v_f_2868_, v_a_2869_, v_b_2870_, v_c_2871_, v_d_2872_);
v___x_2877_ = l_Lean_mkApp3(v___x_2876_, v_e_u2081_2873_, v_e_u2082_2874_, v_e_u2083_2875_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* v_f_2878_, lean_object* v_a_2879_, lean_object* v_b_2880_, lean_object* v_c_2881_, lean_object* v_d_2882_, lean_object* v_e_u2081_2883_, lean_object* v_e_u2082_2884_, lean_object* v_e_u2083_2885_, lean_object* v_e_u2084_2886_){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2887_ = l_Lean_mkApp4(v_f_2878_, v_a_2879_, v_b_2880_, v_c_2881_, v_d_2882_);
v___x_2888_ = l_Lean_mkApp4(v___x_2887_, v_e_u2081_2883_, v_e_u2082_2884_, v_e_u2083_2885_, v_e_u2084_2886_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* v_f_2889_, lean_object* v_a_2890_, lean_object* v_b_2891_, lean_object* v_c_2892_, lean_object* v_d_2893_, lean_object* v_e_u2081_2894_, lean_object* v_e_u2082_2895_, lean_object* v_e_u2083_2896_, lean_object* v_e_u2084_2897_, lean_object* v_e_u2085_2898_){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = l_Lean_mkApp4(v_f_2889_, v_a_2890_, v_b_2891_, v_c_2892_, v_d_2893_);
v___x_2900_ = l_Lean_mkApp5(v___x_2899_, v_e_u2081_2894_, v_e_u2082_2895_, v_e_u2083_2896_, v_e_u2084_2897_, v_e_u2085_2898_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* v_f_2901_, lean_object* v_a_2902_, lean_object* v_b_2903_, lean_object* v_c_2904_, lean_object* v_d_2905_, lean_object* v_e_u2081_2906_, lean_object* v_e_u2082_2907_, lean_object* v_e_u2083_2908_, lean_object* v_e_u2084_2909_, lean_object* v_e_u2085_2910_, lean_object* v_e_u2086_2911_){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = l_Lean_mkApp4(v_f_2901_, v_a_2902_, v_b_2903_, v_c_2904_, v_d_2905_);
v___x_2913_ = l_Lean_mkApp6(v___x_2912_, v_e_u2081_2906_, v_e_u2082_2907_, v_e_u2083_2908_, v_e_u2084_2909_, v_e_u2085_2910_, v_e_u2086_2911_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* v_l_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_Expr_lit___override(v_l_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* v_n_2916_){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2917_, 0, v_n_2916_);
v___x_2918_ = l_Lean_Expr_lit___override(v___x_2917_);
return v___x_2918_;
}
}
static lean_object* _init_l_Lean_mkInstOfNatNat___closed__2(void){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2922_ = lean_box(0);
v___x_2923_ = ((lean_object*)(l_Lean_mkInstOfNatNat___closed__1));
v___x_2924_ = l_Lean_Expr_const___override(v___x_2923_, v___x_2922_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object* v_n_2925_){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = lean_obj_once(&l_Lean_mkInstOfNatNat___closed__2, &l_Lean_mkInstOfNatNat___closed__2_once, _init_l_Lean_mkInstOfNatNat___closed__2);
v___x_2927_ = l_Lean_Expr_app___override(v___x_2926_, v_n_2925_);
return v___x_2927_;
}
}
static lean_object* _init_l_Lean_mkNatLitCore___closed__4(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_2937_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_2938_ = l_Lean_Expr_const___override(v___x_2937_, v___x_2936_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object* v_n_2939_){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2940_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_2941_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
lean_inc_ref(v_n_2939_);
v___x_2942_ = l_Lean_mkInstOfNatNat(v_n_2939_);
v___x_2943_ = l_Lean_mkApp3(v___x_2940_, v___x_2941_, v_n_2939_, v___x_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* v_n_2944_){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = l_Lean_mkRawNatLit(v_n_2944_);
v___x_2946_ = l_Lean_mkNatLitCore(v___x_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* v_s_2947_){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_s_2947_);
v___x_2949_ = l_Lean_Expr_lit___override(v___x_2948_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* v_idx_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Lean_Expr_bvar___override(v_idx_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* v_fvarId_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_Expr_fvar___override(v_fvarId_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object* v_mvarId_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Expr_mvar___override(v_mvarId_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_Expr_sort___override(v_u_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_2958_, lean_object* v_lvls_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_Expr_const___override(v_c_2958_, v_lvls_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_2961_, lean_object* v_a_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_Expr_app___override(v_f_2961_, v_a_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* v_n_2964_, lean_object* v_d_2965_, lean_object* v_b_2966_, uint8_t v_bi_2967_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_Expr_lam___override(v_n_2964_, v_d_2965_, v_b_2966_, v_bi_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_2969_, lean_object* v_d_2970_, lean_object* v_b_2971_, lean_object* v_bi_2972_){
_start:
{
uint8_t v_bi_boxed_2973_; lean_object* v_res_2974_; 
v_bi_boxed_2973_ = lean_unbox(v_bi_2972_);
v_res_2974_ = lean_expr_mk_lambda(v_n_2969_, v_d_2970_, v_b_2971_, v_bi_boxed_2973_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* v_n_2975_, lean_object* v_d_2976_, lean_object* v_b_2977_, uint8_t v_bi_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_Expr_forallE___override(v_n_2975_, v_d_2976_, v_b_2977_, v_bi_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_2980_, lean_object* v_d_2981_, lean_object* v_b_2982_, lean_object* v_bi_2983_){
_start:
{
uint8_t v_bi_boxed_2984_; lean_object* v_res_2985_; 
v_bi_boxed_2984_ = lean_unbox(v_bi_2983_);
v_res_2985_ = lean_expr_mk_forall(v_n_2980_, v_d_2981_, v_b_2982_, v_bi_boxed_2984_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* v_n_2986_, lean_object* v_t_2987_, lean_object* v_v_2988_, lean_object* v_b_2989_, uint8_t v_nondep_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Lean_Expr_letE___override(v_n_2986_, v_t_2987_, v_v_2988_, v_b_2989_, v_nondep_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_2992_, lean_object* v_t_2993_, lean_object* v_v_2994_, lean_object* v_b_2995_, lean_object* v_nondep_2996_){
_start:
{
uint8_t v_nondep_boxed_2997_; lean_object* v_res_2998_; 
v_nondep_boxed_2997_ = lean_unbox(v_nondep_2996_);
v_res_2998_ = lean_expr_mk_let(v_n_2992_, v_t_2993_, v_v_2994_, v_b_2995_, v_nondep_boxed_2997_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_2999_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lean_Expr_lit___override(v_l_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_3001_, lean_object* v_e_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_Expr_mdata___override(v_m_3001_, v_e_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_3004_, lean_object* v_idx_3005_, lean_object* v_struct_3006_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Lean_Expr_proj___override(v_structName_3004_, v_idx_3005_, v_struct_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_3008_, size_t v_i_3009_, size_t v_stop_3010_, lean_object* v_b_3011_){
_start:
{
uint8_t v___x_3012_; 
v___x_3012_ = lean_usize_dec_eq(v_i_3009_, v_stop_3010_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; lean_object* v___x_3014_; size_t v___x_3015_; size_t v___x_3016_; 
v___x_3013_ = lean_array_uget_borrowed(v_as_3008_, v_i_3009_);
lean_inc(v___x_3013_);
v___x_3014_ = l_Lean_Expr_app___override(v_b_3011_, v___x_3013_);
v___x_3015_ = ((size_t)1ULL);
v___x_3016_ = lean_usize_add(v_i_3009_, v___x_3015_);
v_i_3009_ = v___x_3016_;
v_b_3011_ = v___x_3014_;
goto _start;
}
else
{
return v_b_3011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_3018_, lean_object* v_i_3019_, lean_object* v_stop_3020_, lean_object* v_b_3021_){
_start:
{
size_t v_i_boxed_3022_; size_t v_stop_boxed_3023_; lean_object* v_res_3024_; 
v_i_boxed_3022_ = lean_unbox_usize(v_i_3019_);
lean_dec(v_i_3019_);
v_stop_boxed_3023_ = lean_unbox_usize(v_stop_3020_);
lean_dec(v_stop_3020_);
v_res_3024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_3018_, v_i_boxed_3022_, v_stop_boxed_3023_, v_b_3021_);
lean_dec_ref(v_as_3018_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_3025_, lean_object* v_args_3026_){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; 
v___x_3027_ = lean_unsigned_to_nat(0u);
v___x_3028_ = lean_array_get_size(v_args_3026_);
v___x_3029_ = lean_nat_dec_lt(v___x_3027_, v___x_3028_);
if (v___x_3029_ == 0)
{
return v_f_3025_;
}
else
{
uint8_t v___x_3030_; 
v___x_3030_ = lean_nat_dec_le(v___x_3028_, v___x_3028_);
if (v___x_3030_ == 0)
{
if (v___x_3029_ == 0)
{
return v_f_3025_;
}
else
{
size_t v___x_3031_; size_t v___x_3032_; lean_object* v___x_3033_; 
v___x_3031_ = ((size_t)0ULL);
v___x_3032_ = lean_usize_of_nat(v___x_3028_);
v___x_3033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3026_, v___x_3031_, v___x_3032_, v_f_3025_);
return v___x_3033_;
}
}
else
{
size_t v___x_3034_; size_t v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = ((size_t)0ULL);
v___x_3035_ = lean_usize_of_nat(v___x_3028_);
v___x_3036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3026_, v___x_3034_, v___x_3035_, v_f_3025_);
return v___x_3036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_3037_, lean_object* v_args_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_mkAppN(v_f_3037_, v_args_3038_);
lean_dec_ref(v_args_3038_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_3040_, lean_object* v_args_3041_, lean_object* v_i_3042_, lean_object* v_e_3043_){
_start:
{
uint8_t v___x_3044_; 
v___x_3044_ = lean_nat_dec_lt(v_i_3042_, v_n_3040_);
if (v___x_3044_ == 0)
{
lean_dec(v_i_3042_);
return v_e_3043_;
}
else
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3045_ = lean_unsigned_to_nat(1u);
v___x_3046_ = lean_nat_add(v_i_3042_, v___x_3045_);
v___x_3047_ = l_Lean_instInhabitedExpr;
v___x_3048_ = lean_array_get_borrowed(v___x_3047_, v_args_3041_, v_i_3042_);
lean_dec(v_i_3042_);
lean_inc(v___x_3048_);
v___x_3049_ = l_Lean_Expr_app___override(v_e_3043_, v___x_3048_);
v_i_3042_ = v___x_3046_;
v_e_3043_ = v___x_3049_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_3051_, lean_object* v_args_3052_, lean_object* v_i_3053_, lean_object* v_e_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_3051_, v_args_3052_, v_i_3053_, v_e_3054_);
lean_dec_ref(v_args_3052_);
lean_dec(v_n_3051_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_3056_, lean_object* v_i_3057_, lean_object* v_j_3058_, lean_object* v_args_3059_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_3058_, v_args_3059_, v_i_3057_, v_f_3056_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_3061_, lean_object* v_i_3062_, lean_object* v_j_3063_, lean_object* v_args_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_mkAppRange(v_f_3061_, v_i_3062_, v_j_3063_, v_args_3064_);
lean_dec_ref(v_args_3064_);
lean_dec(v_j_3063_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_3066_, size_t v_i_3067_, size_t v_stop_3068_, lean_object* v_b_3069_){
_start:
{
uint8_t v___x_3070_; 
v___x_3070_ = lean_usize_dec_eq(v_i_3067_, v_stop_3068_);
if (v___x_3070_ == 0)
{
size_t v___x_3071_; size_t v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3071_ = ((size_t)1ULL);
v___x_3072_ = lean_usize_sub(v_i_3067_, v___x_3071_);
v___x_3073_ = lean_array_uget_borrowed(v_as_3066_, v___x_3072_);
lean_inc(v___x_3073_);
v___x_3074_ = l_Lean_Expr_app___override(v_b_3069_, v___x_3073_);
v_i_3067_ = v___x_3072_;
v_b_3069_ = v___x_3074_;
goto _start;
}
else
{
return v_b_3069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_3076_, lean_object* v_i_3077_, lean_object* v_stop_3078_, lean_object* v_b_3079_){
_start:
{
size_t v_i_boxed_3080_; size_t v_stop_boxed_3081_; lean_object* v_res_3082_; 
v_i_boxed_3080_ = lean_unbox_usize(v_i_3077_);
lean_dec(v_i_3077_);
v_stop_boxed_3081_ = lean_unbox_usize(v_stop_3078_);
lean_dec(v_stop_3078_);
v_res_3082_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3076_, v_i_boxed_3080_, v_stop_boxed_3081_, v_b_3079_);
lean_dec_ref(v_as_3076_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_3083_, lean_object* v_revArgs_3084_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; 
v___x_3085_ = lean_array_get_size(v_revArgs_3084_);
v___x_3086_ = lean_unsigned_to_nat(0u);
v___x_3087_ = lean_nat_dec_lt(v___x_3086_, v___x_3085_);
if (v___x_3087_ == 0)
{
return v_fn_3083_;
}
else
{
size_t v___x_3088_; size_t v___x_3089_; lean_object* v___x_3090_; 
v___x_3088_ = lean_usize_of_nat(v___x_3085_);
v___x_3089_ = ((size_t)0ULL);
v___x_3090_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_3084_, v___x_3088_, v___x_3089_, v_fn_3083_);
return v___x_3090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_3091_, lean_object* v_revArgs_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_mkAppRev(v_fn_3091_, v_revArgs_3092_);
lean_dec_ref(v_revArgs_3092_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = lean_expr_dbg_to_string(v_e_3095_);
lean_dec_ref(v_e_3095_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_3099_, lean_object* v_b_3100_){
_start:
{
uint8_t v_res_3101_; lean_object* v_r_3102_; 
v_res_3101_ = lean_expr_quick_lt(v_a_3099_, v_b_3100_);
lean_dec_ref(v_b_3100_);
lean_dec_ref(v_a_3099_);
v_r_3102_ = lean_box(v_res_3101_);
return v_r_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_3105_, lean_object* v_b_3106_){
_start:
{
uint8_t v_res_3107_; lean_object* v_r_3108_; 
v_res_3107_ = lean_expr_lt(v_a_3105_, v_b_3106_);
lean_dec_ref(v_b_3106_);
lean_dec_ref(v_a_3105_);
v_r_3108_ = lean_box(v_res_3107_);
return v_r_3108_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* v_a_3109_, lean_object* v_b_3110_){
_start:
{
uint8_t v___x_3111_; 
v___x_3111_ = lean_expr_quick_lt(v_a_3109_, v_b_3110_);
if (v___x_3111_ == 0)
{
uint8_t v___x_3112_; 
v___x_3112_ = lean_expr_quick_lt(v_b_3110_, v_a_3109_);
if (v___x_3112_ == 0)
{
uint8_t v___x_3113_; 
v___x_3113_ = 1;
return v___x_3113_;
}
else
{
uint8_t v___x_3114_; 
v___x_3114_ = 2;
return v___x_3114_;
}
}
else
{
uint8_t v___x_3115_; 
v___x_3115_ = 0;
return v___x_3115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_3116_, lean_object* v_b_3117_){
_start:
{
uint8_t v_res_3118_; lean_object* v_r_3119_; 
v_res_3118_ = l_Lean_Expr_quickComp(v_a_3116_, v_b_3117_);
lean_dec_ref(v_b_3117_);
lean_dec_ref(v_a_3116_);
v_r_3119_ = lean_box(v_res_3118_);
return v_r_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_3122_, lean_object* v_b_3123_){
_start:
{
uint8_t v_res_3124_; lean_object* v_r_3125_; 
v_res_3124_ = lean_expr_eqv(v_a_3122_, v_b_3123_);
lean_dec_ref(v_b_3123_);
lean_dec_ref(v_a_3122_);
v_r_3125_ = lean_box(v_res_3124_);
return v_r_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3130_, lean_object* v_b_3131_){
_start:
{
uint8_t v_res_3132_; lean_object* v_r_3133_; 
v_res_3132_ = lean_expr_equal(v_a_3130_, v_b_3131_);
lean_dec_ref(v_b_3131_);
lean_dec_ref(v_a_3130_);
v_r_3133_ = lean_box(v_res_3132_);
return v_r_3133_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* v_x_3134_){
_start:
{
if (lean_obj_tag(v_x_3134_) == 3)
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3137_){
_start:
{
uint8_t v_res_3138_; lean_object* v_r_3139_; 
v_res_3138_ = l_Lean_Expr_isSort(v_x_3137_);
lean_dec_ref(v_x_3137_);
v_r_3139_ = lean_box(v_res_3138_);
return v_r_3139_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* v_x_3140_){
_start:
{
if (lean_obj_tag(v_x_3140_) == 3)
{
lean_object* v_u_3141_; 
v_u_3141_ = lean_ctor_get(v_x_3140_, 0);
if (lean_obj_tag(v_u_3141_) == 1)
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3145_){
_start:
{
uint8_t v_res_3146_; lean_object* v_r_3147_; 
v_res_3146_ = l_Lean_Expr_isType(v_x_3145_);
lean_dec_ref(v_x_3145_);
v_r_3147_ = lean_box(v_res_3146_);
return v_r_3147_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* v_x_3148_){
_start:
{
if (lean_obj_tag(v_x_3148_) == 3)
{
lean_object* v_u_3149_; 
v_u_3149_ = lean_ctor_get(v_x_3148_, 0);
if (lean_obj_tag(v_u_3149_) == 1)
{
lean_object* v_a_3150_; 
v_a_3150_ = lean_ctor_get(v_u_3149_, 0);
if (lean_obj_tag(v_a_3150_) == 0)
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
else
{
uint8_t v___x_3154_; 
v___x_3154_ = 0;
return v___x_3154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3155_){
_start:
{
uint8_t v_res_3156_; lean_object* v_r_3157_; 
v_res_3156_ = l_Lean_Expr_isType0(v_x_3155_);
lean_dec_ref(v_x_3155_);
v_r_3157_ = lean_box(v_res_3156_);
return v_r_3157_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* v_x_3158_){
_start:
{
if (lean_obj_tag(v_x_3158_) == 3)
{
lean_object* v_u_3159_; 
v_u_3159_ = lean_ctor_get(v_x_3158_, 0);
if (lean_obj_tag(v_u_3159_) == 0)
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
else
{
uint8_t v___x_3162_; 
v___x_3162_ = 0;
return v___x_3162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3163_){
_start:
{
uint8_t v_res_3164_; lean_object* v_r_3165_; 
v_res_3164_ = l_Lean_Expr_isProp(v_x_3163_);
lean_dec_ref(v_x_3163_);
v_r_3165_ = lean_box(v_res_3164_);
return v_r_3165_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3166_){
_start:
{
if (lean_obj_tag(v_x_3166_) == 0)
{
uint8_t v___x_3167_; 
v___x_3167_ = 1;
return v___x_3167_;
}
else
{
uint8_t v___x_3168_; 
v___x_3168_ = 0;
return v___x_3168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3169_){
_start:
{
uint8_t v_res_3170_; lean_object* v_r_3171_; 
v_res_3170_ = l_Lean_Expr_isBVar(v_x_3169_);
lean_dec_ref(v_x_3169_);
v_r_3171_ = lean_box(v_res_3170_);
return v_r_3171_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3172_){
_start:
{
if (lean_obj_tag(v_x_3172_) == 2)
{
uint8_t v___x_3173_; 
v___x_3173_ = 1;
return v___x_3173_;
}
else
{
uint8_t v___x_3174_; 
v___x_3174_ = 0;
return v___x_3174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3175_){
_start:
{
uint8_t v_res_3176_; lean_object* v_r_3177_; 
v_res_3176_ = l_Lean_Expr_isMVar(v_x_3175_);
lean_dec_ref(v_x_3175_);
v_r_3177_ = lean_box(v_res_3176_);
return v_r_3177_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3178_){
_start:
{
if (lean_obj_tag(v_x_3178_) == 1)
{
uint8_t v___x_3179_; 
v___x_3179_ = 1;
return v___x_3179_;
}
else
{
uint8_t v___x_3180_; 
v___x_3180_ = 0;
return v___x_3180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3181_){
_start:
{
uint8_t v_res_3182_; lean_object* v_r_3183_; 
v_res_3182_ = l_Lean_Expr_isFVar(v_x_3181_);
lean_dec_ref(v_x_3181_);
v_r_3183_ = lean_box(v_res_3182_);
return v_r_3183_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* v_x_3184_){
_start:
{
if (lean_obj_tag(v_x_3184_) == 5)
{
uint8_t v___x_3185_; 
v___x_3185_ = 1;
return v___x_3185_;
}
else
{
uint8_t v___x_3186_; 
v___x_3186_ = 0;
return v___x_3186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3187_){
_start:
{
uint8_t v_res_3188_; lean_object* v_r_3189_; 
v_res_3188_ = l_Lean_Expr_isApp(v_x_3187_);
lean_dec_ref(v_x_3187_);
v_r_3189_ = lean_box(v_res_3188_);
return v_r_3189_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* v_x_3190_){
_start:
{
if (lean_obj_tag(v_x_3190_) == 11)
{
uint8_t v___x_3191_; 
v___x_3191_ = 1;
return v___x_3191_;
}
else
{
uint8_t v___x_3192_; 
v___x_3192_ = 0;
return v___x_3192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3193_){
_start:
{
uint8_t v_res_3194_; lean_object* v_r_3195_; 
v_res_3194_ = l_Lean_Expr_isProj(v_x_3193_);
lean_dec_ref(v_x_3193_);
v_r_3195_ = lean_box(v_res_3194_);
return v_r_3195_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* v_x_3196_){
_start:
{
if (lean_obj_tag(v_x_3196_) == 4)
{
uint8_t v___x_3197_; 
v___x_3197_ = 1;
return v___x_3197_;
}
else
{
uint8_t v___x_3198_; 
v___x_3198_ = 0;
return v___x_3198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3199_){
_start:
{
uint8_t v_res_3200_; lean_object* v_r_3201_; 
v_res_3200_ = l_Lean_Expr_isConst(v_x_3199_);
lean_dec_ref(v_x_3199_);
v_r_3201_ = lean_box(v_res_3200_);
return v_r_3201_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3202_, lean_object* v_x_3203_){
_start:
{
if (lean_obj_tag(v_x_3202_) == 4)
{
lean_object* v_declName_3204_; uint8_t v___x_3205_; 
v_declName_3204_ = lean_ctor_get(v_x_3202_, 0);
v___x_3205_ = lean_name_eq(v_declName_3204_, v_x_3203_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3207_, lean_object* v_x_3208_){
_start:
{
uint8_t v_res_3209_; lean_object* v_r_3210_; 
v_res_3209_ = l_Lean_Expr_isConstOf(v_x_3207_, v_x_3208_);
lean_dec(v_x_3208_);
lean_dec_ref(v_x_3207_);
v_r_3210_ = lean_box(v_res_3209_);
return v_r_3210_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3211_, lean_object* v_x_3212_){
_start:
{
if (lean_obj_tag(v_x_3211_) == 1)
{
lean_object* v_fvarId_3213_; uint8_t v___x_3214_; 
v_fvarId_3213_ = lean_ctor_get(v_x_3211_, 0);
v___x_3214_ = lean_name_eq(v_fvarId_3213_, v_x_3212_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3216_, lean_object* v_x_3217_){
_start:
{
uint8_t v_res_3218_; lean_object* v_r_3219_; 
v_res_3218_ = l_Lean_Expr_isFVarOf(v_x_3216_, v_x_3217_);
lean_dec(v_x_3217_);
lean_dec_ref(v_x_3216_);
v_r_3219_ = lean_box(v_res_3218_);
return v_r_3219_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* v_x_3220_){
_start:
{
if (lean_obj_tag(v_x_3220_) == 7)
{
uint8_t v___x_3221_; 
v___x_3221_ = 1;
return v___x_3221_;
}
else
{
uint8_t v___x_3222_; 
v___x_3222_ = 0;
return v___x_3222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3223_){
_start:
{
uint8_t v_res_3224_; lean_object* v_r_3225_; 
v_res_3224_ = l_Lean_Expr_isForall(v_x_3223_);
lean_dec_ref(v_x_3223_);
v_r_3225_ = lean_box(v_res_3224_);
return v_r_3225_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3226_){
_start:
{
if (lean_obj_tag(v_x_3226_) == 6)
{
uint8_t v___x_3227_; 
v___x_3227_ = 1;
return v___x_3227_;
}
else
{
uint8_t v___x_3228_; 
v___x_3228_ = 0;
return v___x_3228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3229_){
_start:
{
uint8_t v_res_3230_; lean_object* v_r_3231_; 
v_res_3230_ = l_Lean_Expr_isLambda(v_x_3229_);
lean_dec_ref(v_x_3229_);
v_r_3231_ = lean_box(v_res_3230_);
return v_r_3231_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3232_){
_start:
{
switch(lean_obj_tag(v_x_3232_))
{
case 6:
{
uint8_t v___x_3233_; 
v___x_3233_ = 1;
return v___x_3233_;
}
case 7:
{
uint8_t v___x_3234_; 
v___x_3234_ = 1;
return v___x_3234_;
}
default: 
{
uint8_t v___x_3235_; 
v___x_3235_ = 0;
return v___x_3235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3236_){
_start:
{
uint8_t v_res_3237_; lean_object* v_r_3238_; 
v_res_3237_ = l_Lean_Expr_isBinding(v_x_3236_);
lean_dec_ref(v_x_3236_);
v_r_3238_ = lean_box(v_res_3237_);
return v_r_3238_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* v_x_3239_){
_start:
{
if (lean_obj_tag(v_x_3239_) == 8)
{
uint8_t v___x_3240_; 
v___x_3240_ = 1;
return v___x_3240_;
}
else
{
uint8_t v___x_3241_; 
v___x_3241_ = 0;
return v___x_3241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3242_){
_start:
{
uint8_t v_res_3243_; lean_object* v_r_3244_; 
v_res_3243_ = l_Lean_Expr_isLet(v_x_3242_);
lean_dec_ref(v_x_3242_);
v_r_3244_ = lean_box(v_res_3243_);
return v_r_3244_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object* v_x_3245_){
_start:
{
if (lean_obj_tag(v_x_3245_) == 8)
{
uint8_t v_nondep_3246_; 
v_nondep_3246_ = lean_ctor_get_uint8(v_x_3245_, sizeof(void*)*4 + 8);
return v_nondep_3246_;
}
else
{
uint8_t v___x_3247_; 
v___x_3247_ = 0;
return v___x_3247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3248_){
_start:
{
uint8_t v_res_3249_; lean_object* v_r_3250_; 
v_res_3249_ = l_Lean_Expr_isHave(v_x_3248_);
lean_dec_ref(v_x_3248_);
v_r_3250_ = lean_box(v_res_3249_);
return v_r_3250_;
}
}
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object* v_a_3251_){
_start:
{
uint8_t v___x_3252_; 
v___x_3252_ = l_Lean_Expr_isHave(v_a_3251_);
lean_dec_ref(v_a_3251_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3253_){
_start:
{
uint8_t v_res_3254_; lean_object* v_r_3255_; 
v_res_3254_ = lean_expr_is_have(v_a_3253_);
v_r_3255_ = lean_box(v_res_3254_);
return v_r_3255_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* v_x_3256_){
_start:
{
if (lean_obj_tag(v_x_3256_) == 10)
{
uint8_t v___x_3257_; 
v___x_3257_ = 1;
return v___x_3257_;
}
else
{
uint8_t v___x_3258_; 
v___x_3258_ = 0;
return v___x_3258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3259_){
_start:
{
uint8_t v_res_3260_; lean_object* v_r_3261_; 
v_res_3260_ = l_Lean_Expr_isMData(v_x_3259_);
lean_dec_ref(v_x_3259_);
v_r_3261_ = lean_box(v_res_3260_);
return v_r_3261_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* v_x_3262_){
_start:
{
if (lean_obj_tag(v_x_3262_) == 9)
{
uint8_t v___x_3263_; 
v___x_3263_ = 1;
return v___x_3263_;
}
else
{
uint8_t v___x_3264_; 
v___x_3264_ = 0;
return v___x_3264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3265_){
_start:
{
uint8_t v_res_3266_; lean_object* v_r_3267_; 
v_res_3266_ = l_Lean_Expr_isLit(v_x_3265_);
lean_dec_ref(v_x_3265_);
v_r_3267_ = lean_box(v_res_3266_);
return v_r_3267_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3268_){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = l_Lean_instInhabitedExpr;
v___x_3270_ = lean_panic_fn_borrowed(v___x_3269_, v_msg_3268_);
return v___x_3270_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3274_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3275_ = lean_unsigned_to_nat(15u);
v___x_3276_ = lean_unsigned_to_nat(932u);
v___x_3277_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3278_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3279_ = l_mkPanicMessageWithDecl(v___x_3278_, v___x_3277_, v___x_3276_, v___x_3275_, v___x_3274_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3280_){
_start:
{
if (lean_obj_tag(v_x_3280_) == 5)
{
lean_object* v_fn_3281_; 
v_fn_3281_ = lean_ctor_get(v_x_3280_, 0);
lean_inc_ref(v_fn_3281_);
return v_fn_3281_;
}
else
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3283_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3282_);
return v___x_3283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_Expr_appFn_x21(v_x_3284_);
lean_dec_ref(v_x_3284_);
return v_res_3285_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3287_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3288_ = lean_unsigned_to_nat(15u);
v___x_3289_ = lean_unsigned_to_nat(936u);
v___x_3290_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3291_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3292_ = l_mkPanicMessageWithDecl(v___x_3291_, v___x_3290_, v___x_3289_, v___x_3288_, v___x_3287_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3293_){
_start:
{
if (lean_obj_tag(v_x_3293_) == 5)
{
lean_object* v_arg_3294_; 
v_arg_3294_ = lean_ctor_get(v_x_3293_, 1);
lean_inc_ref(v_arg_3294_);
return v_arg_3294_;
}
else
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3296_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3295_);
return v___x_3296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_Expr_appArg_x21(v_x_3297_);
lean_dec_ref(v_x_3297_);
return v_res_3298_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3300_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3301_ = lean_unsigned_to_nat(17u);
v___x_3302_ = lean_unsigned_to_nat(941u);
v___x_3303_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3304_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3305_ = l_mkPanicMessageWithDecl(v___x_3304_, v___x_3303_, v___x_3302_, v___x_3301_, v___x_3300_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3306_){
_start:
{
switch(lean_obj_tag(v_x_3306_))
{
case 10:
{
lean_object* v_expr_3307_; 
v_expr_3307_ = lean_ctor_get(v_x_3306_, 1);
v_x_3306_ = v_expr_3307_;
goto _start;
}
case 5:
{
lean_object* v_fn_3309_; 
v_fn_3309_ = lean_ctor_get(v_x_3306_, 0);
lean_inc_ref(v_fn_3309_);
return v_fn_3309_;
}
default: 
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3311_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3310_);
return v___x_3311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_Expr_appFn_x21_x27(v_x_3312_);
lean_dec_ref(v_x_3312_);
return v_res_3313_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3315_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3316_ = lean_unsigned_to_nat(17u);
v___x_3317_ = lean_unsigned_to_nat(946u);
v___x_3318_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3319_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3320_ = l_mkPanicMessageWithDecl(v___x_3319_, v___x_3318_, v___x_3317_, v___x_3316_, v___x_3315_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3321_){
_start:
{
switch(lean_obj_tag(v_x_3321_))
{
case 10:
{
lean_object* v_expr_3322_; 
v_expr_3322_ = lean_ctor_get(v_x_3321_, 1);
v_x_3321_ = v_expr_3322_;
goto _start;
}
case 5:
{
lean_object* v_arg_3324_; 
v_arg_3324_ = lean_ctor_get(v_x_3321_, 1);
lean_inc_ref(v_arg_3324_);
return v_arg_3324_;
}
default: 
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3326_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3325_);
return v___x_3326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Lean_Expr_appArg_x21_x27(v_x_3327_);
lean_dec_ref(v_x_3327_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3329_){
_start:
{
lean_object* v_arg_3330_; 
v_arg_3330_ = lean_ctor_get(v_e_3329_, 1);
lean_inc_ref(v_arg_3330_);
return v_arg_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_Expr_appArg___redArg(v_e_3331_);
lean_dec_ref(v_e_3331_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3333_, lean_object* v_h_3334_){
_start:
{
lean_object* v_arg_3335_; 
v_arg_3335_ = lean_ctor_get(v_e_3333_, 1);
lean_inc_ref(v_arg_3335_);
return v_arg_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3336_, lean_object* v_h_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Lean_Expr_appArg(v_e_3336_, v_h_3337_);
lean_dec_ref(v_e_3336_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3339_){
_start:
{
lean_object* v_fn_3340_; 
v_fn_3340_ = lean_ctor_get(v_e_3339_, 0);
lean_inc_ref(v_fn_3340_);
return v_fn_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Expr_appFn___redArg(v_e_3341_);
lean_dec_ref(v_e_3341_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3343_, lean_object* v_h_3344_){
_start:
{
lean_object* v_fn_3345_; 
v_fn_3345_ = lean_ctor_get(v_e_3343_, 0);
lean_inc_ref(v_fn_3345_);
return v_fn_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3346_, lean_object* v_h_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_Expr_appFn(v_e_3346_, v_h_3347_);
lean_dec_ref(v_e_3346_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3349_){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = lean_box(0);
v___x_3351_ = lean_panic_fn_borrowed(v___x_3350_, v_msg_3349_);
return v___x_3351_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3354_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3355_ = lean_unsigned_to_nat(14u);
v___x_3356_ = lean_unsigned_to_nat(958u);
v___x_3357_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3358_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3359_ = l_mkPanicMessageWithDecl(v___x_3358_, v___x_3357_, v___x_3356_, v___x_3355_, v___x_3354_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3360_){
_start:
{
if (lean_obj_tag(v_x_3360_) == 3)
{
lean_object* v_u_3361_; 
v_u_3361_ = lean_ctor_get(v_x_3360_, 0);
lean_inc(v_u_3361_);
return v_u_3361_;
}
else
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3362_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3363_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3362_);
return v___x_3363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_Lean_Expr_sortLevel_x21(v_x_3364_);
lean_dec_ref(v_x_3364_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3366_){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3368_ = lean_panic_fn_borrowed(v___x_3367_, v_msg_3366_);
return v___x_3368_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3371_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3372_ = lean_unsigned_to_nat(13u);
v___x_3373_ = lean_unsigned_to_nat(962u);
v___x_3374_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3375_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3376_ = l_mkPanicMessageWithDecl(v___x_3375_, v___x_3374_, v___x_3373_, v___x_3372_, v___x_3371_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3377_){
_start:
{
if (lean_obj_tag(v_x_3377_) == 9)
{
lean_object* v_a_3378_; 
v_a_3378_ = lean_ctor_get(v_x_3377_, 0);
lean_inc_ref(v_a_3378_);
return v_a_3378_;
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3380_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3379_);
return v___x_3380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_Expr_litValue_x21(v_x_3381_);
lean_dec_ref(v_x_3381_);
return v_res_3382_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3383_){
_start:
{
if (lean_obj_tag(v_x_3383_) == 9)
{
lean_object* v_a_3384_; 
v_a_3384_ = lean_ctor_get(v_x_3383_, 0);
if (lean_obj_tag(v_a_3384_) == 0)
{
uint8_t v___x_3385_; 
v___x_3385_ = 1;
return v___x_3385_;
}
else
{
uint8_t v___x_3386_; 
v___x_3386_ = 0;
return v___x_3386_;
}
}
else
{
uint8_t v___x_3387_; 
v___x_3387_ = 0;
return v___x_3387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3388_){
_start:
{
uint8_t v_res_3389_; lean_object* v_r_3390_; 
v_res_3389_ = l_Lean_Expr_isRawNatLit(v_x_3388_);
lean_dec_ref(v_x_3388_);
v_r_3390_ = lean_box(v_res_3389_);
return v_r_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3391_){
_start:
{
if (lean_obj_tag(v_x_3391_) == 9)
{
lean_object* v_a_3392_; 
v_a_3392_ = lean_ctor_get(v_x_3391_, 0);
lean_inc_ref(v_a_3392_);
lean_dec_ref_known(v_x_3391_, 1);
if (lean_obj_tag(v_a_3392_) == 0)
{
lean_object* v_val_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
v_val_3393_ = lean_ctor_get(v_a_3392_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v_a_3392_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v_a_3392_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_val_3393_);
lean_dec(v_a_3392_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
lean_ctor_set_tag(v___x_3395_, 1);
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_val_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
else
{
lean_object* v___x_3401_; 
lean_dec_ref(v_a_3392_);
v___x_3401_ = lean_box(0);
return v___x_3401_;
}
}
else
{
lean_object* v___x_3402_; 
lean_dec_ref(v_x_3391_);
v___x_3402_ = lean_box(0);
return v___x_3402_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3403_){
_start:
{
if (lean_obj_tag(v_x_3403_) == 9)
{
lean_object* v_a_3404_; 
v_a_3404_ = lean_ctor_get(v_x_3403_, 0);
if (lean_obj_tag(v_a_3404_) == 1)
{
uint8_t v___x_3405_; 
v___x_3405_ = 1;
return v___x_3405_;
}
else
{
uint8_t v___x_3406_; 
v___x_3406_ = 0;
return v___x_3406_;
}
}
else
{
uint8_t v___x_3407_; 
v___x_3407_ = 0;
return v___x_3407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3408_){
_start:
{
uint8_t v_res_3409_; lean_object* v_r_3410_; 
v_res_3409_ = l_Lean_Expr_isStringLit(v_x_3408_);
lean_dec_ref(v_x_3408_);
v_r_3410_ = lean_box(v_res_3409_);
return v_r_3410_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3415_){
_start:
{
if (lean_obj_tag(v_x_3415_) == 5)
{
lean_object* v_fn_3416_; 
v_fn_3416_ = lean_ctor_get(v_x_3415_, 0);
if (lean_obj_tag(v_fn_3416_) == 4)
{
lean_object* v_arg_3417_; lean_object* v_declName_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
v_arg_3417_ = lean_ctor_get(v_x_3415_, 1);
v_declName_3418_ = lean_ctor_get(v_fn_3416_, 0);
v___x_3419_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3420_ = lean_name_eq(v_declName_3418_, v___x_3419_);
if (v___x_3420_ == 0)
{
return v___x_3420_;
}
else
{
uint8_t v___x_3421_; 
v___x_3421_ = l_Lean_Expr_isRawNatLit(v_arg_3417_);
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
else
{
uint8_t v___x_3423_; 
v___x_3423_ = 0;
return v___x_3423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3424_){
_start:
{
uint8_t v_res_3425_; lean_object* v_r_3426_; 
v_res_3425_ = l_Lean_Expr_isCharLit(v_x_3424_);
lean_dec_ref(v_x_3424_);
v_r_3426_ = lean_box(v_res_3425_);
return v_r_3426_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3427_){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = lean_box(0);
v___x_3429_ = lean_panic_fn_borrowed(v___x_3428_, v_msg_3427_);
return v___x_3429_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3432_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3433_ = lean_unsigned_to_nat(17u);
v___x_3434_ = lean_unsigned_to_nat(986u);
v___x_3435_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3436_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3437_ = l_mkPanicMessageWithDecl(v___x_3436_, v___x_3435_, v___x_3434_, v___x_3433_, v___x_3432_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3438_){
_start:
{
if (lean_obj_tag(v_x_3438_) == 4)
{
lean_object* v_declName_3439_; 
v_declName_3439_ = lean_ctor_get(v_x_3438_, 0);
lean_inc(v_declName_3439_);
return v_declName_3439_;
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3441_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3440_);
return v___x_3441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Lean_Expr_constName_x21(v_x_3442_);
lean_dec_ref(v_x_3442_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3444_){
_start:
{
if (lean_obj_tag(v_x_3444_) == 4)
{
lean_object* v_declName_3445_; lean_object* v___x_3446_; 
v_declName_3445_ = lean_ctor_get(v_x_3444_, 0);
lean_inc(v_declName_3445_);
v___x_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3446_, 0, v_declName_3445_);
return v___x_3446_;
}
else
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_box(0);
return v___x_3447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_Expr_constName_x3f(v_x_3448_);
lean_dec_ref(v_x_3448_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3450_){
_start:
{
lean_object* v___x_3451_; 
v___x_3451_ = l_Lean_Expr_constName_x3f(v_e_3450_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_box(0);
return v___x_3452_;
}
else
{
lean_object* v_val_3453_; 
v_val_3453_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_val_3453_);
lean_dec_ref_known(v___x_3451_, 1);
return v_val_3453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_Expr_constName(v_e_3454_);
lean_dec_ref(v_e_3454_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3456_){
_start:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3457_ = lean_box(0);
v___x_3458_ = lean_panic_fn_borrowed(v___x_3457_, v_msg_3456_);
return v___x_3458_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3460_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3461_ = lean_unsigned_to_nat(18u);
v___x_3462_ = lean_unsigned_to_nat(1006u);
v___x_3463_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3464_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3465_ = l_mkPanicMessageWithDecl(v___x_3464_, v___x_3463_, v___x_3462_, v___x_3461_, v___x_3460_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3466_){
_start:
{
if (lean_obj_tag(v_x_3466_) == 4)
{
lean_object* v_us_3467_; 
v_us_3467_ = lean_ctor_get(v_x_3466_, 1);
lean_inc(v_us_3467_);
return v_us_3467_;
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3469_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3468_);
return v___x_3469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_Lean_Expr_constLevels_x21(v_x_3470_);
lean_dec_ref(v_x_3470_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3472_){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3473_ = lean_unsigned_to_nat(0u);
v___x_3474_ = lean_panic_fn_borrowed(v___x_3473_, v_msg_3472_);
return v___x_3474_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3477_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3478_ = lean_unsigned_to_nat(16u);
v___x_3479_ = lean_unsigned_to_nat(1010u);
v___x_3480_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3481_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3482_ = l_mkPanicMessageWithDecl(v___x_3481_, v___x_3480_, v___x_3479_, v___x_3478_, v___x_3477_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3483_){
_start:
{
if (lean_obj_tag(v_x_3483_) == 0)
{
lean_object* v_deBruijnIndex_3484_; 
v_deBruijnIndex_3484_ = lean_ctor_get(v_x_3483_, 0);
lean_inc(v_deBruijnIndex_3484_);
return v_deBruijnIndex_3484_;
}
else
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3485_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3486_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3485_);
return v___x_3486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Lean_Expr_bvarIdx_x21(v_x_3487_);
lean_dec_ref(v_x_3487_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3489_){
_start:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = lean_box(0);
v___x_3491_ = lean_panic_fn_borrowed(v___x_3490_, v_msg_3489_);
return v___x_3491_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3494_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3495_ = lean_unsigned_to_nat(14u);
v___x_3496_ = lean_unsigned_to_nat(1014u);
v___x_3497_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3498_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3499_ = l_mkPanicMessageWithDecl(v___x_3498_, v___x_3497_, v___x_3496_, v___x_3495_, v___x_3494_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3500_){
_start:
{
if (lean_obj_tag(v_x_3500_) == 1)
{
lean_object* v_fvarId_3501_; 
v_fvarId_3501_ = lean_ctor_get(v_x_3500_, 0);
lean_inc(v_fvarId_3501_);
return v_fvarId_3501_;
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3503_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3502_);
return v___x_3503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Lean_Expr_fvarId_x21(v_x_3504_);
lean_dec_ref(v_x_3504_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3506_){
_start:
{
if (lean_obj_tag(v_x_3506_) == 1)
{
lean_object* v_fvarId_3507_; lean_object* v___x_3508_; 
v_fvarId_3507_ = lean_ctor_get(v_x_3506_, 0);
lean_inc(v_fvarId_3507_);
v___x_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3508_, 0, v_fvarId_3507_);
return v___x_3508_;
}
else
{
lean_object* v___x_3509_; 
v___x_3509_ = lean_box(0);
return v___x_3509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_Expr_fvarId_x3f(v_x_3510_);
lean_dec_ref(v_x_3510_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3512_){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = lean_box(0);
v___x_3514_ = lean_panic_fn_borrowed(v___x_3513_, v_msg_3512_);
return v___x_3514_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3517_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3518_ = lean_unsigned_to_nat(14u);
v___x_3519_ = lean_unsigned_to_nat(1022u);
v___x_3520_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3521_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3522_ = l_mkPanicMessageWithDecl(v___x_3521_, v___x_3520_, v___x_3519_, v___x_3518_, v___x_3517_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3523_){
_start:
{
if (lean_obj_tag(v_x_3523_) == 2)
{
lean_object* v_mvarId_3524_; 
v_mvarId_3524_ = lean_ctor_get(v_x_3523_, 0);
lean_inc(v_mvarId_3524_);
return v_mvarId_3524_;
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3526_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3525_);
return v___x_3526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_Lean_Expr_mvarId_x21(v_x_3527_);
lean_dec_ref(v_x_3527_);
return v_res_3528_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3531_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3532_ = lean_unsigned_to_nat(23u);
v___x_3533_ = lean_unsigned_to_nat(1027u);
v___x_3534_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3535_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3536_ = l_mkPanicMessageWithDecl(v___x_3535_, v___x_3534_, v___x_3533_, v___x_3532_, v___x_3531_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3537_){
_start:
{
switch(lean_obj_tag(v_x_3537_))
{
case 7:
{
lean_object* v_binderName_3538_; 
v_binderName_3538_ = lean_ctor_get(v_x_3537_, 0);
lean_inc(v_binderName_3538_);
return v_binderName_3538_;
}
case 6:
{
lean_object* v_binderName_3539_; 
v_binderName_3539_ = lean_ctor_get(v_x_3537_, 0);
lean_inc(v_binderName_3539_);
return v_binderName_3539_;
}
default: 
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3541_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3540_);
return v___x_3541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Lean_Expr_bindingName_x21(v_x_3542_);
lean_dec_ref(v_x_3542_);
return v_res_3543_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3545_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3546_ = lean_unsigned_to_nat(23u);
v___x_3547_ = lean_unsigned_to_nat(1032u);
v___x_3548_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3549_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3550_ = l_mkPanicMessageWithDecl(v___x_3549_, v___x_3548_, v___x_3547_, v___x_3546_, v___x_3545_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3551_){
_start:
{
switch(lean_obj_tag(v_x_3551_))
{
case 7:
{
lean_object* v_binderType_3552_; 
v_binderType_3552_ = lean_ctor_get(v_x_3551_, 1);
lean_inc_ref(v_binderType_3552_);
return v_binderType_3552_;
}
case 6:
{
lean_object* v_binderType_3553_; 
v_binderType_3553_ = lean_ctor_get(v_x_3551_, 1);
lean_inc_ref(v_binderType_3553_);
return v_binderType_3553_;
}
default: 
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3555_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3554_);
return v___x_3555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Lean_Expr_bindingDomain_x21(v_x_3556_);
lean_dec_ref(v_x_3556_);
return v_res_3557_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3559_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3560_ = lean_unsigned_to_nat(23u);
v___x_3561_ = lean_unsigned_to_nat(1037u);
v___x_3562_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3563_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3564_ = l_mkPanicMessageWithDecl(v___x_3563_, v___x_3562_, v___x_3561_, v___x_3560_, v___x_3559_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3565_){
_start:
{
switch(lean_obj_tag(v_x_3565_))
{
case 7:
{
lean_object* v_body_3566_; 
v_body_3566_ = lean_ctor_get(v_x_3565_, 2);
lean_inc_ref(v_body_3566_);
return v_body_3566_;
}
case 6:
{
lean_object* v_body_3567_; 
v_body_3567_ = lean_ctor_get(v_x_3565_, 2);
lean_inc_ref(v_body_3567_);
return v_body_3567_;
}
default: 
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3569_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3568_);
return v___x_3569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Lean_Expr_bindingBody_x21(v_x_3570_);
lean_dec_ref(v_x_3570_);
return v_res_3571_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3572_){
_start:
{
uint8_t v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3573_ = 0;
v___x_3574_ = lean_box(v___x_3573_);
v___x_3575_ = lean_panic_fn_borrowed(v___x_3574_, v_msg_3572_);
lean_dec(v___x_3574_);
v___x_3576_ = lean_unbox(v___x_3575_);
lean_dec(v___x_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3577_){
_start:
{
uint8_t v_res_3578_; lean_object* v_r_3579_; 
v_res_3578_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3577_);
v_r_3579_ = lean_box(v_res_3578_);
return v_r_3579_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3581_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3582_ = lean_unsigned_to_nat(24u);
v___x_3583_ = lean_unsigned_to_nat(1042u);
v___x_3584_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3585_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3586_ = l_mkPanicMessageWithDecl(v___x_3585_, v___x_3584_, v___x_3583_, v___x_3582_, v___x_3581_);
return v___x_3586_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3587_){
_start:
{
switch(lean_obj_tag(v_x_3587_))
{
case 7:
{
uint8_t v_binderInfo_3588_; 
v_binderInfo_3588_ = lean_ctor_get_uint8(v_x_3587_, sizeof(void*)*3 + 8);
return v_binderInfo_3588_;
}
case 6:
{
uint8_t v_binderInfo_3589_; 
v_binderInfo_3589_ = lean_ctor_get_uint8(v_x_3587_, sizeof(void*)*3 + 8);
return v_binderInfo_3589_;
}
default: 
{
lean_object* v___x_3590_; uint8_t v___x_3591_; 
v___x_3590_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3591_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3590_);
return v___x_3591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3592_){
_start:
{
uint8_t v_res_3593_; lean_object* v_r_3594_; 
v_res_3593_ = l_Lean_Expr_bindingInfo_x21(v_x_3592_);
lean_dec_ref(v_x_3592_);
v_r_3594_ = lean_box(v_res_3593_);
return v_r_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3595_){
_start:
{
lean_object* v_binderName_3596_; 
v_binderName_3596_ = lean_ctor_get(v_x_3595_, 0);
lean_inc(v_binderName_3596_);
return v_binderName_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lean_Expr_forallName___redArg(v_x_3597_);
lean_dec_ref(v_x_3597_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3599_, lean_object* v_x_3600_){
_start:
{
lean_object* v_binderName_3601_; 
v_binderName_3601_ = lean_ctor_get(v_x_3599_, 0);
lean_inc(v_binderName_3601_);
return v_binderName_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3602_, lean_object* v_x_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_Expr_forallName(v_x_3602_, v_x_3603_);
lean_dec_ref(v_x_3602_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3605_){
_start:
{
lean_object* v_binderType_3606_; 
v_binderType_3606_ = lean_ctor_get(v_x_3605_, 1);
lean_inc_ref(v_binderType_3606_);
return v_binderType_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Lean_Expr_forallDomain___redArg(v_x_3607_);
lean_dec_ref(v_x_3607_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3609_, lean_object* v_x_3610_){
_start:
{
lean_object* v_binderType_3611_; 
v_binderType_3611_ = lean_ctor_get(v_x_3609_, 1);
lean_inc_ref(v_binderType_3611_);
return v_binderType_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3612_, lean_object* v_x_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Lean_Expr_forallDomain(v_x_3612_, v_x_3613_);
lean_dec_ref(v_x_3612_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3615_){
_start:
{
lean_object* v_body_3616_; 
v_body_3616_ = lean_ctor_get(v_x_3615_, 2);
lean_inc_ref(v_body_3616_);
return v_body_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Lean_Expr_forallBody___redArg(v_x_3617_);
lean_dec_ref(v_x_3617_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3619_, lean_object* v_x_3620_){
_start:
{
lean_object* v_body_3621_; 
v_body_3621_ = lean_ctor_get(v_x_3619_, 2);
lean_inc_ref(v_body_3621_);
return v_body_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3622_, lean_object* v_x_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_Expr_forallBody(v_x_3622_, v_x_3623_);
lean_dec_ref(v_x_3622_);
return v_res_3624_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3625_){
_start:
{
uint8_t v_binderInfo_3626_; 
v_binderInfo_3626_ = lean_ctor_get_uint8(v_x_3625_, sizeof(void*)*3 + 8);
return v_binderInfo_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3627_){
_start:
{
uint8_t v_res_3628_; lean_object* v_r_3629_; 
v_res_3628_ = l_Lean_Expr_forallInfo___redArg(v_x_3627_);
lean_dec_ref(v_x_3627_);
v_r_3629_ = lean_box(v_res_3628_);
return v_r_3629_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3630_, lean_object* v_x_3631_){
_start:
{
uint8_t v_binderInfo_3632_; 
v_binderInfo_3632_ = lean_ctor_get_uint8(v_x_3630_, sizeof(void*)*3 + 8);
return v_binderInfo_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3633_, lean_object* v_x_3634_){
_start:
{
uint8_t v_res_3635_; lean_object* v_r_3636_; 
v_res_3635_ = l_Lean_Expr_forallInfo(v_x_3633_, v_x_3634_);
lean_dec_ref(v_x_3633_);
v_r_3636_ = lean_box(v_res_3635_);
return v_r_3636_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3639_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3640_ = lean_unsigned_to_nat(17u);
v___x_3641_ = lean_unsigned_to_nat(1058u);
v___x_3642_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3643_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3644_ = l_mkPanicMessageWithDecl(v___x_3643_, v___x_3642_, v___x_3641_, v___x_3640_, v___x_3639_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3645_){
_start:
{
if (lean_obj_tag(v_x_3645_) == 8)
{
lean_object* v_declName_3646_; 
v_declName_3646_ = lean_ctor_get(v_x_3645_, 0);
lean_inc(v_declName_3646_);
return v_declName_3646_;
}
else
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3648_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3647_);
return v___x_3648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Lean_Expr_letName_x21(v_x_3649_);
lean_dec_ref(v_x_3649_);
return v_res_3650_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3652_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3653_ = lean_unsigned_to_nat(19u);
v___x_3654_ = lean_unsigned_to_nat(1062u);
v___x_3655_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3656_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3657_ = l_mkPanicMessageWithDecl(v___x_3656_, v___x_3655_, v___x_3654_, v___x_3653_, v___x_3652_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3658_){
_start:
{
if (lean_obj_tag(v_x_3658_) == 8)
{
lean_object* v_type_3659_; 
v_type_3659_ = lean_ctor_get(v_x_3658_, 1);
lean_inc_ref(v_type_3659_);
return v_type_3659_;
}
else
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3661_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3660_);
return v___x_3661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l_Lean_Expr_letType_x21(v_x_3662_);
lean_dec_ref(v_x_3662_);
return v_res_3663_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3665_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3666_ = lean_unsigned_to_nat(21u);
v___x_3667_ = lean_unsigned_to_nat(1066u);
v___x_3668_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3669_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3670_ = l_mkPanicMessageWithDecl(v___x_3669_, v___x_3668_, v___x_3667_, v___x_3666_, v___x_3665_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3671_){
_start:
{
if (lean_obj_tag(v_x_3671_) == 8)
{
lean_object* v_value_3672_; 
v_value_3672_ = lean_ctor_get(v_x_3671_, 2);
lean_inc_ref(v_value_3672_);
return v_value_3672_;
}
else
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3674_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3673_);
return v___x_3674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Lean_Expr_letValue_x21(v_x_3675_);
lean_dec_ref(v_x_3675_);
return v_res_3676_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3678_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3679_ = lean_unsigned_to_nat(23u);
v___x_3680_ = lean_unsigned_to_nat(1070u);
v___x_3681_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3682_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3683_ = l_mkPanicMessageWithDecl(v___x_3682_, v___x_3681_, v___x_3680_, v___x_3679_, v___x_3678_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3684_){
_start:
{
if (lean_obj_tag(v_x_3684_) == 8)
{
lean_object* v_body_3685_; 
v_body_3685_ = lean_ctor_get(v_x_3684_, 3);
lean_inc_ref(v_body_3685_);
return v_body_3685_;
}
else
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3686_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3687_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3686_);
return v___x_3687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Lean_Expr_letBody_x21(v_x_3688_);
lean_dec_ref(v_x_3688_);
return v_res_3689_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3690_){
_start:
{
uint8_t v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; uint8_t v___x_3694_; 
v___x_3691_ = 0;
v___x_3692_ = lean_box(v___x_3691_);
v___x_3693_ = lean_panic_fn_borrowed(v___x_3692_, v_msg_3690_);
lean_dec(v___x_3692_);
v___x_3694_ = lean_unbox(v___x_3693_);
lean_dec(v___x_3693_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3695_){
_start:
{
uint8_t v_res_3696_; lean_object* v_r_3697_; 
v_res_3696_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3695_);
v_r_3697_ = lean_box(v_res_3696_);
return v_r_3697_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3699_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3700_ = lean_unsigned_to_nat(27u);
v___x_3701_ = lean_unsigned_to_nat(1074u);
v___x_3702_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3703_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3704_ = l_mkPanicMessageWithDecl(v___x_3703_, v___x_3702_, v___x_3701_, v___x_3700_, v___x_3699_);
return v___x_3704_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3705_){
_start:
{
if (lean_obj_tag(v_x_3705_) == 8)
{
uint8_t v_nondep_3706_; 
v_nondep_3706_ = lean_ctor_get_uint8(v_x_3705_, sizeof(void*)*4 + 8);
return v_nondep_3706_;
}
else
{
lean_object* v___x_3707_; uint8_t v___x_3708_; 
v___x_3707_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3708_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3707_);
return v___x_3708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3709_){
_start:
{
uint8_t v_res_3710_; lean_object* v_r_3711_; 
v_res_3710_ = l_Lean_Expr_letNondep_x21(v_x_3709_);
lean_dec_ref(v_x_3709_);
v_r_3711_ = lean_box(v_res_3710_);
return v_r_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3712_){
_start:
{
if (lean_obj_tag(v_x_3712_) == 10)
{
lean_object* v_expr_3713_; 
v_expr_3713_ = lean_ctor_get(v_x_3712_, 1);
v_x_3712_ = v_expr_3713_;
goto _start;
}
else
{
lean_inc_ref(v_x_3712_);
return v_x_3712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Lean_Expr_consumeMData(v_x_3715_);
lean_dec_ref(v_x_3715_);
return v_res_3716_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3719_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3720_ = lean_unsigned_to_nat(17u);
v___x_3721_ = lean_unsigned_to_nat(1082u);
v___x_3722_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3723_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3724_ = l_mkPanicMessageWithDecl(v___x_3723_, v___x_3722_, v___x_3721_, v___x_3720_, v___x_3719_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3725_){
_start:
{
if (lean_obj_tag(v_x_3725_) == 10)
{
lean_object* v_expr_3726_; 
v_expr_3726_ = lean_ctor_get(v_x_3725_, 1);
lean_inc_ref(v_expr_3726_);
return v_expr_3726_;
}
else
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3727_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3728_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3727_);
return v___x_3728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lean_Expr_mdataExpr_x21(v_x_3729_);
lean_dec_ref(v_x_3729_);
return v_res_3730_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3733_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3734_ = lean_unsigned_to_nat(18u);
v___x_3735_ = lean_unsigned_to_nat(1086u);
v___x_3736_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3737_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3738_ = l_mkPanicMessageWithDecl(v___x_3737_, v___x_3736_, v___x_3735_, v___x_3734_, v___x_3733_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3739_){
_start:
{
if (lean_obj_tag(v_x_3739_) == 11)
{
lean_object* v_struct_3740_; 
v_struct_3740_ = lean_ctor_get(v_x_3739_, 2);
lean_inc_ref(v_struct_3740_);
return v_struct_3740_;
}
else
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3741_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3742_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3741_);
return v___x_3742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l_Lean_Expr_projExpr_x21(v_x_3743_);
lean_dec_ref(v_x_3743_);
return v_res_3744_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3746_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3747_ = lean_unsigned_to_nat(18u);
v___x_3748_ = lean_unsigned_to_nat(1090u);
v___x_3749_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3750_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3751_ = l_mkPanicMessageWithDecl(v___x_3750_, v___x_3749_, v___x_3748_, v___x_3747_, v___x_3746_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3752_){
_start:
{
if (lean_obj_tag(v_x_3752_) == 11)
{
lean_object* v_idx_3753_; 
v_idx_3753_ = lean_ctor_get(v_x_3752_, 1);
lean_inc(v_idx_3753_);
return v_idx_3753_;
}
else
{
lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3754_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3755_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3754_);
return v___x_3755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l_Lean_Expr_projIdx_x21(v_x_3756_);
lean_dec_ref(v_x_3756_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3758_){
_start:
{
if (lean_obj_tag(v_x_3758_) == 7)
{
lean_object* v_body_3759_; 
v_body_3759_ = lean_ctor_get(v_x_3758_, 2);
v_x_3758_ = v_body_3759_;
goto _start;
}
else
{
lean_inc_ref(v_x_3758_);
return v_x_3758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l_Lean_Expr_getForallBody(v_x_3761_);
lean_dec_ref(v_x_3761_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3763_, lean_object* v_x_3764_){
_start:
{
lean_object* v_zero_3765_; uint8_t v_isZero_3766_; 
v_zero_3765_ = lean_unsigned_to_nat(0u);
v_isZero_3766_ = lean_nat_dec_eq(v_x_3763_, v_zero_3765_);
if (v_isZero_3766_ == 1)
{
lean_dec(v_x_3763_);
lean_inc_ref(v_x_3764_);
return v_x_3764_;
}
else
{
if (lean_obj_tag(v_x_3764_) == 7)
{
lean_object* v_body_3767_; lean_object* v_one_3768_; lean_object* v_n_3769_; 
v_body_3767_ = lean_ctor_get(v_x_3764_, 2);
v_one_3768_ = lean_unsigned_to_nat(1u);
v_n_3769_ = lean_nat_sub(v_x_3763_, v_one_3768_);
lean_dec(v_x_3763_);
v_x_3763_ = v_n_3769_;
v_x_3764_ = v_body_3767_;
goto _start;
}
else
{
lean_dec(v_x_3763_);
lean_inc_ref(v_x_3764_);
return v_x_3764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3771_, lean_object* v_x_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3771_, v_x_3772_);
lean_dec_ref(v_x_3772_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3774_){
_start:
{
if (lean_obj_tag(v_x_3774_) == 7)
{
lean_object* v_binderName_3775_; lean_object* v_body_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v_binderName_3775_ = lean_ctor_get(v_x_3774_, 0);
v_body_3776_ = lean_ctor_get(v_x_3774_, 2);
v___x_3777_ = l_Lean_Expr_getForallBinderNames(v_body_3776_);
lean_inc(v_binderName_3775_);
v___x_3778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3778_, 0, v_binderName_3775_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
return v___x_3778_;
}
else
{
lean_object* v___x_3779_; 
v___x_3779_ = lean_box(0);
return v___x_3779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l_Lean_Expr_getForallBinderNames(v_x_3780_);
lean_dec_ref(v_x_3780_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3782_){
_start:
{
switch(lean_obj_tag(v_x_3782_))
{
case 10:
{
lean_object* v_expr_3783_; 
v_expr_3783_ = lean_ctor_get(v_x_3782_, 1);
v_x_3782_ = v_expr_3783_;
goto _start;
}
case 7:
{
lean_object* v_body_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v_body_3785_ = lean_ctor_get(v_x_3782_, 2);
v___x_3786_ = l_Lean_Expr_getNumHeadForalls(v_body_3785_);
v___x_3787_ = lean_unsigned_to_nat(1u);
v___x_3788_ = lean_nat_add(v___x_3786_, v___x_3787_);
lean_dec(v___x_3786_);
return v___x_3788_;
}
default: 
{
lean_object* v___x_3789_; 
v___x_3789_ = lean_unsigned_to_nat(0u);
return v___x_3789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l_Lean_Expr_getNumHeadForalls(v_x_3790_);
lean_dec_ref(v_x_3790_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3792_){
_start:
{
if (lean_obj_tag(v_x_3792_) == 5)
{
lean_object* v_fn_3793_; 
v_fn_3793_ = lean_ctor_get(v_x_3792_, 0);
v_x_3792_ = v_fn_3793_;
goto _start;
}
else
{
lean_inc_ref(v_x_3792_);
return v_x_3792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Lean_Expr_getAppFn(v_x_3795_);
lean_dec_ref(v_x_3795_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3797_){
_start:
{
switch(lean_obj_tag(v_x_3797_))
{
case 5:
{
lean_object* v_fn_3798_; 
v_fn_3798_ = lean_ctor_get(v_x_3797_, 0);
v_x_3797_ = v_fn_3798_;
goto _start;
}
case 10:
{
lean_object* v_expr_3800_; 
v_expr_3800_ = lean_ctor_get(v_x_3797_, 1);
v_x_3797_ = v_expr_3800_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3797_);
return v_x_3797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Lean_Expr_getAppFn_x27(v_x_3802_);
lean_dec_ref(v_x_3802_);
return v_res_3803_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3804_, lean_object* v_n_3805_){
_start:
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Lean_Expr_getAppFn(v_e_3804_);
if (lean_obj_tag(v___x_3806_) == 4)
{
lean_object* v_declName_3807_; uint8_t v___x_3808_; 
v_declName_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_declName_3807_);
lean_dec_ref_known(v___x_3806_, 2);
v___x_3808_ = lean_name_eq(v_declName_3807_, v_n_3805_);
lean_dec(v_declName_3807_);
return v___x_3808_;
}
else
{
uint8_t v___x_3809_; 
lean_dec_ref(v___x_3806_);
v___x_3809_ = 0;
return v___x_3809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3810_, lean_object* v_n_3811_){
_start:
{
uint8_t v_res_3812_; lean_object* v_r_3813_; 
v_res_3812_ = l_Lean_Expr_isAppOf(v_e_3810_, v_n_3811_);
lean_dec(v_n_3811_);
lean_dec_ref(v_e_3810_);
v_r_3813_ = lean_box(v_res_3812_);
return v_r_3813_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3814_, lean_object* v_x_3815_, lean_object* v_x_3816_){
_start:
{
switch(lean_obj_tag(v_x_3814_))
{
case 4:
{
lean_object* v_declName_3817_; lean_object* v___x_3818_; uint8_t v___x_3819_; 
v_declName_3817_ = lean_ctor_get(v_x_3814_, 0);
v___x_3818_ = lean_unsigned_to_nat(0u);
v___x_3819_ = lean_nat_dec_eq(v_x_3816_, v___x_3818_);
lean_dec(v_x_3816_);
if (v___x_3819_ == 0)
{
return v___x_3819_;
}
else
{
uint8_t v___x_3820_; 
v___x_3820_ = lean_name_eq(v_declName_3817_, v_x_3815_);
return v___x_3820_;
}
}
case 5:
{
lean_object* v_fn_3821_; lean_object* v_zero_3822_; uint8_t v_isZero_3823_; 
v_fn_3821_ = lean_ctor_get(v_x_3814_, 0);
v_zero_3822_ = lean_unsigned_to_nat(0u);
v_isZero_3823_ = lean_nat_dec_eq(v_x_3816_, v_zero_3822_);
if (v_isZero_3823_ == 0)
{
lean_object* v_one_3824_; lean_object* v_n_3825_; 
v_one_3824_ = lean_unsigned_to_nat(1u);
v_n_3825_ = lean_nat_sub(v_x_3816_, v_one_3824_);
lean_dec(v_x_3816_);
v_x_3814_ = v_fn_3821_;
v_x_3816_ = v_n_3825_;
goto _start;
}
else
{
uint8_t v___x_3827_; 
lean_dec(v_x_3816_);
v___x_3827_ = 0;
return v___x_3827_;
}
}
default: 
{
uint8_t v___x_3828_; 
lean_dec(v_x_3816_);
v___x_3828_ = 0;
return v___x_3828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3829_, lean_object* v_x_3830_, lean_object* v_x_3831_){
_start:
{
uint8_t v_res_3832_; lean_object* v_r_3833_; 
v_res_3832_ = l_Lean_Expr_isAppOfArity(v_x_3829_, v_x_3830_, v_x_3831_);
lean_dec(v_x_3830_);
lean_dec_ref(v_x_3829_);
v_r_3833_ = lean_box(v_res_3832_);
return v_r_3833_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3834_, lean_object* v_x_3835_, lean_object* v_x_3836_){
_start:
{
switch(lean_obj_tag(v_x_3834_))
{
case 10:
{
lean_object* v_expr_3837_; 
v_expr_3837_ = lean_ctor_get(v_x_3834_, 1);
v_x_3834_ = v_expr_3837_;
goto _start;
}
case 4:
{
lean_object* v_declName_3839_; lean_object* v___x_3840_; uint8_t v___x_3841_; 
v_declName_3839_ = lean_ctor_get(v_x_3834_, 0);
v___x_3840_ = lean_unsigned_to_nat(0u);
v___x_3841_ = lean_nat_dec_eq(v_x_3836_, v___x_3840_);
lean_dec(v_x_3836_);
if (v___x_3841_ == 0)
{
return v___x_3841_;
}
else
{
uint8_t v___x_3842_; 
v___x_3842_ = lean_name_eq(v_declName_3839_, v_x_3835_);
return v___x_3842_;
}
}
case 5:
{
lean_object* v_fn_3843_; lean_object* v_zero_3844_; uint8_t v_isZero_3845_; 
v_fn_3843_ = lean_ctor_get(v_x_3834_, 0);
v_zero_3844_ = lean_unsigned_to_nat(0u);
v_isZero_3845_ = lean_nat_dec_eq(v_x_3836_, v_zero_3844_);
if (v_isZero_3845_ == 0)
{
lean_object* v_one_3846_; lean_object* v_n_3847_; 
v_one_3846_ = lean_unsigned_to_nat(1u);
v_n_3847_ = lean_nat_sub(v_x_3836_, v_one_3846_);
lean_dec(v_x_3836_);
v_x_3834_ = v_fn_3843_;
v_x_3836_ = v_n_3847_;
goto _start;
}
else
{
uint8_t v___x_3849_; 
lean_dec(v_x_3836_);
v___x_3849_ = 0;
return v___x_3849_;
}
}
default: 
{
uint8_t v___x_3850_; 
lean_dec(v_x_3836_);
v___x_3850_ = 0;
return v___x_3850_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3851_, lean_object* v_x_3852_, lean_object* v_x_3853_){
_start:
{
uint8_t v_res_3854_; lean_object* v_r_3855_; 
v_res_3854_ = l_Lean_Expr_isAppOfArity_x27(v_x_3851_, v_x_3852_, v_x_3853_);
lean_dec(v_x_3852_);
lean_dec_ref(v_x_3851_);
v_r_3855_ = lean_box(v_res_3854_);
return v_r_3855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3856_, lean_object* v_x_3857_){
_start:
{
if (lean_obj_tag(v_x_3856_) == 5)
{
lean_object* v_fn_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v_fn_3858_ = lean_ctor_get(v_x_3856_, 0);
v___x_3859_ = lean_unsigned_to_nat(1u);
v___x_3860_ = lean_nat_add(v_x_3857_, v___x_3859_);
lean_dec(v_x_3857_);
v_x_3856_ = v_fn_3858_;
v_x_3857_ = v___x_3860_;
goto _start;
}
else
{
return v_x_3857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3862_, lean_object* v_x_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3862_, v_x_3863_);
lean_dec_ref(v_x_3862_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3865_){
_start:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3866_ = lean_unsigned_to_nat(0u);
v___x_3867_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3865_, v___x_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_Lean_Expr_getAppNumArgs(v_e_3868_);
lean_dec_ref(v_e_3868_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3870_, lean_object* v_a_3871_){
_start:
{
switch(lean_obj_tag(v_a_3870_))
{
case 10:
{
lean_object* v_expr_3872_; 
v_expr_3872_ = lean_ctor_get(v_a_3870_, 1);
v_a_3870_ = v_expr_3872_;
goto _start;
}
case 5:
{
lean_object* v_fn_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v_fn_3874_ = lean_ctor_get(v_a_3870_, 0);
v___x_3875_ = lean_unsigned_to_nat(1u);
v___x_3876_ = lean_nat_add(v_a_3871_, v___x_3875_);
lean_dec(v_a_3871_);
v_a_3870_ = v_fn_3874_;
v_a_3871_ = v___x_3876_;
goto _start;
}
default: 
{
return v_a_3871_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3878_, lean_object* v_a_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3878_, v_a_3879_);
lean_dec_ref(v_a_3878_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3881_){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = lean_unsigned_to_nat(0u);
v___x_3883_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3881_, v___x_3882_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3884_);
lean_dec_ref(v_e_3884_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3886_, lean_object* v_x_3887_){
_start:
{
lean_object* v_zero_3888_; uint8_t v_isZero_3889_; 
v_zero_3888_ = lean_unsigned_to_nat(0u);
v_isZero_3889_ = lean_nat_dec_eq(v_x_3886_, v_zero_3888_);
if (v_isZero_3889_ == 0)
{
if (lean_obj_tag(v_x_3887_) == 5)
{
lean_object* v_fn_3890_; lean_object* v_one_3891_; lean_object* v_n_3892_; 
v_fn_3890_ = lean_ctor_get(v_x_3887_, 0);
v_one_3891_ = lean_unsigned_to_nat(1u);
v_n_3892_ = lean_nat_sub(v_x_3886_, v_one_3891_);
lean_dec(v_x_3886_);
v_x_3886_ = v_n_3892_;
v_x_3887_ = v_fn_3890_;
goto _start;
}
else
{
lean_dec(v_x_3886_);
lean_inc_ref(v_x_3887_);
return v_x_3887_;
}
}
else
{
lean_dec(v_x_3886_);
lean_inc_ref(v_x_3887_);
return v_x_3887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_3894_, lean_object* v_x_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Lean_Expr_getBoundedAppFn(v_x_3894_, v_x_3895_);
lean_dec_ref(v_x_3895_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_3897_, lean_object* v_x_3898_, lean_object* v_x_3899_){
_start:
{
if (lean_obj_tag(v_x_3897_) == 5)
{
lean_object* v_fn_3900_; lean_object* v_arg_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v_fn_3900_ = lean_ctor_get(v_x_3897_, 0);
lean_inc_ref(v_fn_3900_);
v_arg_3901_ = lean_ctor_get(v_x_3897_, 1);
lean_inc_ref(v_arg_3901_);
lean_dec_ref_known(v_x_3897_, 2);
v___x_3902_ = lean_array_set(v_x_3898_, v_x_3899_, v_arg_3901_);
v___x_3903_ = lean_unsigned_to_nat(1u);
v___x_3904_ = lean_nat_sub(v_x_3899_, v___x_3903_);
lean_dec(v_x_3899_);
v_x_3897_ = v_fn_3900_;
v_x_3898_ = v___x_3902_;
v_x_3899_ = v___x_3904_;
goto _start;
}
else
{
lean_dec(v_x_3899_);
lean_dec_ref(v_x_3897_);
return v_x_3898_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_3906_; lean_object* v_dummy_3907_; 
v___x_3906_ = lean_box(0);
v_dummy_3907_ = l_Lean_Expr_sort___override(v___x_3906_);
return v_dummy_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_3908_){
_start:
{
lean_object* v_dummy_3909_; lean_object* v_nargs_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_dummy_3909_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3910_ = l_Lean_Expr_getAppNumArgs(v_e_3908_);
lean_inc(v_nargs_3910_);
v___x_3911_ = lean_mk_array(v_nargs_3910_, v_dummy_3909_);
v___x_3912_ = lean_unsigned_to_nat(1u);
v___x_3913_ = lean_nat_sub(v_nargs_3910_, v___x_3912_);
lean_dec(v_nargs_3910_);
v___x_3914_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3908_, v___x_3911_, v___x_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_3915_, lean_object* v_x_3916_, lean_object* v_x_3917_){
_start:
{
if (lean_obj_tag(v_x_3915_) == 5)
{
lean_object* v_fn_3918_; lean_object* v_arg_3919_; lean_object* v_zero_3920_; uint8_t v_isZero_3921_; 
v_fn_3918_ = lean_ctor_get(v_x_3915_, 0);
lean_inc_ref(v_fn_3918_);
v_arg_3919_ = lean_ctor_get(v_x_3915_, 1);
lean_inc_ref(v_arg_3919_);
lean_dec_ref_known(v_x_3915_, 2);
v_zero_3920_ = lean_unsigned_to_nat(0u);
v_isZero_3921_ = lean_nat_dec_eq(v_x_3917_, v_zero_3920_);
if (v_isZero_3921_ == 0)
{
lean_object* v_one_3922_; lean_object* v_n_3923_; lean_object* v___x_3924_; 
v_one_3922_ = lean_unsigned_to_nat(1u);
v_n_3923_ = lean_nat_sub(v_x_3917_, v_one_3922_);
lean_dec(v_x_3917_);
v___x_3924_ = lean_array_set(v_x_3916_, v_n_3923_, v_arg_3919_);
v_x_3915_ = v_fn_3918_;
v_x_3916_ = v___x_3924_;
v_x_3917_ = v_n_3923_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3919_);
lean_dec_ref(v_fn_3918_);
lean_dec(v_x_3917_);
return v_x_3916_;
}
}
else
{
lean_dec(v_x_3917_);
lean_dec_ref(v_x_3915_);
return v_x_3916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_3926_, lean_object* v_e_3927_){
_start:
{
lean_object* v_dummy_3928_; lean_object* v___y_3930_; lean_object* v___x_3933_; uint8_t v___x_3934_; 
v_dummy_3928_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_3933_ = l_Lean_Expr_getAppNumArgs(v_e_3927_);
v___x_3934_ = lean_nat_dec_le(v_maxArgs_3926_, v___x_3933_);
if (v___x_3934_ == 0)
{
lean_dec(v_maxArgs_3926_);
v___y_3930_ = v___x_3933_;
goto v___jp_3929_;
}
else
{
lean_dec(v___x_3933_);
v___y_3930_ = v_maxArgs_3926_;
goto v___jp_3929_;
}
v___jp_3929_:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
lean_inc(v___y_3930_);
v___x_3931_ = lean_mk_array(v___y_3930_, v_dummy_3928_);
v___x_3932_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_3927_, v___x_3931_, v___y_3930_);
return v___x_3932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_3935_, lean_object* v_x_3936_){
_start:
{
if (lean_obj_tag(v_x_3935_) == 5)
{
lean_object* v_fn_3937_; lean_object* v_arg_3938_; lean_object* v___x_3939_; 
v_fn_3937_ = lean_ctor_get(v_x_3935_, 0);
lean_inc_ref(v_fn_3937_);
v_arg_3938_ = lean_ctor_get(v_x_3935_, 1);
lean_inc_ref(v_arg_3938_);
lean_dec_ref_known(v_x_3935_, 2);
v___x_3939_ = lean_array_push(v_x_3936_, v_arg_3938_);
v_x_3935_ = v_fn_3937_;
v_x_3936_ = v___x_3939_;
goto _start;
}
else
{
lean_dec_ref(v_x_3935_);
return v_x_3936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_3941_){
_start:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3942_ = l_Lean_Expr_getAppNumArgs(v_e_3941_);
v___x_3943_ = lean_mk_empty_array_with_capacity(v___x_3942_);
lean_dec(v___x_3942_);
v___x_3944_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3941_, v___x_3943_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_3945_, lean_object* v_x_3946_, lean_object* v_x_3947_, lean_object* v_x_3948_){
_start:
{
if (lean_obj_tag(v_x_3946_) == 5)
{
lean_object* v_fn_3949_; lean_object* v_arg_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v_fn_3949_ = lean_ctor_get(v_x_3946_, 0);
lean_inc_ref(v_fn_3949_);
v_arg_3950_ = lean_ctor_get(v_x_3946_, 1);
lean_inc_ref(v_arg_3950_);
lean_dec_ref_known(v_x_3946_, 2);
v___x_3951_ = lean_array_set(v_x_3947_, v_x_3948_, v_arg_3950_);
v___x_3952_ = lean_unsigned_to_nat(1u);
v___x_3953_ = lean_nat_sub(v_x_3948_, v___x_3952_);
lean_dec(v_x_3948_);
v_x_3946_ = v_fn_3949_;
v_x_3947_ = v___x_3951_;
v_x_3948_ = v___x_3953_;
goto _start;
}
else
{
lean_object* v___x_3955_; 
lean_dec(v_x_3948_);
v___x_3955_ = lean_apply_2(v_k_3945_, v_x_3946_, v_x_3947_);
return v___x_3955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_3956_, lean_object* v_k_3957_, lean_object* v_x_3958_, lean_object* v_x_3959_, lean_object* v_x_3960_){
_start:
{
lean_object* v___x_3961_; 
v___x_3961_ = l_Lean_Expr_withAppAux___redArg(v_k_3957_, v_x_3958_, v_x_3959_, v_x_3960_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_3962_, lean_object* v_k_3963_){
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
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_3970_, lean_object* v_e_3971_, lean_object* v_k_3972_){
_start:
{
lean_object* v_dummy_3973_; lean_object* v_nargs_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v_dummy_3973_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3974_ = l_Lean_Expr_getAppNumArgs(v_e_3971_);
lean_inc(v_nargs_3974_);
v___x_3975_ = lean_mk_array(v_nargs_3974_, v_dummy_3973_);
v___x_3976_ = lean_unsigned_to_nat(1u);
v___x_3977_ = lean_nat_sub(v_nargs_3974_, v___x_3976_);
lean_dec(v_nargs_3974_);
v___x_3978_ = l_Lean_Expr_withAppAux___redArg(v_k_3972_, v_e_3971_, v___x_3975_, v___x_3977_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_3979_, lean_object* v_x_3980_, lean_object* v_x_3981_){
_start:
{
if (lean_obj_tag(v_x_3979_) == 5)
{
lean_object* v_fn_3982_; lean_object* v_arg_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_fn_3982_ = lean_ctor_get(v_x_3979_, 0);
lean_inc_ref(v_fn_3982_);
v_arg_3983_ = lean_ctor_get(v_x_3979_, 1);
lean_inc_ref(v_arg_3983_);
lean_dec_ref_known(v_x_3979_, 2);
v___x_3984_ = lean_array_set(v_x_3980_, v_x_3981_, v_arg_3983_);
v___x_3985_ = lean_unsigned_to_nat(1u);
v___x_3986_ = lean_nat_sub(v_x_3981_, v___x_3985_);
lean_dec(v_x_3981_);
v_x_3979_ = v_fn_3982_;
v_x_3980_ = v___x_3984_;
v_x_3981_ = v___x_3986_;
goto _start;
}
else
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
lean_dec(v_x_3981_);
v___x_3988_ = l_Lean_Expr_constName(v_x_3979_);
lean_dec_ref(v_x_3979_);
v___x_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
lean_ctor_set(v___x_3989_, 1, v_x_3980_);
return v___x_3989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_3990_){
_start:
{
lean_object* v_dummy_3991_; lean_object* v_nargs_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v_dummy_3991_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3992_ = l_Lean_Expr_getAppNumArgs(v_e_3990_);
lean_inc(v_nargs_3992_);
v___x_3993_ = lean_mk_array(v_nargs_3992_, v_dummy_3991_);
v___x_3994_ = lean_unsigned_to_nat(1u);
v___x_3995_ = lean_nat_sub(v_nargs_3992_, v___x_3994_);
lean_dec(v_nargs_3992_);
v___x_3996_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_3990_, v___x_3993_, v___x_3995_);
return v___x_3996_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Array_instInhabited(lean_box(0));
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_3998_){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3999_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_4000_ = lean_panic_fn_borrowed(v___x_3999_, v_msg_3998_);
return v___x_4000_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4003_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_4004_ = lean_unsigned_to_nat(27u);
v___x_4005_ = lean_unsigned_to_nat(1247u);
v___x_4006_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_4007_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4008_ = l_mkPanicMessageWithDecl(v___x_4007_, v___x_4006_, v___x_4005_, v___x_4004_, v___x_4003_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_){
_start:
{
lean_object* v_zero_4012_; uint8_t v_isZero_4013_; 
v_zero_4012_ = lean_unsigned_to_nat(0u);
v_isZero_4013_ = lean_nat_dec_eq(v_a_4009_, v_zero_4012_);
if (v_isZero_4013_ == 1)
{
lean_dec_ref(v_a_4010_);
lean_dec(v_a_4009_);
return v_a_4011_;
}
else
{
if (lean_obj_tag(v_a_4010_) == 5)
{
lean_object* v_fn_4014_; lean_object* v_arg_4015_; lean_object* v_one_4016_; lean_object* v_n_4017_; lean_object* v___x_4018_; 
v_fn_4014_ = lean_ctor_get(v_a_4010_, 0);
lean_inc_ref(v_fn_4014_);
v_arg_4015_ = lean_ctor_get(v_a_4010_, 1);
lean_inc_ref(v_arg_4015_);
lean_dec_ref_known(v_a_4010_, 2);
v_one_4016_ = lean_unsigned_to_nat(1u);
v_n_4017_ = lean_nat_sub(v_a_4009_, v_one_4016_);
lean_dec(v_a_4009_);
v___x_4018_ = lean_array_set(v_a_4011_, v_n_4017_, v_arg_4015_);
v_a_4009_ = v_n_4017_;
v_a_4010_ = v_fn_4014_;
v_a_4011_ = v___x_4018_;
goto _start;
}
else
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
lean_dec_ref(v_a_4011_);
lean_dec_ref(v_a_4010_);
lean_dec(v_a_4009_);
v___x_4020_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_4021_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_4020_);
return v___x_4021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_4022_, lean_object* v_n_4023_){
_start:
{
lean_object* v_dummy_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v_dummy_4024_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_4023_);
v___x_4025_ = lean_mk_array(v_n_4023_, v_dummy_4024_);
v___x_4026_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_4023_, v_e_4022_, v___x_4025_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_4027_, lean_object* v_n_4028_){
_start:
{
lean_object* v_zero_4029_; uint8_t v_isZero_4030_; 
v_zero_4029_ = lean_unsigned_to_nat(0u);
v_isZero_4030_ = lean_nat_dec_eq(v_n_4028_, v_zero_4029_);
if (v_isZero_4030_ == 1)
{
lean_dec(v_n_4028_);
lean_inc_ref(v_e_4027_);
return v_e_4027_;
}
else
{
if (lean_obj_tag(v_e_4027_) == 5)
{
lean_object* v_fn_4031_; lean_object* v_one_4032_; lean_object* v_n_4033_; 
v_fn_4031_ = lean_ctor_get(v_e_4027_, 0);
v_one_4032_ = lean_unsigned_to_nat(1u);
v_n_4033_ = lean_nat_sub(v_n_4028_, v_one_4032_);
lean_dec(v_n_4028_);
v_e_4027_ = v_fn_4031_;
v_n_4028_ = v_n_4033_;
goto _start;
}
else
{
lean_dec(v_n_4028_);
lean_inc_ref(v_e_4027_);
return v_e_4027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_4035_, lean_object* v_n_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l_Lean_Expr_stripArgsN(v_e_4035_, v_n_4036_);
lean_dec_ref(v_e_4035_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_4038_, lean_object* v_n_4039_){
_start:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4040_ = l_Lean_Expr_getAppNumArgs(v_e_4038_);
v___x_4041_ = lean_nat_sub(v___x_4040_, v_n_4039_);
lean_dec(v___x_4040_);
v___x_4042_ = l_Lean_Expr_stripArgsN(v_e_4038_, v___x_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_4043_, lean_object* v_n_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Lean_Expr_getAppPrefix(v_e_4043_, v_n_4044_);
lean_dec(v_n_4044_);
lean_dec_ref(v_e_4043_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_4046_, lean_object* v_inst_4047_, lean_object* v_f_4048_, lean_object* v_x_4049_){
_start:
{
size_t v_sz_4050_; size_t v___x_4051_; lean_object* v___x_4052_; 
v_sz_4050_ = lean_array_size(v_args_4046_);
v___x_4051_ = ((size_t)0ULL);
v___x_4052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4047_, v_f_4048_, v_sz_4050_, v___x_4051_, v_args_4046_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_4054_, lean_object* v_inst_4055_, lean_object* v_f_4056_, lean_object* v_toSeq_4057_, lean_object* v_fn_4058_, lean_object* v_args_4059_){
_start:
{
lean_object* v_map_4060_; lean_object* v___f_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v_map_4060_ = lean_ctor_get(v_toFunctor_4054_, 0);
lean_inc(v_map_4060_);
lean_dec_ref(v_toFunctor_4054_);
lean_inc(v_f_4056_);
v___f_4061_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4061_, 0, v_args_4059_);
lean_closure_set(v___f_4061_, 1, v_inst_4055_);
lean_closure_set(v___f_4061_, 2, v_f_4056_);
v___x_4062_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_4063_ = lean_apply_1(v_f_4056_, v_fn_4058_);
v___x_4064_ = lean_apply_4(v_map_4060_, lean_box(0), lean_box(0), v___x_4062_, v___x_4063_);
v___x_4065_ = lean_apply_4(v_toSeq_4057_, lean_box(0), lean_box(0), v___x_4064_, v___f_4061_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_4066_, lean_object* v_f_4067_, lean_object* v_e_4068_){
_start:
{
lean_object* v_toApplicative_4069_; lean_object* v_toFunctor_4070_; lean_object* v_toSeq_4071_; lean_object* v___f_4072_; lean_object* v_dummy_4073_; lean_object* v_nargs_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v_toApplicative_4069_ = lean_ctor_get(v_inst_4066_, 0);
v_toFunctor_4070_ = lean_ctor_get(v_toApplicative_4069_, 0);
lean_inc_ref(v_toFunctor_4070_);
v_toSeq_4071_ = lean_ctor_get(v_toApplicative_4069_, 2);
lean_inc(v_toSeq_4071_);
v___f_4072_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_4072_, 0, v_toFunctor_4070_);
lean_closure_set(v___f_4072_, 1, v_inst_4066_);
lean_closure_set(v___f_4072_, 2, v_f_4067_);
lean_closure_set(v___f_4072_, 3, v_toSeq_4071_);
v_dummy_4073_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4074_ = l_Lean_Expr_getAppNumArgs(v_e_4068_);
lean_inc(v_nargs_4074_);
v___x_4075_ = lean_mk_array(v_nargs_4074_, v_dummy_4073_);
v___x_4076_ = lean_unsigned_to_nat(1u);
v___x_4077_ = lean_nat_sub(v_nargs_4074_, v___x_4076_);
lean_dec(v_nargs_4074_);
v___x_4078_ = l_Lean_Expr_withAppAux___redArg(v___f_4072_, v_e_4068_, v___x_4075_, v___x_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_4079_, lean_object* v_inst_4080_, lean_object* v_f_4081_, lean_object* v_e_4082_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_Expr_traverseApp___redArg(v_inst_4080_, v_f_4081_, v_e_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_4084_, lean_object* v_x_4085_, lean_object* v_x_4086_){
_start:
{
if (lean_obj_tag(v_x_4085_) == 5)
{
lean_object* v_fn_4087_; lean_object* v_arg_4088_; lean_object* v___x_4089_; 
v_fn_4087_ = lean_ctor_get(v_x_4085_, 0);
lean_inc_ref(v_fn_4087_);
v_arg_4088_ = lean_ctor_get(v_x_4085_, 1);
lean_inc_ref(v_arg_4088_);
lean_dec_ref_known(v_x_4085_, 2);
v___x_4089_ = lean_array_push(v_x_4086_, v_arg_4088_);
v_x_4085_ = v_fn_4087_;
v_x_4086_ = v___x_4089_;
goto _start;
}
else
{
lean_object* v___x_4091_; 
v___x_4091_ = lean_apply_2(v_k_4084_, v_x_4085_, v_x_4086_);
return v___x_4091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_4092_, lean_object* v_k_4093_, lean_object* v_x_4094_, lean_object* v_x_4095_){
_start:
{
lean_object* v___x_4096_; 
v___x_4096_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4093_, v_x_4094_, v_x_4095_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_4097_, lean_object* v_k_4098_){
_start:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4099_ = l_Lean_Expr_getAppNumArgs(v_e_4097_);
v___x_4100_ = lean_mk_empty_array_with_capacity(v___x_4099_);
lean_dec(v___x_4099_);
v___x_4101_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4098_, v_e_4097_, v___x_4100_);
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_4102_, lean_object* v_e_4103_, lean_object* v_k_4104_){
_start:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4105_ = l_Lean_Expr_getAppNumArgs(v_e_4103_);
v___x_4106_ = lean_mk_empty_array_with_capacity(v___x_4105_);
lean_dec(v___x_4105_);
v___x_4107_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4104_, v_e_4103_, v___x_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_4108_, lean_object* v_x_4109_, lean_object* v_x_4110_){
_start:
{
if (lean_obj_tag(v_x_4108_) == 5)
{
lean_object* v_fn_4111_; lean_object* v_arg_4112_; lean_object* v_zero_4113_; uint8_t v_isZero_4114_; 
v_fn_4111_ = lean_ctor_get(v_x_4108_, 0);
v_arg_4112_ = lean_ctor_get(v_x_4108_, 1);
v_zero_4113_ = lean_unsigned_to_nat(0u);
v_isZero_4114_ = lean_nat_dec_eq(v_x_4109_, v_zero_4113_);
if (v_isZero_4114_ == 1)
{
lean_dec(v_x_4109_);
lean_inc_ref(v_arg_4112_);
return v_arg_4112_;
}
else
{
lean_object* v_one_4115_; lean_object* v_n_4116_; 
v_one_4115_ = lean_unsigned_to_nat(1u);
v_n_4116_ = lean_nat_sub(v_x_4109_, v_one_4115_);
lean_dec(v_x_4109_);
v_x_4108_ = v_fn_4111_;
v_x_4109_ = v_n_4116_;
goto _start;
}
}
else
{
lean_dec(v_x_4109_);
lean_inc_ref(v_x_4110_);
return v_x_4110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_4118_, lean_object* v_x_4119_, lean_object* v_x_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_Lean_Expr_getRevArgD(v_x_4118_, v_x_4119_, v_x_4120_);
lean_dec_ref(v_x_4120_);
lean_dec_ref(v_x_4118_);
return v_res_4121_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4124_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4125_ = lean_unsigned_to_nat(20u);
v___x_4126_ = lean_unsigned_to_nat(1288u);
v___x_4127_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4128_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4129_ = l_mkPanicMessageWithDecl(v___x_4128_, v___x_4127_, v___x_4126_, v___x_4125_, v___x_4124_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4130_, lean_object* v_x_4131_){
_start:
{
if (lean_obj_tag(v_x_4130_) == 5)
{
lean_object* v_fn_4132_; lean_object* v_arg_4133_; lean_object* v_zero_4134_; uint8_t v_isZero_4135_; 
v_fn_4132_ = lean_ctor_get(v_x_4130_, 0);
v_arg_4133_ = lean_ctor_get(v_x_4130_, 1);
v_zero_4134_ = lean_unsigned_to_nat(0u);
v_isZero_4135_ = lean_nat_dec_eq(v_x_4131_, v_zero_4134_);
if (v_isZero_4135_ == 1)
{
lean_dec(v_x_4131_);
lean_inc_ref(v_arg_4133_);
return v_arg_4133_;
}
else
{
lean_object* v_one_4136_; lean_object* v_n_4137_; 
v_one_4136_ = lean_unsigned_to_nat(1u);
v_n_4137_ = lean_nat_sub(v_x_4131_, v_one_4136_);
lean_dec(v_x_4131_);
v_x_4130_ = v_fn_4132_;
v_x_4131_ = v_n_4137_;
goto _start;
}
}
else
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
lean_dec(v_x_4131_);
v___x_4139_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4140_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4139_);
return v___x_4140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4141_, lean_object* v_x_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l_Lean_Expr_getRevArg_x21(v_x_4141_, v_x_4142_);
lean_dec_ref(v_x_4141_);
return v_res_4143_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4145_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4146_ = lean_unsigned_to_nat(20u);
v___x_4147_ = lean_unsigned_to_nat(1295u);
v___x_4148_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4149_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4150_ = l_mkPanicMessageWithDecl(v___x_4149_, v___x_4148_, v___x_4147_, v___x_4146_, v___x_4145_);
return v___x_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4151_, lean_object* v_x_4152_){
_start:
{
switch(lean_obj_tag(v_x_4151_))
{
case 10:
{
lean_object* v_expr_4153_; 
v_expr_4153_ = lean_ctor_get(v_x_4151_, 1);
v_x_4151_ = v_expr_4153_;
goto _start;
}
case 5:
{
lean_object* v_fn_4155_; lean_object* v_arg_4156_; lean_object* v_zero_4157_; uint8_t v_isZero_4158_; 
v_fn_4155_ = lean_ctor_get(v_x_4151_, 0);
v_arg_4156_ = lean_ctor_get(v_x_4151_, 1);
v_zero_4157_ = lean_unsigned_to_nat(0u);
v_isZero_4158_ = lean_nat_dec_eq(v_x_4152_, v_zero_4157_);
if (v_isZero_4158_ == 1)
{
lean_dec(v_x_4152_);
lean_inc_ref(v_arg_4156_);
return v_arg_4156_;
}
else
{
lean_object* v_one_4159_; lean_object* v_n_4160_; 
v_one_4159_ = lean_unsigned_to_nat(1u);
v_n_4160_ = lean_nat_sub(v_x_4152_, v_one_4159_);
lean_dec(v_x_4152_);
v_x_4151_ = v_fn_4155_;
v_x_4152_ = v_n_4160_;
goto _start;
}
}
default: 
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
lean_dec(v_x_4152_);
v___x_4162_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4163_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4162_);
return v___x_4163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4164_, lean_object* v_x_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4164_, v_x_4165_);
lean_dec_ref(v_x_4164_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4167_, lean_object* v_i_4168_, lean_object* v_n_4169_){
_start:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4170_ = lean_nat_sub(v_n_4169_, v_i_4168_);
v___x_4171_ = lean_unsigned_to_nat(1u);
v___x_4172_ = lean_nat_sub(v___x_4170_, v___x_4171_);
lean_dec(v___x_4170_);
v___x_4173_ = l_Lean_Expr_getRevArg_x21(v_e_4167_, v___x_4172_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4174_, lean_object* v_i_4175_, lean_object* v_n_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Lean_Expr_getArg_x21(v_e_4174_, v_i_4175_, v_n_4176_);
lean_dec(v_n_4176_);
lean_dec(v_i_4175_);
lean_dec_ref(v_e_4174_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4178_, lean_object* v_i_4179_, lean_object* v_n_4180_){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4181_ = lean_nat_sub(v_n_4180_, v_i_4179_);
v___x_4182_ = lean_unsigned_to_nat(1u);
v___x_4183_ = lean_nat_sub(v___x_4181_, v___x_4182_);
lean_dec(v___x_4181_);
v___x_4184_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4178_, v___x_4183_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4185_, lean_object* v_i_4186_, lean_object* v_n_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_Lean_Expr_getArg_x21_x27(v_e_4185_, v_i_4186_, v_n_4187_);
lean_dec(v_n_4187_);
lean_dec(v_i_4186_);
lean_dec_ref(v_e_4185_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4189_, lean_object* v_i_4190_, lean_object* v_v_u2080_4191_, lean_object* v_n_4192_){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4193_ = lean_nat_sub(v_n_4192_, v_i_4190_);
v___x_4194_ = lean_unsigned_to_nat(1u);
v___x_4195_ = lean_nat_sub(v___x_4193_, v___x_4194_);
lean_dec(v___x_4193_);
v___x_4196_ = l_Lean_Expr_getRevArgD(v_e_4189_, v___x_4195_, v_v_u2080_4191_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4197_, lean_object* v_i_4198_, lean_object* v_v_u2080_4199_, lean_object* v_n_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lean_Expr_getArgD(v_e_4197_, v_i_4198_, v_v_u2080_4199_, v_n_4200_);
lean_dec(v_n_4200_);
lean_dec_ref(v_v_u2080_4199_);
lean_dec(v_i_4198_);
lean_dec_ref(v_e_4197_);
return v_res_4201_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4202_){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; uint8_t v___x_4205_; 
v___x_4203_ = lean_unsigned_to_nat(0u);
v___x_4204_ = l_Lean_Expr_looseBVarRange(v_e_4202_);
v___x_4205_ = lean_nat_dec_lt(v___x_4203_, v___x_4204_);
lean_dec(v___x_4204_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4206_){
_start:
{
uint8_t v_res_4207_; lean_object* v_r_4208_; 
v_res_4207_ = l_Lean_Expr_hasLooseBVars(v_e_4206_);
lean_dec_ref(v_e_4206_);
v_r_4208_ = lean_box(v_res_4207_);
return v_r_4208_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4209_){
_start:
{
if (lean_obj_tag(v_e_4209_) == 7)
{
lean_object* v_body_4210_; uint8_t v___x_4211_; 
v_body_4210_ = lean_ctor_get(v_e_4209_, 2);
v___x_4211_ = l_Lean_Expr_hasLooseBVars(v_body_4210_);
if (v___x_4211_ == 0)
{
uint8_t v___x_4212_; 
v___x_4212_ = 1;
return v___x_4212_;
}
else
{
uint8_t v___x_4213_; 
v___x_4213_ = 0;
return v___x_4213_;
}
}
else
{
uint8_t v___x_4214_; 
v___x_4214_ = 0;
return v___x_4214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4215_){
_start:
{
uint8_t v_res_4216_; lean_object* v_r_4217_; 
v_res_4216_ = l_Lean_Expr_isArrow(v_e_4215_);
lean_dec_ref(v_e_4215_);
v_r_4217_ = lean_box(v_res_4216_);
return v_r_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4220_, lean_object* v_bvarIdx_4221_){
_start:
{
uint8_t v_res_4222_; lean_object* v_r_4223_; 
v_res_4222_ = lean_expr_has_loose_bvar(v_e_4220_, v_bvarIdx_4221_);
lean_dec(v_bvarIdx_4221_);
lean_dec_ref(v_e_4220_);
v_r_4223_ = lean_box(v_res_4222_);
return v_r_4223_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4224_, lean_object* v_bvarIdx_4225_, uint8_t v_considerRange_4226_){
_start:
{
if (lean_obj_tag(v_e_4224_) == 7)
{
lean_object* v_binderType_4227_; lean_object* v_body_4228_; uint8_t v_binderInfo_4229_; uint8_t v___y_4231_; uint8_t v___x_4235_; 
v_binderType_4227_ = lean_ctor_get(v_e_4224_, 1);
v_body_4228_ = lean_ctor_get(v_e_4224_, 2);
v_binderInfo_4229_ = lean_ctor_get_uint8(v_e_4224_, sizeof(void*)*3 + 8);
v___x_4235_ = lean_expr_has_loose_bvar(v_binderType_4227_, v_bvarIdx_4225_);
if (v___x_4235_ == 0)
{
v___y_4231_ = v___x_4235_;
goto v___jp_4230_;
}
else
{
uint8_t v___x_4236_; 
v___x_4236_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4229_);
if (v___x_4236_ == 0)
{
lean_object* v___x_4237_; uint8_t v___x_4238_; 
v___x_4237_ = lean_unsigned_to_nat(0u);
v___x_4238_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4228_, v___x_4237_, v_considerRange_4226_);
v___y_4231_ = v___x_4238_;
goto v___jp_4230_;
}
else
{
v___y_4231_ = v___x_4236_;
goto v___jp_4230_;
}
}
v___jp_4230_:
{
if (v___y_4231_ == 0)
{
lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4232_ = lean_unsigned_to_nat(1u);
v___x_4233_ = lean_nat_add(v_bvarIdx_4225_, v___x_4232_);
lean_dec(v_bvarIdx_4225_);
v_e_4224_ = v_body_4228_;
v_bvarIdx_4225_ = v___x_4233_;
goto _start;
}
else
{
lean_dec(v_bvarIdx_4225_);
return v___y_4231_;
}
}
}
else
{
if (v_considerRange_4226_ == 0)
{
lean_dec(v_bvarIdx_4225_);
return v_considerRange_4226_;
}
else
{
uint8_t v___x_4239_; 
v___x_4239_ = lean_expr_has_loose_bvar(v_e_4224_, v_bvarIdx_4225_);
lean_dec(v_bvarIdx_4225_);
return v___x_4239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4240_, lean_object* v_bvarIdx_4241_, lean_object* v_considerRange_4242_){
_start:
{
uint8_t v_considerRange_boxed_4243_; uint8_t v_res_4244_; lean_object* v_r_4245_; 
v_considerRange_boxed_4243_ = lean_unbox(v_considerRange_4242_);
v_res_4244_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4240_, v_bvarIdx_4241_, v_considerRange_boxed_4243_);
lean_dec_ref(v_e_4240_);
v_r_4245_ = lean_box(v_res_4244_);
return v_r_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4249_, lean_object* v_s_4250_, lean_object* v_d_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = lean_expr_lower_loose_bvars(v_e_4249_, v_s_4250_, v_d_4251_);
lean_dec(v_d_4251_);
lean_dec(v_s_4250_);
lean_dec_ref(v_e_4249_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4256_, lean_object* v_s_4257_, lean_object* v_d_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = lean_expr_lift_loose_bvars(v_e_4256_, v_s_4257_, v_d_4258_);
lean_dec(v_d_4258_);
lean_dec(v_s_4257_);
lean_dec_ref(v_e_4256_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4260_, lean_object* v_numParams_4261_, uint8_t v_considerRange_4262_){
_start:
{
if (lean_obj_tag(v_e_4260_) == 7)
{
lean_object* v_binderName_4263_; lean_object* v_binderType_4264_; lean_object* v_body_4265_; uint8_t v_binderInfo_4266_; lean_object* v_zero_4267_; uint8_t v_isZero_4268_; 
v_binderName_4263_ = lean_ctor_get(v_e_4260_, 0);
v_binderType_4264_ = lean_ctor_get(v_e_4260_, 1);
v_body_4265_ = lean_ctor_get(v_e_4260_, 2);
v_binderInfo_4266_ = lean_ctor_get_uint8(v_e_4260_, sizeof(void*)*3 + 8);
v_zero_4267_ = lean_unsigned_to_nat(0u);
v_isZero_4268_ = lean_nat_dec_eq(v_numParams_4261_, v_zero_4267_);
if (v_isZero_4268_ == 0)
{
lean_object* v_one_4269_; lean_object* v_n_4270_; lean_object* v_b_4271_; uint8_t v___y_4273_; uint8_t v___x_4277_; 
lean_inc_ref(v_body_4265_);
lean_inc_ref(v_binderType_4264_);
lean_inc(v_binderName_4263_);
lean_dec_ref_known(v_e_4260_, 3);
v_one_4269_ = lean_unsigned_to_nat(1u);
v_n_4270_ = lean_nat_sub(v_numParams_4261_, v_one_4269_);
v_b_4271_ = l_Lean_Expr_inferImplicit(v_body_4265_, v_n_4270_, v_considerRange_4262_);
lean_dec(v_n_4270_);
v___x_4277_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4266_);
if (v___x_4277_ == 0)
{
v___y_4273_ = v___x_4277_;
goto v___jp_4272_;
}
else
{
uint8_t v___x_4278_; 
v___x_4278_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4271_, v_zero_4267_, v_considerRange_4262_);
v___y_4273_ = v___x_4278_;
goto v___jp_4272_;
}
v___jp_4272_:
{
if (v___y_4273_ == 0)
{
lean_object* v___x_4274_; 
v___x_4274_ = l_Lean_Expr_forallE___override(v_binderName_4263_, v_binderType_4264_, v_b_4271_, v_binderInfo_4266_);
return v___x_4274_;
}
else
{
uint8_t v___x_4275_; lean_object* v___x_4276_; 
v___x_4275_ = 1;
v___x_4276_ = l_Lean_Expr_forallE___override(v_binderName_4263_, v_binderType_4264_, v_b_4271_, v___x_4275_);
return v___x_4276_;
}
}
}
else
{
return v_e_4260_;
}
}
else
{
return v_e_4260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4279_, lean_object* v_numParams_4280_, lean_object* v_considerRange_4281_){
_start:
{
uint8_t v_considerRange_boxed_4282_; lean_object* v_res_4283_; 
v_considerRange_boxed_4282_ = lean_unbox(v_considerRange_4281_);
v_res_4283_ = l_Lean_Expr_inferImplicit(v_e_4279_, v_numParams_4280_, v_considerRange_boxed_4282_);
lean_dec(v_numParams_4280_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4284_, lean_object* v_binderInfos_x3f_4285_){
_start:
{
if (lean_obj_tag(v_e_4284_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4285_) == 1)
{
lean_object* v_binderName_4286_; lean_object* v_binderType_4287_; lean_object* v_body_4288_; uint8_t v_binderInfo_4289_; lean_object* v_head_4290_; lean_object* v_tail_4291_; lean_object* v_b_4292_; 
v_binderName_4286_ = lean_ctor_get(v_e_4284_, 0);
lean_inc(v_binderName_4286_);
v_binderType_4287_ = lean_ctor_get(v_e_4284_, 1);
lean_inc_ref(v_binderType_4287_);
v_body_4288_ = lean_ctor_get(v_e_4284_, 2);
lean_inc_ref(v_body_4288_);
v_binderInfo_4289_ = lean_ctor_get_uint8(v_e_4284_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4284_, 3);
v_head_4290_ = lean_ctor_get(v_binderInfos_x3f_4285_, 0);
v_tail_4291_ = lean_ctor_get(v_binderInfos_x3f_4285_, 1);
v_b_4292_ = l_Lean_Expr_updateForallBinderInfos(v_body_4288_, v_tail_4291_);
if (lean_obj_tag(v_head_4290_) == 0)
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Lean_Expr_forallE___override(v_binderName_4286_, v_binderType_4287_, v_b_4292_, v_binderInfo_4289_);
return v___x_4293_;
}
else
{
lean_object* v_val_4294_; uint8_t v___x_4295_; lean_object* v___x_4296_; 
v_val_4294_ = lean_ctor_get(v_head_4290_, 0);
v___x_4295_ = lean_unbox(v_val_4294_);
v___x_4296_ = l_Lean_Expr_forallE___override(v_binderName_4286_, v_binderType_4287_, v_b_4292_, v___x_4295_);
return v___x_4296_;
}
}
else
{
return v_e_4284_;
}
}
else
{
return v_e_4284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4297_, lean_object* v_binderInfos_x3f_4298_){
_start:
{
lean_object* v_res_4299_; 
v_res_4299_ = l_Lean_Expr_updateForallBinderInfos(v_e_4297_, v_binderInfos_x3f_4298_);
lean_dec(v_binderInfos_x3f_4298_);
return v_res_4299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4300_, lean_object* v_binderNames_x3f_4301_){
_start:
{
switch(lean_obj_tag(v_e_4300_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4301_) == 1)
{
lean_object* v_binderName_4302_; lean_object* v_binderType_4303_; lean_object* v_body_4304_; uint8_t v_binderInfo_4305_; lean_object* v_head_4306_; lean_object* v_tail_4307_; lean_object* v_b_4308_; 
v_binderName_4302_ = lean_ctor_get(v_e_4300_, 0);
lean_inc(v_binderName_4302_);
v_binderType_4303_ = lean_ctor_get(v_e_4300_, 1);
lean_inc_ref(v_binderType_4303_);
v_body_4304_ = lean_ctor_get(v_e_4300_, 2);
lean_inc_ref(v_body_4304_);
v_binderInfo_4305_ = lean_ctor_get_uint8(v_e_4300_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4300_, 3);
v_head_4306_ = lean_ctor_get(v_binderNames_x3f_4301_, 0);
lean_inc(v_head_4306_);
v_tail_4307_ = lean_ctor_get(v_binderNames_x3f_4301_, 1);
lean_inc(v_tail_4307_);
lean_dec_ref_known(v_binderNames_x3f_4301_, 2);
v_b_4308_ = l_Lean_Expr_updateBinderNames(v_body_4304_, v_tail_4307_);
if (lean_obj_tag(v_head_4306_) == 0)
{
lean_object* v___x_4309_; 
v___x_4309_ = l_Lean_Expr_forallE___override(v_binderName_4302_, v_binderType_4303_, v_b_4308_, v_binderInfo_4305_);
return v___x_4309_;
}
else
{
lean_object* v_val_4310_; lean_object* v___x_4311_; 
lean_dec(v_binderName_4302_);
v_val_4310_ = lean_ctor_get(v_head_4306_, 0);
lean_inc(v_val_4310_);
lean_dec_ref_known(v_head_4306_, 1);
v___x_4311_ = l_Lean_Expr_forallE___override(v_val_4310_, v_binderType_4303_, v_b_4308_, v_binderInfo_4305_);
return v___x_4311_;
}
}
else
{
lean_dec(v_binderNames_x3f_4301_);
return v_e_4300_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4301_) == 1)
{
lean_object* v_binderName_4312_; lean_object* v_binderType_4313_; lean_object* v_body_4314_; uint8_t v_binderInfo_4315_; lean_object* v_head_4316_; lean_object* v_tail_4317_; lean_object* v_b_4318_; 
v_binderName_4312_ = lean_ctor_get(v_e_4300_, 0);
lean_inc(v_binderName_4312_);
v_binderType_4313_ = lean_ctor_get(v_e_4300_, 1);
lean_inc_ref(v_binderType_4313_);
v_body_4314_ = lean_ctor_get(v_e_4300_, 2);
lean_inc_ref(v_body_4314_);
v_binderInfo_4315_ = lean_ctor_get_uint8(v_e_4300_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4300_, 3);
v_head_4316_ = lean_ctor_get(v_binderNames_x3f_4301_, 0);
lean_inc(v_head_4316_);
v_tail_4317_ = lean_ctor_get(v_binderNames_x3f_4301_, 1);
lean_inc(v_tail_4317_);
lean_dec_ref_known(v_binderNames_x3f_4301_, 2);
v_b_4318_ = l_Lean_Expr_updateBinderNames(v_body_4314_, v_tail_4317_);
if (lean_obj_tag(v_head_4316_) == 0)
{
lean_object* v___x_4319_; 
v___x_4319_ = l_Lean_Expr_lam___override(v_binderName_4312_, v_binderType_4313_, v_b_4318_, v_binderInfo_4315_);
return v___x_4319_;
}
else
{
lean_object* v_val_4320_; lean_object* v___x_4321_; 
lean_dec(v_binderName_4312_);
v_val_4320_ = lean_ctor_get(v_head_4316_, 0);
lean_inc(v_val_4320_);
lean_dec_ref_known(v_head_4316_, 1);
v___x_4321_ = l_Lean_Expr_lam___override(v_val_4320_, v_binderType_4313_, v_b_4318_, v_binderInfo_4315_);
return v___x_4321_;
}
}
else
{
lean_dec(v_binderNames_x3f_4301_);
return v_e_4300_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4301_);
return v_e_4300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4324_, lean_object* v_subst_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = lean_expr_instantiate(v_e_4324_, v_subst_4325_);
lean_dec_ref(v_subst_4325_);
lean_dec_ref(v_e_4324_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4329_, lean_object* v_subst_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = lean_expr_instantiate1(v_e_4329_, v_subst_4330_);
lean_dec_ref(v_subst_4330_);
lean_dec_ref(v_e_4329_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4334_, lean_object* v_subst_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = lean_expr_instantiate_rev(v_e_4334_, v_subst_4335_);
lean_dec_ref(v_subst_4335_);
lean_dec_ref(v_e_4334_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4341_, lean_object* v_beginIdx_4342_, lean_object* v_endIdx_4343_, lean_object* v_subst_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = lean_expr_instantiate_range(v_e_4341_, v_beginIdx_4342_, v_endIdx_4343_, v_subst_4344_);
lean_dec_ref(v_subst_4344_);
lean_dec(v_endIdx_4343_);
lean_dec(v_beginIdx_4342_);
lean_dec_ref(v_e_4341_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4350_, lean_object* v_beginIdx_4351_, lean_object* v_endIdx_4352_, lean_object* v_subst_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = lean_expr_instantiate_rev_range(v_e_4350_, v_beginIdx_4351_, v_endIdx_4352_, v_subst_4353_);
lean_dec_ref(v_subst_4353_);
lean_dec(v_endIdx_4352_);
lean_dec(v_beginIdx_4351_);
lean_dec_ref(v_e_4350_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4357_, lean_object* v_xs_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = lean_expr_abstract(v_e_4357_, v_xs_4358_);
lean_dec_ref(v_xs_4358_);
lean_dec_ref(v_e_4357_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4363_, lean_object* v_n_4364_, lean_object* v_xs_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = lean_expr_abstract_range(v_e_4363_, v_n_4364_, v_xs_4365_);
lean_dec_ref(v_xs_4365_);
lean_dec(v_n_4364_);
lean_dec_ref(v_e_4363_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4367_, lean_object* v_fvar_4368_, lean_object* v_v_4369_){
_start:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4370_ = lean_unsigned_to_nat(1u);
v___x_4371_ = lean_mk_empty_array_with_capacity(v___x_4370_);
v___x_4372_ = lean_array_push(v___x_4371_, v_fvar_4368_);
v___x_4373_ = lean_expr_abstract(v_e_4367_, v___x_4372_);
lean_dec_ref(v___x_4372_);
v___x_4374_ = lean_expr_instantiate1(v___x_4373_, v_v_4369_);
lean_dec_ref(v___x_4373_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4375_, lean_object* v_fvar_4376_, lean_object* v_v_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_Lean_Expr_replaceFVar(v_e_4375_, v_fvar_4376_, v_v_4377_);
lean_dec_ref(v_v_4377_);
lean_dec_ref(v_e_4375_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4379_, lean_object* v_fvarId_4380_, lean_object* v_v_4381_){
_start:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4382_ = l_Lean_Expr_fvar___override(v_fvarId_4380_);
v___x_4383_ = l_Lean_Expr_replaceFVar(v_e_4379_, v___x_4382_, v_v_4381_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4384_, lean_object* v_fvarId_4385_, lean_object* v_v_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l_Lean_Expr_replaceFVarId(v_e_4384_, v_fvarId_4385_, v_v_4386_);
lean_dec_ref(v_v_4386_);
lean_dec_ref(v_e_4384_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4388_, lean_object* v_fvars_4389_, lean_object* v_vs_4390_){
_start:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4391_ = lean_expr_abstract(v_e_4388_, v_fvars_4389_);
v___x_4392_ = lean_expr_instantiate_rev(v___x_4391_, v_vs_4390_);
lean_dec_ref(v___x_4391_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4393_, lean_object* v_fvars_4394_, lean_object* v_vs_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Lean_Expr_replaceFVars(v_e_4393_, v_fvars_4394_, v_vs_4395_);
lean_dec_ref(v_vs_4395_);
lean_dec_ref(v_fvars_4394_);
lean_dec_ref(v_e_4393_);
return v_res_4396_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4399_){
_start:
{
switch(lean_obj_tag(v_x_4399_))
{
case 4:
{
uint8_t v___x_4400_; 
v___x_4400_ = 1;
return v___x_4400_;
}
case 3:
{
uint8_t v___x_4401_; 
v___x_4401_ = 1;
return v___x_4401_;
}
case 0:
{
uint8_t v___x_4402_; 
v___x_4402_ = 1;
return v___x_4402_;
}
case 9:
{
uint8_t v___x_4403_; 
v___x_4403_ = 1;
return v___x_4403_;
}
case 2:
{
uint8_t v___x_4404_; 
v___x_4404_ = 1;
return v___x_4404_;
}
case 1:
{
uint8_t v___x_4405_; 
v___x_4405_ = 1;
return v___x_4405_;
}
default: 
{
uint8_t v___x_4406_; 
v___x_4406_ = 0;
return v___x_4406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4407_){
_start:
{
uint8_t v_res_4408_; lean_object* v_r_4409_; 
v_res_4408_ = l_Lean_Expr_isAtomic(v_x_4407_);
lean_dec_ref(v_x_4407_);
v_r_4409_ = lean_box(v_res_4408_);
return v_r_4409_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4415_ = lean_box(0);
v___x_4416_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4417_ = l_Lean_Expr_const___override(v___x_4416_, v___x_4415_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4418_, lean_object* v_proof_4419_){
_start:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; 
v___x_4420_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4421_ = l_Lean_mkAppB(v___x_4420_, v_pred_4418_, v_proof_4419_);
return v___x_4421_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4426_ = lean_box(0);
v___x_4427_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4428_ = l_Lean_Expr_const___override(v___x_4427_, v___x_4426_);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4429_, lean_object* v_proof_4430_){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4431_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4432_ = l_Lean_mkAppB(v___x_4431_, v_pred_4429_, v_proof_4430_);
return v___x_4432_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4433_; 
v___x_4433_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4433_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4435_){
_start:
{
lean_inc_ref(v_val_4435_);
return v_val_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4436_);
lean_dec_ref(v_val_4436_);
return v_res_4437_;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4440_, lean_object* v_x_4441_){
_start:
{
uint8_t v___x_4442_; 
v___x_4442_ = lean_expr_equal(v_x_4440_, v_x_4441_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4443_, lean_object* v_x_4444_){
_start:
{
uint8_t v_res_4445_; lean_object* v_r_4446_; 
v_res_4445_ = l_Lean_ExprStructEq_beq(v_x_4443_, v_x_4444_);
lean_dec_ref(v_x_4444_);
lean_dec_ref(v_x_4443_);
v_r_4446_ = lean_box(v_res_4445_);
return v_r_4446_;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4447_){
_start:
{
uint64_t v___x_4448_; 
v___x_4448_ = l_Lean_Expr_hash(v_x_4447_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4449_){
_start:
{
uint64_t v_res_4450_; lean_object* v_r_4451_; 
v_res_4450_ = l_Lean_ExprStructEq_hash(v_x_4449_);
lean_dec_ref(v_x_4449_);
v_r_4451_ = lean_box_uint64(v_res_4450_);
return v_r_4451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4458_, lean_object* v_start_4459_, lean_object* v_b_4460_, lean_object* v_i_4461_){
_start:
{
uint8_t v___x_4462_; 
v___x_4462_ = lean_nat_dec_le(v_i_4461_, v_start_4459_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; lean_object* v_i_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
v___x_4463_ = lean_unsigned_to_nat(1u);
v_i_4464_ = lean_nat_sub(v_i_4461_, v___x_4463_);
lean_dec(v_i_4461_);
v___x_4465_ = l_Lean_instInhabitedExpr;
v___x_4466_ = lean_array_get_borrowed(v___x_4465_, v_revArgs_4458_, v_i_4464_);
lean_inc(v___x_4466_);
v___x_4467_ = l_Lean_Expr_app___override(v_b_4460_, v___x_4466_);
v_b_4460_ = v___x_4467_;
v_i_4461_ = v_i_4464_;
goto _start;
}
else
{
lean_dec(v_i_4461_);
return v_b_4460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4469_, lean_object* v_start_4470_, lean_object* v_b_4471_, lean_object* v_i_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4469_, v_start_4470_, v_b_4471_, v_i_4472_);
lean_dec(v_start_4470_);
lean_dec_ref(v_revArgs_4469_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4474_, lean_object* v_beginIdx_4475_, lean_object* v_endIdx_4476_, lean_object* v_revArgs_4477_){
_start:
{
lean_object* v___x_4478_; 
v___x_4478_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4477_, v_beginIdx_4475_, v_f_4474_, v_endIdx_4476_);
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4479_, lean_object* v_beginIdx_4480_, lean_object* v_endIdx_4481_, lean_object* v_revArgs_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Lean_Expr_mkAppRevRange(v_f_4479_, v_beginIdx_4480_, v_endIdx_4481_, v_revArgs_4482_);
lean_dec_ref(v_revArgs_4482_);
lean_dec(v_beginIdx_4480_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4484_, uint8_t v_useZeta_4485_, uint8_t v_preserveMData_4486_, lean_object* v_sz_4487_, lean_object* v_e_4488_, lean_object* v_i_4489_){
_start:
{
switch(lean_obj_tag(v_e_4488_))
{
case 6:
{
lean_object* v_body_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; uint8_t v___x_4498_; 
v_body_4495_ = lean_ctor_get(v_e_4488_, 2);
lean_inc_ref(v_body_4495_);
lean_dec_ref_known(v_e_4488_, 3);
v___x_4496_ = lean_unsigned_to_nat(1u);
v___x_4497_ = lean_nat_add(v_i_4489_, v___x_4496_);
lean_dec(v_i_4489_);
v___x_4498_ = lean_nat_dec_lt(v___x_4497_, v_sz_4487_);
if (v___x_4498_ == 0)
{
lean_object* v___x_4499_; 
lean_dec(v___x_4497_);
v___x_4499_ = lean_expr_instantiate(v_body_4495_, v_revArgs_4484_);
lean_dec_ref(v_body_4495_);
return v___x_4499_;
}
else
{
v_e_4488_ = v_body_4495_;
v_i_4489_ = v___x_4497_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4485_ == 0)
{
goto v___jp_4490_;
}
else
{
lean_object* v_value_4501_; lean_object* v_body_4502_; uint8_t v___x_4503_; 
v_value_4501_ = lean_ctor_get(v_e_4488_, 2);
v_body_4502_ = lean_ctor_get(v_e_4488_, 3);
v___x_4503_ = lean_nat_dec_lt(v_i_4489_, v_sz_4487_);
if (v___x_4503_ == 0)
{
goto v___jp_4490_;
}
else
{
lean_object* v___x_4504_; 
lean_inc_ref(v_body_4502_);
lean_inc_ref(v_value_4501_);
lean_dec_ref_known(v_e_4488_, 4);
v___x_4504_ = lean_expr_instantiate1(v_body_4502_, v_value_4501_);
lean_dec_ref(v_value_4501_);
lean_dec_ref(v_body_4502_);
v_e_4488_ = v___x_4504_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4486_ == 0)
{
lean_object* v_expr_4506_; 
v_expr_4506_ = lean_ctor_get(v_e_4488_, 1);
lean_inc_ref(v_expr_4506_);
lean_dec_ref_known(v_e_4488_, 2);
v_e_4488_ = v_expr_4506_;
goto _start;
}
else
{
goto v___jp_4490_;
}
}
default: 
{
goto v___jp_4490_;
}
}
v___jp_4490_:
{
lean_object* v_n_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
v_n_4491_ = lean_nat_sub(v_sz_4487_, v_i_4489_);
lean_dec(v_i_4489_);
v___x_4492_ = lean_expr_instantiate_range(v_e_4488_, v_n_4491_, v_sz_4487_, v_revArgs_4484_);
lean_dec_ref(v_e_4488_);
v___x_4493_ = lean_unsigned_to_nat(0u);
v___x_4494_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4484_, v___x_4493_, v___x_4492_, v_n_4491_);
return v___x_4494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4508_, lean_object* v_useZeta_4509_, lean_object* v_preserveMData_4510_, lean_object* v_sz_4511_, lean_object* v_e_4512_, lean_object* v_i_4513_){
_start:
{
uint8_t v_useZeta_boxed_4514_; uint8_t v_preserveMData_boxed_4515_; lean_object* v_res_4516_; 
v_useZeta_boxed_4514_ = lean_unbox(v_useZeta_4509_);
v_preserveMData_boxed_4515_ = lean_unbox(v_preserveMData_4510_);
v_res_4516_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4508_, v_useZeta_boxed_4514_, v_preserveMData_boxed_4515_, v_sz_4511_, v_e_4512_, v_i_4513_);
lean_dec(v_sz_4511_);
lean_dec_ref(v_revArgs_4508_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4517_, lean_object* v_revArgs_4518_, uint8_t v_useZeta_4519_, uint8_t v_preserveMData_4520_){
_start:
{
lean_object* v_sz_4521_; lean_object* v___x_4522_; uint8_t v___x_4523_; 
v_sz_4521_ = lean_array_get_size(v_revArgs_4518_);
v___x_4522_ = lean_unsigned_to_nat(0u);
v___x_4523_ = lean_nat_dec_eq(v_sz_4521_, v___x_4522_);
if (v___x_4523_ == 0)
{
lean_object* v___x_4524_; 
v___x_4524_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4518_, v_useZeta_4519_, v_preserveMData_4520_, v_sz_4521_, v_f_4517_, v___x_4522_);
return v___x_4524_;
}
else
{
return v_f_4517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4525_, lean_object* v_revArgs_4526_, lean_object* v_useZeta_4527_, lean_object* v_preserveMData_4528_){
_start:
{
uint8_t v_useZeta_boxed_4529_; uint8_t v_preserveMData_boxed_4530_; lean_object* v_res_4531_; 
v_useZeta_boxed_4529_ = lean_unbox(v_useZeta_4527_);
v_preserveMData_boxed_4530_ = lean_unbox(v_preserveMData_4528_);
v_res_4531_ = l_Lean_Expr_betaRev(v_f_4525_, v_revArgs_4526_, v_useZeta_boxed_4529_, v_preserveMData_boxed_4530_);
lean_dec_ref(v_revArgs_4526_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4532_, lean_object* v_args_4533_){
_start:
{
lean_object* v___x_4534_; uint8_t v___x_4535_; lean_object* v___x_4536_; 
v___x_4534_ = l_Array_reverse___redArg(v_args_4533_);
v___x_4535_ = 0;
v___x_4536_ = l_Lean_Expr_betaRev(v_f_4532_, v___x_4534_, v___x_4535_, v___x_4535_);
lean_dec_ref(v___x_4534_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4537_){
_start:
{
switch(lean_obj_tag(v_x_4537_))
{
case 6:
{
lean_object* v_body_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v_body_4538_ = lean_ctor_get(v_x_4537_, 2);
v___x_4539_ = l_Lean_Expr_getNumHeadLambdas(v_body_4538_);
v___x_4540_ = lean_unsigned_to_nat(1u);
v___x_4541_ = lean_nat_add(v___x_4539_, v___x_4540_);
lean_dec(v___x_4539_);
return v___x_4541_;
}
case 10:
{
lean_object* v_expr_4542_; 
v_expr_4542_ = lean_ctor_get(v_x_4537_, 1);
v_x_4537_ = v_expr_4542_;
goto _start;
}
default: 
{
lean_object* v___x_4544_; 
v___x_4544_ = lean_unsigned_to_nat(0u);
return v___x_4544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Lean_Expr_getNumHeadLambdas(v_x_4545_);
lean_dec_ref(v_x_4545_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object* v_x_4547_){
_start:
{
switch(lean_obj_tag(v_x_4547_))
{
case 6:
{
lean_object* v_body_4548_; 
v_body_4548_ = lean_ctor_get(v_x_4547_, 2);
v_x_4547_ = v_body_4548_;
goto _start;
}
case 10:
{
lean_object* v_expr_4550_; 
v_expr_4550_ = lean_ctor_get(v_x_4547_, 1);
v_x_4547_ = v_expr_4550_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_4547_);
return v_x_4547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object* v_x_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = l_Lean_Expr_getLambdaBody(v_x_4552_);
lean_dec_ref(v_x_4552_);
return v_res_4553_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4554_, lean_object* v_x_4555_){
_start:
{
switch(lean_obj_tag(v_x_4555_))
{
case 6:
{
uint8_t v___x_4556_; 
v___x_4556_ = 1;
return v___x_4556_;
}
case 8:
{
if (v_useZeta_4554_ == 0)
{
return v_useZeta_4554_;
}
else
{
lean_object* v_body_4557_; 
v_body_4557_ = lean_ctor_get(v_x_4555_, 3);
v_x_4555_ = v_body_4557_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4559_; 
v_expr_4559_ = lean_ctor_get(v_x_4555_, 1);
v_x_4555_ = v_expr_4559_;
goto _start;
}
default: 
{
uint8_t v___x_4561_; 
v___x_4561_ = 0;
return v___x_4561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4562_, lean_object* v_x_4563_){
_start:
{
uint8_t v_useZeta_boxed_4564_; uint8_t v_res_4565_; lean_object* v_r_4566_; 
v_useZeta_boxed_4564_ = lean_unbox(v_useZeta_4562_);
v_res_4565_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4564_, v_x_4563_);
lean_dec_ref(v_x_4563_);
v_r_4566_ = lean_box(v_res_4565_);
return v_r_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4567_){
_start:
{
lean_object* v_f_4568_; uint8_t v___x_4569_; uint8_t v___x_4570_; 
v_f_4568_ = l_Lean_Expr_getAppFn(v_e_4567_);
v___x_4569_ = 0;
v___x_4570_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4569_, v_f_4568_);
if (v___x_4570_ == 0)
{
lean_dec_ref(v_f_4568_);
return v_e_4567_;
}
else
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4571_ = l_Lean_Expr_getAppNumArgs(v_e_4567_);
v___x_4572_ = lean_mk_empty_array_with_capacity(v___x_4571_);
lean_dec(v___x_4571_);
v___x_4573_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4567_, v___x_4572_);
v___x_4574_ = l_Lean_Expr_betaRev(v_f_4568_, v___x_4573_, v___x_4569_, v___x_4569_);
lean_dec_ref(v___x_4573_);
return v___x_4574_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4575_, uint8_t v_useZeta_4576_){
_start:
{
uint8_t v___x_4577_; 
v___x_4577_ = l_Lean_Expr_isApp(v_e_4575_);
if (v___x_4577_ == 0)
{
return v___x_4577_;
}
else
{
lean_object* v___x_4578_; uint8_t v___x_4579_; 
v___x_4578_ = l_Lean_Expr_getAppFn(v_e_4575_);
v___x_4579_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4576_, v___x_4578_);
lean_dec_ref(v___x_4578_);
return v___x_4579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4580_, lean_object* v_useZeta_4581_){
_start:
{
uint8_t v_useZeta_boxed_4582_; uint8_t v_res_4583_; lean_object* v_r_4584_; 
v_useZeta_boxed_4582_ = lean_unbox(v_useZeta_4581_);
v_res_4583_ = l_Lean_Expr_isHeadBetaTarget(v_e_4580_, v_useZeta_boxed_4582_);
lean_dec_ref(v_e_4580_);
v_r_4584_ = lean_box(v_res_4583_);
return v_r_4584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4585_, lean_object* v_x_4586_, lean_object* v_x_4587_){
_start:
{
lean_object* v_f_4589_; 
if (lean_obj_tag(v_x_4585_) == 5)
{
lean_object* v_arg_4593_; 
v_arg_4593_ = lean_ctor_get(v_x_4585_, 1);
if (lean_obj_tag(v_arg_4593_) == 0)
{
lean_object* v_fn_4594_; lean_object* v_deBruijnIndex_4595_; lean_object* v_zero_4596_; uint8_t v_isZero_4597_; 
v_fn_4594_ = lean_ctor_get(v_x_4585_, 0);
v_deBruijnIndex_4595_ = lean_ctor_get(v_arg_4593_, 0);
v_zero_4596_ = lean_unsigned_to_nat(0u);
v_isZero_4597_ = lean_nat_dec_eq(v_x_4586_, v_zero_4596_);
if (v_isZero_4597_ == 1)
{
lean_dec(v_x_4587_);
lean_dec(v_x_4586_);
v_f_4589_ = v_x_4585_;
goto v___jp_4588_;
}
else
{
uint8_t v___x_4598_; 
lean_inc(v_deBruijnIndex_4595_);
lean_inc_ref(v_fn_4594_);
lean_dec_ref_known(v_x_4585_, 2);
v___x_4598_ = lean_nat_dec_eq(v_deBruijnIndex_4595_, v_x_4587_);
lean_dec(v_deBruijnIndex_4595_);
if (v___x_4598_ == 0)
{
lean_object* v___x_4599_; 
lean_dec_ref(v_fn_4594_);
lean_dec(v_x_4587_);
lean_dec(v_x_4586_);
v___x_4599_ = lean_box(0);
return v___x_4599_;
}
else
{
lean_object* v_one_4600_; lean_object* v_n_4601_; lean_object* v___x_4602_; 
v_one_4600_ = lean_unsigned_to_nat(1u);
v_n_4601_ = lean_nat_sub(v_x_4586_, v_one_4600_);
lean_dec(v_x_4586_);
v___x_4602_ = lean_nat_add(v_x_4587_, v_one_4600_);
lean_dec(v_x_4587_);
v_x_4585_ = v_fn_4594_;
v_x_4586_ = v_n_4601_;
v_x_4587_ = v___x_4602_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4604_; uint8_t v_isZero_4605_; 
lean_dec(v_x_4587_);
v_zero_4604_ = lean_unsigned_to_nat(0u);
v_isZero_4605_ = lean_nat_dec_eq(v_x_4586_, v_zero_4604_);
lean_dec(v_x_4586_);
if (v_isZero_4605_ == 1)
{
v_f_4589_ = v_x_4585_;
goto v___jp_4588_;
}
else
{
lean_object* v___x_4606_; 
lean_dec_ref_known(v_x_4585_, 2);
v___x_4606_ = lean_box(0);
return v___x_4606_;
}
}
}
else
{
lean_object* v_zero_4607_; uint8_t v_isZero_4608_; 
lean_dec(v_x_4587_);
v_zero_4607_ = lean_unsigned_to_nat(0u);
v_isZero_4608_ = lean_nat_dec_eq(v_x_4586_, v_zero_4607_);
lean_dec(v_x_4586_);
if (v_isZero_4608_ == 1)
{
v_f_4589_ = v_x_4585_;
goto v___jp_4588_;
}
else
{
lean_object* v___x_4609_; 
lean_dec_ref(v_x_4585_);
v___x_4609_ = lean_box(0);
return v___x_4609_;
}
}
v___jp_4588_:
{
uint8_t v___x_4590_; 
v___x_4590_ = l_Lean_Expr_hasLooseBVars(v_f_4589_);
if (v___x_4590_ == 0)
{
lean_object* v___x_4591_; 
v___x_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4591_, 0, v_f_4589_);
return v___x_4591_;
}
else
{
lean_object* v___x_4592_; 
lean_dec_ref(v_f_4589_);
v___x_4592_ = lean_box(0);
return v___x_4592_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4610_, lean_object* v_x_4611_){
_start:
{
if (lean_obj_tag(v_x_4610_) == 6)
{
lean_object* v_body_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; 
v_body_4612_ = lean_ctor_get(v_x_4610_, 2);
lean_inc_ref(v_body_4612_);
lean_dec_ref_known(v_x_4610_, 3);
v___x_4613_ = lean_unsigned_to_nat(1u);
v___x_4614_ = lean_nat_add(v_x_4611_, v___x_4613_);
lean_dec(v_x_4611_);
v_x_4610_ = v_body_4612_;
v_x_4611_ = v___x_4614_;
goto _start;
}
else
{
lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4616_ = lean_unsigned_to_nat(0u);
v___x_4617_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4610_, v_x_4611_, v___x_4616_);
return v___x_4617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4618_){
_start:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4619_ = lean_unsigned_to_nat(0u);
v___x_4620_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4618_, v___x_4619_);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4621_){
_start:
{
if (lean_obj_tag(v_x_4621_) == 6)
{
lean_object* v_body_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v_body_4622_ = lean_ctor_get(v_x_4621_, 2);
lean_inc_ref(v_body_4622_);
lean_dec_ref_known(v_x_4621_, 3);
v___x_4623_ = lean_unsigned_to_nat(1u);
v___x_4624_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4622_, v___x_4623_);
return v___x_4624_;
}
else
{
lean_object* v___x_4625_; 
lean_dec_ref(v_x_4621_);
v___x_4625_ = lean_box(0);
return v___x_4625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4629_){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; uint8_t v___x_4632_; 
v___x_4630_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4631_ = lean_unsigned_to_nat(2u);
v___x_4632_ = l_Lean_Expr_isAppOfArity(v_e_4629_, v___x_4630_, v___x_4631_);
if (v___x_4632_ == 0)
{
lean_object* v___x_4633_; 
v___x_4633_ = lean_box(0);
return v___x_4633_;
}
else
{
lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4634_ = l_Lean_Expr_appArg_x21(v_e_4629_);
v___x_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
return v___x_4635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4636_);
lean_dec_ref(v_e_4636_);
return v_res_4637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4641_){
_start:
{
lean_object* v___x_4642_; lean_object* v___x_4643_; uint8_t v___x_4644_; 
v___x_4642_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4643_ = lean_unsigned_to_nat(2u);
v___x_4644_ = l_Lean_Expr_isAppOfArity(v_e_4641_, v___x_4642_, v___x_4643_);
if (v___x_4644_ == 0)
{
lean_object* v___x_4645_; 
v___x_4645_ = lean_box(0);
return v___x_4645_;
}
else
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4646_ = l_Lean_Expr_appArg_x21(v_e_4641_);
v___x_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4646_);
return v___x_4647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4648_);
lean_dec_ref(v_e_4648_);
return v_res_4649_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOutParam(lean_object* v_e_4653_){
_start:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; uint8_t v___x_4656_; 
v___x_4654_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4655_ = lean_unsigned_to_nat(1u);
v___x_4656_ = l_Lean_Expr_isAppOfArity(v_e_4653_, v___x_4654_, v___x_4655_);
return v___x_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4657_){
_start:
{
uint8_t v_res_4658_; lean_object* v_r_4659_; 
v_res_4658_ = l_Lean_Expr_isOutParam(v_e_4657_);
lean_dec_ref(v_e_4657_);
v_r_4659_ = lean_box(v_res_4658_);
return v_r_4659_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4663_){
_start:
{
lean_object* v___x_4664_; lean_object* v___x_4665_; uint8_t v___x_4666_; 
v___x_4664_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4665_ = lean_unsigned_to_nat(1u);
v___x_4666_ = l_Lean_Expr_isAppOfArity(v_e_4663_, v___x_4664_, v___x_4665_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4667_){
_start:
{
uint8_t v_res_4668_; lean_object* v_r_4669_; 
v_res_4668_ = l_Lean_Expr_isSemiOutParam(v_e_4667_);
lean_dec_ref(v_e_4667_);
v_r_4669_ = lean_box(v_res_4668_);
return v_r_4669_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4670_){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; uint8_t v___x_4673_; 
v___x_4671_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4672_ = lean_unsigned_to_nat(2u);
v___x_4673_ = l_Lean_Expr_isAppOfArity(v_e_4670_, v___x_4671_, v___x_4672_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4674_){
_start:
{
uint8_t v_res_4675_; lean_object* v_r_4676_; 
v_res_4675_ = l_Lean_Expr_isOptParam(v_e_4674_);
lean_dec_ref(v_e_4674_);
v_r_4676_ = lean_box(v_res_4675_);
return v_r_4676_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4677_){
_start:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; uint8_t v___x_4680_; 
v___x_4678_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4679_ = lean_unsigned_to_nat(2u);
v___x_4680_ = l_Lean_Expr_isAppOfArity(v_e_4677_, v___x_4678_, v___x_4679_);
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4681_){
_start:
{
uint8_t v_res_4682_; lean_object* v_r_4683_; 
v_res_4682_ = l_Lean_Expr_isAutoParam(v_e_4681_);
lean_dec_ref(v_e_4681_);
v_r_4683_ = lean_box(v_res_4682_);
return v_r_4683_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4684_){
_start:
{
lean_object* v___x_4685_; 
v___x_4685_ = l_Lean_Expr_getAppFn(v_e_4684_);
if (lean_obj_tag(v___x_4685_) == 4)
{
lean_object* v_declName_4686_; uint8_t v___y_4688_; lean_object* v___x_4693_; uint8_t v___x_4694_; 
v_declName_4686_ = lean_ctor_get(v___x_4685_, 0);
lean_inc(v_declName_4686_);
lean_dec_ref_known(v___x_4685_, 2);
v___x_4693_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4694_ = lean_name_eq(v_declName_4686_, v___x_4693_);
if (v___x_4694_ == 0)
{
lean_object* v___x_4695_; uint8_t v___x_4696_; 
v___x_4695_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4696_ = lean_name_eq(v_declName_4686_, v___x_4695_);
v___y_4688_ = v___x_4696_;
goto v___jp_4687_;
}
else
{
v___y_4688_ = v___x_4694_;
goto v___jp_4687_;
}
v___jp_4687_:
{
if (v___y_4688_ == 0)
{
lean_object* v___x_4689_; uint8_t v___x_4690_; 
v___x_4689_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4690_ = lean_name_eq(v_declName_4686_, v___x_4689_);
if (v___x_4690_ == 0)
{
lean_object* v___x_4691_; uint8_t v___x_4692_; 
v___x_4691_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4692_ = lean_name_eq(v_declName_4686_, v___x_4691_);
lean_dec(v_declName_4686_);
return v___x_4692_;
}
else
{
lean_dec(v_declName_4686_);
return v___x_4690_;
}
}
else
{
lean_dec(v_declName_4686_);
return v___y_4688_;
}
}
}
else
{
uint8_t v___x_4697_; 
lean_dec_ref(v___x_4685_);
v___x_4697_ = 0;
return v___x_4697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4698_){
_start:
{
uint8_t v_res_4699_; lean_object* v_r_4700_; 
v_res_4699_ = l_Lean_Expr_isTypeAnnotation(v_e_4698_);
lean_dec_ref(v_e_4698_);
v_r_4700_ = lean_box(v_res_4699_);
return v_r_4700_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4701_){
_start:
{
uint8_t v___y_4703_; uint8_t v___y_4707_; uint8_t v___x_4713_; 
v___x_4713_ = l_Lean_Expr_isOptParam(v_e_4701_);
if (v___x_4713_ == 0)
{
uint8_t v___x_4714_; 
v___x_4714_ = l_Lean_Expr_isAutoParam(v_e_4701_);
v___y_4707_ = v___x_4714_;
goto v___jp_4706_;
}
else
{
v___y_4707_ = v___x_4713_;
goto v___jp_4706_;
}
v___jp_4702_:
{
if (v___y_4703_ == 0)
{
return v_e_4701_;
}
else
{
lean_object* v___x_4704_; 
v___x_4704_ = l_Lean_Expr_appArg_x21(v_e_4701_);
lean_dec_ref(v_e_4701_);
v_e_4701_ = v___x_4704_;
goto _start;
}
}
v___jp_4706_:
{
if (v___y_4707_ == 0)
{
uint8_t v___x_4708_; 
v___x_4708_ = l_Lean_Expr_isOutParam(v_e_4701_);
if (v___x_4708_ == 0)
{
uint8_t v___x_4709_; 
v___x_4709_ = l_Lean_Expr_isSemiOutParam(v_e_4701_);
v___y_4703_ = v___x_4709_;
goto v___jp_4702_;
}
else
{
v___y_4703_ = v___x_4708_;
goto v___jp_4702_;
}
}
else
{
lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4710_ = l_Lean_Expr_appFn_x21(v_e_4701_);
lean_dec_ref(v_e_4701_);
v___x_4711_ = l_Lean_Expr_appArg_x21(v___x_4710_);
lean_dec_ref(v___x_4710_);
v_e_4701_ = v___x_4711_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4715_){
_start:
{
lean_object* v___x_4716_; lean_object* v_e_x27_4717_; uint8_t v___x_4718_; 
v___x_4716_ = l_Lean_Expr_consumeMData(v_e_4715_);
v_e_x27_4717_ = lean_expr_consume_type_annotations(v___x_4716_);
v___x_4718_ = lean_expr_eqv(v_e_x27_4717_, v_e_4715_);
if (v___x_4718_ == 0)
{
lean_dec_ref(v_e_4715_);
v_e_4715_ = v_e_x27_4717_;
goto _start;
}
else
{
lean_dec_ref(v_e_x27_4717_);
return v_e_4715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4720_){
_start:
{
lean_object* v_fn_4721_; lean_object* v___x_4722_; 
v_fn_4721_ = lean_ctor_get(v_e_4720_, 0);
lean_inc_ref(v_fn_4721_);
lean_dec_ref(v_e_4720_);
v___x_4722_ = l_Lean_Expr_cleanupAnnotations(v_fn_4721_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* v_e_4723_, lean_object* v_h_4724_){
_start:
{
lean_object* v___x_4725_; 
v___x_4725_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4723_);
return v___x_4725_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4729_){
_start:
{
lean_object* v___x_4730_; lean_object* v___x_4731_; uint8_t v___x_4732_; 
v___x_4730_ = l_Lean_Expr_cleanupAnnotations(v_e_4729_);
v___x_4731_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4732_ = l_Lean_Expr_isConstOf(v___x_4730_, v___x_4731_);
lean_dec_ref(v___x_4730_);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4733_){
_start:
{
uint8_t v_res_4734_; lean_object* v_r_4735_; 
v_res_4734_ = l_Lean_Expr_isFalse(v_e_4733_);
v_r_4735_ = lean_box(v_res_4734_);
return v_r_4735_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4739_){
_start:
{
lean_object* v___x_4740_; lean_object* v___x_4741_; uint8_t v___x_4742_; 
v___x_4740_ = l_Lean_Expr_cleanupAnnotations(v_e_4739_);
v___x_4741_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4742_ = l_Lean_Expr_isConstOf(v___x_4740_, v___x_4741_);
lean_dec_ref(v___x_4740_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4743_){
_start:
{
uint8_t v_res_4744_; lean_object* v_r_4745_; 
v_res_4744_ = l_Lean_Expr_isTrue(v_e_4743_);
v_r_4745_ = lean_box(v_res_4744_);
return v_r_4745_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object* v_e_4750_){
_start:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; uint8_t v___x_4753_; 
v___x_4751_ = l_Lean_Expr_cleanupAnnotations(v_e_4750_);
v___x_4752_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_4753_ = l_Lean_Expr_isConstOf(v___x_4751_, v___x_4752_);
lean_dec_ref(v___x_4751_);
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object* v_e_4754_){
_start:
{
uint8_t v_res_4755_; lean_object* v_r_4756_; 
v_res_4755_ = l_Lean_Expr_isBoolFalse(v_e_4754_);
v_r_4756_ = lean_box(v_res_4755_);
return v_r_4756_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object* v_e_4760_){
_start:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; uint8_t v___x_4763_; 
v___x_4761_ = l_Lean_Expr_cleanupAnnotations(v_e_4760_);
v___x_4762_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_4763_ = l_Lean_Expr_isConstOf(v___x_4761_, v___x_4762_);
lean_dec_ref(v___x_4761_);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object* v_e_4764_){
_start:
{
uint8_t v_res_4765_; lean_object* v_r_4766_; 
v_res_4765_ = l_Lean_Expr_isBoolTrue(v_e_4764_);
v_r_4766_ = lean_box(v_res_4765_);
return v_r_4766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* v_x_4767_){
_start:
{
switch(lean_obj_tag(v_x_4767_))
{
case 10:
{
lean_object* v_expr_4768_; 
v_expr_4768_ = lean_ctor_get(v_x_4767_, 1);
lean_inc_ref(v_expr_4768_);
lean_dec_ref_known(v_x_4767_, 2);
v_x_4767_ = v_expr_4768_;
goto _start;
}
case 7:
{
lean_object* v_body_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; 
v_body_4770_ = lean_ctor_get(v_x_4767_, 2);
lean_inc_ref(v_body_4770_);
lean_dec_ref_known(v_x_4767_, 3);
v___x_4771_ = l_Lean_Expr_getForallArity(v_body_4770_);
v___x_4772_ = lean_unsigned_to_nat(1u);
v___x_4773_ = lean_nat_add(v___x_4771_, v___x_4772_);
lean_dec(v___x_4771_);
return v___x_4773_;
}
default: 
{
uint8_t v___x_4774_; uint8_t v___x_4775_; 
v___x_4774_ = 0;
v___x_4775_ = l_Lean_Expr_isHeadBetaTarget(v_x_4767_, v___x_4774_);
if (v___x_4775_ == 0)
{
lean_object* v_e_x27_4776_; uint8_t v___x_4777_; 
lean_inc_ref(v_x_4767_);
v_e_x27_4776_ = l_Lean_Expr_cleanupAnnotations(v_x_4767_);
v___x_4777_ = lean_expr_eqv(v_x_4767_, v_e_x27_4776_);
lean_dec_ref(v_x_4767_);
if (v___x_4777_ == 0)
{
v_x_4767_ = v_e_x27_4776_;
goto _start;
}
else
{
lean_object* v___x_4779_; 
lean_dec_ref(v_e_x27_4776_);
v___x_4779_ = lean_unsigned_to_nat(0u);
return v___x_4779_;
}
}
else
{
lean_object* v___x_4780_; 
v___x_4780_ = l_Lean_Expr_headBeta(v_x_4767_);
v_x_4767_ = v___x_4780_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4782_){
_start:
{
lean_object* v___x_4783_; uint8_t v___x_4784_; 
v___x_4783_ = l_Lean_Expr_cleanupAnnotations(v_e_4782_);
v___x_4784_ = l_Lean_Expr_isApp(v___x_4783_);
if (v___x_4784_ == 0)
{
lean_object* v___x_4785_; 
lean_dec_ref(v___x_4783_);
v___x_4785_ = lean_box(0);
return v___x_4785_;
}
else
{
lean_object* v___x_4786_; uint8_t v___x_4787_; 
v___x_4786_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4783_);
v___x_4787_ = l_Lean_Expr_isApp(v___x_4786_);
if (v___x_4787_ == 0)
{
lean_object* v___x_4788_; 
lean_dec_ref(v___x_4786_);
v___x_4788_ = lean_box(0);
return v___x_4788_;
}
else
{
lean_object* v_arg_4789_; lean_object* v___x_4790_; uint8_t v___x_4791_; 
v_arg_4789_ = lean_ctor_get(v___x_4786_, 1);
lean_inc_ref(v_arg_4789_);
v___x_4790_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4786_);
v___x_4791_ = l_Lean_Expr_isApp(v___x_4790_);
if (v___x_4791_ == 0)
{
lean_object* v___x_4792_; 
lean_dec_ref(v___x_4790_);
lean_dec_ref(v_arg_4789_);
v___x_4792_ = lean_box(0);
return v___x_4792_;
}
else
{
lean_object* v___x_4793_; lean_object* v___x_4794_; uint8_t v___x_4795_; 
v___x_4793_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4790_);
v___x_4794_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4795_ = l_Lean_Expr_isConstOf(v___x_4793_, v___x_4794_);
lean_dec_ref(v___x_4793_);
if (v___x_4795_ == 0)
{
lean_object* v___x_4796_; 
lean_dec_ref(v_arg_4789_);
v___x_4796_ = lean_box(0);
return v___x_4796_;
}
else
{
if (lean_obj_tag(v_arg_4789_) == 9)
{
lean_object* v_a_4797_; 
v_a_4797_ = lean_ctor_get(v_arg_4789_, 0);
lean_inc_ref(v_a_4797_);
lean_dec_ref_known(v_arg_4789_, 1);
if (lean_obj_tag(v_a_4797_) == 0)
{
lean_object* v_val_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
v_val_4798_ = lean_ctor_get(v_a_4797_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v_a_4797_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v_a_4797_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_val_4798_);
lean_dec(v_a_4797_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
lean_ctor_set_tag(v___x_4800_, 1);
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_val_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
else
{
lean_object* v___x_4806_; 
lean_dec_ref(v_a_4797_);
v___x_4806_ = lean_box(0);
return v___x_4806_;
}
}
else
{
lean_object* v___x_4807_; 
lean_dec_ref(v_arg_4789_);
v___x_4807_ = lean_box(0);
return v___x_4807_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4813_){
_start:
{
lean_object* v___x_4826_; uint8_t v___x_4827_; 
lean_inc_ref(v_e_4813_);
v___x_4826_ = l_Lean_Expr_cleanupAnnotations(v_e_4813_);
v___x_4827_ = l_Lean_Expr_isApp(v___x_4826_);
if (v___x_4827_ == 0)
{
lean_dec_ref(v___x_4826_);
goto v___jp_4814_;
}
else
{
lean_object* v_arg_4828_; lean_object* v___x_4829_; uint8_t v___x_4830_; 
v_arg_4828_ = lean_ctor_get(v___x_4826_, 1);
lean_inc_ref(v_arg_4828_);
v___x_4829_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4826_);
v___x_4830_ = l_Lean_Expr_isApp(v___x_4829_);
if (v___x_4830_ == 0)
{
lean_dec_ref(v___x_4829_);
lean_dec_ref(v_arg_4828_);
goto v___jp_4814_;
}
else
{
lean_object* v___x_4831_; uint8_t v___x_4832_; 
v___x_4831_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4829_);
v___x_4832_ = l_Lean_Expr_isApp(v___x_4831_);
if (v___x_4832_ == 0)
{
lean_dec_ref(v___x_4831_);
lean_dec_ref(v_arg_4828_);
goto v___jp_4814_;
}
else
{
lean_object* v___x_4833_; lean_object* v___x_4834_; uint8_t v___x_4835_; 
v___x_4833_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4831_);
v___x_4834_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4835_ = l_Lean_Expr_isConstOf(v___x_4833_, v___x_4834_);
lean_dec_ref(v___x_4833_);
if (v___x_4835_ == 0)
{
lean_dec_ref(v_arg_4828_);
goto v___jp_4814_;
}
else
{
lean_object* v___x_4836_; 
lean_dec_ref(v_e_4813_);
v___x_4836_ = l_Lean_Expr_nat_x3f(v_arg_4828_);
if (lean_obj_tag(v___x_4836_) == 0)
{
lean_object* v___x_4837_; 
v___x_4837_ = lean_box(0);
return v___x_4837_;
}
else
{
lean_object* v_val_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4850_; 
v_val_4838_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4850_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4850_ == 0)
{
v___x_4840_ = v___x_4836_;
v_isShared_4841_ = v_isSharedCheck_4850_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_val_4838_);
lean_dec(v___x_4836_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4850_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4842_; uint8_t v___x_4843_; 
v___x_4842_ = lean_unsigned_to_nat(0u);
v___x_4843_ = lean_nat_dec_eq(v_val_4838_, v___x_4842_);
if (v___x_4843_ == 0)
{
lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4847_; 
v___x_4844_ = lean_nat_to_int(v_val_4838_);
v___x_4845_ = lean_int_neg(v___x_4844_);
lean_dec(v___x_4844_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 0, v___x_4845_);
v___x_4847_ = v___x_4840_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4845_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
else
{
lean_object* v___x_4849_; 
lean_del_object(v___x_4840_);
lean_dec(v_val_4838_);
v___x_4849_ = lean_box(0);
return v___x_4849_;
}
}
}
}
}
}
}
v___jp_4814_:
{
lean_object* v___x_4815_; 
v___x_4815_ = l_Lean_Expr_nat_x3f(v_e_4813_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v___x_4816_; 
v___x_4816_ = lean_box(0);
return v___x_4816_;
}
else
{
lean_object* v_val_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4825_; 
v_val_4817_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4819_ = v___x_4815_;
v_isShared_4820_ = v_isSharedCheck_4825_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_val_4817_);
lean_dec(v___x_4815_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4825_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4821_; lean_object* v___x_4823_; 
v___x_4821_ = lean_nat_to_int(v_val_4817_);
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 0, v___x_4821_);
v___x_4823_ = v___x_4819_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v___x_4821_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4851_, lean_object* v_e_4852_){
_start:
{
uint8_t v___x_4853_; lean_object* v_d_4855_; lean_object* v_b_4856_; 
v___x_4853_ = l_Lean_Expr_hasFVar(v_e_4852_);
if (v___x_4853_ == 0)
{
lean_dec_ref(v_e_4852_);
lean_dec_ref(v_p_4851_);
return v___x_4853_;
}
else
{
switch(lean_obj_tag(v_e_4852_))
{
case 7:
{
lean_object* v_binderType_4859_; lean_object* v_body_4860_; 
v_binderType_4859_ = lean_ctor_get(v_e_4852_, 1);
lean_inc_ref(v_binderType_4859_);
v_body_4860_ = lean_ctor_get(v_e_4852_, 2);
lean_inc_ref(v_body_4860_);
lean_dec_ref_known(v_e_4852_, 3);
v_d_4855_ = v_binderType_4859_;
v_b_4856_ = v_body_4860_;
goto v___jp_4854_;
}
case 6:
{
lean_object* v_binderType_4861_; lean_object* v_body_4862_; 
v_binderType_4861_ = lean_ctor_get(v_e_4852_, 1);
lean_inc_ref(v_binderType_4861_);
v_body_4862_ = lean_ctor_get(v_e_4852_, 2);
lean_inc_ref(v_body_4862_);
lean_dec_ref_known(v_e_4852_, 3);
v_d_4855_ = v_binderType_4861_;
v_b_4856_ = v_body_4862_;
goto v___jp_4854_;
}
case 10:
{
lean_object* v_expr_4863_; 
v_expr_4863_ = lean_ctor_get(v_e_4852_, 1);
lean_inc_ref(v_expr_4863_);
lean_dec_ref_known(v_e_4852_, 2);
v_e_4852_ = v_expr_4863_;
goto _start;
}
case 8:
{
lean_object* v_type_4865_; lean_object* v_value_4866_; lean_object* v_body_4867_; uint8_t v___x_4868_; 
v_type_4865_ = lean_ctor_get(v_e_4852_, 1);
lean_inc_ref(v_type_4865_);
v_value_4866_ = lean_ctor_get(v_e_4852_, 2);
lean_inc_ref(v_value_4866_);
v_body_4867_ = lean_ctor_get(v_e_4852_, 3);
lean_inc_ref(v_body_4867_);
lean_dec_ref_known(v_e_4852_, 4);
lean_inc_ref(v_p_4851_);
v___x_4868_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4851_, v_type_4865_);
if (v___x_4868_ == 0)
{
uint8_t v___x_4869_; 
lean_inc_ref(v_p_4851_);
v___x_4869_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4851_, v_value_4866_);
if (v___x_4869_ == 0)
{
v_e_4852_ = v_body_4867_;
goto _start;
}
else
{
lean_dec_ref(v_body_4867_);
lean_dec_ref(v_p_4851_);
return v___x_4853_;
}
}
else
{
lean_dec_ref(v_body_4867_);
lean_dec_ref(v_value_4866_);
lean_dec_ref(v_p_4851_);
return v___x_4853_;
}
}
case 5:
{
lean_object* v_fn_4871_; lean_object* v_arg_4872_; uint8_t v___x_4873_; 
v_fn_4871_ = lean_ctor_get(v_e_4852_, 0);
lean_inc_ref(v_fn_4871_);
v_arg_4872_ = lean_ctor_get(v_e_4852_, 1);
lean_inc_ref(v_arg_4872_);
lean_dec_ref_known(v_e_4852_, 2);
lean_inc_ref(v_p_4851_);
v___x_4873_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4851_, v_fn_4871_);
if (v___x_4873_ == 0)
{
v_e_4852_ = v_arg_4872_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4872_);
lean_dec_ref(v_p_4851_);
return v___x_4853_;
}
}
case 11:
{
lean_object* v_struct_4875_; 
v_struct_4875_ = lean_ctor_get(v_e_4852_, 2);
lean_inc_ref(v_struct_4875_);
lean_dec_ref_known(v_e_4852_, 3);
v_e_4852_ = v_struct_4875_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4877_; lean_object* v___x_4878_; uint8_t v___x_4879_; 
v_fvarId_4877_ = lean_ctor_get(v_e_4852_, 0);
lean_inc(v_fvarId_4877_);
lean_dec_ref_known(v_e_4852_, 1);
v___x_4878_ = lean_apply_1(v_p_4851_, v_fvarId_4877_);
v___x_4879_ = lean_unbox(v___x_4878_);
return v___x_4879_;
}
default: 
{
uint8_t v___x_4880_; 
lean_dec_ref(v_e_4852_);
lean_dec_ref(v_p_4851_);
v___x_4880_ = 0;
return v___x_4880_;
}
}
}
v___jp_4854_:
{
uint8_t v___x_4857_; 
lean_inc_ref(v_p_4851_);
v___x_4857_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4851_, v_d_4855_);
if (v___x_4857_ == 0)
{
v_e_4852_ = v_b_4856_;
goto _start;
}
else
{
lean_dec_ref(v_b_4856_);
lean_dec_ref(v_p_4851_);
return v___x_4853_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_4881_, lean_object* v_e_4882_){
_start:
{
uint8_t v_res_4883_; lean_object* v_r_4884_; 
v_res_4883_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4881_, v_e_4882_);
v_r_4884_ = lean_box(v_res_4883_);
return v_r_4884_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_4885_, lean_object* v_p_4886_){
_start:
{
uint8_t v___x_4887_; 
v___x_4887_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4886_, v_e_4885_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_4888_, lean_object* v_p_4889_){
_start:
{
uint8_t v_res_4890_; lean_object* v_r_4891_; 
v_res_4890_ = l_Lean_Expr_hasAnyFVar(v_e_4888_, v_p_4889_);
v_r_4891_ = lean_box(v_res_4890_);
return v_r_4891_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_4892_, lean_object* v_e_4893_){
_start:
{
uint8_t v___x_4894_; lean_object* v_d_4896_; lean_object* v_b_4897_; 
v___x_4894_ = l_Lean_Expr_hasFVar(v_e_4893_);
if (v___x_4894_ == 0)
{
return v___x_4894_;
}
else
{
switch(lean_obj_tag(v_e_4893_))
{
case 7:
{
lean_object* v_binderType_4900_; lean_object* v_body_4901_; 
v_binderType_4900_ = lean_ctor_get(v_e_4893_, 1);
v_body_4901_ = lean_ctor_get(v_e_4893_, 2);
v_d_4896_ = v_binderType_4900_;
v_b_4897_ = v_body_4901_;
goto v___jp_4895_;
}
case 6:
{
lean_object* v_binderType_4902_; lean_object* v_body_4903_; 
v_binderType_4902_ = lean_ctor_get(v_e_4893_, 1);
v_body_4903_ = lean_ctor_get(v_e_4893_, 2);
v_d_4896_ = v_binderType_4902_;
v_b_4897_ = v_body_4903_;
goto v___jp_4895_;
}
case 10:
{
lean_object* v_expr_4904_; 
v_expr_4904_ = lean_ctor_get(v_e_4893_, 1);
v_e_4893_ = v_expr_4904_;
goto _start;
}
case 8:
{
lean_object* v_type_4906_; lean_object* v_value_4907_; lean_object* v_body_4908_; uint8_t v___x_4909_; 
v_type_4906_ = lean_ctor_get(v_e_4893_, 1);
v_value_4907_ = lean_ctor_get(v_e_4893_, 2);
v_body_4908_ = lean_ctor_get(v_e_4893_, 3);
v___x_4909_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4892_, v_type_4906_);
if (v___x_4909_ == 0)
{
uint8_t v___x_4910_; 
v___x_4910_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4892_, v_value_4907_);
if (v___x_4910_ == 0)
{
v_e_4893_ = v_body_4908_;
goto _start;
}
else
{
return v___x_4894_;
}
}
else
{
return v___x_4894_;
}
}
case 5:
{
lean_object* v_fn_4912_; lean_object* v_arg_4913_; uint8_t v___x_4914_; 
v_fn_4912_ = lean_ctor_get(v_e_4893_, 0);
v_arg_4913_ = lean_ctor_get(v_e_4893_, 1);
v___x_4914_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4892_, v_fn_4912_);
if (v___x_4914_ == 0)
{
v_e_4893_ = v_arg_4913_;
goto _start;
}
else
{
return v___x_4894_;
}
}
case 11:
{
lean_object* v_struct_4916_; 
v_struct_4916_ = lean_ctor_get(v_e_4893_, 2);
v_e_4893_ = v_struct_4916_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4918_; uint8_t v___x_4919_; 
v_fvarId_4918_ = lean_ctor_get(v_e_4893_, 0);
v___x_4919_ = lean_name_eq(v_fvarId_4918_, v_fvarId_4892_);
return v___x_4919_;
}
default: 
{
uint8_t v___x_4920_; 
v___x_4920_ = 0;
return v___x_4920_;
}
}
}
v___jp_4895_:
{
uint8_t v___x_4898_; 
v___x_4898_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4892_, v_d_4896_);
if (v___x_4898_ == 0)
{
v_e_4893_ = v_b_4897_;
goto _start;
}
else
{
return v___x_4894_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_4921_, lean_object* v_e_4922_){
_start:
{
uint8_t v_res_4923_; lean_object* v_r_4924_; 
v_res_4923_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4921_, v_e_4922_);
lean_dec_ref(v_e_4922_);
lean_dec(v_fvarId_4921_);
v_r_4924_ = lean_box(v_res_4923_);
return v_r_4924_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_4925_, lean_object* v_fvarId_4926_){
_start:
{
uint8_t v___x_4927_; 
v___x_4927_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4926_, v_e_4925_);
return v___x_4927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_4928_, lean_object* v_fvarId_4929_){
_start:
{
uint8_t v_res_4930_; lean_object* v_r_4931_; 
v_res_4930_ = l_Lean_Expr_containsFVar(v_e_4928_, v_fvarId_4929_);
lean_dec(v_fvarId_4929_);
lean_dec_ref(v_e_4928_);
v_r_4931_ = lean_box(v_res_4930_);
return v_r_4931_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4933_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_4934_ = lean_unsigned_to_nat(18u);
v___x_4935_ = lean_unsigned_to_nat(1847u);
v___x_4936_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_4937_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4938_ = l_mkPanicMessageWithDecl(v___x_4937_, v___x_4936_, v___x_4935_, v___x_4934_, v___x_4933_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_4939_, lean_object* v_newFn_4940_, lean_object* v_newArg_4941_){
_start:
{
uint8_t v___y_4943_; 
if (lean_obj_tag(v_e_4939_) == 5)
{
lean_object* v_fn_4945_; lean_object* v_arg_4946_; size_t v___x_4947_; size_t v___x_4948_; uint8_t v___x_4949_; 
v_fn_4945_ = lean_ctor_get(v_e_4939_, 0);
v_arg_4946_ = lean_ctor_get(v_e_4939_, 1);
v___x_4947_ = lean_ptr_addr(v_fn_4945_);
v___x_4948_ = lean_ptr_addr(v_newFn_4940_);
v___x_4949_ = lean_usize_dec_eq(v___x_4947_, v___x_4948_);
if (v___x_4949_ == 0)
{
v___y_4943_ = v___x_4949_;
goto v___jp_4942_;
}
else
{
size_t v___x_4950_; size_t v___x_4951_; uint8_t v___x_4952_; 
v___x_4950_ = lean_ptr_addr(v_arg_4946_);
v___x_4951_ = lean_ptr_addr(v_newArg_4941_);
v___x_4952_ = lean_usize_dec_eq(v___x_4950_, v___x_4951_);
v___y_4943_ = v___x_4952_;
goto v___jp_4942_;
}
}
else
{
lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
lean_dec_ref(v_newArg_4941_);
lean_dec_ref(v_newFn_4940_);
v___x_4953_ = l_Lean_instInhabitedExpr;
v___x_4954_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_4955_ = l_panic___redArg(v___x_4953_, v___x_4954_);
return v___x_4955_;
}
v___jp_4942_:
{
if (v___y_4943_ == 0)
{
lean_object* v___x_4944_; 
v___x_4944_ = l_Lean_Expr_app___override(v_newFn_4940_, v_newArg_4941_);
return v___x_4944_;
}
else
{
lean_dec_ref(v_newArg_4941_);
lean_dec_ref(v_newFn_4940_);
lean_inc_ref(v_e_4939_);
return v_e_4939_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_4956_, lean_object* v_newFn_4957_, lean_object* v_newArg_4958_){
_start:
{
lean_object* v_res_4959_; 
v_res_4959_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_4956_, v_newFn_4957_, v_newArg_4958_);
lean_dec_ref(v_e_4956_);
return v_res_4959_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4961_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_4962_ = lean_unsigned_to_nat(20u);
v___x_4963_ = lean_unsigned_to_nat(1858u);
v___x_4964_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_4965_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4966_ = l_mkPanicMessageWithDecl(v___x_4965_, v___x_4964_, v___x_4963_, v___x_4962_, v___x_4961_);
return v___x_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_4967_, lean_object* v_fvarIdNew_4968_){
_start:
{
if (lean_obj_tag(v_e_4967_) == 1)
{
lean_object* v_fvarId_4969_; uint8_t v___x_4970_; 
v_fvarId_4969_ = lean_ctor_get(v_e_4967_, 0);
v___x_4970_ = lean_name_eq(v_fvarId_4969_, v_fvarIdNew_4968_);
if (v___x_4970_ == 0)
{
lean_object* v___x_4971_; 
v___x_4971_ = l_Lean_Expr_fvar___override(v_fvarIdNew_4968_);
return v___x_4971_;
}
else
{
lean_dec(v_fvarIdNew_4968_);
lean_inc_ref(v_e_4967_);
return v_e_4967_;
}
}
else
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
lean_dec(v_fvarIdNew_4968_);
v___x_4972_ = l_Lean_instInhabitedExpr;
v___x_4973_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_4974_ = l_panic___redArg(v___x_4972_, v___x_4973_);
return v___x_4974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_4975_, lean_object* v_fvarIdNew_4976_){
_start:
{
lean_object* v_res_4977_; 
v_res_4977_ = l_Lean_Expr_updateFVar_x21(v_e_4975_, v_fvarIdNew_4976_);
lean_dec_ref(v_e_4975_);
return v_res_4977_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4979_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_4980_ = lean_unsigned_to_nat(18u);
v___x_4981_ = lean_unsigned_to_nat(1863u);
v___x_4982_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_4983_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4984_ = l_mkPanicMessageWithDecl(v___x_4983_, v___x_4982_, v___x_4981_, v___x_4980_, v___x_4979_);
return v___x_4984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_4985_, lean_object* v_newLevels_4986_){
_start:
{
if (lean_obj_tag(v_e_4985_) == 4)
{
lean_object* v_declName_4987_; lean_object* v_us_4988_; uint8_t v___x_4989_; 
v_declName_4987_ = lean_ctor_get(v_e_4985_, 0);
v_us_4988_ = lean_ctor_get(v_e_4985_, 1);
v___x_4989_ = l_ptrEqList___redArg(v_us_4988_, v_newLevels_4986_);
if (v___x_4989_ == 0)
{
lean_object* v___x_4990_; 
lean_inc(v_declName_4987_);
lean_dec_ref_known(v_e_4985_, 2);
v___x_4990_ = l_Lean_Expr_const___override(v_declName_4987_, v_newLevels_4986_);
return v___x_4990_;
}
else
{
lean_dec(v_newLevels_4986_);
return v_e_4985_;
}
}
else
{
lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; 
lean_dec(v_newLevels_4986_);
lean_dec_ref(v_e_4985_);
v___x_4991_ = l_Lean_instInhabitedExpr;
v___x_4992_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_4993_ = l_panic___redArg(v___x_4991_, v___x_4992_);
return v___x_4993_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; 
v___x_4996_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_4997_ = lean_unsigned_to_nat(14u);
v___x_4998_ = lean_unsigned_to_nat(1874u);
v___x_4999_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_5000_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5001_ = l_mkPanicMessageWithDecl(v___x_5000_, v___x_4999_, v___x_4998_, v___x_4997_, v___x_4996_);
return v___x_5001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_5002_, lean_object* v_u_x27_5003_){
_start:
{
if (lean_obj_tag(v_e_5002_) == 3)
{
lean_object* v_u_5004_; size_t v___x_5005_; size_t v___x_5006_; uint8_t v___x_5007_; 
v_u_5004_ = lean_ctor_get(v_e_5002_, 0);
v___x_5005_ = lean_ptr_addr(v_u_5004_);
v___x_5006_ = lean_ptr_addr(v_u_x27_5003_);
v___x_5007_ = lean_usize_dec_eq(v___x_5005_, v___x_5006_);
if (v___x_5007_ == 0)
{
lean_object* v___x_5008_; 
v___x_5008_ = l_Lean_Expr_sort___override(v_u_x27_5003_);
return v___x_5008_;
}
else
{
lean_dec(v_u_x27_5003_);
lean_inc_ref(v_e_5002_);
return v_e_5002_;
}
}
else
{
lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; 
lean_dec(v_u_x27_5003_);
v___x_5009_ = l_Lean_instInhabitedExpr;
v___x_5010_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_5011_ = l_panic___redArg(v___x_5009_, v___x_5010_);
return v___x_5011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_5012_, lean_object* v_u_x27_5013_){
_start:
{
lean_object* v_res_5014_; 
v_res_5014_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_5012_, v_u_x27_5013_);
lean_dec_ref(v_e_5012_);
return v_res_5014_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5017_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_5018_ = lean_unsigned_to_nat(17u);
v___x_5019_ = lean_unsigned_to_nat(1885u);
v___x_5020_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_5021_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5022_ = l_mkPanicMessageWithDecl(v___x_5021_, v___x_5020_, v___x_5019_, v___x_5018_, v___x_5017_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_5023_, lean_object* v_newExpr_5024_){
_start:
{
if (lean_obj_tag(v_e_5023_) == 10)
{
lean_object* v_data_5025_; lean_object* v_expr_5026_; size_t v___x_5027_; size_t v___x_5028_; uint8_t v___x_5029_; 
v_data_5025_ = lean_ctor_get(v_e_5023_, 0);
v_expr_5026_ = lean_ctor_get(v_e_5023_, 1);
v___x_5027_ = lean_ptr_addr(v_expr_5026_);
v___x_5028_ = lean_ptr_addr(v_newExpr_5024_);
v___x_5029_ = lean_usize_dec_eq(v___x_5027_, v___x_5028_);
if (v___x_5029_ == 0)
{
lean_object* v___x_5030_; 
lean_inc(v_data_5025_);
lean_dec_ref_known(v_e_5023_, 2);
v___x_5030_ = l_Lean_Expr_mdata___override(v_data_5025_, v_newExpr_5024_);
return v___x_5030_;
}
else
{
lean_dec_ref(v_newExpr_5024_);
return v_e_5023_;
}
}
else
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; 
lean_dec_ref(v_newExpr_5024_);
lean_dec_ref(v_e_5023_);
v___x_5031_ = l_Lean_instInhabitedExpr;
v___x_5032_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_5033_ = l_panic___redArg(v___x_5031_, v___x_5032_);
return v___x_5033_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5036_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_5037_ = lean_unsigned_to_nat(18u);
v___x_5038_ = lean_unsigned_to_nat(1896u);
v___x_5039_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_5040_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5041_ = l_mkPanicMessageWithDecl(v___x_5040_, v___x_5039_, v___x_5038_, v___x_5037_, v___x_5036_);
return v___x_5041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_5042_, lean_object* v_newExpr_5043_){
_start:
{
if (lean_obj_tag(v_e_5042_) == 11)
{
lean_object* v_typeName_5044_; lean_object* v_idx_5045_; lean_object* v_struct_5046_; size_t v___x_5047_; size_t v___x_5048_; uint8_t v___x_5049_; 
v_typeName_5044_ = lean_ctor_get(v_e_5042_, 0);
v_idx_5045_ = lean_ctor_get(v_e_5042_, 1);
v_struct_5046_ = lean_ctor_get(v_e_5042_, 2);
v___x_5047_ = lean_ptr_addr(v_struct_5046_);
v___x_5048_ = lean_ptr_addr(v_newExpr_5043_);
v___x_5049_ = lean_usize_dec_eq(v___x_5047_, v___x_5048_);
if (v___x_5049_ == 0)
{
lean_object* v___x_5050_; 
lean_inc(v_idx_5045_);
lean_inc(v_typeName_5044_);
lean_dec_ref_known(v_e_5042_, 3);
v___x_5050_ = l_Lean_Expr_proj___override(v_typeName_5044_, v_idx_5045_, v_newExpr_5043_);
return v___x_5050_;
}
else
{
lean_dec_ref(v_newExpr_5043_);
return v_e_5042_;
}
}
else
{
lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
lean_dec_ref(v_newExpr_5043_);
lean_dec_ref(v_e_5042_);
v___x_5051_ = l_Lean_instInhabitedExpr;
v___x_5052_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_5053_ = l_panic___redArg(v___x_5051_, v___x_5052_);
return v___x_5053_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; 
v___x_5056_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5057_ = lean_unsigned_to_nat(23u);
v___x_5058_ = lean_unsigned_to_nat(1911u);
v___x_5059_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_5060_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5061_ = l_mkPanicMessageWithDecl(v___x_5060_, v___x_5059_, v___x_5058_, v___x_5057_, v___x_5056_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_5062_, uint8_t v_newBinfo_5063_, lean_object* v_newDomain_5064_, lean_object* v_newBody_5065_){
_start:
{
if (lean_obj_tag(v_e_5062_) == 7)
{
lean_object* v_binderName_5066_; lean_object* v_binderType_5067_; lean_object* v_body_5068_; uint8_t v_binderInfo_5069_; uint8_t v___y_5071_; size_t v___x_5075_; size_t v___x_5076_; uint8_t v___x_5077_; 
v_binderName_5066_ = lean_ctor_get(v_e_5062_, 0);
v_binderType_5067_ = lean_ctor_get(v_e_5062_, 1);
v_body_5068_ = lean_ctor_get(v_e_5062_, 2);
v_binderInfo_5069_ = lean_ctor_get_uint8(v_e_5062_, sizeof(void*)*3 + 8);
v___x_5075_ = lean_ptr_addr(v_binderType_5067_);
v___x_5076_ = lean_ptr_addr(v_newDomain_5064_);
v___x_5077_ = lean_usize_dec_eq(v___x_5075_, v___x_5076_);
if (v___x_5077_ == 0)
{
v___y_5071_ = v___x_5077_;
goto v___jp_5070_;
}
else
{
size_t v___x_5078_; size_t v___x_5079_; uint8_t v___x_5080_; 
v___x_5078_ = lean_ptr_addr(v_body_5068_);
v___x_5079_ = lean_ptr_addr(v_newBody_5065_);
v___x_5080_ = lean_usize_dec_eq(v___x_5078_, v___x_5079_);
v___y_5071_ = v___x_5080_;
goto v___jp_5070_;
}
v___jp_5070_:
{
if (v___y_5071_ == 0)
{
lean_object* v___x_5072_; 
lean_inc(v_binderName_5066_);
lean_dec_ref_known(v_e_5062_, 3);
v___x_5072_ = l_Lean_Expr_forallE___override(v_binderName_5066_, v_newDomain_5064_, v_newBody_5065_, v_newBinfo_5063_);
return v___x_5072_;
}
else
{
uint8_t v___x_5073_; 
v___x_5073_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5069_, v_newBinfo_5063_);
if (v___x_5073_ == 0)
{
lean_object* v___x_5074_; 
lean_inc(v_binderName_5066_);
lean_dec_ref_known(v_e_5062_, 3);
v___x_5074_ = l_Lean_Expr_forallE___override(v_binderName_5066_, v_newDomain_5064_, v_newBody_5065_, v_newBinfo_5063_);
return v___x_5074_;
}
else
{
lean_dec_ref(v_newBody_5065_);
lean_dec_ref(v_newDomain_5064_);
return v_e_5062_;
}
}
}
}
else
{
lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; 
lean_dec_ref(v_newBody_5065_);
lean_dec_ref(v_newDomain_5064_);
lean_dec_ref(v_e_5062_);
v___x_5081_ = l_Lean_instInhabitedExpr;
v___x_5082_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_5083_ = l_panic___redArg(v___x_5081_, v___x_5082_);
return v___x_5083_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_5084_, lean_object* v_newBinfo_5085_, lean_object* v_newDomain_5086_, lean_object* v_newBody_5087_){
_start:
{
uint8_t v_newBinfo_boxed_5088_; lean_object* v_res_5089_; 
v_newBinfo_boxed_5088_ = lean_unbox(v_newBinfo_5085_);
v_res_5089_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5084_, v_newBinfo_boxed_5088_, v_newDomain_5086_, v_newBody_5087_);
return v_res_5089_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; 
v___x_5091_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5092_ = lean_unsigned_to_nat(24u);
v___x_5093_ = lean_unsigned_to_nat(1922u);
v___x_5094_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_5095_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5096_ = l_mkPanicMessageWithDecl(v___x_5095_, v___x_5094_, v___x_5093_, v___x_5092_, v___x_5091_);
return v___x_5096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_5097_, lean_object* v_newDomain_5098_, lean_object* v_newBody_5099_){
_start:
{
if (lean_obj_tag(v_e_5097_) == 7)
{
lean_object* v_binderName_5100_; lean_object* v_binderType_5101_; lean_object* v_body_5102_; uint8_t v_binderInfo_5103_; uint8_t v___y_5105_; size_t v___x_5109_; size_t v___x_5110_; uint8_t v___x_5111_; 
v_binderName_5100_ = lean_ctor_get(v_e_5097_, 0);
v_binderType_5101_ = lean_ctor_get(v_e_5097_, 1);
v_body_5102_ = lean_ctor_get(v_e_5097_, 2);
v_binderInfo_5103_ = lean_ctor_get_uint8(v_e_5097_, sizeof(void*)*3 + 8);
v___x_5109_ = lean_ptr_addr(v_binderType_5101_);
v___x_5110_ = lean_ptr_addr(v_newDomain_5098_);
v___x_5111_ = lean_usize_dec_eq(v___x_5109_, v___x_5110_);
if (v___x_5111_ == 0)
{
v___y_5105_ = v___x_5111_;
goto v___jp_5104_;
}
else
{
size_t v___x_5112_; size_t v___x_5113_; uint8_t v___x_5114_; 
v___x_5112_ = lean_ptr_addr(v_body_5102_);
v___x_5113_ = lean_ptr_addr(v_newBody_5099_);
v___x_5114_ = lean_usize_dec_eq(v___x_5112_, v___x_5113_);
v___y_5105_ = v___x_5114_;
goto v___jp_5104_;
}
v___jp_5104_:
{
if (v___y_5105_ == 0)
{
lean_object* v___x_5106_; 
lean_inc(v_binderName_5100_);
lean_dec_ref_known(v_e_5097_, 3);
v___x_5106_ = l_Lean_Expr_forallE___override(v_binderName_5100_, v_newDomain_5098_, v_newBody_5099_, v_binderInfo_5103_);
return v___x_5106_;
}
else
{
uint8_t v___x_5107_; 
v___x_5107_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5103_, v_binderInfo_5103_);
if (v___x_5107_ == 0)
{
lean_object* v___x_5108_; 
lean_inc(v_binderName_5100_);
lean_dec_ref_known(v_e_5097_, 3);
v___x_5108_ = l_Lean_Expr_forallE___override(v_binderName_5100_, v_newDomain_5098_, v_newBody_5099_, v_binderInfo_5103_);
return v___x_5108_;
}
else
{
lean_dec_ref(v_newBody_5099_);
lean_dec_ref(v_newDomain_5098_);
return v_e_5097_;
}
}
}
}
else
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; 
lean_dec_ref(v_newBody_5099_);
lean_dec_ref(v_newDomain_5098_);
lean_dec_ref(v_e_5097_);
v___x_5115_ = l_Lean_instInhabitedExpr;
v___x_5116_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_5117_ = l_panic___redArg(v___x_5115_, v___x_5116_);
return v___x_5117_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; 
v___x_5120_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5121_ = lean_unsigned_to_nat(19u);
v___x_5122_ = lean_unsigned_to_nat(1931u);
v___x_5123_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_5124_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5125_ = l_mkPanicMessageWithDecl(v___x_5124_, v___x_5123_, v___x_5122_, v___x_5121_, v___x_5120_);
return v___x_5125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_5126_, uint8_t v_newBinfo_5127_, lean_object* v_newDomain_5128_, lean_object* v_newBody_5129_){
_start:
{
if (lean_obj_tag(v_e_5126_) == 6)
{
lean_object* v_binderName_5130_; lean_object* v_binderType_5131_; lean_object* v_body_5132_; uint8_t v_binderInfo_5133_; uint8_t v___y_5135_; size_t v___x_5139_; size_t v___x_5140_; uint8_t v___x_5141_; 
v_binderName_5130_ = lean_ctor_get(v_e_5126_, 0);
v_binderType_5131_ = lean_ctor_get(v_e_5126_, 1);
v_body_5132_ = lean_ctor_get(v_e_5126_, 2);
v_binderInfo_5133_ = lean_ctor_get_uint8(v_e_5126_, sizeof(void*)*3 + 8);
v___x_5139_ = lean_ptr_addr(v_binderType_5131_);
v___x_5140_ = lean_ptr_addr(v_newDomain_5128_);
v___x_5141_ = lean_usize_dec_eq(v___x_5139_, v___x_5140_);
if (v___x_5141_ == 0)
{
v___y_5135_ = v___x_5141_;
goto v___jp_5134_;
}
else
{
size_t v___x_5142_; size_t v___x_5143_; uint8_t v___x_5144_; 
v___x_5142_ = lean_ptr_addr(v_body_5132_);
v___x_5143_ = lean_ptr_addr(v_newBody_5129_);
v___x_5144_ = lean_usize_dec_eq(v___x_5142_, v___x_5143_);
v___y_5135_ = v___x_5144_;
goto v___jp_5134_;
}
v___jp_5134_:
{
if (v___y_5135_ == 0)
{
lean_object* v___x_5136_; 
lean_inc(v_binderName_5130_);
lean_dec_ref_known(v_e_5126_, 3);
v___x_5136_ = l_Lean_Expr_lam___override(v_binderName_5130_, v_newDomain_5128_, v_newBody_5129_, v_newBinfo_5127_);
return v___x_5136_;
}
else
{
uint8_t v___x_5137_; 
v___x_5137_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5133_, v_newBinfo_5127_);
if (v___x_5137_ == 0)
{
lean_object* v___x_5138_; 
lean_inc(v_binderName_5130_);
lean_dec_ref_known(v_e_5126_, 3);
v___x_5138_ = l_Lean_Expr_lam___override(v_binderName_5130_, v_newDomain_5128_, v_newBody_5129_, v_newBinfo_5127_);
return v___x_5138_;
}
else
{
lean_dec_ref(v_newBody_5129_);
lean_dec_ref(v_newDomain_5128_);
return v_e_5126_;
}
}
}
}
else
{
lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; 
lean_dec_ref(v_newBody_5129_);
lean_dec_ref(v_newDomain_5128_);
lean_dec_ref(v_e_5126_);
v___x_5145_ = l_Lean_instInhabitedExpr;
v___x_5146_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_5147_ = l_panic___redArg(v___x_5145_, v___x_5146_);
return v___x_5147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_5148_, lean_object* v_newBinfo_5149_, lean_object* v_newDomain_5150_, lean_object* v_newBody_5151_){
_start:
{
uint8_t v_newBinfo_boxed_5152_; lean_object* v_res_5153_; 
v_newBinfo_boxed_5152_ = lean_unbox(v_newBinfo_5149_);
v_res_5153_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5148_, v_newBinfo_boxed_5152_, v_newDomain_5150_, v_newBody_5151_);
return v_res_5153_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; 
v___x_5155_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5156_ = lean_unsigned_to_nat(20u);
v___x_5157_ = lean_unsigned_to_nat(1942u);
v___x_5158_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5159_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5160_ = l_mkPanicMessageWithDecl(v___x_5159_, v___x_5158_, v___x_5157_, v___x_5156_, v___x_5155_);
return v___x_5160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5161_, lean_object* v_newDomain_5162_, lean_object* v_newBody_5163_){
_start:
{
if (lean_obj_tag(v_e_5161_) == 6)
{
lean_object* v_binderName_5164_; lean_object* v_binderType_5165_; lean_object* v_body_5166_; uint8_t v_binderInfo_5167_; uint8_t v___y_5169_; size_t v___x_5173_; size_t v___x_5174_; uint8_t v___x_5175_; 
v_binderName_5164_ = lean_ctor_get(v_e_5161_, 0);
v_binderType_5165_ = lean_ctor_get(v_e_5161_, 1);
v_body_5166_ = lean_ctor_get(v_e_5161_, 2);
v_binderInfo_5167_ = lean_ctor_get_uint8(v_e_5161_, sizeof(void*)*3 + 8);
v___x_5173_ = lean_ptr_addr(v_binderType_5165_);
v___x_5174_ = lean_ptr_addr(v_newDomain_5162_);
v___x_5175_ = lean_usize_dec_eq(v___x_5173_, v___x_5174_);
if (v___x_5175_ == 0)
{
v___y_5169_ = v___x_5175_;
goto v___jp_5168_;
}
else
{
size_t v___x_5176_; size_t v___x_5177_; uint8_t v___x_5178_; 
v___x_5176_ = lean_ptr_addr(v_body_5166_);
v___x_5177_ = lean_ptr_addr(v_newBody_5163_);
v___x_5178_ = lean_usize_dec_eq(v___x_5176_, v___x_5177_);
v___y_5169_ = v___x_5178_;
goto v___jp_5168_;
}
v___jp_5168_:
{
if (v___y_5169_ == 0)
{
lean_object* v___x_5170_; 
lean_inc(v_binderName_5164_);
lean_dec_ref_known(v_e_5161_, 3);
v___x_5170_ = l_Lean_Expr_lam___override(v_binderName_5164_, v_newDomain_5162_, v_newBody_5163_, v_binderInfo_5167_);
return v___x_5170_;
}
else
{
uint8_t v___x_5171_; 
v___x_5171_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5167_, v_binderInfo_5167_);
if (v___x_5171_ == 0)
{
lean_object* v___x_5172_; 
lean_inc(v_binderName_5164_);
lean_dec_ref_known(v_e_5161_, 3);
v___x_5172_ = l_Lean_Expr_lam___override(v_binderName_5164_, v_newDomain_5162_, v_newBody_5163_, v_binderInfo_5167_);
return v___x_5172_;
}
else
{
lean_dec_ref(v_newBody_5163_);
lean_dec_ref(v_newDomain_5162_);
return v_e_5161_;
}
}
}
}
else
{
lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; 
lean_dec_ref(v_newBody_5163_);
lean_dec_ref(v_newDomain_5162_);
lean_dec_ref(v_e_5161_);
v___x_5179_ = l_Lean_instInhabitedExpr;
v___x_5180_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5181_ = l_panic___redArg(v___x_5179_, v___x_5180_);
return v___x_5181_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
v___x_5183_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5184_ = lean_unsigned_to_nat(22u);
v___x_5185_ = lean_unsigned_to_nat(1951u);
v___x_5186_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5187_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5188_ = l_mkPanicMessageWithDecl(v___x_5187_, v___x_5186_, v___x_5185_, v___x_5184_, v___x_5183_);
return v___x_5188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5189_, lean_object* v_newType_5190_, lean_object* v_newVal_5191_, lean_object* v_newBody_5192_, uint8_t v_newNondep_5193_){
_start:
{
if (lean_obj_tag(v_e_5189_) == 8)
{
lean_object* v_declName_5194_; lean_object* v_type_5195_; lean_object* v_value_5196_; lean_object* v_body_5197_; uint8_t v_nondep_5198_; uint8_t v___y_5200_; size_t v___x_5208_; size_t v___x_5209_; uint8_t v___x_5210_; 
v_declName_5194_ = lean_ctor_get(v_e_5189_, 0);
v_type_5195_ = lean_ctor_get(v_e_5189_, 1);
v_value_5196_ = lean_ctor_get(v_e_5189_, 2);
v_body_5197_ = lean_ctor_get(v_e_5189_, 3);
v_nondep_5198_ = lean_ctor_get_uint8(v_e_5189_, sizeof(void*)*4 + 8);
v___x_5208_ = lean_ptr_addr(v_type_5195_);
v___x_5209_ = lean_ptr_addr(v_newType_5190_);
v___x_5210_ = lean_usize_dec_eq(v___x_5208_, v___x_5209_);
if (v___x_5210_ == 0)
{
v___y_5200_ = v___x_5210_;
goto v___jp_5199_;
}
else
{
size_t v___x_5211_; size_t v___x_5212_; uint8_t v___x_5213_; 
v___x_5211_ = lean_ptr_addr(v_value_5196_);
v___x_5212_ = lean_ptr_addr(v_newVal_5191_);
v___x_5213_ = lean_usize_dec_eq(v___x_5211_, v___x_5212_);
v___y_5200_ = v___x_5213_;
goto v___jp_5199_;
}
v___jp_5199_:
{
if (v___y_5200_ == 0)
{
lean_object* v___x_5201_; 
lean_inc(v_declName_5194_);
lean_dec_ref_known(v_e_5189_, 4);
v___x_5201_ = l_Lean_Expr_letE___override(v_declName_5194_, v_newType_5190_, v_newVal_5191_, v_newBody_5192_, v_newNondep_5193_);
return v___x_5201_;
}
else
{
size_t v___x_5202_; size_t v___x_5203_; uint8_t v___x_5204_; 
v___x_5202_ = lean_ptr_addr(v_body_5197_);
v___x_5203_ = lean_ptr_addr(v_newBody_5192_);
v___x_5204_ = lean_usize_dec_eq(v___x_5202_, v___x_5203_);
if (v___x_5204_ == 0)
{
lean_object* v___x_5205_; 
lean_inc(v_declName_5194_);
lean_dec_ref_known(v_e_5189_, 4);
v___x_5205_ = l_Lean_Expr_letE___override(v_declName_5194_, v_newType_5190_, v_newVal_5191_, v_newBody_5192_, v_newNondep_5193_);
return v___x_5205_;
}
else
{
if (v_nondep_5198_ == 0)
{
if (v_newNondep_5193_ == 0)
{
lean_dec_ref(v_newBody_5192_);
lean_dec_ref(v_newVal_5191_);
lean_dec_ref(v_newType_5190_);
return v_e_5189_;
}
else
{
lean_object* v___x_5206_; 
lean_inc(v_declName_5194_);
lean_dec_ref_known(v_e_5189_, 4);
v___x_5206_ = l_Lean_Expr_letE___override(v_declName_5194_, v_newType_5190_, v_newVal_5191_, v_newBody_5192_, v_newNondep_5193_);
return v___x_5206_;
}
}
else
{
if (v_newNondep_5193_ == 0)
{
lean_object* v___x_5207_; 
lean_inc(v_declName_5194_);
lean_dec_ref_known(v_e_5189_, 4);
v___x_5207_ = l_Lean_Expr_letE___override(v_declName_5194_, v_newType_5190_, v_newVal_5191_, v_newBody_5192_, v_newNondep_5193_);
return v___x_5207_;
}
else
{
lean_dec_ref(v_newBody_5192_);
lean_dec_ref(v_newVal_5191_);
lean_dec_ref(v_newType_5190_);
return v_e_5189_;
}
}
}
}
}
}
else
{
lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; 
lean_dec_ref(v_newBody_5192_);
lean_dec_ref(v_newVal_5191_);
lean_dec_ref(v_newType_5190_);
lean_dec_ref(v_e_5189_);
v___x_5214_ = l_Lean_instInhabitedExpr;
v___x_5215_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5216_ = l_panic___redArg(v___x_5214_, v___x_5215_);
return v___x_5216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5217_, lean_object* v_newType_5218_, lean_object* v_newVal_5219_, lean_object* v_newBody_5220_, lean_object* v_newNondep_5221_){
_start:
{
uint8_t v_newNondep_boxed_5222_; lean_object* v_res_5223_; 
v_newNondep_boxed_5222_ = lean_unbox(v_newNondep_5221_);
v_res_5223_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5217_, v_newType_5218_, v_newVal_5219_, v_newBody_5220_, v_newNondep_boxed_5222_);
return v_res_5223_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; 
v___x_5225_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5226_ = lean_unsigned_to_nat(27u);
v___x_5227_ = lean_unsigned_to_nat(1964u);
v___x_5228_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5229_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5230_ = l_mkPanicMessageWithDecl(v___x_5229_, v___x_5228_, v___x_5227_, v___x_5226_, v___x_5225_);
return v___x_5230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5231_, lean_object* v_newType_5232_, lean_object* v_newVal_5233_, lean_object* v_newBody_5234_){
_start:
{
if (lean_obj_tag(v_e_5231_) == 8)
{
lean_object* v_declName_5235_; lean_object* v_type_5236_; lean_object* v_value_5237_; lean_object* v_body_5238_; uint8_t v_nondep_5239_; uint8_t v___y_5241_; size_t v___x_5247_; size_t v___x_5248_; uint8_t v___x_5249_; 
v_declName_5235_ = lean_ctor_get(v_e_5231_, 0);
v_type_5236_ = lean_ctor_get(v_e_5231_, 1);
v_value_5237_ = lean_ctor_get(v_e_5231_, 2);
v_body_5238_ = lean_ctor_get(v_e_5231_, 3);
v_nondep_5239_ = lean_ctor_get_uint8(v_e_5231_, sizeof(void*)*4 + 8);
v___x_5247_ = lean_ptr_addr(v_type_5236_);
v___x_5248_ = lean_ptr_addr(v_newType_5232_);
v___x_5249_ = lean_usize_dec_eq(v___x_5247_, v___x_5248_);
if (v___x_5249_ == 0)
{
v___y_5241_ = v___x_5249_;
goto v___jp_5240_;
}
else
{
size_t v___x_5250_; size_t v___x_5251_; uint8_t v___x_5252_; 
v___x_5250_ = lean_ptr_addr(v_value_5237_);
v___x_5251_ = lean_ptr_addr(v_newVal_5233_);
v___x_5252_ = lean_usize_dec_eq(v___x_5250_, v___x_5251_);
v___y_5241_ = v___x_5252_;
goto v___jp_5240_;
}
v___jp_5240_:
{
if (v___y_5241_ == 0)
{
lean_object* v___x_5242_; 
lean_inc(v_declName_5235_);
lean_dec_ref_known(v_e_5231_, 4);
v___x_5242_ = l_Lean_Expr_letE___override(v_declName_5235_, v_newType_5232_, v_newVal_5233_, v_newBody_5234_, v_nondep_5239_);
return v___x_5242_;
}
else
{
size_t v___x_5243_; size_t v___x_5244_; uint8_t v___x_5245_; 
v___x_5243_ = lean_ptr_addr(v_body_5238_);
v___x_5244_ = lean_ptr_addr(v_newBody_5234_);
v___x_5245_ = lean_usize_dec_eq(v___x_5243_, v___x_5244_);
if (v___x_5245_ == 0)
{
lean_object* v___x_5246_; 
lean_inc(v_declName_5235_);
lean_dec_ref_known(v_e_5231_, 4);
v___x_5246_ = l_Lean_Expr_letE___override(v_declName_5235_, v_newType_5232_, v_newVal_5233_, v_newBody_5234_, v_nondep_5239_);
return v___x_5246_;
}
else
{
lean_dec_ref(v_newBody_5234_);
lean_dec_ref(v_newVal_5233_);
lean_dec_ref(v_newType_5232_);
return v_e_5231_;
}
}
}
}
else
{
lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; 
lean_dec_ref(v_newBody_5234_);
lean_dec_ref(v_newVal_5233_);
lean_dec_ref(v_newType_5232_);
lean_dec_ref(v_e_5231_);
v___x_5253_ = l_Lean_instInhabitedExpr;
v___x_5254_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5255_ = l_panic___redArg(v___x_5253_, v___x_5254_);
return v___x_5255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5256_, lean_object* v_x_5257_){
_start:
{
if (lean_obj_tag(v_x_5256_) == 5)
{
lean_object* v_fn_5258_; lean_object* v_arg_5259_; lean_object* v___x_5260_; uint8_t v___y_5262_; size_t v___x_5264_; size_t v___x_5265_; uint8_t v___x_5266_; 
v_fn_5258_ = lean_ctor_get(v_x_5256_, 0);
v_arg_5259_ = lean_ctor_get(v_x_5256_, 1);
lean_inc_ref(v_fn_5258_);
v___x_5260_ = l_Lean_Expr_updateFn(v_fn_5258_, v_x_5257_);
v___x_5264_ = lean_ptr_addr(v_fn_5258_);
v___x_5265_ = lean_ptr_addr(v___x_5260_);
v___x_5266_ = lean_usize_dec_eq(v___x_5264_, v___x_5265_);
if (v___x_5266_ == 0)
{
v___y_5262_ = v___x_5266_;
goto v___jp_5261_;
}
else
{
size_t v___x_5267_; uint8_t v___x_5268_; 
v___x_5267_ = lean_ptr_addr(v_arg_5259_);
v___x_5268_ = lean_usize_dec_eq(v___x_5267_, v___x_5267_);
v___y_5262_ = v___x_5268_;
goto v___jp_5261_;
}
v___jp_5261_:
{
if (v___y_5262_ == 0)
{
lean_object* v___x_5263_; 
lean_inc_ref(v_arg_5259_);
lean_dec_ref_known(v_x_5256_, 2);
v___x_5263_ = l_Lean_Expr_app___override(v___x_5260_, v_arg_5259_);
return v___x_5263_;
}
else
{
lean_dec_ref(v___x_5260_);
return v_x_5256_;
}
}
}
else
{
lean_dec_ref(v_x_5256_);
lean_inc_ref(v_x_5257_);
return v_x_5257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5269_, lean_object* v_x_5270_){
_start:
{
lean_object* v_res_5271_; 
v_res_5271_ = l_Lean_Expr_updateFn(v_x_5269_, v_x_5270_);
lean_dec_ref(v_x_5270_);
return v_res_5271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5272_){
_start:
{
if (lean_obj_tag(v_e_5272_) == 6)
{
lean_object* v_binderName_5273_; lean_object* v_binderType_5274_; lean_object* v_body_5275_; uint8_t v_binderInfo_5276_; lean_object* v_b_x27_5277_; uint8_t v___y_5279_; uint8_t v___y_5284_; 
v_binderName_5273_ = lean_ctor_get(v_e_5272_, 0);
v_binderType_5274_ = lean_ctor_get(v_e_5272_, 1);
v_body_5275_ = lean_ctor_get(v_e_5272_, 2);
v_binderInfo_5276_ = lean_ctor_get_uint8(v_e_5272_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5275_);
v_b_x27_5277_ = l_Lean_Expr_eta(v_body_5275_);
if (lean_obj_tag(v_b_x27_5277_) == 5)
{
lean_object* v_arg_5294_; 
v_arg_5294_ = lean_ctor_get(v_b_x27_5277_, 1);
lean_inc_ref(v_arg_5294_);
if (lean_obj_tag(v_arg_5294_) == 0)
{
lean_object* v_fn_5295_; lean_object* v_deBruijnIndex_5296_; lean_object* v___x_5297_; uint8_t v___x_5298_; 
v_fn_5295_ = lean_ctor_get(v_b_x27_5277_, 0);
lean_inc_ref(v_fn_5295_);
v_deBruijnIndex_5296_ = lean_ctor_get(v_arg_5294_, 0);
lean_inc(v_deBruijnIndex_5296_);
lean_dec_ref_known(v_arg_5294_, 1);
v___x_5297_ = lean_unsigned_to_nat(0u);
v___x_5298_ = lean_nat_dec_eq(v_deBruijnIndex_5296_, v___x_5297_);
lean_dec(v_deBruijnIndex_5296_);
if (v___x_5298_ == 0)
{
lean_dec_ref(v_fn_5295_);
goto v___jp_5288_;
}
else
{
uint8_t v___x_5299_; 
v___x_5299_ = lean_expr_has_loose_bvar(v_fn_5295_, v___x_5297_);
if (v___x_5299_ == 0)
{
lean_object* v___x_5300_; lean_object* v___x_5301_; 
lean_dec_ref_known(v_b_x27_5277_, 2);
lean_dec_ref_known(v_e_5272_, 3);
v___x_5300_ = lean_unsigned_to_nat(1u);
v___x_5301_ = lean_expr_lower_loose_bvars(v_fn_5295_, v___x_5300_, v___x_5300_);
lean_dec_ref(v_fn_5295_);
return v___x_5301_;
}
else
{
size_t v___x_5302_; uint8_t v___x_5303_; 
lean_dec_ref(v_fn_5295_);
v___x_5302_ = lean_ptr_addr(v_binderType_5274_);
v___x_5303_ = lean_usize_dec_eq(v___x_5302_, v___x_5302_);
if (v___x_5303_ == 0)
{
v___y_5279_ = v___x_5303_;
goto v___jp_5278_;
}
else
{
size_t v___x_5304_; size_t v___x_5305_; uint8_t v___x_5306_; 
v___x_5304_ = lean_ptr_addr(v_body_5275_);
v___x_5305_ = lean_ptr_addr(v_b_x27_5277_);
v___x_5306_ = lean_usize_dec_eq(v___x_5304_, v___x_5305_);
v___y_5279_ = v___x_5306_;
goto v___jp_5278_;
}
}
}
}
else
{
lean_dec_ref(v_arg_5294_);
goto v___jp_5288_;
}
}
else
{
goto v___jp_5288_;
}
v___jp_5278_:
{
if (v___y_5279_ == 0)
{
lean_object* v___x_5280_; 
lean_inc_ref(v_binderType_5274_);
lean_inc(v_binderName_5273_);
lean_dec_ref_known(v_e_5272_, 3);
v___x_5280_ = l_Lean_Expr_lam___override(v_binderName_5273_, v_binderType_5274_, v_b_x27_5277_, v_binderInfo_5276_);
return v___x_5280_;
}
else
{
uint8_t v___x_5281_; 
v___x_5281_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5276_, v_binderInfo_5276_);
if (v___x_5281_ == 0)
{
lean_object* v___x_5282_; 
lean_inc_ref(v_binderType_5274_);
lean_inc(v_binderName_5273_);
lean_dec_ref_known(v_e_5272_, 3);
v___x_5282_ = l_Lean_Expr_lam___override(v_binderName_5273_, v_binderType_5274_, v_b_x27_5277_, v_binderInfo_5276_);
return v___x_5282_;
}
else
{
lean_dec_ref(v_b_x27_5277_);
return v_e_5272_;
}
}
}
v___jp_5283_:
{
if (v___y_5284_ == 0)
{
lean_object* v___x_5285_; 
lean_inc_ref(v_binderType_5274_);
lean_inc(v_binderName_5273_);
lean_dec_ref_known(v_e_5272_, 3);
v___x_5285_ = l_Lean_Expr_lam___override(v_binderName_5273_, v_binderType_5274_, v_b_x27_5277_, v_binderInfo_5276_);
return v___x_5285_;
}
else
{
uint8_t v___x_5286_; 
v___x_5286_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5276_, v_binderInfo_5276_);
if (v___x_5286_ == 0)
{
lean_object* v___x_5287_; 
lean_inc_ref(v_binderType_5274_);
lean_inc(v_binderName_5273_);
lean_dec_ref_known(v_e_5272_, 3);
v___x_5287_ = l_Lean_Expr_lam___override(v_binderName_5273_, v_binderType_5274_, v_b_x27_5277_, v_binderInfo_5276_);
return v___x_5287_;
}
else
{
lean_dec_ref(v_b_x27_5277_);
return v_e_5272_;
}
}
}
v___jp_5288_:
{
size_t v___x_5289_; uint8_t v___x_5290_; 
v___x_5289_ = lean_ptr_addr(v_binderType_5274_);
v___x_5290_ = lean_usize_dec_eq(v___x_5289_, v___x_5289_);
if (v___x_5290_ == 0)
{
v___y_5284_ = v___x_5290_;
goto v___jp_5283_;
}
else
{
size_t v___x_5291_; size_t v___x_5292_; uint8_t v___x_5293_; 
v___x_5291_ = lean_ptr_addr(v_body_5275_);
v___x_5292_ = lean_ptr_addr(v_b_x27_5277_);
v___x_5293_ = lean_usize_dec_eq(v___x_5291_, v___x_5292_);
v___y_5284_ = v___x_5293_;
goto v___jp_5283_;
}
}
}
else
{
return v_e_5272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5307_, lean_object* v_optionName_5308_, lean_object* v_inst_5309_, lean_object* v_val_5310_){
_start:
{
lean_object* v_toDataValue_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; 
v_toDataValue_5311_ = lean_ctor_get(v_inst_5309_, 0);
lean_inc_ref(v_toDataValue_5311_);
lean_dec_ref(v_inst_5309_);
v___x_5312_ = lean_box(0);
v___x_5313_ = lean_apply_1(v_toDataValue_5311_, v_val_5310_);
v___x_5314_ = l_Lean_KVMap_insert(v___x_5312_, v_optionName_5308_, v___x_5313_);
v___x_5315_ = l_Lean_Expr_mdata___override(v___x_5314_, v_e_5307_);
return v___x_5315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5316_, lean_object* v_e_5317_, lean_object* v_optionName_5318_, lean_object* v_inst_5319_, lean_object* v_val_5320_){
_start:
{
lean_object* v___x_5321_; 
v___x_5321_ = l_Lean_Expr_setOption___redArg(v_e_5317_, v_optionName_5318_, v_inst_5319_, v_val_5320_);
return v___x_5321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5322_, lean_object* v_optionName_5323_, uint8_t v_val_5324_){
_start:
{
lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; 
v___x_5325_ = lean_box(0);
v___x_5326_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5326_, 0, v_val_5324_);
v___x_5327_ = l_Lean_KVMap_insert(v___x_5325_, v_optionName_5323_, v___x_5326_);
v___x_5328_ = l_Lean_Expr_mdata___override(v___x_5327_, v_e_5322_);
return v___x_5328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5329_, lean_object* v_optionName_5330_, lean_object* v_val_5331_){
_start:
{
uint8_t v_val_boxed_5332_; lean_object* v_res_5333_; 
v_val_boxed_5332_ = lean_unbox(v_val_5331_);
v_res_5333_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5329_, v_optionName_5330_, v_val_boxed_5332_);
return v_res_5333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5339_, uint8_t v_flag_5340_){
_start:
{
lean_object* v___x_5341_; lean_object* v___x_5342_; 
v___x_5341_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5342_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5339_, v___x_5341_, v_flag_5340_);
return v___x_5342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5343_, lean_object* v_flag_5344_){
_start:
{
uint8_t v_flag_boxed_5345_; lean_object* v_res_5346_; 
v_flag_boxed_5345_ = lean_unbox(v_flag_5344_);
v_res_5346_ = l_Lean_Expr_setPPExplicit(v_e_5343_, v_flag_boxed_5345_);
return v_res_5346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5351_, uint8_t v_flag_5352_){
_start:
{
lean_object* v___x_5353_; lean_object* v___x_5354_; 
v___x_5353_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5354_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5351_, v___x_5353_, v_flag_5352_);
return v___x_5354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5355_, lean_object* v_flag_5356_){
_start:
{
uint8_t v_flag_boxed_5357_; lean_object* v_res_5358_; 
v_flag_boxed_5357_ = lean_unbox(v_flag_5356_);
v_res_5358_ = l_Lean_Expr_setPPUniverses(v_e_5355_, v_flag_boxed_5357_);
return v_res_5358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5363_, uint8_t v_flag_5364_){
_start:
{
lean_object* v___x_5365_; lean_object* v___x_5366_; 
v___x_5365_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5366_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5363_, v___x_5365_, v_flag_5364_);
return v___x_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5367_, lean_object* v_flag_5368_){
_start:
{
uint8_t v_flag_boxed_5369_; lean_object* v_res_5370_; 
v_flag_boxed_5369_ = lean_unbox(v_flag_5368_);
v_res_5370_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5367_, v_flag_boxed_5369_);
return v_res_5370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5375_, uint8_t v_flag_5376_){
_start:
{
lean_object* v___x_5377_; lean_object* v___x_5378_; 
v___x_5377_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5378_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5375_, v___x_5377_, v_flag_5376_);
return v___x_5378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5379_, lean_object* v_flag_5380_){
_start:
{
uint8_t v_flag_boxed_5381_; lean_object* v_res_5382_; 
v_flag_boxed_5381_ = lean_unbox(v_flag_5380_);
v_res_5382_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5379_, v_flag_boxed_5381_);
return v_res_5382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5387_, uint8_t v_flag_5388_){
_start:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; 
v___x_5389_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5390_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5387_, v___x_5389_, v_flag_5388_);
return v___x_5390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5391_, lean_object* v_flag_5392_){
_start:
{
uint8_t v_flag_boxed_5393_; lean_object* v_res_5394_; 
v_flag_boxed_5393_ = lean_unbox(v_flag_5392_);
v_res_5394_ = l_Lean_Expr_setPPNumericTypes(v_e_5391_, v_flag_boxed_5393_);
return v_res_5394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5395_, size_t v_i_5396_, lean_object* v_bs_5397_){
_start:
{
uint8_t v___x_5398_; 
v___x_5398_ = lean_usize_dec_lt(v_i_5396_, v_sz_5395_);
if (v___x_5398_ == 0)
{
return v_bs_5397_;
}
else
{
uint8_t v___x_5399_; lean_object* v_v_5400_; lean_object* v___x_5401_; lean_object* v_bs_x27_5402_; lean_object* v___x_5403_; size_t v___x_5404_; size_t v___x_5405_; lean_object* v___x_5406_; 
v___x_5399_ = 0;
v_v_5400_ = lean_array_uget(v_bs_5397_, v_i_5396_);
v___x_5401_ = lean_unsigned_to_nat(0u);
v_bs_x27_5402_ = lean_array_uset(v_bs_5397_, v_i_5396_, v___x_5401_);
v___x_5403_ = l_Lean_Expr_setPPExplicit(v_v_5400_, v___x_5399_);
v___x_5404_ = ((size_t)1ULL);
v___x_5405_ = lean_usize_add(v_i_5396_, v___x_5404_);
v___x_5406_ = lean_array_uset(v_bs_x27_5402_, v_i_5396_, v___x_5403_);
v_i_5396_ = v___x_5405_;
v_bs_5397_ = v___x_5406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5408_, lean_object* v_i_5409_, lean_object* v_bs_5410_){
_start:
{
size_t v_sz_boxed_5411_; size_t v_i_boxed_5412_; lean_object* v_res_5413_; 
v_sz_boxed_5411_ = lean_unbox_usize(v_sz_5408_);
lean_dec(v_sz_5408_);
v_i_boxed_5412_ = lean_unbox_usize(v_i_5409_);
lean_dec(v_i_5409_);
v_res_5413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5411_, v_i_boxed_5412_, v_bs_5410_);
return v_res_5413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5414_){
_start:
{
if (lean_obj_tag(v_e_5414_) == 5)
{
lean_object* v___x_5415_; uint8_t v___x_5416_; lean_object* v_f_5417_; lean_object* v_dummy_5418_; lean_object* v_nargs_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; size_t v_sz_5424_; size_t v___x_5425_; lean_object* v_args_5426_; lean_object* v___x_5427_; uint8_t v___x_5428_; lean_object* v___x_5429_; 
v___x_5415_ = l_Lean_Expr_getAppFn(v_e_5414_);
v___x_5416_ = 0;
v_f_5417_ = l_Lean_Expr_setPPExplicit(v___x_5415_, v___x_5416_);
v_dummy_5418_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5419_ = l_Lean_Expr_getAppNumArgs(v_e_5414_);
lean_inc(v_nargs_5419_);
v___x_5420_ = lean_mk_array(v_nargs_5419_, v_dummy_5418_);
v___x_5421_ = lean_unsigned_to_nat(1u);
v___x_5422_ = lean_nat_sub(v_nargs_5419_, v___x_5421_);
lean_dec(v_nargs_5419_);
v___x_5423_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5414_, v___x_5420_, v___x_5422_);
v_sz_5424_ = lean_array_size(v___x_5423_);
v___x_5425_ = ((size_t)0ULL);
v_args_5426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5424_, v___x_5425_, v___x_5423_);
v___x_5427_ = l_Lean_mkAppN(v_f_5417_, v_args_5426_);
lean_dec_ref(v_args_5426_);
v___x_5428_ = 1;
v___x_5429_ = l_Lean_Expr_setPPExplicit(v___x_5427_, v___x_5428_);
return v___x_5429_;
}
else
{
return v_e_5414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5430_, size_t v_i_5431_, lean_object* v_bs_5432_){
_start:
{
uint8_t v___x_5433_; 
v___x_5433_ = lean_usize_dec_lt(v_i_5431_, v_sz_5430_);
if (v___x_5433_ == 0)
{
return v_bs_5432_;
}
else
{
lean_object* v_v_5434_; lean_object* v___x_5435_; lean_object* v_bs_x27_5436_; lean_object* v___y_5438_; uint8_t v___x_5443_; 
v_v_5434_ = lean_array_uget(v_bs_5432_, v_i_5431_);
v___x_5435_ = lean_unsigned_to_nat(0u);
v_bs_x27_5436_ = lean_array_uset(v_bs_5432_, v_i_5431_, v___x_5435_);
v___x_5443_ = l_Lean_Expr_hasMVar(v_v_5434_);
if (v___x_5443_ == 0)
{
lean_object* v___x_5444_; 
v___x_5444_ = l_Lean_Expr_setPPExplicit(v_v_5434_, v___x_5443_);
v___y_5438_ = v___x_5444_;
goto v___jp_5437_;
}
else
{
v___y_5438_ = v_v_5434_;
goto v___jp_5437_;
}
v___jp_5437_:
{
size_t v___x_5439_; size_t v___x_5440_; lean_object* v___x_5441_; 
v___x_5439_ = ((size_t)1ULL);
v___x_5440_ = lean_usize_add(v_i_5431_, v___x_5439_);
v___x_5441_ = lean_array_uset(v_bs_x27_5436_, v_i_5431_, v___y_5438_);
v_i_5431_ = v___x_5440_;
v_bs_5432_ = v___x_5441_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5445_, lean_object* v_i_5446_, lean_object* v_bs_5447_){
_start:
{
size_t v_sz_boxed_5448_; size_t v_i_boxed_5449_; lean_object* v_res_5450_; 
v_sz_boxed_5448_ = lean_unbox_usize(v_sz_5445_);
lean_dec(v_sz_5445_);
v_i_boxed_5449_ = lean_unbox_usize(v_i_5446_);
lean_dec(v_i_5446_);
v_res_5450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5448_, v_i_boxed_5449_, v_bs_5447_);
return v_res_5450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5451_){
_start:
{
if (lean_obj_tag(v_e_5451_) == 5)
{
lean_object* v___x_5452_; uint8_t v___x_5453_; lean_object* v_f_5454_; lean_object* v_dummy_5455_; lean_object* v_nargs_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; size_t v_sz_5461_; size_t v___x_5462_; lean_object* v_args_5463_; lean_object* v___x_5464_; uint8_t v___x_5465_; lean_object* v___x_5466_; 
v___x_5452_ = l_Lean_Expr_getAppFn(v_e_5451_);
v___x_5453_ = 0;
v_f_5454_ = l_Lean_Expr_setPPExplicit(v___x_5452_, v___x_5453_);
v_dummy_5455_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5456_ = l_Lean_Expr_getAppNumArgs(v_e_5451_);
lean_inc(v_nargs_5456_);
v___x_5457_ = lean_mk_array(v_nargs_5456_, v_dummy_5455_);
v___x_5458_ = lean_unsigned_to_nat(1u);
v___x_5459_ = lean_nat_sub(v_nargs_5456_, v___x_5458_);
lean_dec(v_nargs_5456_);
v___x_5460_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5451_, v___x_5457_, v___x_5459_);
v_sz_5461_ = lean_array_size(v___x_5460_);
v___x_5462_ = ((size_t)0ULL);
v_args_5463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5461_, v___x_5462_, v___x_5460_);
v___x_5464_ = l_Lean_mkAppN(v_f_5454_, v_args_5463_);
lean_dec_ref(v_args_5463_);
v___x_5465_ = 1;
v___x_5466_ = l_Lean_Expr_setPPExplicit(v___x_5464_, v___x_5465_);
return v___x_5466_;
}
else
{
return v_e_5451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5467_, lean_object* v_body_5468_, lean_object* v_x_5469_){
_start:
{
lean_object* v___x_5470_; 
v___x_5470_ = lean_apply_1(v_f_5467_, v_body_5468_);
return v___x_5470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5471_, lean_object* v_binderType_5472_, lean_object* v_x_5473_){
_start:
{
lean_object* v___x_5474_; 
v___x_5474_ = lean_apply_1(v_f_5471_, v_binderType_5472_);
return v___x_5474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5475_, lean_object* v_value_5476_, lean_object* v_x_5477_){
_start:
{
lean_object* v___x_5478_; 
v___x_5478_ = lean_apply_1(v_f_5475_, v_value_5476_);
return v___x_5478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5479_, lean_object* v_type_5480_, lean_object* v_x_5481_){
_start:
{
lean_object* v___x_5482_; 
v___x_5482_ = lean_apply_1(v_f_5479_, v_type_5480_);
return v___x_5482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5483_, lean_object* v_arg_5484_, lean_object* v_x_5485_){
_start:
{
lean_object* v___x_5486_; 
v___x_5486_ = lean_apply_1(v_f_5483_, v_arg_5484_);
return v___x_5486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5487_, lean_object* v_fn_5488_, lean_object* v_x_5489_){
_start:
{
lean_object* v___x_5490_; 
v___x_5490_ = lean_apply_1(v_f_5487_, v_fn_5488_);
return v___x_5490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5491_, lean_object* v_f_5492_, lean_object* v_x_5493_){
_start:
{
switch(lean_obj_tag(v_x_5493_))
{
case 7:
{
lean_object* v_toPure_5494_; lean_object* v_toSeq_5495_; lean_object* v_binderType_5496_; lean_object* v_body_5497_; lean_object* v___f_5498_; lean_object* v___f_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; 
v_toPure_5494_ = lean_ctor_get(v_inst_5491_, 1);
lean_inc(v_toPure_5494_);
v_toSeq_5495_ = lean_ctor_get(v_inst_5491_, 2);
lean_inc_n(v_toSeq_5495_, 2);
lean_dec_ref(v_inst_5491_);
v_binderType_5496_ = lean_ctor_get(v_x_5493_, 1);
v_body_5497_ = lean_ctor_get(v_x_5493_, 2);
lean_inc_ref(v_body_5497_);
lean_inc(v_f_5492_);
v___f_5498_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5498_, 0, v_f_5492_);
lean_closure_set(v___f_5498_, 1, v_body_5497_);
lean_inc_ref(v_binderType_5496_);
v___f_5499_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5499_, 0, v_f_5492_);
lean_closure_set(v___f_5499_, 1, v_binderType_5496_);
v___x_5500_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5500_, 0, v_x_5493_);
v___x_5501_ = lean_apply_2(v_toPure_5494_, lean_box(0), v___x_5500_);
v___x_5502_ = lean_apply_4(v_toSeq_5495_, lean_box(0), lean_box(0), v___x_5501_, v___f_5499_);
v___x_5503_ = lean_apply_4(v_toSeq_5495_, lean_box(0), lean_box(0), v___x_5502_, v___f_5498_);
return v___x_5503_;
}
case 6:
{
lean_object* v_toPure_5504_; lean_object* v_toSeq_5505_; lean_object* v_binderType_5506_; lean_object* v_body_5507_; lean_object* v___f_5508_; lean_object* v___f_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; 
v_toPure_5504_ = lean_ctor_get(v_inst_5491_, 1);
lean_inc(v_toPure_5504_);
v_toSeq_5505_ = lean_ctor_get(v_inst_5491_, 2);
lean_inc_n(v_toSeq_5505_, 2);
lean_dec_ref(v_inst_5491_);
v_binderType_5506_ = lean_ctor_get(v_x_5493_, 1);
v_body_5507_ = lean_ctor_get(v_x_5493_, 2);
lean_inc_ref(v_body_5507_);
lean_inc(v_f_5492_);
v___f_5508_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5508_, 0, v_f_5492_);
lean_closure_set(v___f_5508_, 1, v_body_5507_);
lean_inc_ref(v_binderType_5506_);
v___f_5509_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5509_, 0, v_f_5492_);
lean_closure_set(v___f_5509_, 1, v_binderType_5506_);
v___x_5510_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5510_, 0, v_x_5493_);
v___x_5511_ = lean_apply_2(v_toPure_5504_, lean_box(0), v___x_5510_);
v___x_5512_ = lean_apply_4(v_toSeq_5505_, lean_box(0), lean_box(0), v___x_5511_, v___f_5509_);
v___x_5513_ = lean_apply_4(v_toSeq_5505_, lean_box(0), lean_box(0), v___x_5512_, v___f_5508_);
return v___x_5513_;
}
case 10:
{
lean_object* v_toFunctor_5514_; lean_object* v_expr_5515_; lean_object* v_map_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; 
v_toFunctor_5514_ = lean_ctor_get(v_inst_5491_, 0);
lean_inc_ref(v_toFunctor_5514_);
lean_dec_ref(v_inst_5491_);
v_expr_5515_ = lean_ctor_get(v_x_5493_, 1);
lean_inc_ref(v_expr_5515_);
v_map_5516_ = lean_ctor_get(v_toFunctor_5514_, 0);
lean_inc(v_map_5516_);
lean_dec_ref(v_toFunctor_5514_);
v___x_5517_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5517_, 0, v_x_5493_);
v___x_5518_ = lean_apply_1(v_f_5492_, v_expr_5515_);
v___x_5519_ = lean_apply_4(v_map_5516_, lean_box(0), lean_box(0), v___x_5517_, v___x_5518_);
return v___x_5519_;
}
case 8:
{
lean_object* v_toPure_5520_; lean_object* v_toSeq_5521_; lean_object* v_type_5522_; lean_object* v_value_5523_; lean_object* v_body_5524_; lean_object* v___f_5525_; lean_object* v___f_5526_; lean_object* v___f_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; 
v_toPure_5520_ = lean_ctor_get(v_inst_5491_, 1);
lean_inc(v_toPure_5520_);
v_toSeq_5521_ = lean_ctor_get(v_inst_5491_, 2);
lean_inc_n(v_toSeq_5521_, 3);
lean_dec_ref(v_inst_5491_);
v_type_5522_ = lean_ctor_get(v_x_5493_, 1);
v_value_5523_ = lean_ctor_get(v_x_5493_, 2);
v_body_5524_ = lean_ctor_get(v_x_5493_, 3);
lean_inc_ref(v_body_5524_);
lean_inc_n(v_f_5492_, 2);
v___f_5525_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5525_, 0, v_f_5492_);
lean_closure_set(v___f_5525_, 1, v_body_5524_);
lean_inc_ref(v_value_5523_);
v___f_5526_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5526_, 0, v_f_5492_);
lean_closure_set(v___f_5526_, 1, v_value_5523_);
lean_inc_ref(v_type_5522_);
v___f_5527_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5527_, 0, v_f_5492_);
lean_closure_set(v___f_5527_, 1, v_type_5522_);
v___x_5528_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5528_, 0, v_x_5493_);
v___x_5529_ = lean_apply_2(v_toPure_5520_, lean_box(0), v___x_5528_);
v___x_5530_ = lean_apply_4(v_toSeq_5521_, lean_box(0), lean_box(0), v___x_5529_, v___f_5527_);
v___x_5531_ = lean_apply_4(v_toSeq_5521_, lean_box(0), lean_box(0), v___x_5530_, v___f_5526_);
v___x_5532_ = lean_apply_4(v_toSeq_5521_, lean_box(0), lean_box(0), v___x_5531_, v___f_5525_);
return v___x_5532_;
}
case 5:
{
lean_object* v_toPure_5533_; lean_object* v_toSeq_5534_; lean_object* v_fn_5535_; lean_object* v_arg_5536_; lean_object* v___f_5537_; lean_object* v___f_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; 
v_toPure_5533_ = lean_ctor_get(v_inst_5491_, 1);
lean_inc(v_toPure_5533_);
v_toSeq_5534_ = lean_ctor_get(v_inst_5491_, 2);
lean_inc_n(v_toSeq_5534_, 2);
lean_dec_ref(v_inst_5491_);
v_fn_5535_ = lean_ctor_get(v_x_5493_, 0);
v_arg_5536_ = lean_ctor_get(v_x_5493_, 1);
lean_inc_ref(v_arg_5536_);
lean_inc(v_f_5492_);
v___f_5537_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5537_, 0, v_f_5492_);
lean_closure_set(v___f_5537_, 1, v_arg_5536_);
lean_inc_ref(v_fn_5535_);
v___f_5538_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5538_, 0, v_f_5492_);
lean_closure_set(v___f_5538_, 1, v_fn_5535_);
v___x_5539_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5539_, 0, v_x_5493_);
v___x_5540_ = lean_apply_2(v_toPure_5533_, lean_box(0), v___x_5539_);
v___x_5541_ = lean_apply_4(v_toSeq_5534_, lean_box(0), lean_box(0), v___x_5540_, v___f_5538_);
v___x_5542_ = lean_apply_4(v_toSeq_5534_, lean_box(0), lean_box(0), v___x_5541_, v___f_5537_);
return v___x_5542_;
}
case 11:
{
lean_object* v_toFunctor_5543_; lean_object* v_struct_5544_; lean_object* v_map_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; 
v_toFunctor_5543_ = lean_ctor_get(v_inst_5491_, 0);
lean_inc_ref(v_toFunctor_5543_);
lean_dec_ref(v_inst_5491_);
v_struct_5544_ = lean_ctor_get(v_x_5493_, 2);
lean_inc_ref(v_struct_5544_);
v_map_5545_ = lean_ctor_get(v_toFunctor_5543_, 0);
lean_inc(v_map_5545_);
lean_dec_ref(v_toFunctor_5543_);
v___x_5546_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5546_, 0, v_x_5493_);
v___x_5547_ = lean_apply_1(v_f_5492_, v_struct_5544_);
v___x_5548_ = lean_apply_4(v_map_5545_, lean_box(0), lean_box(0), v___x_5546_, v___x_5547_);
return v___x_5548_;
}
default: 
{
lean_object* v_toPure_5549_; lean_object* v___x_5550_; 
lean_dec(v_f_5492_);
v_toPure_5549_ = lean_ctor_get(v_inst_5491_, 1);
lean_inc(v_toPure_5549_);
lean_dec_ref(v_inst_5491_);
v___x_5550_ = lean_apply_2(v_toPure_5549_, lean_box(0), v_x_5493_);
return v___x_5550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5551_, lean_object* v_inst_5552_, lean_object* v_f_5553_, lean_object* v_x_5554_){
_start:
{
lean_object* v___x_5555_; 
v___x_5555_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5552_, v_f_5553_, v_x_5554_);
return v___x_5555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5556_){
_start:
{
lean_object* v_snd_5557_; 
v_snd_5557_ = lean_ctor_get(v_self_5556_, 1);
lean_inc(v_snd_5557_);
return v_snd_5557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5558_){
_start:
{
lean_object* v_res_5559_; 
v_res_5559_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5558_);
lean_dec_ref(v_self_5558_);
return v_res_5559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5560_, lean_object* v_snd_5561_){
_start:
{
lean_object* v___x_5562_; 
v___x_5562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5562_, 0, v_e_x27_5560_);
lean_ctor_set(v___x_5562_, 1, v_snd_5561_);
return v___x_5562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5563_, lean_object* v_map_5564_, lean_object* v_e_x27_5565_, lean_object* v_a_5566_){
_start:
{
lean_object* v___f_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; 
lean_inc_ref(v_e_x27_5565_);
v___f_5567_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5567_, 0, v_e_x27_5565_);
v___x_5568_ = lean_apply_2(v_f_5563_, v_a_5566_, v_e_x27_5565_);
v___x_5569_ = lean_apply_4(v_map_5564_, lean_box(0), lean_box(0), v___f_5567_, v___x_5568_);
return v___x_5569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5571_, lean_object* v_f_5572_, lean_object* v_init_5573_, lean_object* v_e_5574_){
_start:
{
lean_object* v_toApplicative_5575_; lean_object* v_toFunctor_5576_; lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5603_; 
v_toApplicative_5575_ = lean_ctor_get(v_inst_5571_, 0);
lean_inc_ref(v_toApplicative_5575_);
v_toFunctor_5576_ = lean_ctor_get(v_toApplicative_5575_, 0);
v_isSharedCheck_5603_ = !lean_is_exclusive(v_toApplicative_5575_);
if (v_isSharedCheck_5603_ == 0)
{
lean_object* v_unused_5604_; lean_object* v_unused_5605_; lean_object* v_unused_5606_; lean_object* v_unused_5607_; 
v_unused_5604_ = lean_ctor_get(v_toApplicative_5575_, 4);
lean_dec(v_unused_5604_);
v_unused_5605_ = lean_ctor_get(v_toApplicative_5575_, 3);
lean_dec(v_unused_5605_);
v_unused_5606_ = lean_ctor_get(v_toApplicative_5575_, 2);
lean_dec(v_unused_5606_);
v_unused_5607_ = lean_ctor_get(v_toApplicative_5575_, 1);
lean_dec(v_unused_5607_);
v___x_5578_ = v_toApplicative_5575_;
v_isShared_5579_ = v_isSharedCheck_5603_;
goto v_resetjp_5577_;
}
else
{
lean_inc(v_toFunctor_5576_);
lean_dec(v_toApplicative_5575_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5603_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v_map_5580_; lean_object* v___x_5582_; uint8_t v_isShared_5583_; uint8_t v_isSharedCheck_5601_; 
v_map_5580_ = lean_ctor_get(v_toFunctor_5576_, 0);
v_isSharedCheck_5601_ = !lean_is_exclusive(v_toFunctor_5576_);
if (v_isSharedCheck_5601_ == 0)
{
lean_object* v_unused_5602_; 
v_unused_5602_ = lean_ctor_get(v_toFunctor_5576_, 1);
lean_dec(v_unused_5602_);
v___x_5582_ = v_toFunctor_5576_;
v_isShared_5583_ = v_isSharedCheck_5601_;
goto v_resetjp_5581_;
}
else
{
lean_inc(v_map_5580_);
lean_dec(v_toFunctor_5576_);
v___x_5582_ = lean_box(0);
v_isShared_5583_ = v_isSharedCheck_5601_;
goto v_resetjp_5581_;
}
v_resetjp_5581_:
{
lean_object* v___f_5584_; lean_object* v___f_5585_; lean_object* v___f_5586_; lean_object* v___f_5587_; lean_object* v___f_5588_; lean_object* v___f_5589_; lean_object* v___x_5590_; lean_object* v___x_5592_; 
v___f_5584_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5580_);
v___f_5585_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5585_, 0, v_f_5572_);
lean_closure_set(v___f_5585_, 1, v_map_5580_);
lean_inc_ref_n(v_inst_5571_, 5);
v___f_5586_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5586_, 0, v_inst_5571_);
v___f_5587_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5587_, 0, v_inst_5571_);
v___f_5588_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5588_, 0, v_inst_5571_);
v___f_5589_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5589_, 0, v_inst_5571_);
v___x_5590_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5590_, 0, lean_box(0));
lean_closure_set(v___x_5590_, 1, lean_box(0));
lean_closure_set(v___x_5590_, 2, v_inst_5571_);
if (v_isShared_5583_ == 0)
{
lean_ctor_set(v___x_5582_, 1, v___f_5586_);
lean_ctor_set(v___x_5582_, 0, v___x_5590_);
v___x_5592_ = v___x_5582_;
goto v_reusejp_5591_;
}
else
{
lean_object* v_reuseFailAlloc_5600_; 
v_reuseFailAlloc_5600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5600_, 0, v___x_5590_);
lean_ctor_set(v_reuseFailAlloc_5600_, 1, v___f_5586_);
v___x_5592_ = v_reuseFailAlloc_5600_;
goto v_reusejp_5591_;
}
v_reusejp_5591_:
{
lean_object* v___x_5593_; lean_object* v___x_5595_; 
v___x_5593_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5593_, 0, lean_box(0));
lean_closure_set(v___x_5593_, 1, lean_box(0));
lean_closure_set(v___x_5593_, 2, v_inst_5571_);
if (v_isShared_5579_ == 0)
{
lean_ctor_set(v___x_5578_, 4, v___f_5589_);
lean_ctor_set(v___x_5578_, 3, v___f_5588_);
lean_ctor_set(v___x_5578_, 2, v___f_5587_);
lean_ctor_set(v___x_5578_, 1, v___x_5593_);
lean_ctor_set(v___x_5578_, 0, v___x_5592_);
v___x_5595_ = v___x_5578_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5599_; 
v_reuseFailAlloc_5599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5599_, 0, v___x_5592_);
lean_ctor_set(v_reuseFailAlloc_5599_, 1, v___x_5593_);
lean_ctor_set(v_reuseFailAlloc_5599_, 2, v___f_5587_);
lean_ctor_set(v_reuseFailAlloc_5599_, 3, v___f_5588_);
lean_ctor_set(v_reuseFailAlloc_5599_, 4, v___f_5589_);
v___x_5595_ = v_reuseFailAlloc_5599_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
lean_object* v___x_18__overap_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; 
v___x_18__overap_5596_ = l_Lean_Expr_traverseChildren___redArg(v___x_5595_, v___f_5585_, v_e_5574_);
v___x_5597_ = lean_apply_1(v___x_18__overap_5596_, v_init_5573_);
v___x_5598_ = lean_apply_4(v_map_5580_, lean_box(0), lean_box(0), v___f_5584_, v___x_5597_);
return v___x_5598_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5608_, lean_object* v_m_5609_, lean_object* v_inst_5610_, lean_object* v_f_5611_, lean_object* v_init_5612_, lean_object* v_e_5613_){
_start:
{
lean_object* v___x_5614_; 
v___x_5614_ = l_Lean_Expr_foldlM___redArg(v_inst_5610_, v_f_5611_, v_init_5612_, v_e_5613_);
return v___x_5614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5615_){
_start:
{
lean_object* v_d_5617_; lean_object* v_b_5618_; 
switch(lean_obj_tag(v_x_5615_))
{
case 5:
{
lean_object* v_fn_5624_; lean_object* v_arg_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; 
v_fn_5624_ = lean_ctor_get(v_x_5615_, 0);
v_arg_5625_ = lean_ctor_get(v_x_5615_, 1);
v___x_5626_ = lean_unsigned_to_nat(1u);
v___x_5627_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5624_);
v___x_5628_ = lean_nat_add(v___x_5626_, v___x_5627_);
lean_dec(v___x_5627_);
v___x_5629_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5625_);
v___x_5630_ = lean_nat_add(v___x_5628_, v___x_5629_);
lean_dec(v___x_5629_);
lean_dec(v___x_5628_);
return v___x_5630_;
}
case 6:
{
lean_object* v_binderType_5631_; lean_object* v_body_5632_; 
v_binderType_5631_ = lean_ctor_get(v_x_5615_, 1);
v_body_5632_ = lean_ctor_get(v_x_5615_, 2);
v_d_5617_ = v_binderType_5631_;
v_b_5618_ = v_body_5632_;
goto v___jp_5616_;
}
case 7:
{
lean_object* v_binderType_5633_; lean_object* v_body_5634_; 
v_binderType_5633_ = lean_ctor_get(v_x_5615_, 1);
v_body_5634_ = lean_ctor_get(v_x_5615_, 2);
v_d_5617_ = v_binderType_5633_;
v_b_5618_ = v_body_5634_;
goto v___jp_5616_;
}
case 8:
{
lean_object* v_type_5635_; lean_object* v_value_5636_; lean_object* v_body_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; 
v_type_5635_ = lean_ctor_get(v_x_5615_, 1);
v_value_5636_ = lean_ctor_get(v_x_5615_, 2);
v_body_5637_ = lean_ctor_get(v_x_5615_, 3);
v___x_5638_ = lean_unsigned_to_nat(1u);
v___x_5639_ = l_Lean_Expr_sizeWithoutSharing(v_type_5635_);
v___x_5640_ = lean_nat_add(v___x_5638_, v___x_5639_);
lean_dec(v___x_5639_);
v___x_5641_ = l_Lean_Expr_sizeWithoutSharing(v_value_5636_);
v___x_5642_ = lean_nat_add(v___x_5640_, v___x_5641_);
lean_dec(v___x_5641_);
lean_dec(v___x_5640_);
v___x_5643_ = l_Lean_Expr_sizeWithoutSharing(v_body_5637_);
v___x_5644_ = lean_nat_add(v___x_5642_, v___x_5643_);
lean_dec(v___x_5643_);
lean_dec(v___x_5642_);
return v___x_5644_;
}
case 10:
{
lean_object* v_expr_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; 
v_expr_5645_ = lean_ctor_get(v_x_5615_, 1);
v___x_5646_ = lean_unsigned_to_nat(1u);
v___x_5647_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5645_);
v___x_5648_ = lean_nat_add(v___x_5646_, v___x_5647_);
lean_dec(v___x_5647_);
return v___x_5648_;
}
case 11:
{
lean_object* v_struct_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; 
v_struct_5649_ = lean_ctor_get(v_x_5615_, 2);
v___x_5650_ = lean_unsigned_to_nat(1u);
v___x_5651_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5649_);
v___x_5652_ = lean_nat_add(v___x_5650_, v___x_5651_);
lean_dec(v___x_5651_);
return v___x_5652_;
}
default: 
{
lean_object* v___x_5653_; 
v___x_5653_ = lean_unsigned_to_nat(1u);
return v___x_5653_;
}
}
v___jp_5616_:
{
lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; 
v___x_5619_ = lean_unsigned_to_nat(1u);
v___x_5620_ = l_Lean_Expr_sizeWithoutSharing(v_d_5617_);
v___x_5621_ = lean_nat_add(v___x_5619_, v___x_5620_);
lean_dec(v___x_5620_);
v___x_5622_ = l_Lean_Expr_sizeWithoutSharing(v_b_5618_);
v___x_5623_ = lean_nat_add(v___x_5621_, v___x_5622_);
lean_dec(v___x_5622_);
lean_dec(v___x_5621_);
return v___x_5623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5654_){
_start:
{
lean_object* v_res_5655_; 
v_res_5655_ = l_Lean_Expr_sizeWithoutSharing(v_x_5654_);
lean_dec_ref(v_x_5654_);
return v_res_5655_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5658_, lean_object* v_e_5659_){
_start:
{
lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; 
v___x_5660_ = l_Lean_KVMap_empty;
v___x_5661_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5662_ = l_Lean_KVMap_insert(v___x_5660_, v_kind_5658_, v___x_5661_);
v___x_5663_ = l_Lean_Expr_mdata___override(v___x_5662_, v_e_5659_);
return v___x_5663_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5664_, lean_object* v_e_5665_){
_start:
{
if (lean_obj_tag(v_e_5665_) == 10)
{
lean_object* v_data_5666_; lean_object* v_expr_5667_; uint8_t v___y_5669_; lean_object* v___x_5672_; lean_object* v___x_5673_; uint8_t v___x_5674_; 
v_data_5666_ = lean_ctor_get(v_e_5665_, 0);
v_expr_5667_ = lean_ctor_get(v_e_5665_, 1);
v___x_5672_ = l_Lean_KVMap_size(v_data_5666_);
v___x_5673_ = lean_unsigned_to_nat(1u);
v___x_5674_ = lean_nat_dec_eq(v___x_5672_, v___x_5673_);
lean_dec(v___x_5672_);
if (v___x_5674_ == 0)
{
v___y_5669_ = v___x_5674_;
goto v___jp_5668_;
}
else
{
uint8_t v___x_5675_; uint8_t v___x_5676_; 
v___x_5675_ = 0;
v___x_5676_ = l_Lean_KVMap_getBool(v_data_5666_, v_kind_5664_, v___x_5675_);
v___y_5669_ = v___x_5676_;
goto v___jp_5668_;
}
v___jp_5668_:
{
if (v___y_5669_ == 0)
{
lean_object* v___x_5670_; 
v___x_5670_ = lean_box(0);
return v___x_5670_;
}
else
{
lean_object* v___x_5671_; 
lean_inc_ref(v_expr_5667_);
v___x_5671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5671_, 0, v_expr_5667_);
return v___x_5671_;
}
}
}
else
{
lean_object* v___x_5677_; 
v___x_5677_ = lean_box(0);
return v___x_5677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* v_kind_5678_, lean_object* v_e_5679_){
_start:
{
lean_object* v_res_5680_; 
v_res_5680_ = l_Lean_annotation_x3f(v_kind_5678_, v_e_5679_);
lean_dec_ref(v_e_5679_);
lean_dec(v_kind_5678_);
return v_res_5680_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* v_e_5684_){
_start:
{
lean_object* v___x_5685_; lean_object* v___x_5686_; 
v___x_5685_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5686_ = l_Lean_mkAnnotation(v___x_5685_, v_e_5684_);
return v___x_5686_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* v_e_5687_){
_start:
{
lean_object* v___x_5688_; lean_object* v___x_5689_; 
v___x_5688_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5689_ = l_Lean_annotation_x3f(v___x_5688_, v_e_5687_);
return v___x_5689_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* v_e_5690_){
_start:
{
lean_object* v_res_5691_; 
v_res_5691_ = l_Lean_inaccessible_x3f(v_e_5690_);
lean_dec_ref(v_e_5690_);
return v_res_5691_;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* v_p_5696_){
_start:
{
if (lean_obj_tag(v_p_5696_) == 10)
{
lean_object* v_data_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; 
v_data_5697_ = lean_ctor_get(v_p_5696_, 0);
v___x_5698_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5699_ = l_Lean_KVMap_find(v_data_5697_, v___x_5698_);
if (lean_obj_tag(v___x_5699_) == 1)
{
lean_object* v_val_5700_; lean_object* v___x_5702_; uint8_t v_isShared_5703_; uint8_t v_isSharedCheck_5711_; 
v_val_5700_ = lean_ctor_get(v___x_5699_, 0);
v_isSharedCheck_5711_ = !lean_is_exclusive(v___x_5699_);
if (v_isSharedCheck_5711_ == 0)
{
v___x_5702_ = v___x_5699_;
v_isShared_5703_ = v_isSharedCheck_5711_;
goto v_resetjp_5701_;
}
else
{
lean_inc(v_val_5700_);
lean_dec(v___x_5699_);
v___x_5702_ = lean_box(0);
v_isShared_5703_ = v_isSharedCheck_5711_;
goto v_resetjp_5701_;
}
v_resetjp_5701_:
{
if (lean_obj_tag(v_val_5700_) == 5)
{
lean_object* v_v_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5708_; 
v_v_5704_ = lean_ctor_get(v_val_5700_, 0);
lean_inc(v_v_5704_);
lean_dec_ref_known(v_val_5700_, 1);
v___x_5705_ = l_Lean_Expr_mdataExpr_x21(v_p_5696_);
v___x_5706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5706_, 0, v_v_5704_);
lean_ctor_set(v___x_5706_, 1, v___x_5705_);
if (v_isShared_5703_ == 0)
{
lean_ctor_set(v___x_5702_, 0, v___x_5706_);
v___x_5708_ = v___x_5702_;
goto v_reusejp_5707_;
}
else
{
lean_object* v_reuseFailAlloc_5709_; 
v_reuseFailAlloc_5709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5709_, 0, v___x_5706_);
v___x_5708_ = v_reuseFailAlloc_5709_;
goto v_reusejp_5707_;
}
v_reusejp_5707_:
{
return v___x_5708_;
}
}
else
{
lean_object* v___x_5710_; 
lean_del_object(v___x_5702_);
lean_dec(v_val_5700_);
v___x_5710_ = lean_box(0);
return v___x_5710_;
}
}
}
else
{
lean_object* v___x_5712_; 
lean_dec(v___x_5699_);
v___x_5712_ = lean_box(0);
return v___x_5712_;
}
}
else
{
lean_object* v___x_5713_; 
v___x_5713_ = lean_box(0);
return v___x_5713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* v_p_5714_){
_start:
{
lean_object* v_res_5715_; 
v_res_5715_ = l_Lean_patternWithRef_x3f(v_p_5714_);
lean_dec_ref(v_p_5714_);
return v_res_5715_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object* v_p_5716_){
_start:
{
lean_object* v___x_5717_; 
v___x_5717_ = l_Lean_patternWithRef_x3f(v_p_5716_);
if (lean_obj_tag(v___x_5717_) == 0)
{
uint8_t v___x_5718_; 
v___x_5718_ = 0;
return v___x_5718_;
}
else
{
uint8_t v___x_5719_; 
lean_dec_ref_known(v___x_5717_, 1);
v___x_5719_ = 1;
return v___x_5719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* v_p_5720_){
_start:
{
uint8_t v_res_5721_; lean_object* v_r_5722_; 
v_res_5721_ = l_Lean_isPatternWithRef(v_p_5720_);
lean_dec_ref(v_p_5720_);
v_r_5722_ = lean_box(v_res_5721_);
return v_r_5722_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* v_p_5723_, lean_object* v_stx_5724_){
_start:
{
lean_object* v___x_5725_; 
v___x_5725_ = l_Lean_patternWithRef_x3f(v_p_5723_);
if (lean_obj_tag(v___x_5725_) == 0)
{
lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; 
v___x_5726_ = l_Lean_KVMap_empty;
v___x_5727_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5728_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_5728_, 0, v_stx_5724_);
v___x_5729_ = l_Lean_KVMap_insert(v___x_5726_, v___x_5727_, v___x_5728_);
v___x_5730_ = l_Lean_Expr_mdata___override(v___x_5729_, v_p_5723_);
return v___x_5730_;
}
else
{
lean_dec_ref_known(v___x_5725_, 1);
lean_dec(v_stx_5724_);
return v_p_5723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* v_e_5731_){
_start:
{
lean_object* v___x_5732_; 
v___x_5732_ = l_Lean_inaccessible_x3f(v_e_5731_);
if (lean_obj_tag(v___x_5732_) == 1)
{
return v___x_5732_;
}
else
{
lean_object* v___x_5733_; 
lean_dec(v___x_5732_);
v___x_5733_ = l_Lean_patternWithRef_x3f(v_e_5731_);
if (lean_obj_tag(v___x_5733_) == 1)
{
lean_object* v_val_5734_; lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5742_; 
v_val_5734_ = lean_ctor_get(v___x_5733_, 0);
v_isSharedCheck_5742_ = !lean_is_exclusive(v___x_5733_);
if (v_isSharedCheck_5742_ == 0)
{
v___x_5736_ = v___x_5733_;
v_isShared_5737_ = v_isSharedCheck_5742_;
goto v_resetjp_5735_;
}
else
{
lean_inc(v_val_5734_);
lean_dec(v___x_5733_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5742_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v_snd_5738_; lean_object* v___x_5740_; 
v_snd_5738_ = lean_ctor_get(v_val_5734_, 1);
lean_inc(v_snd_5738_);
lean_dec(v_val_5734_);
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 0, v_snd_5738_);
v___x_5740_ = v___x_5736_;
goto v_reusejp_5739_;
}
else
{
lean_object* v_reuseFailAlloc_5741_; 
v_reuseFailAlloc_5741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5741_, 0, v_snd_5738_);
v___x_5740_ = v_reuseFailAlloc_5741_;
goto v_reusejp_5739_;
}
v_reusejp_5739_:
{
return v___x_5740_;
}
}
}
else
{
lean_object* v___x_5743_; 
lean_dec(v___x_5733_);
v___x_5743_ = lean_box(0);
return v___x_5743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* v_e_5744_){
_start:
{
lean_object* v_res_5745_; 
v_res_5745_ = l_Lean_patternAnnotation_x3f(v_e_5744_);
lean_dec_ref(v_e_5744_);
return v_res_5745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* v_e_5749_){
_start:
{
lean_object* v___x_5750_; lean_object* v___x_5751_; 
v___x_5750_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5751_ = l_Lean_mkAnnotation(v___x_5750_, v_e_5749_);
return v___x_5751_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* v_e_5755_){
_start:
{
lean_object* v___x_5756_; lean_object* v___x_5757_; 
v___x_5756_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5757_ = l_Lean_annotation_x3f(v___x_5756_, v_e_5755_);
if (lean_obj_tag(v___x_5757_) == 0)
{
return v___x_5757_;
}
else
{
lean_object* v_val_5758_; lean_object* v___x_5760_; uint8_t v_isShared_5761_; uint8_t v_isSharedCheck_5771_; 
v_val_5758_ = lean_ctor_get(v___x_5757_, 0);
v_isSharedCheck_5771_ = !lean_is_exclusive(v___x_5757_);
if (v_isSharedCheck_5771_ == 0)
{
v___x_5760_ = v___x_5757_;
v_isShared_5761_ = v_isSharedCheck_5771_;
goto v_resetjp_5759_;
}
else
{
lean_inc(v_val_5758_);
lean_dec(v___x_5757_);
v___x_5760_ = lean_box(0);
v_isShared_5761_ = v_isSharedCheck_5771_;
goto v_resetjp_5759_;
}
v_resetjp_5759_:
{
lean_object* v___x_5762_; lean_object* v___x_5763_; uint8_t v___x_5764_; 
v___x_5762_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5763_ = lean_unsigned_to_nat(3u);
v___x_5764_ = l_Lean_Expr_isAppOfArity(v_val_5758_, v___x_5762_, v___x_5763_);
if (v___x_5764_ == 0)
{
lean_object* v___x_5765_; 
lean_del_object(v___x_5760_);
lean_dec(v_val_5758_);
v___x_5765_ = lean_box(0);
return v___x_5765_;
}
else
{
lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5769_; 
v___x_5766_ = l_Lean_Expr_appFn_x21(v_val_5758_);
lean_dec(v_val_5758_);
v___x_5767_ = l_Lean_Expr_appArg_x21(v___x_5766_);
lean_dec_ref(v___x_5766_);
if (v_isShared_5761_ == 0)
{
lean_ctor_set(v___x_5760_, 0, v___x_5767_);
v___x_5769_ = v___x_5760_;
goto v_reusejp_5768_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v___x_5767_);
v___x_5769_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5768_;
}
v_reusejp_5768_:
{
return v___x_5769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* v_e_5772_){
_start:
{
lean_object* v_res_5773_; 
v_res_5773_ = l_Lean_isLHSGoal_x3f(v_e_5772_);
lean_dec_ref(v_e_5772_);
return v_res_5773_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* v_toPure_5774_, lean_object* v_____do__lift_5775_){
_start:
{
lean_object* v___x_5776_; 
v___x_5776_ = lean_apply_2(v_toPure_5774_, lean_box(0), v_____do__lift_5775_);
return v___x_5776_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* v_inst_5777_, lean_object* v_inst_5778_){
_start:
{
lean_object* v_toApplicative_5779_; lean_object* v_toBind_5780_; lean_object* v_toPure_5781_; lean_object* v___x_5782_; lean_object* v___f_5783_; lean_object* v___x_5784_; 
v_toApplicative_5779_ = lean_ctor_get(v_inst_5777_, 0);
v_toBind_5780_ = lean_ctor_get(v_inst_5777_, 1);
lean_inc(v_toBind_5780_);
v_toPure_5781_ = lean_ctor_get(v_toApplicative_5779_, 1);
lean_inc(v_toPure_5781_);
v___x_5782_ = l_Lean_mkFreshId___redArg(v_inst_5777_, v_inst_5778_);
v___f_5783_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5783_, 0, v_toPure_5781_);
v___x_5784_ = lean_apply_4(v_toBind_5780_, lean_box(0), lean_box(0), v___x_5782_, v___f_5783_);
return v___x_5784_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* v_m_5785_, lean_object* v_inst_5786_, lean_object* v_inst_5787_){
_start:
{
lean_object* v___x_5788_; 
v___x_5788_ = l_Lean_mkFreshFVarId___redArg(v_inst_5786_, v_inst_5787_);
return v___x_5788_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* v_inst_5789_, lean_object* v_inst_5790_){
_start:
{
lean_object* v_toApplicative_5791_; lean_object* v_toBind_5792_; lean_object* v_toPure_5793_; lean_object* v___x_5794_; lean_object* v___f_5795_; lean_object* v___x_5796_; 
v_toApplicative_5791_ = lean_ctor_get(v_inst_5789_, 0);
v_toBind_5792_ = lean_ctor_get(v_inst_5789_, 1);
lean_inc(v_toBind_5792_);
v_toPure_5793_ = lean_ctor_get(v_toApplicative_5791_, 1);
lean_inc(v_toPure_5793_);
v___x_5794_ = l_Lean_mkFreshId___redArg(v_inst_5789_, v_inst_5790_);
v___f_5795_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5795_, 0, v_toPure_5793_);
v___x_5796_ = lean_apply_4(v_toBind_5792_, lean_box(0), lean_box(0), v___x_5794_, v___f_5795_);
return v___x_5796_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* v_m_5797_, lean_object* v_inst_5798_, lean_object* v_inst_5799_){
_start:
{
lean_object* v___x_5800_; 
v___x_5800_ = l_Lean_mkFreshMVarId___redArg(v_inst_5798_, v_inst_5799_);
return v___x_5800_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* v_inst_5801_, lean_object* v_inst_5802_){
_start:
{
lean_object* v_toApplicative_5803_; lean_object* v_toBind_5804_; lean_object* v_toPure_5805_; lean_object* v___x_5806_; lean_object* v___f_5807_; lean_object* v___x_5808_; 
v_toApplicative_5803_ = lean_ctor_get(v_inst_5801_, 0);
v_toBind_5804_ = lean_ctor_get(v_inst_5801_, 1);
lean_inc(v_toBind_5804_);
v_toPure_5805_ = lean_ctor_get(v_toApplicative_5803_, 1);
lean_inc(v_toPure_5805_);
v___x_5806_ = l_Lean_mkFreshId___redArg(v_inst_5801_, v_inst_5802_);
v___f_5807_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5807_, 0, v_toPure_5805_);
v___x_5808_ = lean_apply_4(v_toBind_5804_, lean_box(0), lean_box(0), v___x_5806_, v___f_5807_);
return v___x_5808_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* v_m_5809_, lean_object* v_inst_5810_, lean_object* v_inst_5811_){
_start:
{
lean_object* v___x_5812_; 
v___x_5812_ = l_Lean_mkFreshLMVarId___redArg(v_inst_5810_, v_inst_5811_);
return v___x_5812_;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2(void){
_start:
{
lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; 
v___x_5816_ = lean_box(0);
v___x_5817_ = ((lean_object*)(l_Lean_mkNot___closed__1));
v___x_5818_ = l_Lean_Expr_const___override(v___x_5817_, v___x_5816_);
return v___x_5818_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* v_p_5819_){
_start:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; 
v___x_5820_ = lean_obj_once(&l_Lean_mkNot___closed__2, &l_Lean_mkNot___closed__2_once, _init_l_Lean_mkNot___closed__2);
v___x_5821_ = l_Lean_Expr_app___override(v___x_5820_, v_p_5819_);
return v___x_5821_;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2(void){
_start:
{
lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; 
v___x_5825_ = lean_box(0);
v___x_5826_ = ((lean_object*)(l_Lean_mkOr___closed__1));
v___x_5827_ = l_Lean_Expr_const___override(v___x_5826_, v___x_5825_);
return v___x_5827_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* v_p_5828_, lean_object* v_q_5829_){
_start:
{
lean_object* v___x_5830_; lean_object* v___x_5831_; 
v___x_5830_ = lean_obj_once(&l_Lean_mkOr___closed__2, &l_Lean_mkOr___closed__2_once, _init_l_Lean_mkOr___closed__2);
v___x_5831_ = l_Lean_mkAppB(v___x_5830_, v_p_5828_, v_q_5829_);
return v___x_5831_;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2(void){
_start:
{
lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; 
v___x_5835_ = lean_box(0);
v___x_5836_ = ((lean_object*)(l_Lean_mkAnd___closed__1));
v___x_5837_ = l_Lean_Expr_const___override(v___x_5836_, v___x_5835_);
return v___x_5837_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* v_p_5838_, lean_object* v_q_5839_){
_start:
{
lean_object* v___x_5840_; lean_object* v___x_5841_; 
v___x_5840_ = lean_obj_once(&l_Lean_mkAnd___closed__2, &l_Lean_mkAnd___closed__2_once, _init_l_Lean_mkAnd___closed__2);
v___x_5841_ = l_Lean_mkAppB(v___x_5840_, v_p_5838_, v_q_5839_);
return v___x_5841_;
}
}
static lean_object* _init_l_Lean_mkAndN___closed__0(void){
_start:
{
lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; 
v___x_5842_ = lean_box(0);
v___x_5843_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_5844_ = l_Lean_Expr_const___override(v___x_5843_, v___x_5842_);
return v___x_5844_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* v_x_5845_){
_start:
{
if (lean_obj_tag(v_x_5845_) == 0)
{
lean_object* v___x_5846_; 
v___x_5846_ = lean_obj_once(&l_Lean_mkAndN___closed__0, &l_Lean_mkAndN___closed__0_once, _init_l_Lean_mkAndN___closed__0);
return v___x_5846_;
}
else
{
lean_object* v_tail_5847_; 
v_tail_5847_ = lean_ctor_get(v_x_5845_, 1);
if (lean_obj_tag(v_tail_5847_) == 0)
{
lean_object* v_head_5848_; 
v_head_5848_ = lean_ctor_get(v_x_5845_, 0);
lean_inc(v_head_5848_);
lean_dec_ref_known(v_x_5845_, 2);
return v_head_5848_;
}
else
{
lean_object* v_head_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; 
lean_inc(v_tail_5847_);
v_head_5849_ = lean_ctor_get(v_x_5845_, 0);
lean_inc(v_head_5849_);
lean_dec_ref_known(v_x_5845_, 2);
v___x_5850_ = l_Lean_mkAndN(v_tail_5847_);
v___x_5851_ = l_Lean_mkAnd(v_head_5849_, v___x_5850_);
return v___x_5851_;
}
}
}
}
static lean_object* _init_l_Lean_mkEM___closed__3(void){
_start:
{
lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; 
v___x_5857_ = lean_box(0);
v___x_5858_ = ((lean_object*)(l_Lean_mkEM___closed__2));
v___x_5859_ = l_Lean_Expr_const___override(v___x_5858_, v___x_5857_);
return v___x_5859_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* v_p_5860_){
_start:
{
lean_object* v___x_5861_; lean_object* v___x_5862_; 
v___x_5861_ = lean_obj_once(&l_Lean_mkEM___closed__3, &l_Lean_mkEM___closed__3_once, _init_l_Lean_mkEM___closed__3);
v___x_5862_ = l_Lean_Expr_app___override(v___x_5861_, v_p_5860_);
return v___x_5862_;
}
}
static lean_object* _init_l_Lean_mkIff___closed__2(void){
_start:
{
lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; 
v___x_5866_ = lean_box(0);
v___x_5867_ = ((lean_object*)(l_Lean_mkIff___closed__1));
v___x_5868_ = l_Lean_Expr_const___override(v___x_5867_, v___x_5866_);
return v___x_5868_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* v_p_5869_, lean_object* v_q_5870_){
_start:
{
lean_object* v___x_5871_; lean_object* v___x_5872_; 
v___x_5871_ = lean_obj_once(&l_Lean_mkIff___closed__2, &l_Lean_mkIff___closed__2_once, _init_l_Lean_mkIff___closed__2);
v___x_5872_ = l_Lean_mkAppB(v___x_5871_, v_p_5869_, v_q_5870_);
return v___x_5872_;
}
}
static lean_object* _init_l_Lean_Nat_mkType(void){
_start:
{
lean_object* v___x_5873_; 
v___x_5873_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_5873_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; 
v___x_5877_ = lean_box(0);
v___x_5878_ = ((lean_object*)(l_Lean_Nat_mkInstAdd___closed__1));
v___x_5879_ = l_Lean_Expr_const___override(v___x_5878_, v___x_5877_);
return v___x_5879_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd(void){
_start:
{
lean_object* v___x_5880_; 
v___x_5880_ = lean_obj_once(&l_Lean_Nat_mkInstAdd___closed__2, &l_Lean_Nat_mkInstAdd___closed__2_once, _init_l_Lean_Nat_mkInstAdd___closed__2);
return v___x_5880_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__2(void){
_start:
{
lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; 
v___x_5884_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5885_ = ((lean_object*)(l_Lean_Nat_mkInstHAdd___closed__1));
v___x_5886_ = l_Lean_Expr_const___override(v___x_5885_, v___x_5884_);
return v___x_5886_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__3(void){
_start:
{
lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; 
v___x_5887_ = l_Lean_Nat_mkInstAdd;
v___x_5888_ = l_Lean_Nat_mkType;
v___x_5889_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_5890_ = l_Lean_mkAppB(v___x_5889_, v___x_5888_, v___x_5887_);
return v___x_5890_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd(void){
_start:
{
lean_object* v___x_5891_; 
v___x_5891_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__3, &l_Lean_Nat_mkInstHAdd___closed__3_once, _init_l_Lean_Nat_mkInstHAdd___closed__3);
return v___x_5891_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; 
v___x_5895_ = lean_box(0);
v___x_5896_ = ((lean_object*)(l_Lean_Nat_mkInstSub___closed__1));
v___x_5897_ = l_Lean_Expr_const___override(v___x_5896_, v___x_5895_);
return v___x_5897_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub(void){
_start:
{
lean_object* v___x_5898_; 
v___x_5898_ = lean_obj_once(&l_Lean_Nat_mkInstSub___closed__2, &l_Lean_Nat_mkInstSub___closed__2_once, _init_l_Lean_Nat_mkInstSub___closed__2);
return v___x_5898_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__2(void){
_start:
{
lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; 
v___x_5902_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5903_ = ((lean_object*)(l_Lean_Nat_mkInstHSub___closed__1));
v___x_5904_ = l_Lean_Expr_const___override(v___x_5903_, v___x_5902_);
return v___x_5904_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__3(void){
_start:
{
lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; 
v___x_5905_ = l_Lean_Nat_mkInstSub;
v___x_5906_ = l_Lean_Nat_mkType;
v___x_5907_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_5908_ = l_Lean_mkAppB(v___x_5907_, v___x_5906_, v___x_5905_);
return v___x_5908_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub(void){
_start:
{
lean_object* v___x_5909_; 
v___x_5909_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__3, &l_Lean_Nat_mkInstHSub___closed__3_once, _init_l_Lean_Nat_mkInstHSub___closed__3);
return v___x_5909_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; 
v___x_5913_ = lean_box(0);
v___x_5914_ = ((lean_object*)(l_Lean_Nat_mkInstMul___closed__1));
v___x_5915_ = l_Lean_Expr_const___override(v___x_5914_, v___x_5913_);
return v___x_5915_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul(void){
_start:
{
lean_object* v___x_5916_; 
v___x_5916_ = lean_obj_once(&l_Lean_Nat_mkInstMul___closed__2, &l_Lean_Nat_mkInstMul___closed__2_once, _init_l_Lean_Nat_mkInstMul___closed__2);
return v___x_5916_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__2(void){
_start:
{
lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; 
v___x_5920_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5921_ = ((lean_object*)(l_Lean_Nat_mkInstHMul___closed__1));
v___x_5922_ = l_Lean_Expr_const___override(v___x_5921_, v___x_5920_);
return v___x_5922_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; 
v___x_5923_ = l_Lean_Nat_mkInstMul;
v___x_5924_ = l_Lean_Nat_mkType;
v___x_5925_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_5926_ = l_Lean_mkAppB(v___x_5925_, v___x_5924_, v___x_5923_);
return v___x_5926_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul(void){
_start:
{
lean_object* v___x_5927_; 
v___x_5927_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__3, &l_Lean_Nat_mkInstHMul___closed__3_once, _init_l_Lean_Nat_mkInstHMul___closed__3);
return v___x_5927_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv___closed__2(void){
_start:
{
lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; 
v___x_5932_ = lean_box(0);
v___x_5933_ = ((lean_object*)(l_Lean_Nat_mkInstDiv___closed__1));
v___x_5934_ = l_Lean_Expr_const___override(v___x_5933_, v___x_5932_);
return v___x_5934_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv(void){
_start:
{
lean_object* v___x_5935_; 
v___x_5935_ = lean_obj_once(&l_Lean_Nat_mkInstDiv___closed__2, &l_Lean_Nat_mkInstDiv___closed__2_once, _init_l_Lean_Nat_mkInstDiv___closed__2);
return v___x_5935_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__2(void){
_start:
{
lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; 
v___x_5939_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5940_ = ((lean_object*)(l_Lean_Nat_mkInstHDiv___closed__1));
v___x_5941_ = l_Lean_Expr_const___override(v___x_5940_, v___x_5939_);
return v___x_5941_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__3(void){
_start:
{
lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; 
v___x_5942_ = l_Lean_Nat_mkInstDiv;
v___x_5943_ = l_Lean_Nat_mkType;
v___x_5944_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_5945_ = l_Lean_mkAppB(v___x_5944_, v___x_5943_, v___x_5942_);
return v___x_5945_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv(void){
_start:
{
lean_object* v___x_5946_; 
v___x_5946_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__3, &l_Lean_Nat_mkInstHDiv___closed__3_once, _init_l_Lean_Nat_mkInstHDiv___closed__3);
return v___x_5946_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod___closed__2(void){
_start:
{
lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; 
v___x_5951_ = lean_box(0);
v___x_5952_ = ((lean_object*)(l_Lean_Nat_mkInstMod___closed__1));
v___x_5953_ = l_Lean_Expr_const___override(v___x_5952_, v___x_5951_);
return v___x_5953_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod(void){
_start:
{
lean_object* v___x_5954_; 
v___x_5954_ = lean_obj_once(&l_Lean_Nat_mkInstMod___closed__2, &l_Lean_Nat_mkInstMod___closed__2_once, _init_l_Lean_Nat_mkInstMod___closed__2);
return v___x_5954_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__2(void){
_start:
{
lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; 
v___x_5958_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5959_ = ((lean_object*)(l_Lean_Nat_mkInstHMod___closed__1));
v___x_5960_ = l_Lean_Expr_const___override(v___x_5959_, v___x_5958_);
return v___x_5960_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__3(void){
_start:
{
lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; 
v___x_5961_ = l_Lean_Nat_mkInstMod;
v___x_5962_ = l_Lean_Nat_mkType;
v___x_5963_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_5964_ = l_Lean_mkAppB(v___x_5963_, v___x_5962_, v___x_5961_);
return v___x_5964_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod(void){
_start:
{
lean_object* v___x_5965_; 
v___x_5965_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__3, &l_Lean_Nat_mkInstHMod___closed__3_once, _init_l_Lean_Nat_mkInstHMod___closed__3);
return v___x_5965_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow___closed__2(void){
_start:
{
lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; 
v___x_5969_ = lean_box(0);
v___x_5970_ = ((lean_object*)(l_Lean_Nat_mkInstNatPow___closed__1));
v___x_5971_ = l_Lean_Expr_const___override(v___x_5970_, v___x_5969_);
return v___x_5971_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow(void){
_start:
{
lean_object* v___x_5972_; 
v___x_5972_ = lean_obj_once(&l_Lean_Nat_mkInstNatPow___closed__2, &l_Lean_Nat_mkInstNatPow___closed__2_once, _init_l_Lean_Nat_mkInstNatPow___closed__2);
return v___x_5972_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; 
v___x_5976_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5977_ = ((lean_object*)(l_Lean_Nat_mkInstPow___closed__1));
v___x_5978_ = l_Lean_Expr_const___override(v___x_5977_, v___x_5976_);
return v___x_5978_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__3(void){
_start:
{
lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; 
v___x_5979_ = l_Lean_Nat_mkInstNatPow;
v___x_5980_ = l_Lean_Nat_mkType;
v___x_5981_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_5982_ = l_Lean_mkAppB(v___x_5981_, v___x_5980_, v___x_5979_);
return v___x_5982_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow(void){
_start:
{
lean_object* v___x_5983_; 
v___x_5983_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__3, &l_Lean_Nat_mkInstPow___closed__3_once, _init_l_Lean_Nat_mkInstPow___closed__3);
return v___x_5983_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__3(void){
_start:
{
lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; 
v___x_5990_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__2));
v___x_5991_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__1));
v___x_5992_ = l_Lean_Expr_const___override(v___x_5991_, v___x_5990_);
return v___x_5992_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__4(void){
_start:
{
lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; 
v___x_5993_ = l_Lean_Nat_mkInstPow;
v___x_5994_ = l_Lean_Nat_mkType;
v___x_5995_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_5996_ = l_Lean_mkApp3(v___x_5995_, v___x_5994_, v___x_5994_, v___x_5993_);
return v___x_5996_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow(void){
_start:
{
lean_object* v___x_5997_; 
v___x_5997_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__4, &l_Lean_Nat_mkInstHPow___closed__4_once, _init_l_Lean_Nat_mkInstHPow___closed__4);
return v___x_5997_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; 
v___x_6001_ = lean_box(0);
v___x_6002_ = ((lean_object*)(l_Lean_Nat_mkInstLT___closed__1));
v___x_6003_ = l_Lean_Expr_const___override(v___x_6002_, v___x_6001_);
return v___x_6003_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT(void){
_start:
{
lean_object* v___x_6004_; 
v___x_6004_ = lean_obj_once(&l_Lean_Nat_mkInstLT___closed__2, &l_Lean_Nat_mkInstLT___closed__2_once, _init_l_Lean_Nat_mkInstLT___closed__2);
return v___x_6004_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; 
v___x_6008_ = lean_box(0);
v___x_6009_ = ((lean_object*)(l_Lean_Nat_mkInstLE___closed__1));
v___x_6010_ = l_Lean_Expr_const___override(v___x_6009_, v___x_6008_);
return v___x_6010_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE(void){
_start:
{
lean_object* v___x_6011_; 
v___x_6011_ = lean_obj_once(&l_Lean_Nat_mkInstLE___closed__2, &l_Lean_Nat_mkInstLE___closed__2_once, _init_l_Lean_Nat_mkInstLE___closed__2);
return v___x_6011_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3(void){
_start:
{
lean_object* v___x_6017_; lean_object* v___x_6018_; 
v___x_6017_ = lean_unsigned_to_nat(0u);
v___x_6018_ = l_Lean_Level_ofNat(v___x_6017_);
return v___x_6018_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4(void){
_start:
{
lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; 
v___x_6019_ = lean_box(0);
v___x_6020_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6021_, 0, v___x_6020_);
lean_ctor_set(v___x_6021_, 1, v___x_6019_);
return v___x_6021_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5(void){
_start:
{
lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; 
v___x_6022_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6023_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6024_, 0, v___x_6023_);
lean_ctor_set(v___x_6024_, 1, v___x_6022_);
return v___x_6024_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6(void){
_start:
{
lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; 
v___x_6025_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__5, &l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5);
v___x_6026_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6026_);
lean_ctor_set(v___x_6027_, 1, v___x_6025_);
return v___x_6027_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7(void){
_start:
{
lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; 
v___x_6028_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6029_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natAddFn___closed__2));
v___x_6030_ = l_Lean_Expr_const___override(v___x_6029_, v___x_6028_);
return v___x_6030_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8(void){
_start:
{
lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; 
v___x_6031_ = l_Lean_Nat_mkInstHAdd;
v___x_6032_ = l_Lean_Nat_mkType;
v___x_6033_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6034_ = l_Lean_mkApp4(v___x_6033_, v___x_6032_, v___x_6032_, v___x_6032_, v___x_6031_);
return v___x_6034_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn(void){
_start:
{
lean_object* v___x_6035_; 
v___x_6035_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__8, &l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8);
return v___x_6035_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3(void){
_start:
{
lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; 
v___x_6041_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6042_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natSubFn___closed__2));
v___x_6043_ = l_Lean_Expr_const___override(v___x_6042_, v___x_6041_);
return v___x_6043_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4(void){
_start:
{
lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; 
v___x_6044_ = l_Lean_Nat_mkInstHSub;
v___x_6045_ = l_Lean_Nat_mkType;
v___x_6046_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6047_ = l_Lean_mkApp4(v___x_6046_, v___x_6045_, v___x_6045_, v___x_6045_, v___x_6044_);
return v___x_6047_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn(void){
_start:
{
lean_object* v___x_6048_; 
v___x_6048_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__4, &l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4);
return v___x_6048_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3(void){
_start:
{
lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; 
v___x_6054_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6055_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natMulFn___closed__2));
v___x_6056_ = l_Lean_Expr_const___override(v___x_6055_, v___x_6054_);
return v___x_6056_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4(void){
_start:
{
lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; 
v___x_6057_ = l_Lean_Nat_mkInstHMul;
v___x_6058_ = l_Lean_Nat_mkType;
v___x_6059_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6060_ = l_Lean_mkApp4(v___x_6059_, v___x_6058_, v___x_6058_, v___x_6058_, v___x_6057_);
return v___x_6060_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn(void){
_start:
{
lean_object* v___x_6061_; 
v___x_6061_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__4, &l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4);
return v___x_6061_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3(void){
_start:
{
lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; 
v___x_6067_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6068_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natPowFn___closed__2));
v___x_6069_ = l_Lean_Expr_const___override(v___x_6068_, v___x_6067_);
return v___x_6069_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4(void){
_start:
{
lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; 
v___x_6070_ = l_Lean_Nat_mkInstHPow;
v___x_6071_ = l_Lean_Nat_mkType;
v___x_6072_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6073_ = l_Lean_mkApp4(v___x_6072_, v___x_6071_, v___x_6071_, v___x_6071_, v___x_6070_);
return v___x_6073_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn(void){
_start:
{
lean_object* v___x_6074_; 
v___x_6074_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__4, &l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4);
return v___x_6074_;
}
}
static lean_object* _init_l_Lean_mkNatSucc___closed__2(void){
_start:
{
lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; 
v___x_6079_ = lean_box(0);
v___x_6080_ = ((lean_object*)(l_Lean_mkNatSucc___closed__1));
v___x_6081_ = l_Lean_Expr_const___override(v___x_6080_, v___x_6079_);
return v___x_6081_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* v_a_6082_){
_start:
{
lean_object* v___x_6083_; lean_object* v___x_6084_; 
v___x_6083_ = lean_obj_once(&l_Lean_mkNatSucc___closed__2, &l_Lean_mkNatSucc___closed__2_once, _init_l_Lean_mkNatSucc___closed__2);
v___x_6084_ = l_Lean_Expr_app___override(v___x_6083_, v_a_6082_);
return v___x_6084_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* v_a_6085_, lean_object* v_b_6086_){
_start:
{
lean_object* v___x_6087_; lean_object* v___x_6088_; 
v___x_6087_ = l___private_Lean_Expr_0__Lean_natAddFn;
v___x_6088_ = l_Lean_mkAppB(v___x_6087_, v_a_6085_, v_b_6086_);
return v___x_6088_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* v_a_6089_, lean_object* v_b_6090_){
_start:
{
lean_object* v___x_6091_; lean_object* v___x_6092_; 
v___x_6091_ = l___private_Lean_Expr_0__Lean_natSubFn;
v___x_6092_ = l_Lean_mkAppB(v___x_6091_, v_a_6089_, v_b_6090_);
return v___x_6092_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* v_a_6093_, lean_object* v_b_6094_){
_start:
{
lean_object* v___x_6095_; lean_object* v___x_6096_; 
v___x_6095_ = l___private_Lean_Expr_0__Lean_natMulFn;
v___x_6096_ = l_Lean_mkAppB(v___x_6095_, v_a_6093_, v_b_6094_);
return v___x_6096_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object* v_a_6097_, lean_object* v_b_6098_){
_start:
{
lean_object* v___x_6099_; lean_object* v___x_6100_; 
v___x_6099_ = l___private_Lean_Expr_0__Lean_natPowFn;
v___x_6100_ = l_Lean_mkAppB(v___x_6099_, v_a_6097_, v_b_6098_);
return v___x_6100_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3(void){
_start:
{
lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; 
v___x_6106_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6107_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natLEPred___closed__2));
v___x_6108_ = l_Lean_Expr_const___override(v___x_6107_, v___x_6106_);
return v___x_6108_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4(void){
_start:
{
lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; 
v___x_6109_ = l_Lean_Nat_mkInstLE;
v___x_6110_ = l_Lean_Nat_mkType;
v___x_6111_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6112_ = l_Lean_mkAppB(v___x_6111_, v___x_6110_, v___x_6109_);
return v___x_6112_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred(void){
_start:
{
lean_object* v___x_6113_; 
v___x_6113_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__4, &l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4);
return v___x_6113_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* v_a_6114_, lean_object* v_b_6115_){
_start:
{
lean_object* v___x_6116_; lean_object* v___x_6117_; 
v___x_6116_ = l___private_Lean_Expr_0__Lean_natLEPred;
v___x_6117_ = l_Lean_mkAppB(v___x_6116_, v_a_6114_, v_b_6115_);
return v___x_6117_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0(void){
_start:
{
lean_object* v___x_6118_; lean_object* v___x_6119_; 
v___x_6118_ = lean_unsigned_to_nat(1u);
v___x_6119_ = l_Lean_Level_ofNat(v___x_6118_);
return v___x_6119_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1(void){
_start:
{
lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; 
v___x_6120_ = lean_box(0);
v___x_6121_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__0, &l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0);
v___x_6122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6122_, 0, v___x_6121_);
lean_ctor_set(v___x_6122_, 1, v___x_6120_);
return v___x_6122_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2(void){
_start:
{
lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; 
v___x_6123_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__1, &l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1);
v___x_6124_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_6125_ = l_Lean_Expr_const___override(v___x_6124_, v___x_6123_);
return v___x_6125_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3(void){
_start:
{
lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; 
v___x_6126_ = l_Lean_Nat_mkType;
v___x_6127_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6128_ = l_Lean_Expr_app___override(v___x_6127_, v___x_6126_);
return v___x_6128_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred(void){
_start:
{
lean_object* v___x_6129_; 
v___x_6129_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__3, &l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3);
return v___x_6129_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* v_a_6130_, lean_object* v_b_6131_){
_start:
{
lean_object* v___x_6132_; lean_object* v___x_6133_; 
v___x_6132_ = l___private_Lean_Expr_0__Lean_natEqPred;
v___x_6133_ = l_Lean_mkAppB(v___x_6132_, v_a_6130_, v_b_6131_);
return v___x_6133_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__0(void){
_start:
{
lean_object* v___x_6134_; lean_object* v___x_6135_; 
v___x_6134_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6135_ = l_Lean_Expr_sort___override(v___x_6134_);
return v___x_6135_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__1(void){
_start:
{
lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; 
v___x_6136_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__0, &l___private_Lean_Expr_0__Lean_propEq___closed__0_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__0);
v___x_6137_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6138_ = l_Lean_Expr_app___override(v___x_6137_, v___x_6136_);
return v___x_6138_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq(void){
_start:
{
lean_object* v___x_6139_; 
v___x_6139_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__1, &l___private_Lean_Expr_0__Lean_propEq___closed__1_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__1);
return v___x_6139_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* v_a_6140_, lean_object* v_b_6141_){
_start:
{
lean_object* v___x_6142_; lean_object* v___x_6143_; 
v___x_6142_ = l___private_Lean_Expr_0__Lean_propEq;
v___x_6143_ = l_Lean_mkAppB(v___x_6142_, v_a_6140_, v_b_6141_);
return v___x_6143_;
}
}
static lean_object* _init_l_Lean_Int_mkType___closed__2(void){
_start:
{
lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; 
v___x_6147_ = lean_box(0);
v___x_6148_ = ((lean_object*)(l_Lean_Int_mkType___closed__1));
v___x_6149_ = l_Lean_Expr_const___override(v___x_6148_, v___x_6147_);
return v___x_6149_;
}
}
static lean_object* _init_l_Lean_Int_mkType(void){
_start:
{
lean_object* v___x_6150_; 
v___x_6150_ = lean_obj_once(&l_Lean_Int_mkType___closed__2, &l_Lean_Int_mkType___closed__2_once, _init_l_Lean_Int_mkType___closed__2);
return v___x_6150_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg___closed__2(void){
_start:
{
lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; 
v___x_6155_ = lean_box(0);
v___x_6156_ = ((lean_object*)(l_Lean_Int_mkInstNeg___closed__1));
v___x_6157_ = l_Lean_Expr_const___override(v___x_6156_, v___x_6155_);
return v___x_6157_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg(void){
_start:
{
lean_object* v___x_6158_; 
v___x_6158_ = lean_obj_once(&l_Lean_Int_mkInstNeg___closed__2, &l_Lean_Int_mkInstNeg___closed__2_once, _init_l_Lean_Int_mkInstNeg___closed__2);
return v___x_6158_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; 
v___x_6163_ = lean_box(0);
v___x_6164_ = ((lean_object*)(l_Lean_Int_mkInstAdd___closed__1));
v___x_6165_ = l_Lean_Expr_const___override(v___x_6164_, v___x_6163_);
return v___x_6165_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd(void){
_start:
{
lean_object* v___x_6166_; 
v___x_6166_ = lean_obj_once(&l_Lean_Int_mkInstAdd___closed__2, &l_Lean_Int_mkInstAdd___closed__2_once, _init_l_Lean_Int_mkInstAdd___closed__2);
return v___x_6166_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd___closed__0(void){
_start:
{
lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; 
v___x_6167_ = l_Lean_Int_mkInstAdd;
v___x_6168_ = l_Lean_Int_mkType;
v___x_6169_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6170_ = l_Lean_mkAppB(v___x_6169_, v___x_6168_, v___x_6167_);
return v___x_6170_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd(void){
_start:
{
lean_object* v___x_6171_; 
v___x_6171_ = lean_obj_once(&l_Lean_Int_mkInstHAdd___closed__0, &l_Lean_Int_mkInstHAdd___closed__0_once, _init_l_Lean_Int_mkInstHAdd___closed__0);
return v___x_6171_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; 
v___x_6176_ = lean_box(0);
v___x_6177_ = ((lean_object*)(l_Lean_Int_mkInstSub___closed__1));
v___x_6178_ = l_Lean_Expr_const___override(v___x_6177_, v___x_6176_);
return v___x_6178_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub(void){
_start:
{
lean_object* v___x_6179_; 
v___x_6179_ = lean_obj_once(&l_Lean_Int_mkInstSub___closed__2, &l_Lean_Int_mkInstSub___closed__2_once, _init_l_Lean_Int_mkInstSub___closed__2);
return v___x_6179_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub___closed__0(void){
_start:
{
lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; 
v___x_6180_ = l_Lean_Int_mkInstSub;
v___x_6181_ = l_Lean_Int_mkType;
v___x_6182_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6183_ = l_Lean_mkAppB(v___x_6182_, v___x_6181_, v___x_6180_);
return v___x_6183_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub(void){
_start:
{
lean_object* v___x_6184_; 
v___x_6184_ = lean_obj_once(&l_Lean_Int_mkInstHSub___closed__0, &l_Lean_Int_mkInstHSub___closed__0_once, _init_l_Lean_Int_mkInstHSub___closed__0);
return v___x_6184_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; 
v___x_6189_ = lean_box(0);
v___x_6190_ = ((lean_object*)(l_Lean_Int_mkInstMul___closed__1));
v___x_6191_ = l_Lean_Expr_const___override(v___x_6190_, v___x_6189_);
return v___x_6191_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul(void){
_start:
{
lean_object* v___x_6192_; 
v___x_6192_ = lean_obj_once(&l_Lean_Int_mkInstMul___closed__2, &l_Lean_Int_mkInstMul___closed__2_once, _init_l_Lean_Int_mkInstMul___closed__2);
return v___x_6192_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul___closed__0(void){
_start:
{
lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; 
v___x_6193_ = l_Lean_Int_mkInstMul;
v___x_6194_ = l_Lean_Int_mkType;
v___x_6195_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6196_ = l_Lean_mkAppB(v___x_6195_, v___x_6194_, v___x_6193_);
return v___x_6196_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul(void){
_start:
{
lean_object* v___x_6197_; 
v___x_6197_ = lean_obj_once(&l_Lean_Int_mkInstHMul___closed__0, &l_Lean_Int_mkInstHMul___closed__0_once, _init_l_Lean_Int_mkInstHMul___closed__0);
return v___x_6197_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv___closed__1(void){
_start:
{
lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; 
v___x_6201_ = lean_box(0);
v___x_6202_ = ((lean_object*)(l_Lean_Int_mkInstDiv___closed__0));
v___x_6203_ = l_Lean_Expr_const___override(v___x_6202_, v___x_6201_);
return v___x_6203_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv(void){
_start:
{
lean_object* v___x_6204_; 
v___x_6204_ = lean_obj_once(&l_Lean_Int_mkInstDiv___closed__1, &l_Lean_Int_mkInstDiv___closed__1_once, _init_l_Lean_Int_mkInstDiv___closed__1);
return v___x_6204_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv___closed__0(void){
_start:
{
lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; 
v___x_6205_ = l_Lean_Int_mkInstDiv;
v___x_6206_ = l_Lean_Int_mkType;
v___x_6207_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6208_ = l_Lean_mkAppB(v___x_6207_, v___x_6206_, v___x_6205_);
return v___x_6208_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv(void){
_start:
{
lean_object* v___x_6209_; 
v___x_6209_ = lean_obj_once(&l_Lean_Int_mkInstHDiv___closed__0, &l_Lean_Int_mkInstHDiv___closed__0_once, _init_l_Lean_Int_mkInstHDiv___closed__0);
return v___x_6209_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod___closed__1(void){
_start:
{
lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; 
v___x_6213_ = lean_box(0);
v___x_6214_ = ((lean_object*)(l_Lean_Int_mkInstMod___closed__0));
v___x_6215_ = l_Lean_Expr_const___override(v___x_6214_, v___x_6213_);
return v___x_6215_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod(void){
_start:
{
lean_object* v___x_6216_; 
v___x_6216_ = lean_obj_once(&l_Lean_Int_mkInstMod___closed__1, &l_Lean_Int_mkInstMod___closed__1_once, _init_l_Lean_Int_mkInstMod___closed__1);
return v___x_6216_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod___closed__0(void){
_start:
{
lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; 
v___x_6217_ = l_Lean_Int_mkInstMod;
v___x_6218_ = l_Lean_Int_mkType;
v___x_6219_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6220_ = l_Lean_mkAppB(v___x_6219_, v___x_6218_, v___x_6217_);
return v___x_6220_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod(void){
_start:
{
lean_object* v___x_6221_; 
v___x_6221_ = lean_obj_once(&l_Lean_Int_mkInstHMod___closed__0, &l_Lean_Int_mkInstHMod___closed__0_once, _init_l_Lean_Int_mkInstHMod___closed__0);
return v___x_6221_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; 
v___x_6226_ = lean_box(0);
v___x_6227_ = ((lean_object*)(l_Lean_Int_mkInstPow___closed__1));
v___x_6228_ = l_Lean_Expr_const___override(v___x_6227_, v___x_6226_);
return v___x_6228_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow(void){
_start:
{
lean_object* v___x_6229_; 
v___x_6229_ = lean_obj_once(&l_Lean_Int_mkInstPow___closed__2, &l_Lean_Int_mkInstPow___closed__2_once, _init_l_Lean_Int_mkInstPow___closed__2);
return v___x_6229_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat___closed__0(void){
_start:
{
lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; 
v___x_6230_ = l_Lean_Int_mkInstPow;
v___x_6231_ = l_Lean_Int_mkType;
v___x_6232_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6233_ = l_Lean_mkAppB(v___x_6232_, v___x_6231_, v___x_6230_);
return v___x_6233_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat(void){
_start:
{
lean_object* v___x_6234_; 
v___x_6234_ = lean_obj_once(&l_Lean_Int_mkInstPowNat___closed__0, &l_Lean_Int_mkInstPowNat___closed__0_once, _init_l_Lean_Int_mkInstPowNat___closed__0);
return v___x_6234_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow___closed__0(void){
_start:
{
lean_object* v___x_6235_; lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; lean_object* v___x_6239_; 
v___x_6235_ = l_Lean_Int_mkInstPowNat;
v___x_6236_ = l_Lean_Nat_mkType;
v___x_6237_ = l_Lean_Int_mkType;
v___x_6238_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6239_ = l_Lean_mkApp3(v___x_6238_, v___x_6237_, v___x_6236_, v___x_6235_);
return v___x_6239_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow(void){
_start:
{
lean_object* v___x_6240_; 
v___x_6240_ = lean_obj_once(&l_Lean_Int_mkInstHPow___closed__0, &l_Lean_Int_mkInstHPow___closed__0_once, _init_l_Lean_Int_mkInstHPow___closed__0);
return v___x_6240_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6245_; lean_object* v___x_6246_; lean_object* v___x_6247_; 
v___x_6245_ = lean_box(0);
v___x_6246_ = ((lean_object*)(l_Lean_Int_mkInstLT___closed__1));
v___x_6247_ = l_Lean_Expr_const___override(v___x_6246_, v___x_6245_);
return v___x_6247_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT(void){
_start:
{
lean_object* v___x_6248_; 
v___x_6248_ = lean_obj_once(&l_Lean_Int_mkInstLT___closed__2, &l_Lean_Int_mkInstLT___closed__2_once, _init_l_Lean_Int_mkInstLT___closed__2);
return v___x_6248_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; 
v___x_6253_ = lean_box(0);
v___x_6254_ = ((lean_object*)(l_Lean_Int_mkInstLE___closed__1));
v___x_6255_ = l_Lean_Expr_const___override(v___x_6254_, v___x_6253_);
return v___x_6255_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE(void){
_start:
{
lean_object* v___x_6256_; 
v___x_6256_ = lean_obj_once(&l_Lean_Int_mkInstLE___closed__2, &l_Lean_Int_mkInstLE___closed__2_once, _init_l_Lean_Int_mkInstLE___closed__2);
return v___x_6256_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast___closed__2(void){
_start:
{
lean_object* v___x_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; 
v___x_6260_ = lean_box(0);
v___x_6261_ = ((lean_object*)(l_Lean_Int_mkInstNatCast___closed__1));
v___x_6262_ = l_Lean_Expr_const___override(v___x_6261_, v___x_6260_);
return v___x_6262_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast(void){
_start:
{
lean_object* v___x_6263_; 
v___x_6263_ = lean_obj_once(&l_Lean_Int_mkInstNatCast___closed__2, &l_Lean_Int_mkInstNatCast___closed__2_once, _init_l_Lean_Int_mkInstNatCast___closed__2);
return v___x_6263_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0(void){
_start:
{
lean_object* v___x_6264_; lean_object* v___x_6265_; lean_object* v___x_6266_; 
v___x_6264_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6265_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_6266_ = l_Lean_Expr_const___override(v___x_6265_, v___x_6264_);
return v___x_6266_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1(void){
_start:
{
lean_object* v___x_6267_; lean_object* v___x_6268_; lean_object* v___x_6269_; lean_object* v___x_6270_; 
v___x_6267_ = l_Lean_Int_mkInstNeg;
v___x_6268_ = l_Lean_Int_mkType;
v___x_6269_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__0, &l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0);
v___x_6270_ = l_Lean_mkAppB(v___x_6269_, v___x_6268_, v___x_6267_);
return v___x_6270_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn(void){
_start:
{
lean_object* v___x_6271_; 
v___x_6271_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__1, &l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1);
return v___x_6271_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0(void){
_start:
{
lean_object* v___x_6272_; lean_object* v___x_6273_; lean_object* v___x_6274_; lean_object* v___x_6275_; 
v___x_6272_ = l_Lean_Int_mkInstHAdd;
v___x_6273_ = l_Lean_Int_mkType;
v___x_6274_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6275_ = l_Lean_mkApp4(v___x_6274_, v___x_6273_, v___x_6273_, v___x_6273_, v___x_6272_);
return v___x_6275_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn(void){
_start:
{
lean_object* v___x_6276_; 
v___x_6276_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intAddFn___closed__0, &l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0);
return v___x_6276_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0(void){
_start:
{
lean_object* v___x_6277_; lean_object* v___x_6278_; lean_object* v___x_6279_; lean_object* v___x_6280_; 
v___x_6277_ = l_Lean_Int_mkInstHSub;
v___x_6278_ = l_Lean_Int_mkType;
v___x_6279_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6280_ = l_Lean_mkApp4(v___x_6279_, v___x_6278_, v___x_6278_, v___x_6278_, v___x_6277_);
return v___x_6280_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn(void){
_start:
{
lean_object* v___x_6281_; 
v___x_6281_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intSubFn___closed__0, &l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0);
return v___x_6281_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0(void){
_start:
{
lean_object* v___x_6282_; lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; 
v___x_6282_ = l_Lean_Int_mkInstHMul;
v___x_6283_ = l_Lean_Int_mkType;
v___x_6284_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6285_ = l_Lean_mkApp4(v___x_6284_, v___x_6283_, v___x_6283_, v___x_6283_, v___x_6282_);
return v___x_6285_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn(void){
_start:
{
lean_object* v___x_6286_; 
v___x_6286_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intMulFn___closed__0, &l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0);
return v___x_6286_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3(void){
_start:
{
lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; 
v___x_6292_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6293_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intDivFn___closed__2));
v___x_6294_ = l_Lean_Expr_const___override(v___x_6293_, v___x_6292_);
return v___x_6294_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4(void){
_start:
{
lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; 
v___x_6295_ = l_Lean_Int_mkInstHDiv;
v___x_6296_ = l_Lean_Int_mkType;
v___x_6297_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__3, &l___private_Lean_Expr_0__Lean_intDivFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3);
v___x_6298_ = l_Lean_mkApp4(v___x_6297_, v___x_6296_, v___x_6296_, v___x_6296_, v___x_6295_);
return v___x_6298_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn(void){
_start:
{
lean_object* v___x_6299_; 
v___x_6299_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__4, &l___private_Lean_Expr_0__Lean_intDivFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4);
return v___x_6299_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3(void){
_start:
{
lean_object* v___x_6305_; lean_object* v___x_6306_; lean_object* v___x_6307_; 
v___x_6305_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6306_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intModFn___closed__2));
v___x_6307_ = l_Lean_Expr_const___override(v___x_6306_, v___x_6305_);
return v___x_6307_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4(void){
_start:
{
lean_object* v___x_6308_; lean_object* v___x_6309_; lean_object* v___x_6310_; lean_object* v___x_6311_; 
v___x_6308_ = l_Lean_Int_mkInstHMod;
v___x_6309_ = l_Lean_Int_mkType;
v___x_6310_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__3, &l___private_Lean_Expr_0__Lean_intModFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3);
v___x_6311_ = l_Lean_mkApp4(v___x_6310_, v___x_6309_, v___x_6309_, v___x_6309_, v___x_6308_);
return v___x_6311_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn(void){
_start:
{
lean_object* v___x_6312_; 
v___x_6312_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__4, &l___private_Lean_Expr_0__Lean_intModFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4);
return v___x_6312_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0(void){
_start:
{
lean_object* v___x_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; 
v___x_6313_ = l_Lean_Int_mkInstHPow;
v___x_6314_ = l_Lean_Nat_mkType;
v___x_6315_ = l_Lean_Int_mkType;
v___x_6316_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6317_ = l_Lean_mkApp4(v___x_6316_, v___x_6315_, v___x_6314_, v___x_6315_, v___x_6313_);
return v___x_6317_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn(void){
_start:
{
lean_object* v___x_6318_; 
v___x_6318_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0, &l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0);
return v___x_6318_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3(void){
_start:
{
lean_object* v___x_6324_; lean_object* v___x_6325_; lean_object* v___x_6326_; 
v___x_6324_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6325_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2));
v___x_6326_ = l_Lean_Expr_const___override(v___x_6325_, v___x_6324_);
return v___x_6326_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4(void){
_start:
{
lean_object* v___x_6327_; lean_object* v___x_6328_; lean_object* v___x_6329_; lean_object* v___x_6330_; 
v___x_6327_ = l_Lean_Int_mkInstNatCast;
v___x_6328_ = l_Lean_Int_mkType;
v___x_6329_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3);
v___x_6330_ = l_Lean_mkAppB(v___x_6329_, v___x_6328_, v___x_6327_);
return v___x_6330_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn(void){
_start:
{
lean_object* v___x_6331_; 
v___x_6331_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4);
return v___x_6331_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* v_a_6332_){
_start:
{
lean_object* v___x_6333_; lean_object* v___x_6334_; 
v___x_6333_ = l___private_Lean_Expr_0__Lean_intNegFn;
v___x_6334_ = l_Lean_Expr_app___override(v___x_6333_, v_a_6332_);
return v___x_6334_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* v_a_6335_, lean_object* v_b_6336_){
_start:
{
lean_object* v___x_6337_; lean_object* v___x_6338_; 
v___x_6337_ = l___private_Lean_Expr_0__Lean_intAddFn;
v___x_6338_ = l_Lean_mkAppB(v___x_6337_, v_a_6335_, v_b_6336_);
return v___x_6338_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* v_a_6339_, lean_object* v_b_6340_){
_start:
{
lean_object* v___x_6341_; lean_object* v___x_6342_; 
v___x_6341_ = l___private_Lean_Expr_0__Lean_intSubFn;
v___x_6342_ = l_Lean_mkAppB(v___x_6341_, v_a_6339_, v_b_6340_);
return v___x_6342_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* v_a_6343_, lean_object* v_b_6344_){
_start:
{
lean_object* v___x_6345_; lean_object* v___x_6346_; 
v___x_6345_ = l___private_Lean_Expr_0__Lean_intMulFn;
v___x_6346_ = l_Lean_mkAppB(v___x_6345_, v_a_6343_, v_b_6344_);
return v___x_6346_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* v_a_6347_, lean_object* v_b_6348_){
_start:
{
lean_object* v___x_6349_; lean_object* v___x_6350_; 
v___x_6349_ = l___private_Lean_Expr_0__Lean_intDivFn;
v___x_6350_ = l_Lean_mkAppB(v___x_6349_, v_a_6347_, v_b_6348_);
return v___x_6350_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* v_a_6351_, lean_object* v_b_6352_){
_start:
{
lean_object* v___x_6353_; lean_object* v___x_6354_; 
v___x_6353_ = l___private_Lean_Expr_0__Lean_intModFn;
v___x_6354_ = l_Lean_mkAppB(v___x_6353_, v_a_6351_, v_b_6352_);
return v___x_6354_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* v_a_6355_){
_start:
{
lean_object* v___x_6356_; lean_object* v___x_6357_; 
v___x_6356_ = l___private_Lean_Expr_0__Lean_intNatCastFn;
v___x_6357_ = l_Lean_Expr_app___override(v___x_6356_, v_a_6355_);
return v___x_6357_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object* v_a_6358_, lean_object* v_b_6359_){
_start:
{
lean_object* v___x_6360_; lean_object* v___x_6361_; 
v___x_6360_ = l___private_Lean_Expr_0__Lean_intPowNatFn;
v___x_6361_ = l_Lean_mkAppB(v___x_6360_, v_a_6358_, v_b_6359_);
return v___x_6361_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0(void){
_start:
{
lean_object* v___x_6362_; lean_object* v___x_6363_; lean_object* v___x_6364_; lean_object* v___x_6365_; 
v___x_6362_ = l_Lean_Int_mkInstLE;
v___x_6363_ = l_Lean_Int_mkType;
v___x_6364_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6365_ = l_Lean_mkAppB(v___x_6364_, v___x_6363_, v___x_6362_);
return v___x_6365_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred(void){
_start:
{
lean_object* v___x_6366_; 
v___x_6366_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLEPred___closed__0, &l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0);
return v___x_6366_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* v_a_6367_, lean_object* v_b_6368_){
_start:
{
lean_object* v___x_6369_; lean_object* v___x_6370_; 
v___x_6369_ = l___private_Lean_Expr_0__Lean_intLEPred;
v___x_6370_ = l_Lean_mkAppB(v___x_6369_, v_a_6367_, v_b_6368_);
return v___x_6370_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3(void){
_start:
{
lean_object* v___x_6376_; lean_object* v___x_6377_; lean_object* v___x_6378_; 
v___x_6376_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6377_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intLTPred___closed__2));
v___x_6378_ = l_Lean_Expr_const___override(v___x_6377_, v___x_6376_);
return v___x_6378_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4(void){
_start:
{
lean_object* v___x_6379_; lean_object* v___x_6380_; lean_object* v___x_6381_; lean_object* v___x_6382_; 
v___x_6379_ = l_Lean_Int_mkInstLT;
v___x_6380_ = l_Lean_Int_mkType;
v___x_6381_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__3, &l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3);
v___x_6382_ = l_Lean_mkAppB(v___x_6381_, v___x_6380_, v___x_6379_);
return v___x_6382_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred(void){
_start:
{
lean_object* v___x_6383_; 
v___x_6383_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__4, &l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4);
return v___x_6383_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object* v_a_6384_, lean_object* v_b_6385_){
_start:
{
lean_object* v___x_6386_; lean_object* v___x_6387_; 
v___x_6386_ = l___private_Lean_Expr_0__Lean_intLTPred;
v___x_6387_ = l_Lean_mkAppB(v___x_6386_, v_a_6384_, v_b_6385_);
return v___x_6387_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0(void){
_start:
{
lean_object* v___x_6388_; lean_object* v___x_6389_; lean_object* v___x_6390_; 
v___x_6388_ = l_Lean_Int_mkType;
v___x_6389_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6390_ = l_Lean_Expr_app___override(v___x_6389_, v___x_6388_);
return v___x_6390_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred(void){
_start:
{
lean_object* v___x_6391_; 
v___x_6391_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intEqPred___closed__0, &l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0);
return v___x_6391_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* v_a_6392_, lean_object* v_b_6393_){
_start:
{
lean_object* v___x_6394_; lean_object* v___x_6395_; 
v___x_6394_ = l___private_Lean_Expr_0__Lean_intEqPred;
v___x_6395_ = l_Lean_mkAppB(v___x_6394_, v_a_6392_, v_b_6393_);
return v___x_6395_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__3(void){
_start:
{
lean_object* v___x_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; 
v___x_6401_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6402_ = ((lean_object*)(l_Lean_mkIntDvd___closed__2));
v___x_6403_ = l_Lean_Expr_const___override(v___x_6402_, v___x_6401_);
return v___x_6403_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__6(void){
_start:
{
lean_object* v___x_6408_; lean_object* v___x_6409_; lean_object* v___x_6410_; 
v___x_6408_ = lean_box(0);
v___x_6409_ = ((lean_object*)(l_Lean_mkIntDvd___closed__5));
v___x_6410_ = l_Lean_Expr_const___override(v___x_6409_, v___x_6408_);
return v___x_6410_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* v_a_6411_, lean_object* v_b_6412_){
_start:
{
lean_object* v___x_6413_; lean_object* v___x_6414_; lean_object* v___x_6415_; lean_object* v___x_6416_; 
v___x_6413_ = lean_obj_once(&l_Lean_mkIntDvd___closed__3, &l_Lean_mkIntDvd___closed__3_once, _init_l_Lean_mkIntDvd___closed__3);
v___x_6414_ = l_Lean_Int_mkType;
v___x_6415_ = lean_obj_once(&l_Lean_mkIntDvd___closed__6, &l_Lean_mkIntDvd___closed__6_once, _init_l_Lean_mkIntDvd___closed__6);
v___x_6416_ = l_Lean_mkApp4(v___x_6413_, v___x_6414_, v___x_6415_, v_a_6411_, v_b_6412_);
return v___x_6416_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__2(void){
_start:
{
lean_object* v___x_6420_; lean_object* v___x_6421_; lean_object* v___x_6422_; 
v___x_6420_ = lean_box(0);
v___x_6421_ = ((lean_object*)(l_Lean_mkIntLit___closed__1));
v___x_6422_ = l_Lean_Expr_const___override(v___x_6421_, v___x_6420_);
return v___x_6422_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__3(void){
_start:
{
lean_object* v___x_6423_; lean_object* v___x_6424_; 
v___x_6423_ = lean_unsigned_to_nat(0u);
v___x_6424_ = lean_nat_to_int(v___x_6423_);
return v___x_6424_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* v_n_6425_){
_start:
{
lean_object* v___x_6426_; lean_object* v_r_6427_; lean_object* v___x_6428_; lean_object* v___x_6429_; lean_object* v___x_6430_; lean_object* v___x_6431_; lean_object* v_r_6432_; lean_object* v___x_6433_; uint8_t v___x_6434_; 
v___x_6426_ = lean_nat_abs(v_n_6425_);
v_r_6427_ = l_Lean_mkRawNatLit(v___x_6426_);
v___x_6428_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_6429_ = l_Lean_Int_mkType;
v___x_6430_ = lean_obj_once(&l_Lean_mkIntLit___closed__2, &l_Lean_mkIntLit___closed__2_once, _init_l_Lean_mkIntLit___closed__2);
lean_inc_ref(v_r_6427_);
v___x_6431_ = l_Lean_Expr_app___override(v___x_6430_, v_r_6427_);
v_r_6432_ = l_Lean_mkApp3(v___x_6428_, v___x_6429_, v_r_6427_, v___x_6431_);
v___x_6433_ = lean_obj_once(&l_Lean_mkIntLit___closed__3, &l_Lean_mkIntLit___closed__3_once, _init_l_Lean_mkIntLit___closed__3);
v___x_6434_ = lean_int_dec_lt(v_n_6425_, v___x_6433_);
if (v___x_6434_ == 0)
{
return v_r_6432_;
}
else
{
lean_object* v___x_6435_; 
v___x_6435_ = l_Lean_mkIntNeg(v_r_6432_);
return v___x_6435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* v_n_6436_){
_start:
{
lean_object* v_res_6437_; 
v_res_6437_ = l_Lean_mkIntLit(v_n_6436_);
lean_dec(v_n_6436_);
return v_res_6437_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6442_; lean_object* v___x_6443_; 
v___x_6442_ = lean_box(0);
v___x_6443_ = l_Lean_Level_succ___override(v___x_6442_);
return v___x_6443_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6444_; lean_object* v___x_6445_; lean_object* v___x_6446_; 
v___x_6444_ = lean_box(0);
v___x_6445_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__2, &l_Lean_reflBoolTrue___closed__2_once, _init_l_Lean_reflBoolTrue___closed__2);
v___x_6446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6446_, 0, v___x_6445_);
lean_ctor_set(v___x_6446_, 1, v___x_6444_);
return v___x_6446_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6447_; lean_object* v___x_6448_; lean_object* v___x_6449_; 
v___x_6447_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__3, &l_Lean_reflBoolTrue___closed__3_once, _init_l_Lean_reflBoolTrue___closed__3);
v___x_6448_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__1));
v___x_6449_ = l_Lean_Expr_const___override(v___x_6448_, v___x_6447_);
return v___x_6449_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__6(void){
_start:
{
lean_object* v___x_6452_; lean_object* v___x_6453_; lean_object* v___x_6454_; 
v___x_6452_ = lean_box(0);
v___x_6453_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__5));
v___x_6454_ = l_Lean_Expr_const___override(v___x_6453_, v___x_6452_);
return v___x_6454_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__7(void){
_start:
{
lean_object* v___x_6455_; lean_object* v___x_6456_; lean_object* v___x_6457_; 
v___x_6455_ = lean_box(0);
v___x_6456_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_6457_ = l_Lean_Expr_const___override(v___x_6456_, v___x_6455_);
return v___x_6457_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__8(void){
_start:
{
lean_object* v___x_6458_; lean_object* v___x_6459_; lean_object* v___x_6460_; lean_object* v___x_6461_; 
v___x_6458_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6459_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6460_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6461_ = l_Lean_mkAppB(v___x_6460_, v___x_6459_, v___x_6458_);
return v___x_6461_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue(void){
_start:
{
lean_object* v___x_6462_; 
v___x_6462_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__8, &l_Lean_reflBoolTrue___closed__8_once, _init_l_Lean_reflBoolTrue___closed__8);
return v___x_6462_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6463_; lean_object* v___x_6464_; lean_object* v___x_6465_; 
v___x_6463_ = lean_box(0);
v___x_6464_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_6465_ = l_Lean_Expr_const___override(v___x_6464_, v___x_6463_);
return v___x_6465_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6466_; lean_object* v___x_6467_; lean_object* v___x_6468_; lean_object* v___x_6469_; 
v___x_6466_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6467_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6468_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6469_ = l_Lean_mkAppB(v___x_6468_, v___x_6467_, v___x_6466_);
return v___x_6469_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse(void){
_start:
{
lean_object* v___x_6470_; 
v___x_6470_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
return v___x_6470_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; 
v___x_6474_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6475_ = ((lean_object*)(l_Lean_eagerReflBoolTrue___closed__1));
v___x_6476_ = l_Lean_Expr_const___override(v___x_6475_, v___x_6474_);
return v___x_6476_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; lean_object* v___x_6480_; 
v___x_6477_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6478_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6479_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6480_ = l_Lean_mkApp3(v___x_6479_, v___x_6478_, v___x_6477_, v___x_6477_);
return v___x_6480_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; 
v___x_6481_ = l_Lean_reflBoolTrue;
v___x_6482_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__3, &l_Lean_eagerReflBoolTrue___closed__3_once, _init_l_Lean_eagerReflBoolTrue___closed__3);
v___x_6483_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6484_ = l_Lean_mkAppB(v___x_6483_, v___x_6482_, v___x_6481_);
return v___x_6484_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue(void){
_start:
{
lean_object* v___x_6485_; 
v___x_6485_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__4, &l_Lean_eagerReflBoolTrue___closed__4_once, _init_l_Lean_eagerReflBoolTrue___closed__4);
return v___x_6485_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; 
v___x_6486_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6487_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6488_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6489_ = l_Lean_mkApp3(v___x_6488_, v___x_6487_, v___x_6486_, v___x_6486_);
return v___x_6489_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; 
v___x_6490_ = l_Lean_reflBoolFalse;
v___x_6491_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__0, &l_Lean_eagerReflBoolFalse___closed__0_once, _init_l_Lean_eagerReflBoolFalse___closed__0);
v___x_6492_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6493_ = l_Lean_mkAppB(v___x_6492_, v___x_6491_, v___x_6490_);
return v___x_6493_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse(void){
_start:
{
lean_object* v___x_6494_; 
v___x_6494_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__1, &l_Lean_eagerReflBoolFalse___closed__1_once, _init_l_Lean_eagerReflBoolFalse___closed__1);
return v___x_6494_;
}
}
static lean_object* _init_l_Lean_Expr_replaceFn___closed__2(void){
_start:
{
lean_object* v___x_6497_; lean_object* v___x_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; lean_object* v___x_6501_; lean_object* v___x_6502_; 
v___x_6497_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__1));
v___x_6498_ = lean_unsigned_to_nat(9u);
v___x_6499_ = lean_unsigned_to_nat(2441u);
v___x_6500_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__0));
v___x_6501_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_6502_ = l_mkPanicMessageWithDecl(v___x_6501_, v___x_6500_, v___x_6499_, v___x_6498_, v___x_6497_);
return v___x_6502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object* v_e_6503_, lean_object* v_declName_6504_){
_start:
{
switch(lean_obj_tag(v_e_6503_))
{
case 5:
{
lean_object* v_fn_6505_; lean_object* v_arg_6506_; lean_object* v___x_6507_; lean_object* v___x_6508_; 
v_fn_6505_ = lean_ctor_get(v_e_6503_, 0);
lean_inc_ref(v_fn_6505_);
v_arg_6506_ = lean_ctor_get(v_e_6503_, 1);
lean_inc_ref(v_arg_6506_);
lean_dec_ref_known(v_e_6503_, 2);
v___x_6507_ = l_Lean_Expr_replaceFn(v_fn_6505_, v_declName_6504_);
v___x_6508_ = l_Lean_Expr_app___override(v___x_6507_, v_arg_6506_);
return v___x_6508_;
}
case 4:
{
lean_object* v_us_6509_; lean_object* v___x_6510_; 
v_us_6509_ = lean_ctor_get(v_e_6503_, 1);
lean_inc(v_us_6509_);
lean_dec_ref_known(v_e_6503_, 2);
v___x_6510_ = l_Lean_Expr_const___override(v_declName_6504_, v_us_6509_);
return v___x_6510_;
}
default: 
{
lean_object* v___x_6511_; lean_object* v___x_6512_; 
lean_dec(v_declName_6504_);
lean_dec_ref(v_e_6503_);
v___x_6511_ = lean_obj_once(&l_Lean_Expr_replaceFn___closed__2, &l_Lean_Expr_replaceFn___closed__2_once, _init_l_Lean_Expr_replaceFn___closed__2);
v___x_6512_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_6511_);
return v___x_6512_;
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
