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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
lean_object* l_Array_instInhabited___redArg();
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
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg();
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg();
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg();
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg();
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyMVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyMVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_containsMVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_containsMVar___boxed(lean_object*, lean_object*);
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
uint8_t v_x_21__boxed_241_; uint8_t v_y_22__boxed_242_; uint8_t v_res_243_; lean_object* v_r_244_; 
v_x_21__boxed_241_ = lean_unbox(v_x_239_);
v_y_22__boxed_242_ = lean_unbox(v_y_240_);
v_res_243_ = l_Lean_instBEqBinderInfo_beq(v_x_21__boxed_241_, v_y_22__boxed_242_);
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
uint8_t v_x_221__boxed_307_; lean_object* v_res_308_; 
v_x_221__boxed_307_ = lean_unbox(v_x_305_);
v_res_308_ = l_Lean_instReprBinderInfo_repr(v_x_221__boxed_307_, v_prec_306_);
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
uint8_t v_x_27__boxed_326_; uint8_t v_res_327_; lean_object* v_r_328_; 
v_x_27__boxed_326_ = lean_unbox(v_x_325_);
v_res_327_ = l_Lean_BinderInfo_isExplicit(v_x_27__boxed_326_);
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
uint8_t v_x_17__boxed_335_; uint8_t v_res_336_; lean_object* v_r_337_; 
v_x_17__boxed_335_ = lean_unbox(v_x_334_);
v_res_336_ = l_Lean_BinderInfo_isInstImplicit(v_x_17__boxed_335_);
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
uint8_t v_x_17__boxed_342_; uint8_t v_res_343_; lean_object* v_r_344_; 
v_x_17__boxed_342_ = lean_unbox(v_x_341_);
v_res_343_ = l_Lean_BinderInfo_isImplicit(v_x_17__boxed_342_);
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
uint8_t v_x_17__boxed_349_; uint8_t v_res_350_; lean_object* v_r_351_; 
v_x_17__boxed_349_ = lean_unbox(v_x_348_);
v_res_350_ = l_Lean_BinderInfo_isStrictImplicit(v_x_17__boxed_349_);
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
LEAN_EXPORT uint64_t l_Lean_instHashableFVarId_hash(lean_object* v_x_601_){
_start:
{
uint64_t v___x_602_; 
v___x_602_ = 0ULL;
if (lean_obj_tag(v_x_601_) == 0)
{
uint64_t v___x_603_; 
v___x_603_ = 8934034000889494153ULL;
return v___x_603_;
}
else
{
uint64_t v_hash_604_; uint64_t v___x_605_; 
v_hash_604_ = lean_ctor_get_uint64(v_x_601_, sizeof(void*)*2);
v___x_605_ = lean_uint64_mix_hash(v___x_602_, v_hash_604_);
return v___x_605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object* v_x_606_){
_start:
{
uint64_t v_res_607_; lean_object* v_r_608_; 
v_res_607_ = l_Lean_instHashableFVarId_hash(v_x_606_);
lean_dec(v_x_606_);
v_r_608_ = lean_box_uint64(v_res_607_);
return v_r_608_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_box(1);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet(void){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = lean_box(1);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_box(1);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_box(1);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___aux__1(lean_object* v_e_618_){
_start:
{
lean_object* v___f_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___f_619_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_620_ = lean_box(1);
lean_inc(v_e_618_);
v___x_621_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___f_619_, v_e_618_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_box(0);
v___x_623_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_619_, v_e_618_, v___x_622_, v___x_620_);
return v___x_623_;
}
else
{
lean_dec(v_e_618_);
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object* v_k_624_, lean_object* v_v_625_, lean_object* v_t_626_){
_start:
{
if (lean_obj_tag(v_t_626_) == 0)
{
lean_object* v_size_627_; lean_object* v_k_628_; lean_object* v_v_629_; lean_object* v_l_630_; lean_object* v_r_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_911_; 
v_size_627_ = lean_ctor_get(v_t_626_, 0);
v_k_628_ = lean_ctor_get(v_t_626_, 1);
v_v_629_ = lean_ctor_get(v_t_626_, 2);
v_l_630_ = lean_ctor_get(v_t_626_, 3);
v_r_631_ = lean_ctor_get(v_t_626_, 4);
v_isSharedCheck_911_ = !lean_is_exclusive(v_t_626_);
if (v_isSharedCheck_911_ == 0)
{
v___x_633_ = v_t_626_;
v_isShared_634_ = v_isSharedCheck_911_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_r_631_);
lean_inc(v_l_630_);
lean_inc(v_v_629_);
lean_inc(v_k_628_);
lean_inc(v_size_627_);
lean_dec(v_t_626_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_911_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
uint8_t v___x_635_; 
v___x_635_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_624_, v_k_628_);
switch(v___x_635_)
{
case 0:
{
lean_object* v_impl_636_; lean_object* v___x_637_; 
lean_dec(v_size_627_);
v_impl_636_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_624_, v_v_625_, v_l_630_);
v___x_637_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_631_) == 0)
{
lean_object* v_size_638_; lean_object* v_size_639_; lean_object* v_k_640_; lean_object* v_v_641_; lean_object* v_l_642_; lean_object* v_r_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_size_638_ = lean_ctor_get(v_r_631_, 0);
v_size_639_ = lean_ctor_get(v_impl_636_, 0);
v_k_640_ = lean_ctor_get(v_impl_636_, 1);
v_v_641_ = lean_ctor_get(v_impl_636_, 2);
v_l_642_ = lean_ctor_get(v_impl_636_, 3);
v_r_643_ = lean_ctor_get(v_impl_636_, 4);
lean_inc(v_r_643_);
v___x_644_ = lean_unsigned_to_nat(3u);
v___x_645_ = lean_nat_mul(v___x_644_, v_size_638_);
v___x_646_ = lean_nat_dec_lt(v___x_645_, v_size_639_);
lean_dec(v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_650_; 
lean_dec(v_r_643_);
v___x_647_ = lean_nat_add(v___x_637_, v_size_639_);
v___x_648_ = lean_nat_add(v___x_647_, v_size_638_);
lean_dec(v___x_647_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 3, v_impl_636_);
lean_ctor_set(v___x_633_, 0, v___x_648_);
v___x_650_ = v___x_633_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_651_, 3, v_impl_636_);
lean_ctor_set(v_reuseFailAlloc_651_, 4, v_r_631_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
else
{
lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_717_; 
lean_inc(v_l_642_);
lean_inc(v_v_641_);
lean_inc(v_k_640_);
lean_inc(v_size_639_);
v_isSharedCheck_717_ = !lean_is_exclusive(v_impl_636_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; lean_object* v_unused_719_; lean_object* v_unused_720_; lean_object* v_unused_721_; lean_object* v_unused_722_; 
v_unused_718_ = lean_ctor_get(v_impl_636_, 4);
lean_dec(v_unused_718_);
v_unused_719_ = lean_ctor_get(v_impl_636_, 3);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_impl_636_, 2);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v_impl_636_, 1);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_impl_636_, 0);
lean_dec(v_unused_722_);
v___x_653_ = v_impl_636_;
v_isShared_654_ = v_isSharedCheck_717_;
goto v_resetjp_652_;
}
else
{
lean_dec(v_impl_636_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_717_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_size_655_; lean_object* v_size_656_; lean_object* v_k_657_; lean_object* v_v_658_; lean_object* v_l_659_; lean_object* v_r_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_size_655_ = lean_ctor_get(v_l_642_, 0);
v_size_656_ = lean_ctor_get(v_r_643_, 0);
v_k_657_ = lean_ctor_get(v_r_643_, 1);
v_v_658_ = lean_ctor_get(v_r_643_, 2);
v_l_659_ = lean_ctor_get(v_r_643_, 3);
v_r_660_ = lean_ctor_get(v_r_643_, 4);
v___x_661_ = lean_unsigned_to_nat(2u);
v___x_662_ = lean_nat_mul(v___x_661_, v_size_655_);
v___x_663_ = lean_nat_dec_lt(v_size_656_, v___x_662_);
lean_dec(v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_692_; 
lean_inc(v_r_660_);
lean_inc(v_l_659_);
lean_inc(v_v_658_);
lean_inc(v_k_657_);
v_isSharedCheck_692_ = !lean_is_exclusive(v_r_643_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; lean_object* v_unused_694_; lean_object* v_unused_695_; lean_object* v_unused_696_; lean_object* v_unused_697_; 
v_unused_693_ = lean_ctor_get(v_r_643_, 4);
lean_dec(v_unused_693_);
v_unused_694_ = lean_ctor_get(v_r_643_, 3);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v_r_643_, 2);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_r_643_, 1);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_r_643_, 0);
lean_dec(v_unused_697_);
v___x_665_ = v_r_643_;
v_isShared_666_ = v_isSharedCheck_692_;
goto v_resetjp_664_;
}
else
{
lean_dec(v_r_643_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_692_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___x_680_; lean_object* v___y_682_; 
v___x_667_ = lean_nat_add(v___x_637_, v_size_639_);
lean_dec(v_size_639_);
v___x_668_ = lean_nat_add(v___x_667_, v_size_638_);
lean_dec(v___x_667_);
v___x_680_ = lean_nat_add(v___x_637_, v_size_655_);
if (lean_obj_tag(v_l_659_) == 0)
{
lean_object* v_size_690_; 
v_size_690_ = lean_ctor_get(v_l_659_, 0);
lean_inc(v_size_690_);
v___y_682_ = v_size_690_;
goto v___jp_681_;
}
else
{
lean_object* v___x_691_; 
v___x_691_ = lean_unsigned_to_nat(0u);
v___y_682_ = v___x_691_;
goto v___jp_681_;
}
v___jp_669_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_nat_add(v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec(v___y_671_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 4, v_r_631_);
lean_ctor_set(v___x_665_, 3, v_r_660_);
lean_ctor_set(v___x_665_, 2, v_v_629_);
lean_ctor_set(v___x_665_, 1, v_k_628_);
lean_ctor_set(v___x_665_, 0, v___x_673_);
v___x_675_ = v___x_665_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_r_660_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v_r_631_);
v___x_675_ = v_reuseFailAlloc_679_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_677_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 4, v___x_675_);
lean_ctor_set(v___x_653_, 3, v___y_670_);
lean_ctor_set(v___x_653_, 2, v_v_658_);
lean_ctor_set(v___x_653_, 1, v_k_657_);
lean_ctor_set(v___x_653_, 0, v___x_668_);
v___x_677_ = v___x_653_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_k_657_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_v_658_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v___y_670_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
v___jp_681_:
{
lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_683_ = lean_nat_add(v___x_680_, v___y_682_);
lean_dec(v___y_682_);
lean_dec(v___x_680_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v_l_659_);
lean_ctor_set(v___x_633_, 3, v_l_642_);
lean_ctor_set(v___x_633_, 2, v_v_641_);
lean_ctor_set(v___x_633_, 1, v_k_640_);
lean_ctor_set(v___x_633_, 0, v___x_683_);
v___x_685_ = v___x_633_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_689_, 3, v_l_642_);
lean_ctor_set(v_reuseFailAlloc_689_, 4, v_l_659_);
v___x_685_ = v_reuseFailAlloc_689_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; 
v___x_686_ = lean_nat_add(v___x_637_, v_size_638_);
if (lean_obj_tag(v_r_660_) == 0)
{
lean_object* v_size_687_; 
v_size_687_ = lean_ctor_get(v_r_660_, 0);
lean_inc(v_size_687_);
v___y_670_ = v___x_685_;
v___y_671_ = v___x_686_;
v___y_672_ = v_size_687_;
goto v___jp_669_;
}
else
{
lean_object* v___x_688_; 
v___x_688_ = lean_unsigned_to_nat(0u);
v___y_670_ = v___x_685_;
v___y_671_ = v___x_686_;
v___y_672_ = v___x_688_;
goto v___jp_669_;
}
}
}
}
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
lean_del_object(v___x_633_);
v___x_698_ = lean_nat_add(v___x_637_, v_size_639_);
lean_dec(v_size_639_);
v___x_699_ = lean_nat_add(v___x_698_, v_size_638_);
lean_dec(v___x_698_);
v___x_700_ = lean_nat_add(v___x_637_, v_size_638_);
v___x_701_ = lean_nat_add(v___x_700_, v_size_656_);
lean_dec(v___x_700_);
lean_inc_ref(v_r_631_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 4, v_r_631_);
lean_ctor_set(v___x_653_, 3, v_r_643_);
lean_ctor_set(v___x_653_, 2, v_v_629_);
lean_ctor_set(v___x_653_, 1, v_k_628_);
lean_ctor_set(v___x_653_, 0, v___x_701_);
v___x_703_ = v___x_653_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_r_643_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v_r_631_);
v___x_703_ = v_reuseFailAlloc_716_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v_isSharedCheck_710_ = !lean_is_exclusive(v_r_631_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; lean_object* v_unused_712_; lean_object* v_unused_713_; lean_object* v_unused_714_; lean_object* v_unused_715_; 
v_unused_711_ = lean_ctor_get(v_r_631_, 4);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_r_631_, 3);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_r_631_, 2);
lean_dec(v_unused_713_);
v_unused_714_ = lean_ctor_get(v_r_631_, 1);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_r_631_, 0);
lean_dec(v_unused_715_);
v___x_705_ = v_r_631_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_dec(v_r_631_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v___x_703_);
lean_ctor_set(v___x_705_, 3, v_l_642_);
lean_ctor_set(v___x_705_, 2, v_v_641_);
lean_ctor_set(v___x_705_, 1, v_k_640_);
lean_ctor_set(v___x_705_, 0, v___x_699_);
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v_l_642_);
lean_ctor_set(v_reuseFailAlloc_709_, 4, v___x_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_723_; 
v_l_723_ = lean_ctor_get(v_impl_636_, 3);
if (lean_obj_tag(v_l_723_) == 0)
{
lean_object* v_r_724_; lean_object* v_k_725_; lean_object* v_v_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_737_; 
lean_inc_ref(v_l_723_);
v_r_724_ = lean_ctor_get(v_impl_636_, 4);
v_k_725_ = lean_ctor_get(v_impl_636_, 1);
v_v_726_ = lean_ctor_get(v_impl_636_, 2);
v_isSharedCheck_737_ = !lean_is_exclusive(v_impl_636_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; lean_object* v_unused_739_; 
v_unused_738_ = lean_ctor_get(v_impl_636_, 3);
lean_dec(v_unused_738_);
v_unused_739_ = lean_ctor_get(v_impl_636_, 0);
lean_dec(v_unused_739_);
v___x_728_ = v_impl_636_;
v_isShared_729_ = v_isSharedCheck_737_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_r_724_);
lean_inc(v_v_726_);
lean_inc(v_k_725_);
lean_dec(v_impl_636_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_737_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_724_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 3, v_r_724_);
lean_ctor_set(v___x_728_, 2, v_v_629_);
lean_ctor_set(v___x_728_, 1, v_k_628_);
lean_ctor_set(v___x_728_, 0, v___x_637_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_736_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_736_, 3, v_r_724_);
lean_ctor_set(v_reuseFailAlloc_736_, 4, v_r_724_);
v___x_732_ = v_reuseFailAlloc_736_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_734_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v___x_732_);
lean_ctor_set(v___x_633_, 3, v_l_723_);
lean_ctor_set(v___x_633_, 2, v_v_726_);
lean_ctor_set(v___x_633_, 1, v_k_725_);
lean_ctor_set(v___x_633_, 0, v___x_730_);
v___x_734_ = v___x_633_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_k_725_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_v_726_);
lean_ctor_set(v_reuseFailAlloc_735_, 3, v_l_723_);
lean_ctor_set(v_reuseFailAlloc_735_, 4, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
else
{
lean_object* v_r_740_; 
v_r_740_ = lean_ctor_get(v_impl_636_, 4);
lean_inc(v_r_740_);
if (lean_obj_tag(v_r_740_) == 0)
{
lean_object* v_k_741_; lean_object* v_v_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_765_; 
lean_inc(v_l_723_);
v_k_741_ = lean_ctor_get(v_impl_636_, 1);
v_v_742_ = lean_ctor_get(v_impl_636_, 2);
v_isSharedCheck_765_ = !lean_is_exclusive(v_impl_636_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; lean_object* v_unused_767_; lean_object* v_unused_768_; 
v_unused_766_ = lean_ctor_get(v_impl_636_, 4);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_impl_636_, 3);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_impl_636_, 0);
lean_dec(v_unused_768_);
v___x_744_ = v_impl_636_;
v_isShared_745_ = v_isSharedCheck_765_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_v_742_);
lean_inc(v_k_741_);
lean_dec(v_impl_636_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_765_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_k_746_; lean_object* v_v_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_761_; 
v_k_746_ = lean_ctor_get(v_r_740_, 1);
v_v_747_ = lean_ctor_get(v_r_740_, 2);
v_isSharedCheck_761_ = !lean_is_exclusive(v_r_740_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; lean_object* v_unused_763_; lean_object* v_unused_764_; 
v_unused_762_ = lean_ctor_get(v_r_740_, 4);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_r_740_, 3);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_r_740_, 0);
lean_dec(v_unused_764_);
v___x_749_ = v_r_740_;
v_isShared_750_ = v_isSharedCheck_761_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_v_747_);
lean_inc(v_k_746_);
lean_dec(v_r_740_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_761_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = lean_unsigned_to_nat(3u);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 4, v_l_723_);
lean_ctor_set(v___x_749_, 3, v_l_723_);
lean_ctor_set(v___x_749_, 2, v_v_742_);
lean_ctor_set(v___x_749_, 1, v_k_741_);
lean_ctor_set(v___x_749_, 0, v___x_637_);
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_k_741_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v_v_742_);
lean_ctor_set(v_reuseFailAlloc_760_, 3, v_l_723_);
lean_ctor_set(v_reuseFailAlloc_760_, 4, v_l_723_);
v___x_753_ = v_reuseFailAlloc_760_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 4, v_l_723_);
lean_ctor_set(v___x_744_, 2, v_v_629_);
lean_ctor_set(v___x_744_, 1, v_k_628_);
lean_ctor_set(v___x_744_, 0, v___x_637_);
v___x_755_ = v___x_744_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_l_723_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_l_723_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_757_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v___x_755_);
lean_ctor_set(v___x_633_, 3, v___x_753_);
lean_ctor_set(v___x_633_, 2, v_v_747_);
lean_ctor_set(v___x_633_, 1, v_k_746_);
lean_ctor_set(v___x_633_, 0, v___x_751_);
v___x_757_ = v___x_633_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_k_746_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_v_747_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
}
else
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_unsigned_to_nat(2u);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v_r_740_);
lean_ctor_set(v___x_633_, 3, v_impl_636_);
lean_ctor_set(v___x_633_, 0, v___x_769_);
v___x_771_ = v___x_633_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_impl_636_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_r_740_);
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
case 1:
{
lean_object* v___x_774_; 
lean_dec(v_v_629_);
lean_dec(v_k_628_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 2, v_v_625_);
lean_ctor_set(v___x_633_, 1, v_k_624_);
v___x_774_ = v___x_633_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_size_627_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_k_624_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_v_625_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_l_630_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_r_631_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
default: 
{
lean_object* v_impl_776_; lean_object* v___x_777_; 
lean_dec(v_size_627_);
v_impl_776_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_624_, v_v_625_, v_r_631_);
v___x_777_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_630_) == 0)
{
lean_object* v_size_778_; lean_object* v_size_779_; lean_object* v_k_780_; lean_object* v_v_781_; lean_object* v_l_782_; lean_object* v_r_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v_size_778_ = lean_ctor_get(v_l_630_, 0);
v_size_779_ = lean_ctor_get(v_impl_776_, 0);
v_k_780_ = lean_ctor_get(v_impl_776_, 1);
v_v_781_ = lean_ctor_get(v_impl_776_, 2);
v_l_782_ = lean_ctor_get(v_impl_776_, 3);
lean_inc(v_l_782_);
v_r_783_ = lean_ctor_get(v_impl_776_, 4);
v___x_784_ = lean_unsigned_to_nat(3u);
v___x_785_ = lean_nat_mul(v___x_784_, v_size_778_);
v___x_786_ = lean_nat_dec_lt(v___x_785_, v_size_779_);
lean_dec(v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
lean_dec(v_l_782_);
v___x_787_ = lean_nat_add(v___x_777_, v_size_778_);
v___x_788_ = lean_nat_add(v___x_787_, v_size_779_);
lean_dec(v___x_787_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v_impl_776_);
lean_ctor_set(v___x_633_, 0, v___x_788_);
v___x_790_ = v___x_633_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_l_630_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_impl_776_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
else
{
lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_855_; 
lean_inc(v_r_783_);
lean_inc(v_v_781_);
lean_inc(v_k_780_);
lean_inc(v_size_779_);
v_isSharedCheck_855_ = !lean_is_exclusive(v_impl_776_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; lean_object* v_unused_860_; 
v_unused_856_ = lean_ctor_get(v_impl_776_, 4);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_impl_776_, 3);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_impl_776_, 2);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_impl_776_, 1);
lean_dec(v_unused_859_);
v_unused_860_ = lean_ctor_get(v_impl_776_, 0);
lean_dec(v_unused_860_);
v___x_793_ = v_impl_776_;
v_isShared_794_ = v_isSharedCheck_855_;
goto v_resetjp_792_;
}
else
{
lean_dec(v_impl_776_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_855_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_size_795_; lean_object* v_k_796_; lean_object* v_v_797_; lean_object* v_l_798_; lean_object* v_r_799_; lean_object* v_size_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_size_795_ = lean_ctor_get(v_l_782_, 0);
v_k_796_ = lean_ctor_get(v_l_782_, 1);
v_v_797_ = lean_ctor_get(v_l_782_, 2);
v_l_798_ = lean_ctor_get(v_l_782_, 3);
v_r_799_ = lean_ctor_get(v_l_782_, 4);
v_size_800_ = lean_ctor_get(v_r_783_, 0);
v___x_801_ = lean_unsigned_to_nat(2u);
v___x_802_ = lean_nat_mul(v___x_801_, v_size_800_);
v___x_803_ = lean_nat_dec_lt(v_size_795_, v___x_802_);
lean_dec(v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_831_; 
lean_inc(v_r_799_);
lean_inc(v_l_798_);
lean_inc(v_v_797_);
lean_inc(v_k_796_);
v_isSharedCheck_831_ = !lean_is_exclusive(v_l_782_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; lean_object* v_unused_833_; lean_object* v_unused_834_; lean_object* v_unused_835_; lean_object* v_unused_836_; 
v_unused_832_ = lean_ctor_get(v_l_782_, 4);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_l_782_, 3);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_l_782_, 2);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_l_782_, 1);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_l_782_, 0);
lean_dec(v_unused_836_);
v___x_805_ = v_l_782_;
v_isShared_806_ = v_isSharedCheck_831_;
goto v_resetjp_804_;
}
else
{
lean_dec(v_l_782_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_831_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_821_; 
v___x_807_ = lean_nat_add(v___x_777_, v_size_778_);
v___x_808_ = lean_nat_add(v___x_807_, v_size_779_);
lean_dec(v_size_779_);
if (lean_obj_tag(v_l_798_) == 0)
{
lean_object* v_size_829_; 
v_size_829_ = lean_ctor_get(v_l_798_, 0);
lean_inc(v_size_829_);
v___y_821_ = v_size_829_;
goto v___jp_820_;
}
else
{
lean_object* v___x_830_; 
v___x_830_ = lean_unsigned_to_nat(0u);
v___y_821_ = v___x_830_;
goto v___jp_820_;
}
v___jp_809_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_nat_add(v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec(v___y_811_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 4, v_r_783_);
lean_ctor_set(v___x_805_, 3, v_r_799_);
lean_ctor_set(v___x_805_, 2, v_v_781_);
lean_ctor_set(v___x_805_, 1, v_k_780_);
lean_ctor_set(v___x_805_, 0, v___x_813_);
v___x_815_ = v___x_805_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_k_780_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_v_781_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v_r_799_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v_r_783_);
v___x_815_ = v_reuseFailAlloc_819_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 4, v___x_815_);
lean_ctor_set(v___x_793_, 3, v___y_810_);
lean_ctor_set(v___x_793_, 2, v_v_797_);
lean_ctor_set(v___x_793_, 1, v_k_796_);
lean_ctor_set(v___x_793_, 0, v___x_808_);
v___x_817_ = v___x_793_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_k_796_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_v_797_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v___y_810_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
v___jp_820_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_nat_add(v___x_807_, v___y_821_);
lean_dec(v___y_821_);
lean_dec(v___x_807_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v_l_798_);
lean_ctor_set(v___x_633_, 0, v___x_822_);
v___x_824_ = v___x_633_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_l_630_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v_l_798_);
v___x_824_ = v_reuseFailAlloc_828_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; 
v___x_825_ = lean_nat_add(v___x_777_, v_size_800_);
if (lean_obj_tag(v_r_799_) == 0)
{
lean_object* v_size_826_; 
v_size_826_ = lean_ctor_get(v_r_799_, 0);
lean_inc(v_size_826_);
v___y_810_ = v___x_824_;
v___y_811_ = v___x_825_;
v___y_812_ = v_size_826_;
goto v___jp_809_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = lean_unsigned_to_nat(0u);
v___y_810_ = v___x_824_;
v___y_811_ = v___x_825_;
v___y_812_ = v___x_827_;
goto v___jp_809_;
}
}
}
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
lean_del_object(v___x_633_);
v___x_837_ = lean_nat_add(v___x_777_, v_size_778_);
v___x_838_ = lean_nat_add(v___x_837_, v_size_779_);
lean_dec(v_size_779_);
v___x_839_ = lean_nat_add(v___x_837_, v_size_795_);
lean_dec(v___x_837_);
lean_inc_ref(v_l_630_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 4, v_l_782_);
lean_ctor_set(v___x_793_, 3, v_l_630_);
lean_ctor_set(v___x_793_, 2, v_v_629_);
lean_ctor_set(v___x_793_, 1, v_k_628_);
lean_ctor_set(v___x_793_, 0, v___x_839_);
v___x_841_ = v___x_793_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_854_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_854_, 3, v_l_630_);
lean_ctor_set(v_reuseFailAlloc_854_, 4, v_l_782_);
v___x_841_ = v_reuseFailAlloc_854_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
v_isSharedCheck_848_ = !lean_is_exclusive(v_l_630_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; lean_object* v_unused_850_; lean_object* v_unused_851_; lean_object* v_unused_852_; lean_object* v_unused_853_; 
v_unused_849_ = lean_ctor_get(v_l_630_, 4);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v_l_630_, 3);
lean_dec(v_unused_850_);
v_unused_851_ = lean_ctor_get(v_l_630_, 2);
lean_dec(v_unused_851_);
v_unused_852_ = lean_ctor_get(v_l_630_, 1);
lean_dec(v_unused_852_);
v_unused_853_ = lean_ctor_get(v_l_630_, 0);
lean_dec(v_unused_853_);
v___x_843_ = v_l_630_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_dec(v_l_630_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_r_783_);
lean_ctor_set(v___x_843_, 3, v___x_841_);
lean_ctor_set(v___x_843_, 2, v_v_781_);
lean_ctor_set(v___x_843_, 1, v_k_780_);
lean_ctor_set(v___x_843_, 0, v___x_838_);
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_k_780_);
lean_ctor_set(v_reuseFailAlloc_847_, 2, v_v_781_);
lean_ctor_set(v_reuseFailAlloc_847_, 3, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_847_, 4, v_r_783_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_861_; 
v_l_861_ = lean_ctor_get(v_impl_776_, 3);
lean_inc(v_l_861_);
if (lean_obj_tag(v_l_861_) == 0)
{
lean_object* v_r_862_; lean_object* v_k_863_; lean_object* v_v_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_887_; 
v_r_862_ = lean_ctor_get(v_impl_776_, 4);
v_k_863_ = lean_ctor_get(v_impl_776_, 1);
v_v_864_ = lean_ctor_get(v_impl_776_, 2);
v_isSharedCheck_887_ = !lean_is_exclusive(v_impl_776_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; lean_object* v_unused_889_; 
v_unused_888_ = lean_ctor_get(v_impl_776_, 3);
lean_dec(v_unused_888_);
v_unused_889_ = lean_ctor_get(v_impl_776_, 0);
lean_dec(v_unused_889_);
v___x_866_ = v_impl_776_;
v_isShared_867_ = v_isSharedCheck_887_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_r_862_);
lean_inc(v_v_864_);
lean_inc(v_k_863_);
lean_dec(v_impl_776_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_887_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_k_868_; lean_object* v_v_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_883_; 
v_k_868_ = lean_ctor_get(v_l_861_, 1);
v_v_869_ = lean_ctor_get(v_l_861_, 2);
v_isSharedCheck_883_ = !lean_is_exclusive(v_l_861_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; lean_object* v_unused_885_; lean_object* v_unused_886_; 
v_unused_884_ = lean_ctor_get(v_l_861_, 4);
lean_dec(v_unused_884_);
v_unused_885_ = lean_ctor_get(v_l_861_, 3);
lean_dec(v_unused_885_);
v_unused_886_ = lean_ctor_get(v_l_861_, 0);
lean_dec(v_unused_886_);
v___x_871_ = v_l_861_;
v_isShared_872_ = v_isSharedCheck_883_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_v_869_);
lean_inc(v_k_868_);
lean_dec(v_l_861_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_883_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_862_, 2);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 4, v_r_862_);
lean_ctor_set(v___x_871_, 3, v_r_862_);
lean_ctor_set(v___x_871_, 2, v_v_629_);
lean_ctor_set(v___x_871_, 1, v_k_628_);
lean_ctor_set(v___x_871_, 0, v___x_777_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_882_, 3, v_r_862_);
lean_ctor_set(v_reuseFailAlloc_882_, 4, v_r_862_);
v___x_875_ = v_reuseFailAlloc_882_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_877_; 
lean_inc(v_r_862_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 3, v_r_862_);
lean_ctor_set(v___x_866_, 0, v___x_777_);
v___x_877_ = v___x_866_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_k_863_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_v_864_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v_r_862_);
lean_ctor_set(v_reuseFailAlloc_881_, 4, v_r_862_);
v___x_877_ = v_reuseFailAlloc_881_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_879_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v___x_877_);
lean_ctor_set(v___x_633_, 3, v___x_875_);
lean_ctor_set(v___x_633_, 2, v_v_869_);
lean_ctor_set(v___x_633_, 1, v_k_868_);
lean_ctor_set(v___x_633_, 0, v___x_873_);
v___x_879_ = v___x_633_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_k_868_);
lean_ctor_set(v_reuseFailAlloc_880_, 2, v_v_869_);
lean_ctor_set(v_reuseFailAlloc_880_, 3, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_880_, 4, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
}
else
{
lean_object* v_r_890_; 
v_r_890_ = lean_ctor_get(v_impl_776_, 4);
lean_inc(v_r_890_);
if (lean_obj_tag(v_r_890_) == 0)
{
lean_object* v_k_891_; lean_object* v_v_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_903_; 
v_k_891_ = lean_ctor_get(v_impl_776_, 1);
v_v_892_ = lean_ctor_get(v_impl_776_, 2);
v_isSharedCheck_903_ = !lean_is_exclusive(v_impl_776_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; lean_object* v_unused_905_; lean_object* v_unused_906_; 
v_unused_904_ = lean_ctor_get(v_impl_776_, 4);
lean_dec(v_unused_904_);
v_unused_905_ = lean_ctor_get(v_impl_776_, 3);
lean_dec(v_unused_905_);
v_unused_906_ = lean_ctor_get(v_impl_776_, 0);
lean_dec(v_unused_906_);
v___x_894_ = v_impl_776_;
v_isShared_895_ = v_isSharedCheck_903_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_v_892_);
lean_inc(v_k_891_);
lean_dec(v_impl_776_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_903_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_unsigned_to_nat(3u);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 4, v_l_861_);
lean_ctor_set(v___x_894_, 2, v_v_629_);
lean_ctor_set(v___x_894_, 1, v_k_628_);
lean_ctor_set(v___x_894_, 0, v___x_777_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_l_861_);
lean_ctor_set(v_reuseFailAlloc_902_, 4, v_l_861_);
v___x_898_ = v_reuseFailAlloc_902_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v_r_890_);
lean_ctor_set(v___x_633_, 3, v___x_898_);
lean_ctor_set(v___x_633_, 2, v_v_892_);
lean_ctor_set(v___x_633_, 1, v_k_891_);
lean_ctor_set(v___x_633_, 0, v___x_896_);
v___x_900_ = v___x_633_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_k_891_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_v_892_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_901_, 4, v_r_890_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = lean_unsigned_to_nat(2u);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v_impl_776_);
lean_ctor_set(v___x_633_, 3, v_r_890_);
lean_ctor_set(v___x_633_, 0, v___x_907_);
v___x_909_ = v___x_633_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_r_890_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_impl_776_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
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
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_unsigned_to_nat(1u);
v___x_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v_k_624_);
lean_ctor_set(v___x_913_, 2, v_v_625_);
lean_ctor_set(v___x_913_, 3, v_t_626_);
lean_ctor_set(v___x_913_, 4, v_t_626_);
return v___x_913_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(lean_object* v_k_914_, lean_object* v_t_915_){
_start:
{
if (lean_obj_tag(v_t_915_) == 0)
{
lean_object* v_k_916_; lean_object* v_l_917_; lean_object* v_r_918_; uint8_t v___x_919_; 
v_k_916_ = lean_ctor_get(v_t_915_, 1);
v_l_917_ = lean_ctor_get(v_t_915_, 3);
v_r_918_ = lean_ctor_get(v_t_915_, 4);
v___x_919_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_914_, v_k_916_);
switch(v___x_919_)
{
case 0:
{
v_t_915_ = v_l_917_;
goto _start;
}
case 1:
{
uint8_t v___x_921_; 
v___x_921_ = 1;
return v___x_921_;
}
default: 
{
v_t_915_ = v_r_918_;
goto _start;
}
}
}
else
{
uint8_t v___x_923_; 
v___x_923_ = 0;
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg___boxed(lean_object* v_k_924_, lean_object* v_t_925_){
_start:
{
uint8_t v_res_926_; lean_object* v_r_927_; 
v_res_926_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_924_, v_t_925_);
lean_dec(v_t_925_);
lean_dec(v_k_924_);
v_r_927_ = lean_box(v_res_926_);
return v_r_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object* v___y_928_){
_start:
{
lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_929_ = lean_box(1);
v___x_930_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v___y_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_box(0);
v___x_932_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___y_928_, v___x_931_, v___x_929_);
return v___x_932_;
}
else
{
lean_dec(v___y_928_);
return v___x_929_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(lean_object* v_00_u03b2_935_, lean_object* v_k_936_, lean_object* v_t_937_){
_start:
{
uint8_t v___x_938_; 
v___x_938_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_936_, v_t_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___boxed(lean_object* v_00_u03b2_939_, lean_object* v_k_940_, lean_object* v_t_941_){
_start:
{
uint8_t v_res_942_; lean_object* v_r_943_; 
v_res_942_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(v_00_u03b2_939_, v_k_940_, v_t_941_);
lean_dec(v_t_941_);
lean_dec(v_k_940_);
v_r_943_ = lean_box(v_res_942_);
return v_r_943_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1(lean_object* v_00_u03b2_944_, lean_object* v_k_945_, lean_object* v_v_946_, lean_object* v_t_947_, lean_object* v_hl_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_945_, v_v_946_, v_t_947_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_950_, lean_object* v_a_951_, lean_object* v_b_952_, lean_object* v_c_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = lean_apply_2(v_f_950_, v_a_951_, v_c_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_955_, lean_object* v_____do__lift_956_){
_start:
{
lean_object* v_a_957_; lean_object* v___x_958_; 
v_a_957_ = lean_ctor_get(v_____do__lift_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref(v_____do__lift_956_);
v___x_958_ = lean_apply_2(v_toPure_955_, lean_box(0), v_a_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg(lean_object* v_inst_959_, lean_object* v_m_960_, lean_object* v_init_961_, lean_object* v_f_962_){
_start:
{
lean_object* v_toApplicative_963_; lean_object* v_toBind_964_; lean_object* v_toPure_965_; lean_object* v___f_966_; lean_object* v___x_967_; lean_object* v___f_968_; lean_object* v___x_969_; 
v_toApplicative_963_ = lean_ctor_get(v_inst_959_, 0);
v_toBind_964_ = lean_ctor_get(v_inst_959_, 1);
lean_inc(v_toBind_964_);
v_toPure_965_ = lean_ctor_get(v_toApplicative_963_, 1);
lean_inc(v_toPure_965_);
v___f_966_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_966_, 0, v_f_962_);
v___x_967_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_959_, v___f_966_, v_init_961_, v_m_960_);
v___f_968_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_968_, 0, v_toPure_965_);
v___x_969_ = lean_apply_4(v_toBind_964_, lean_box(0), lean_box(0), v___x_967_, v___f_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1(lean_object* v_m_970_, lean_object* v_inst_971_, lean_object* v_00_u03b2_972_, lean_object* v_m_973_, lean_object* v_init_974_, lean_object* v_f_975_){
_start:
{
lean_object* v_toApplicative_976_; lean_object* v_toBind_977_; lean_object* v_toPure_978_; lean_object* v___f_979_; lean_object* v___x_980_; lean_object* v___f_981_; lean_object* v___x_982_; 
v_toApplicative_976_ = lean_ctor_get(v_inst_971_, 0);
v_toBind_977_ = lean_ctor_get(v_inst_971_, 1);
lean_inc(v_toBind_977_);
v_toPure_978_ = lean_ctor_get(v_toApplicative_976_, 1);
lean_inc(v_toPure_978_);
v___f_979_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_979_, 0, v_f_975_);
v___x_980_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_971_, v___f_979_, v_init_974_, v_m_973_);
v___f_981_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_981_, 0, v_toPure_978_);
v___x_982_ = lean_apply_4(v_toBind_977_, lean_box(0), lean_box(0), v___x_980_, v___f_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___redArg(lean_object* v_inst_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_984_, 0, lean_box(0));
lean_closure_set(v___x_984_, 1, v_inst_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad(lean_object* v_m_985_, lean_object* v_inst_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_987_, 0, lean_box(0));
lean_closure_set(v___x_987_, 1, v_inst_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object* v_s_988_, lean_object* v_fvarId_989_){
_start:
{
uint8_t v___x_990_; 
v___x_990_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_fvarId_989_, v_s_988_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_box(0);
v___x_992_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_989_, v___x_991_, v_s_988_);
return v___x_992_;
}
else
{
lean_dec(v_fvarId_989_);
return v_s_988_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(lean_object* v_init_993_, lean_object* v_x_994_){
_start:
{
if (lean_obj_tag(v_x_994_) == 0)
{
lean_object* v_k_995_; lean_object* v_l_996_; lean_object* v_r_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_k_995_ = lean_ctor_get(v_x_994_, 1);
lean_inc(v_k_995_);
v_l_996_ = lean_ctor_get(v_x_994_, 3);
lean_inc(v_l_996_);
v_r_997_ = lean_ctor_get(v_x_994_, 4);
lean_inc(v_r_997_);
lean_dec_ref_known(v_x_994_, 5);
v___x_998_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_993_, v_l_996_);
v___x_999_ = l_Lean_FVarIdSet_insert(v___x_998_, v_k_995_);
v_init_993_ = v___x_999_;
v_x_994_ = v_r_997_;
goto _start;
}
else
{
return v_init_993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_union(lean_object* v_vs_u2081_1001_, lean_object* v_vs_u2082_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_vs_u2082_1002_, v_vs_u2081_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0(lean_object* v_init_1004_, lean_object* v_t_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_1004_, v_t_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList(lean_object* v_l_1007_){
_start:
{
lean_object* v___f_1008_; lean_object* v___x_1009_; 
v___f_1008_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1009_ = l_Std_TreeSet_ofList___redArg(v_l_1007_, v___f_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList___boxed(lean_object* v_l_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_FVarIdSet_ofList(v_l_1010_);
lean_dec(v_l_1010_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object* v_l_1012_){
_start:
{
lean_object* v___f_1013_; lean_object* v___x_1014_; 
v___f_1013_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1014_ = l_Std_TreeSet_ofArray___redArg(v_l_1012_, v___f_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object* v_l_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_FVarIdSet_ofArray(v_l_1015_);
lean_dec_ref(v_l_1015_);
return v_res_1016_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = lean_box(0);
v___x_1018_ = lean_unsigned_to_nat(16u);
v___x_1019_ = lean_mk_array(v___x_1018_, v___x_1017_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0);
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v___x_1020_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet(void){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet(void){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object* v_s_1027_, lean_object* v_fvarId_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1028_, v_a_1029_, v_s_1027_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object* v_00_u03b1_1031_, lean_object* v_s_1032_, lean_object* v_fvarId_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1033_, v_a_1034_, v_s_1032_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_box(1);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg();
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1(lean_object* v_00_u03b1_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_box(1);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg(){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_box(1);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg___boxed(lean_object* v___dummy_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_instEmptyCollectionFVarIdMap___redArg();
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* v_00_u03b1_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_box(1);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg(){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_box(1);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg___boxed(lean_object* v___dummy_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_instInhabitedFVarIdMap___redArg();
return v_res_1051_;
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
v___x_1067_ = 8934034000889494153ULL;
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
v_k_1110_ = lean_ctor_get(v_impl_1106_, 1);
v_v_1111_ = lean_ctor_get(v_impl_1106_, 2);
v_l_1112_ = lean_ctor_get(v_impl_1106_, 3);
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
v___x_1117_ = lean_nat_add(v___x_1107_, v_size_1109_);
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
lean_inc(v_l_1112_);
lean_inc(v_v_1111_);
lean_inc(v_k_1110_);
lean_inc(v_size_1109_);
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
v___x_1143_ = lean_nat_add(v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec(v___y_1141_);
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
lean_ctor_set(v___x_1123_, 3, v___y_1140_);
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
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v___y_1140_);
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
v___y_1140_ = v___x_1155_;
v___y_1141_ = v___x_1156_;
v___y_1142_ = v_size_1157_;
goto v___jp_1139_;
}
else
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_unsigned_to_nat(0u);
v___y_1140_ = v___x_1155_;
v___y_1141_ = v___x_1156_;
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
if (lean_obj_tag(v_l_1193_) == 0)
{
lean_object* v_r_1194_; lean_object* v_k_1195_; lean_object* v_v_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1207_; 
lean_inc_ref(v_l_1193_);
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
lean_inc(v_l_1193_);
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
v_k_1250_ = lean_ctor_get(v_impl_1246_, 1);
v_v_1251_ = lean_ctor_get(v_impl_1246_, 2);
v_l_1252_ = lean_ctor_get(v_impl_1246_, 3);
lean_inc(v_l_1252_);
v_r_1253_ = lean_ctor_get(v_impl_1246_, 4);
v___x_1254_ = lean_unsigned_to_nat(3u);
v___x_1255_ = lean_nat_mul(v___x_1254_, v_size_1248_);
v___x_1256_ = lean_nat_dec_lt(v___x_1255_, v_size_1249_);
lean_dec(v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
lean_dec(v_l_1252_);
v___x_1257_ = lean_nat_add(v___x_1247_, v_size_1248_);
v___x_1258_ = lean_nat_add(v___x_1257_, v_size_1249_);
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
lean_inc(v_r_1253_);
lean_inc(v_v_1251_);
lean_inc(v_k_1250_);
lean_inc(v_size_1249_);
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
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_box(1);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg();
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object* v_00_u03b1_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_box(1);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg(){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_box(1);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg___boxed(lean_object* v___dummy_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_instEmptyCollectionMVarIdMap___redArg();
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* v_00_u03b1_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_box(1);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_1464_, lean_object* v_a_1465_, lean_object* v_b_1466_, lean_object* v_c_1467_){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_a_1465_);
lean_ctor_set(v___x_1468_, 1, v_b_1466_);
v___x_1469_ = lean_apply_2(v_f_1464_, v___x_1468_, v_c_1467_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1470_, lean_object* v_m_1471_, lean_object* v_init_1472_, lean_object* v_f_1473_){
_start:
{
lean_object* v_toApplicative_1474_; lean_object* v_toBind_1475_; lean_object* v_toPure_1476_; lean_object* v___f_1477_; lean_object* v___x_1478_; lean_object* v___f_1479_; lean_object* v___x_1480_; 
v_toApplicative_1474_ = lean_ctor_get(v_inst_1470_, 0);
v_toBind_1475_ = lean_ctor_get(v_inst_1470_, 1);
lean_inc(v_toBind_1475_);
v_toPure_1476_ = lean_ctor_get(v_toApplicative_1474_, 1);
lean_inc(v_toPure_1476_);
v___f_1477_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1477_, 0, v_f_1473_);
v___x_1478_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1470_, v___f_1477_, v_init_1472_, v_m_1471_);
v___f_1479_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1479_, 0, v_toPure_1476_);
v___x_1480_ = lean_apply_4(v_toBind_1475_, lean_box(0), lean_box(0), v___x_1478_, v___f_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object* v_m_1481_, lean_object* v_00_u03b1_1482_, lean_object* v_inst_1483_, lean_object* v_00_u03b2_1484_, lean_object* v_m_1485_, lean_object* v_init_1486_, lean_object* v_f_1487_){
_start:
{
lean_object* v_toApplicative_1488_; lean_object* v_toBind_1489_; lean_object* v_toPure_1490_; lean_object* v___f_1491_; lean_object* v___x_1492_; lean_object* v___f_1493_; lean_object* v___x_1494_; 
v_toApplicative_1488_ = lean_ctor_get(v_inst_1483_, 0);
v_toBind_1489_ = lean_ctor_get(v_inst_1483_, 1);
lean_inc(v_toBind_1489_);
v_toPure_1490_ = lean_ctor_get(v_toApplicative_1488_, 1);
lean_inc(v_toPure_1490_);
v___f_1491_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1491_, 0, v_f_1487_);
v___x_1492_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1483_, v___f_1491_, v_init_1486_, v_m_1485_);
v___f_1493_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1493_, 0, v_toPure_1490_);
v___x_1494_ = lean_apply_4(v_toBind_1489_, lean_box(0), lean_box(0), v___x_1492_, v___f_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object* v_inst_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1496_, 0, lean_box(0));
lean_closure_set(v___x_1496_, 1, lean_box(0));
lean_closure_set(v___x_1496_, 2, v_inst_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object* v_m_1497_, lean_object* v_00_u03b1_1498_, lean_object* v_inst_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1500_, 0, lean_box(0));
lean_closure_set(v___x_1500_, 1, lean_box(0));
lean_closure_set(v___x_1500_, 2, v_inst_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg(){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_box(1);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg___boxed(lean_object* v___dummy_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_instInhabitedMVarIdMap___redArg();
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* v_00_u03b1_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_box(1);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx(lean_object* v_x_1507_){
_start:
{
switch(lean_obj_tag(v_x_1507_))
{
case 0:
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_unsigned_to_nat(0u);
return v___x_1508_;
}
case 1:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_unsigned_to_nat(1u);
return v___x_1509_;
}
case 2:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_unsigned_to_nat(2u);
return v___x_1510_;
}
case 3:
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_unsigned_to_nat(3u);
return v___x_1511_;
}
case 4:
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_unsigned_to_nat(4u);
return v___x_1512_;
}
case 5:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_unsigned_to_nat(5u);
return v___x_1513_;
}
case 6:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_unsigned_to_nat(6u);
return v___x_1514_;
}
case 7:
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_unsigned_to_nat(7u);
return v___x_1515_;
}
case 8:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_unsigned_to_nat(8u);
return v___x_1516_;
}
case 9:
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_unsigned_to_nat(9u);
return v___x_1517_;
}
case 10:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_unsigned_to_nat(10u);
return v___x_1518_;
}
default: 
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_unsigned_to_nat(11u);
return v___x_1519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___boxed(lean_object* v_x_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Expr_ctorIdx(v_x_1520_);
lean_dec_ref(v_x_1520_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object* v_t_1522_, lean_object* v_k_1523_){
_start:
{
switch(lean_obj_tag(v_t_1522_))
{
case 4:
{
lean_object* v_declName_1524_; lean_object* v_us_1525_; lean_object* v___x_1526_; 
v_declName_1524_ = lean_ctor_get(v_t_1522_, 0);
lean_inc(v_declName_1524_);
v_us_1525_ = lean_ctor_get(v_t_1522_, 1);
lean_inc(v_us_1525_);
lean_dec_ref_known(v_t_1522_, 2);
v___x_1526_ = lean_apply_2(v_k_1523_, v_declName_1524_, v_us_1525_);
return v___x_1526_;
}
case 5:
{
lean_object* v_fn_1527_; lean_object* v_arg_1528_; lean_object* v___x_1529_; 
v_fn_1527_ = lean_ctor_get(v_t_1522_, 0);
lean_inc_ref(v_fn_1527_);
v_arg_1528_ = lean_ctor_get(v_t_1522_, 1);
lean_inc_ref(v_arg_1528_);
lean_dec_ref_known(v_t_1522_, 2);
v___x_1529_ = lean_apply_2(v_k_1523_, v_fn_1527_, v_arg_1528_);
return v___x_1529_;
}
case 6:
{
lean_object* v_binderName_1530_; lean_object* v_binderType_1531_; lean_object* v_body_1532_; uint8_t v_binderInfo_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v_binderName_1530_ = lean_ctor_get(v_t_1522_, 0);
lean_inc(v_binderName_1530_);
v_binderType_1531_ = lean_ctor_get(v_t_1522_, 1);
lean_inc_ref(v_binderType_1531_);
v_body_1532_ = lean_ctor_get(v_t_1522_, 2);
lean_inc_ref(v_body_1532_);
v_binderInfo_1533_ = lean_ctor_get_uint8(v_t_1522_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1522_, 3);
v___x_1534_ = lean_box(v_binderInfo_1533_);
v___x_1535_ = lean_apply_4(v_k_1523_, v_binderName_1530_, v_binderType_1531_, v_body_1532_, v___x_1534_);
return v___x_1535_;
}
case 7:
{
lean_object* v_binderName_1536_; lean_object* v_binderType_1537_; lean_object* v_body_1538_; uint8_t v_binderInfo_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_binderName_1536_ = lean_ctor_get(v_t_1522_, 0);
lean_inc(v_binderName_1536_);
v_binderType_1537_ = lean_ctor_get(v_t_1522_, 1);
lean_inc_ref(v_binderType_1537_);
v_body_1538_ = lean_ctor_get(v_t_1522_, 2);
lean_inc_ref(v_body_1538_);
v_binderInfo_1539_ = lean_ctor_get_uint8(v_t_1522_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1522_, 3);
v___x_1540_ = lean_box(v_binderInfo_1539_);
v___x_1541_ = lean_apply_4(v_k_1523_, v_binderName_1536_, v_binderType_1537_, v_body_1538_, v___x_1540_);
return v___x_1541_;
}
case 8:
{
lean_object* v_declName_1542_; lean_object* v_type_1543_; lean_object* v_value_1544_; lean_object* v_body_1545_; uint8_t v_nondep_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_declName_1542_ = lean_ctor_get(v_t_1522_, 0);
lean_inc(v_declName_1542_);
v_type_1543_ = lean_ctor_get(v_t_1522_, 1);
lean_inc_ref(v_type_1543_);
v_value_1544_ = lean_ctor_get(v_t_1522_, 2);
lean_inc_ref(v_value_1544_);
v_body_1545_ = lean_ctor_get(v_t_1522_, 3);
lean_inc_ref(v_body_1545_);
v_nondep_1546_ = lean_ctor_get_uint8(v_t_1522_, sizeof(void*)*4);
lean_dec_ref_known(v_t_1522_, 4);
v___x_1547_ = lean_box(v_nondep_1546_);
v___x_1548_ = lean_apply_5(v_k_1523_, v_declName_1542_, v_type_1543_, v_value_1544_, v_body_1545_, v___x_1547_);
return v___x_1548_;
}
case 9:
{
lean_object* v_a_1549_; lean_object* v___x_1550_; 
v_a_1549_ = lean_ctor_get(v_t_1522_, 0);
lean_inc_ref(v_a_1549_);
lean_dec_ref_known(v_t_1522_, 1);
v___x_1550_ = lean_apply_1(v_k_1523_, v_a_1549_);
return v___x_1550_;
}
case 10:
{
lean_object* v_data_1551_; lean_object* v_expr_1552_; lean_object* v___x_1553_; 
v_data_1551_ = lean_ctor_get(v_t_1522_, 0);
lean_inc(v_data_1551_);
v_expr_1552_ = lean_ctor_get(v_t_1522_, 1);
lean_inc_ref(v_expr_1552_);
lean_dec_ref_known(v_t_1522_, 2);
v___x_1553_ = lean_apply_2(v_k_1523_, v_data_1551_, v_expr_1552_);
return v___x_1553_;
}
case 11:
{
lean_object* v_typeName_1554_; lean_object* v_idx_1555_; lean_object* v_struct_1556_; lean_object* v___x_1557_; 
v_typeName_1554_ = lean_ctor_get(v_t_1522_, 0);
lean_inc(v_typeName_1554_);
v_idx_1555_ = lean_ctor_get(v_t_1522_, 1);
lean_inc(v_idx_1555_);
v_struct_1556_ = lean_ctor_get(v_t_1522_, 2);
lean_inc_ref(v_struct_1556_);
lean_dec_ref_known(v_t_1522_, 3);
v___x_1557_ = lean_apply_3(v_k_1523_, v_typeName_1554_, v_idx_1555_, v_struct_1556_);
return v___x_1557_;
}
default: 
{
lean_object* v_deBruijnIndex_1558_; lean_object* v___x_1559_; 
v_deBruijnIndex_1558_ = lean_ctor_get(v_t_1522_, 0);
lean_inc(v_deBruijnIndex_1558_);
lean_dec_ref(v_t_1522_);
v___x_1559_ = lean_apply_1(v_k_1523_, v_deBruijnIndex_1558_);
return v___x_1559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object* v_motive_1560_, lean_object* v_ctorIdx_1561_, lean_object* v_t_1562_, lean_object* v_h_1563_, lean_object* v_k_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Expr_ctorElim___redArg(v_t_1562_, v_k_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object* v_motive_1566_, lean_object* v_ctorIdx_1567_, lean_object* v_t_1568_, lean_object* v_h_1569_, lean_object* v_k_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Expr_ctorElim(v_motive_1566_, v_ctorIdx_1567_, v_t_1568_, v_h_1569_, v_k_1570_);
lean_dec(v_ctorIdx_1567_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object* v_t_1572_, lean_object* v_bvar_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_Expr_ctorElim___redArg(v_t_1572_, v_bvar_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object* v_motive_1575_, lean_object* v_t_1576_, lean_object* v_h_1577_, lean_object* v_bvar_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Expr_ctorElim___redArg(v_t_1576_, v_bvar_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object* v_t_1580_, lean_object* v_fvar_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_Expr_ctorElim___redArg(v_t_1580_, v_fvar_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object* v_motive_1583_, lean_object* v_t_1584_, lean_object* v_h_1585_, lean_object* v_fvar_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Expr_ctorElim___redArg(v_t_1584_, v_fvar_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object* v_t_1588_, lean_object* v_mvar_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Expr_ctorElim___redArg(v_t_1588_, v_mvar_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object* v_motive_1591_, lean_object* v_t_1592_, lean_object* v_h_1593_, lean_object* v_mvar_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_Expr_ctorElim___redArg(v_t_1592_, v_mvar_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object* v_t_1596_, lean_object* v_sort_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_Expr_ctorElim___redArg(v_t_1596_, v_sort_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object* v_motive_1599_, lean_object* v_t_1600_, lean_object* v_h_1601_, lean_object* v_sort_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Expr_ctorElim___redArg(v_t_1600_, v_sort_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object* v_t_1604_, lean_object* v_const_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Expr_ctorElim___redArg(v_t_1604_, v_const_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object* v_motive_1607_, lean_object* v_t_1608_, lean_object* v_h_1609_, lean_object* v_const_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Expr_ctorElim___redArg(v_t_1608_, v_const_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object* v_t_1612_, lean_object* v_app_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Expr_ctorElim___redArg(v_t_1612_, v_app_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object* v_motive_1615_, lean_object* v_t_1616_, lean_object* v_h_1617_, lean_object* v_app_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Expr_ctorElim___redArg(v_t_1616_, v_app_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object* v_t_1620_, lean_object* v_lam_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Expr_ctorElim___redArg(v_t_1620_, v_lam_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object* v_motive_1623_, lean_object* v_t_1624_, lean_object* v_h_1625_, lean_object* v_lam_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Expr_ctorElim___redArg(v_t_1624_, v_lam_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object* v_t_1628_, lean_object* v_forallE_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Expr_ctorElim___redArg(v_t_1628_, v_forallE_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object* v_motive_1631_, lean_object* v_t_1632_, lean_object* v_h_1633_, lean_object* v_forallE_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Expr_ctorElim___redArg(v_t_1632_, v_forallE_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object* v_t_1636_, lean_object* v_letE_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Expr_ctorElim___redArg(v_t_1636_, v_letE_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object* v_motive_1639_, lean_object* v_t_1640_, lean_object* v_h_1641_, lean_object* v_letE_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Expr_ctorElim___redArg(v_t_1640_, v_letE_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object* v_t_1644_, lean_object* v_lit_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Expr_ctorElim___redArg(v_t_1644_, v_lit_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object* v_motive_1647_, lean_object* v_t_1648_, lean_object* v_h_1649_, lean_object* v_lit_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_Expr_ctorElim___redArg(v_t_1648_, v_lit_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object* v_t_1652_, lean_object* v_mdata_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Expr_ctorElim___redArg(v_t_1652_, v_mdata_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object* v_motive_1655_, lean_object* v_t_1656_, lean_object* v_h_1657_, lean_object* v_mdata_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_Expr_ctorElim___redArg(v_t_1656_, v_mdata_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object* v_t_1660_, lean_object* v_proj_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Expr_ctorElim___redArg(v_t_1660_, v_proj_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object* v_motive_1663_, lean_object* v_t_1664_, lean_object* v_h_1665_, lean_object* v_proj_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_Expr_ctorElim___redArg(v_t_1664_, v_proj_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* v_a_00___x40___internal___hyg_1669_){
_start:
{
uint64_t v_res_1670_; lean_object* v_r_1671_; 
v_res_1670_ = lean_expr_data(v_a_00___x40___internal___hyg_1669_);
lean_dec_ref(v_a_00___x40___internal___hyg_1669_);
v_r_1671_ = lean_box_uint64(v_res_1670_);
return v_r_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object* v_t_1672_, lean_object* v_bvar_1673_, lean_object* v_fvar_1674_, lean_object* v_mvar_1675_, lean_object* v_sort_1676_, lean_object* v_const_1677_, lean_object* v_app_1678_, lean_object* v_lam_1679_, lean_object* v_forallE_1680_, lean_object* v_letE_1681_, lean_object* v_lit_1682_, lean_object* v_mdata_1683_, lean_object* v_proj_1684_){
_start:
{
switch(lean_obj_tag(v_t_1672_))
{
case 0:
{
lean_object* v_deBruijnIndex_1685_; lean_object* v___x_1686_; 
lean_dec(v_proj_1684_);
lean_dec(v_mdata_1683_);
lean_dec(v_lit_1682_);
lean_dec(v_letE_1681_);
lean_dec(v_forallE_1680_);
lean_dec(v_lam_1679_);
lean_dec(v_app_1678_);
lean_dec(v_const_1677_);
lean_dec(v_sort_1676_);
lean_dec(v_mvar_1675_);
lean_dec(v_fvar_1674_);
v_deBruijnIndex_1685_ = lean_ctor_get(v_t_1672_, 0);
lean_inc(v_deBruijnIndex_1685_);
lean_dec_ref_known(v_t_1672_, 1);
v___x_1686_ = lean_apply_1(v_bvar_1673_, v_deBruijnIndex_1685_);
return v___x_1686_;
}
case 1:
{
lean_object* v_fvarId_1687_; lean_object* v___x_1688_; 
lean_dec(v_proj_1684_);
lean_dec(v_mdata_1683_);
lean_dec(v_lit_1682_);
lean_dec(v_letE_1681_);
lean_dec(v_forallE_1680_);
lean_dec(v_lam_1679_);
lean_dec(v_app_1678_);
lean_dec(v_const_1677_);
lean_dec(v_sort_1676_);
lean_dec(v_mvar_1675_);
lean_dec(v_bvar_1673_);
v_fvarId_1687_ = lean_ctor_get(v_t_1672_, 0);
lean_inc(v_fvarId_1687_);
lean_dec_ref_known(v_t_1672_, 1);
v___x_1688_ = lean_apply_1(v_fvar_1674_, v_fvarId_1687_);
return v___x_1688_;
}
case 2:
{
lean_object* v_mvarId_1689_; lean_object* v___x_1690_; 
lean_dec(v_proj_1684_);
lean_dec(v_mdata_1683_);
lean_dec(v_lit_1682_);
lean_dec(v_letE_1681_);
lean_dec(v_forallE_1680_);
lean_dec(v_lam_1679_);
lean_dec(v_app_1678_);
lean_dec(v_const_1677_);
lean_dec(v_sort_1676_);
lean_dec(v_fvar_1674_);
lean_dec(v_bvar_1673_);
v_mvarId_1689_ = lean_ctor_get(v_t_1672_, 0);
lean_inc(v_mvarId_1689_);
lean_dec_ref_known(v_t_1672_, 1);
v___x_1690_ = lean_apply_1(v_mvar_1675_, v_mvarId_1689_);
return v___x_1690_;
}
case 3:
{
lean_object* v_u_1691_; lean_object* v___x_1692_; 
lean_dec(v_proj_1684_);
lean_dec(v_mdata_1683_);
lean_dec(v_lit_1682_);
lean_dec(v_letE_1681_);
lean_dec(v_forallE_1680_);
lean_dec(v_lam_1679_);
lean_dec(v_app_1678_);
lean_dec(v_const_1677_);
lean_dec(v_mvar_1675_);
lean_dec(v_fvar_1674_);
lean_dec(v_bvar_1673_);
v_u_1691_ = lean_ctor_get(v_t_1672_, 0);
lean_inc(v_u_1691_);
lean_dec_ref_known(v_t_1672_, 1);
v___x_1692_ = lean_apply_1(v_sort_1676_, v_u_1691_);
return v___x_1692_;
}
case 4:
{
lean_object* v_declName_1693_; lean_object* v_us_1694_; lean_object* v___x_1695_; 
lean_dec(v_proj_1684_);
lean_dec(v_mdata_1683_);
lean_dec(v_lit_1682_);
lean_dec(v_letE_1681_);
lean_dec(v_forallE_1680_);
lean_dec(v_lam_1679_);
lean_dec(v_app_1678_);
lean_dec(v_sort_1676_);
lean_dec(v_mvar_1675_);
lean_dec(v_fvar_1674_);
lean_dec(v_bvar_1673_);
v_declName_1693_ = lean_ctor_get(v_t_1672_, 0);
lean_inc(v_declName_1693_);
v_us_1694_ = lean_ctor_get(v_t_1672_, 1);
lean_inc(v_us_1694_);
lean_dec_ref_known(v_t_1672_, 2);
v___x_1695_ = lean_apply_2(v_const_1677_, v_declName_1693_, v_us_1694_);
return v___x_1695_;
}
case 5:
{
lean_object* v_fn_1696_; lean_object* v_arg_1697_; lean_object* v___x_1698_; 
lean_dec(v_proj_1684_);
lean_dec(v_mdata_1683_);
lean_dec(v_lit_1682_);
lean_dec(v_letE_1681_);
lean_dec(v_forallE_1680_);
lean_dec(v_lam_1679_);
lean_dec(v_const_1677_);
lean_dec(v_sort_1676_);
lean_dec(v_mvar_1675_);
lean_dec(v_fvar_1674_);
lean_dec(v_bvar_1673_);
v_fn_1696_ = lean_ctor_get(v_t_1672_, 0);
lean_inc_ref(v_fn_1696_);
v_arg_1697_ = lean_ctor_get(v_t_1672_, 1);
lean_inc_ref(v_arg_1697_);
lean_dec_ref_known(v_t_1672_, 2);
v___x_1698_ = lean_apply_2(v_app_1678_, v_fn_1696_, v_arg_1697_);
return v___x_1698_;
}
case 6:
{
lean_object* v_binderName_1699_; lean_object* v_binderType_1700_; lean_object* v_body_1701_; uint8_t v_binderInfo_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec(v_proj_1684_);
lean_dec(v_mdata_1683_);
lean_dec(v_lit_1682_);
lean_dec(v_letE_1681_);
lean_dec(v_forallE_1680_);
lean_dec(v_app_1678_);
lean_dec(v_const_1677_);
lean_dec(v_sort_1676_);
lean_dec(v_mvar_1675_);
lean_dec(v_fvar_1674_);
lean_dec(v_bvar_1673_);
v_binderName_1699_ = lean_ctor_get(v_t_1672_, 0);
lean_inc(v_binderName_1699_);
v_binderType_1700_ = lean_ctor_get(v_t_1672_, 1);
lean_inc_ref(v_binderType_1700_);
v_body_1701_ = lean_ctor_get(v_t_1672_, 2);
lean_inc_ref(v_body_1701_);
v_binderInfo_1702_ = lean_ctor_get_uint8(v_t_1672_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1672_, 3);
v___x_1703_ = lean_box(v_binderInfo_1702_);
v___x_1704_ = lean_apply_4(v_lam_1679_, v_binderName_1699_, v_binderType_1700_, v_body_1701_, v___x_1703_);
return v___x_1704_;
}
case 7:
{
lean_object* v_binderName_1705_; lean_object* v_binderType_1706_; lean_object* v_body_1707_; uint8_t v_binderInfo_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_dec(v_proj_1684_);
lean_dec(v_mdata_1683_);
lean_dec(v_lit_1682_);
lean_dec(v_letE_1681_);
lean_dec(v_lam_1679_);
lean_dec(v_app_1678_);
lean_dec(v_const_1677_);
lean_dec(v_sort_1676_);
lean_dec(v_mvar_1675_);
lean_dec(v_fvar_1674_);
lean_dec(v_bvar_1673_);
v_binderName_1705_ = lean_ctor_get(v_t_1672_, 0);
lean_inc(v_binderName_1705_);
v_binderType_1706_ = lean_ctor_get(v_t_1672_, 1);
lean_inc_ref(v_binderType_1706_);
v_body_1707_ = lean_ctor_get(v_t_1672_, 2);
lean_inc_ref(v_body_1707_);
v_binderInfo_1708_ = lean_ctor_get_uint8(v_t_1672_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1672_, 3);
v___x_1709_ = lean_box(v_binderInfo_1708_);
v___x_1710_ = lean_apply_4(v_forallE_1680_, v_binderName_1705_, v_binderType_1706_, v_body_1707_, v___x_1709_);
return v___x_1710_;
}
case 8:
{
lean_object* v_declName_1711_; lean_object* v_type_1712_; lean_object* v_value_1713_; lean_object* v_body_1714_; uint8_t v_nondep_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_dec(v_proj_1684_);
lean_dec(v_mdata_1683_);
lean_dec(v_lit_1682_);
lean_dec(v_forallE_1680_);
lean_dec(v_lam_1679_);
lean_dec(v_app_1678_);
lean_dec(v_const_1677_);
lean_dec(v_sort_1676_);
lean_dec(v_mvar_1675_);
lean_dec(v_fvar_1674_);
lean_dec(v_bvar_1673_);
v_declName_1711_ = lean_ctor_get(v_t_1672_, 0);
lean_inc(v_declName_1711_);
v_type_1712_ = lean_ctor_get(v_t_1672_, 1);
lean_inc_ref(v_type_1712_);
v_value_1713_ = lean_ctor_get(v_t_1672_, 2);
lean_inc_ref(v_value_1713_);
v_body_1714_ = lean_ctor_get(v_t_1672_, 3);
lean_inc_ref(v_body_1714_);
v_nondep_1715_ = lean_ctor_get_uint8(v_t_1672_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1672_, 4);
v___x_1716_ = lean_box(v_nondep_1715_);
v___x_1717_ = lean_apply_5(v_letE_1681_, v_declName_1711_, v_type_1712_, v_value_1713_, v_body_1714_, v___x_1716_);
return v___x_1717_;
}
case 9:
{
lean_object* v_a_1718_; lean_object* v___x_1719_; 
lean_dec(v_proj_1684_);
lean_dec(v_mdata_1683_);
lean_dec(v_letE_1681_);
lean_dec(v_forallE_1680_);
lean_dec(v_lam_1679_);
lean_dec(v_app_1678_);
lean_dec(v_const_1677_);
lean_dec(v_sort_1676_);
lean_dec(v_mvar_1675_);
lean_dec(v_fvar_1674_);
lean_dec(v_bvar_1673_);
v_a_1718_ = lean_ctor_get(v_t_1672_, 0);
lean_inc_ref(v_a_1718_);
lean_dec_ref_known(v_t_1672_, 1);
v___x_1719_ = lean_apply_1(v_lit_1682_, v_a_1718_);
return v___x_1719_;
}
case 10:
{
lean_object* v_data_1720_; lean_object* v_expr_1721_; lean_object* v___x_1722_; 
lean_dec(v_proj_1684_);
lean_dec(v_lit_1682_);
lean_dec(v_letE_1681_);
lean_dec(v_forallE_1680_);
lean_dec(v_lam_1679_);
lean_dec(v_app_1678_);
lean_dec(v_const_1677_);
lean_dec(v_sort_1676_);
lean_dec(v_mvar_1675_);
lean_dec(v_fvar_1674_);
lean_dec(v_bvar_1673_);
v_data_1720_ = lean_ctor_get(v_t_1672_, 0);
lean_inc(v_data_1720_);
v_expr_1721_ = lean_ctor_get(v_t_1672_, 1);
lean_inc_ref(v_expr_1721_);
lean_dec_ref_known(v_t_1672_, 2);
v___x_1722_ = lean_apply_2(v_mdata_1683_, v_data_1720_, v_expr_1721_);
return v___x_1722_;
}
default: 
{
lean_object* v_typeName_1723_; lean_object* v_idx_1724_; lean_object* v_struct_1725_; lean_object* v___x_1726_; 
lean_dec(v_mdata_1683_);
lean_dec(v_lit_1682_);
lean_dec(v_letE_1681_);
lean_dec(v_forallE_1680_);
lean_dec(v_lam_1679_);
lean_dec(v_app_1678_);
lean_dec(v_const_1677_);
lean_dec(v_sort_1676_);
lean_dec(v_mvar_1675_);
lean_dec(v_fvar_1674_);
lean_dec(v_bvar_1673_);
v_typeName_1723_ = lean_ctor_get(v_t_1672_, 0);
lean_inc(v_typeName_1723_);
v_idx_1724_ = lean_ctor_get(v_t_1672_, 1);
lean_inc(v_idx_1724_);
v_struct_1725_ = lean_ctor_get(v_t_1672_, 2);
lean_inc_ref(v_struct_1725_);
lean_dec_ref_known(v_t_1672_, 3);
v___x_1726_ = lean_apply_3(v_proj_1684_, v_typeName_1723_, v_idx_1724_, v_struct_1725_);
return v___x_1726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* v_motive_1727_, lean_object* v_t_1728_, lean_object* v_bvar_1729_, lean_object* v_fvar_1730_, lean_object* v_mvar_1731_, lean_object* v_sort_1732_, lean_object* v_const_1733_, lean_object* v_app_1734_, lean_object* v_lam_1735_, lean_object* v_forallE_1736_, lean_object* v_letE_1737_, lean_object* v_lit_1738_, lean_object* v_mdata_1739_, lean_object* v_proj_1740_){
_start:
{
switch(lean_obj_tag(v_t_1728_))
{
case 0:
{
lean_object* v_deBruijnIndex_1741_; lean_object* v___x_1742_; 
lean_dec(v_proj_1740_);
lean_dec(v_mdata_1739_);
lean_dec(v_lit_1738_);
lean_dec(v_letE_1737_);
lean_dec(v_forallE_1736_);
lean_dec(v_lam_1735_);
lean_dec(v_app_1734_);
lean_dec(v_const_1733_);
lean_dec(v_sort_1732_);
lean_dec(v_mvar_1731_);
lean_dec(v_fvar_1730_);
v_deBruijnIndex_1741_ = lean_ctor_get(v_t_1728_, 0);
lean_inc(v_deBruijnIndex_1741_);
lean_dec_ref_known(v_t_1728_, 1);
v___x_1742_ = lean_apply_1(v_bvar_1729_, v_deBruijnIndex_1741_);
return v___x_1742_;
}
case 1:
{
lean_object* v_fvarId_1743_; lean_object* v___x_1744_; 
lean_dec(v_proj_1740_);
lean_dec(v_mdata_1739_);
lean_dec(v_lit_1738_);
lean_dec(v_letE_1737_);
lean_dec(v_forallE_1736_);
lean_dec(v_lam_1735_);
lean_dec(v_app_1734_);
lean_dec(v_const_1733_);
lean_dec(v_sort_1732_);
lean_dec(v_mvar_1731_);
lean_dec(v_bvar_1729_);
v_fvarId_1743_ = lean_ctor_get(v_t_1728_, 0);
lean_inc(v_fvarId_1743_);
lean_dec_ref_known(v_t_1728_, 1);
v___x_1744_ = lean_apply_1(v_fvar_1730_, v_fvarId_1743_);
return v___x_1744_;
}
case 2:
{
lean_object* v_mvarId_1745_; lean_object* v___x_1746_; 
lean_dec(v_proj_1740_);
lean_dec(v_mdata_1739_);
lean_dec(v_lit_1738_);
lean_dec(v_letE_1737_);
lean_dec(v_forallE_1736_);
lean_dec(v_lam_1735_);
lean_dec(v_app_1734_);
lean_dec(v_const_1733_);
lean_dec(v_sort_1732_);
lean_dec(v_fvar_1730_);
lean_dec(v_bvar_1729_);
v_mvarId_1745_ = lean_ctor_get(v_t_1728_, 0);
lean_inc(v_mvarId_1745_);
lean_dec_ref_known(v_t_1728_, 1);
v___x_1746_ = lean_apply_1(v_mvar_1731_, v_mvarId_1745_);
return v___x_1746_;
}
case 3:
{
lean_object* v_u_1747_; lean_object* v___x_1748_; 
lean_dec(v_proj_1740_);
lean_dec(v_mdata_1739_);
lean_dec(v_lit_1738_);
lean_dec(v_letE_1737_);
lean_dec(v_forallE_1736_);
lean_dec(v_lam_1735_);
lean_dec(v_app_1734_);
lean_dec(v_const_1733_);
lean_dec(v_mvar_1731_);
lean_dec(v_fvar_1730_);
lean_dec(v_bvar_1729_);
v_u_1747_ = lean_ctor_get(v_t_1728_, 0);
lean_inc(v_u_1747_);
lean_dec_ref_known(v_t_1728_, 1);
v___x_1748_ = lean_apply_1(v_sort_1732_, v_u_1747_);
return v___x_1748_;
}
case 4:
{
lean_object* v_declName_1749_; lean_object* v_us_1750_; lean_object* v___x_1751_; 
lean_dec(v_proj_1740_);
lean_dec(v_mdata_1739_);
lean_dec(v_lit_1738_);
lean_dec(v_letE_1737_);
lean_dec(v_forallE_1736_);
lean_dec(v_lam_1735_);
lean_dec(v_app_1734_);
lean_dec(v_sort_1732_);
lean_dec(v_mvar_1731_);
lean_dec(v_fvar_1730_);
lean_dec(v_bvar_1729_);
v_declName_1749_ = lean_ctor_get(v_t_1728_, 0);
lean_inc(v_declName_1749_);
v_us_1750_ = lean_ctor_get(v_t_1728_, 1);
lean_inc(v_us_1750_);
lean_dec_ref_known(v_t_1728_, 2);
v___x_1751_ = lean_apply_2(v_const_1733_, v_declName_1749_, v_us_1750_);
return v___x_1751_;
}
case 5:
{
lean_object* v_fn_1752_; lean_object* v_arg_1753_; lean_object* v___x_1754_; 
lean_dec(v_proj_1740_);
lean_dec(v_mdata_1739_);
lean_dec(v_lit_1738_);
lean_dec(v_letE_1737_);
lean_dec(v_forallE_1736_);
lean_dec(v_lam_1735_);
lean_dec(v_const_1733_);
lean_dec(v_sort_1732_);
lean_dec(v_mvar_1731_);
lean_dec(v_fvar_1730_);
lean_dec(v_bvar_1729_);
v_fn_1752_ = lean_ctor_get(v_t_1728_, 0);
lean_inc_ref(v_fn_1752_);
v_arg_1753_ = lean_ctor_get(v_t_1728_, 1);
lean_inc_ref(v_arg_1753_);
lean_dec_ref_known(v_t_1728_, 2);
v___x_1754_ = lean_apply_2(v_app_1734_, v_fn_1752_, v_arg_1753_);
return v___x_1754_;
}
case 6:
{
lean_object* v_binderName_1755_; lean_object* v_binderType_1756_; lean_object* v_body_1757_; uint8_t v_binderInfo_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v_proj_1740_);
lean_dec(v_mdata_1739_);
lean_dec(v_lit_1738_);
lean_dec(v_letE_1737_);
lean_dec(v_forallE_1736_);
lean_dec(v_app_1734_);
lean_dec(v_const_1733_);
lean_dec(v_sort_1732_);
lean_dec(v_mvar_1731_);
lean_dec(v_fvar_1730_);
lean_dec(v_bvar_1729_);
v_binderName_1755_ = lean_ctor_get(v_t_1728_, 0);
lean_inc(v_binderName_1755_);
v_binderType_1756_ = lean_ctor_get(v_t_1728_, 1);
lean_inc_ref(v_binderType_1756_);
v_body_1757_ = lean_ctor_get(v_t_1728_, 2);
lean_inc_ref(v_body_1757_);
v_binderInfo_1758_ = lean_ctor_get_uint8(v_t_1728_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1728_, 3);
v___x_1759_ = lean_box(v_binderInfo_1758_);
v___x_1760_ = lean_apply_4(v_lam_1735_, v_binderName_1755_, v_binderType_1756_, v_body_1757_, v___x_1759_);
return v___x_1760_;
}
case 7:
{
lean_object* v_binderName_1761_; lean_object* v_binderType_1762_; lean_object* v_body_1763_; uint8_t v_binderInfo_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_dec(v_proj_1740_);
lean_dec(v_mdata_1739_);
lean_dec(v_lit_1738_);
lean_dec(v_letE_1737_);
lean_dec(v_lam_1735_);
lean_dec(v_app_1734_);
lean_dec(v_const_1733_);
lean_dec(v_sort_1732_);
lean_dec(v_mvar_1731_);
lean_dec(v_fvar_1730_);
lean_dec(v_bvar_1729_);
v_binderName_1761_ = lean_ctor_get(v_t_1728_, 0);
lean_inc(v_binderName_1761_);
v_binderType_1762_ = lean_ctor_get(v_t_1728_, 1);
lean_inc_ref(v_binderType_1762_);
v_body_1763_ = lean_ctor_get(v_t_1728_, 2);
lean_inc_ref(v_body_1763_);
v_binderInfo_1764_ = lean_ctor_get_uint8(v_t_1728_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1728_, 3);
v___x_1765_ = lean_box(v_binderInfo_1764_);
v___x_1766_ = lean_apply_4(v_forallE_1736_, v_binderName_1761_, v_binderType_1762_, v_body_1763_, v___x_1765_);
return v___x_1766_;
}
case 8:
{
lean_object* v_declName_1767_; lean_object* v_type_1768_; lean_object* v_value_1769_; lean_object* v_body_1770_; uint8_t v_nondep_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_dec(v_proj_1740_);
lean_dec(v_mdata_1739_);
lean_dec(v_lit_1738_);
lean_dec(v_forallE_1736_);
lean_dec(v_lam_1735_);
lean_dec(v_app_1734_);
lean_dec(v_const_1733_);
lean_dec(v_sort_1732_);
lean_dec(v_mvar_1731_);
lean_dec(v_fvar_1730_);
lean_dec(v_bvar_1729_);
v_declName_1767_ = lean_ctor_get(v_t_1728_, 0);
lean_inc(v_declName_1767_);
v_type_1768_ = lean_ctor_get(v_t_1728_, 1);
lean_inc_ref(v_type_1768_);
v_value_1769_ = lean_ctor_get(v_t_1728_, 2);
lean_inc_ref(v_value_1769_);
v_body_1770_ = lean_ctor_get(v_t_1728_, 3);
lean_inc_ref(v_body_1770_);
v_nondep_1771_ = lean_ctor_get_uint8(v_t_1728_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1728_, 4);
v___x_1772_ = lean_box(v_nondep_1771_);
v___x_1773_ = lean_apply_5(v_letE_1737_, v_declName_1767_, v_type_1768_, v_value_1769_, v_body_1770_, v___x_1772_);
return v___x_1773_;
}
case 9:
{
lean_object* v_a_1774_; lean_object* v___x_1775_; 
lean_dec(v_proj_1740_);
lean_dec(v_mdata_1739_);
lean_dec(v_letE_1737_);
lean_dec(v_forallE_1736_);
lean_dec(v_lam_1735_);
lean_dec(v_app_1734_);
lean_dec(v_const_1733_);
lean_dec(v_sort_1732_);
lean_dec(v_mvar_1731_);
lean_dec(v_fvar_1730_);
lean_dec(v_bvar_1729_);
v_a_1774_ = lean_ctor_get(v_t_1728_, 0);
lean_inc_ref(v_a_1774_);
lean_dec_ref_known(v_t_1728_, 1);
v___x_1775_ = lean_apply_1(v_lit_1738_, v_a_1774_);
return v___x_1775_;
}
case 10:
{
lean_object* v_data_1776_; lean_object* v_expr_1777_; lean_object* v___x_1778_; 
lean_dec(v_proj_1740_);
lean_dec(v_lit_1738_);
lean_dec(v_letE_1737_);
lean_dec(v_forallE_1736_);
lean_dec(v_lam_1735_);
lean_dec(v_app_1734_);
lean_dec(v_const_1733_);
lean_dec(v_sort_1732_);
lean_dec(v_mvar_1731_);
lean_dec(v_fvar_1730_);
lean_dec(v_bvar_1729_);
v_data_1776_ = lean_ctor_get(v_t_1728_, 0);
lean_inc(v_data_1776_);
v_expr_1777_ = lean_ctor_get(v_t_1728_, 1);
lean_inc_ref(v_expr_1777_);
lean_dec_ref_known(v_t_1728_, 2);
v___x_1778_ = lean_apply_2(v_mdata_1739_, v_data_1776_, v_expr_1777_);
return v___x_1778_;
}
default: 
{
lean_object* v_typeName_1779_; lean_object* v_idx_1780_; lean_object* v_struct_1781_; lean_object* v___x_1782_; 
lean_dec(v_mdata_1739_);
lean_dec(v_lit_1738_);
lean_dec(v_letE_1737_);
lean_dec(v_forallE_1736_);
lean_dec(v_lam_1735_);
lean_dec(v_app_1734_);
lean_dec(v_const_1733_);
lean_dec(v_sort_1732_);
lean_dec(v_mvar_1731_);
lean_dec(v_fvar_1730_);
lean_dec(v_bvar_1729_);
v_typeName_1779_ = lean_ctor_get(v_t_1728_, 0);
lean_inc(v_typeName_1779_);
v_idx_1780_ = lean_ctor_get(v_t_1728_, 1);
lean_inc(v_idx_1780_);
v_struct_1781_ = lean_ctor_get(v_t_1728_, 2);
lean_inc_ref(v_struct_1781_);
lean_dec_ref_known(v_t_1728_, 3);
v___x_1782_ = lean_apply_3(v_proj_1740_, v_typeName_1779_, v_idx_1780_, v_struct_1781_);
return v___x_1782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* v_deBruijnIndex_1783_){
_start:
{
uint64_t v___x_1784_; uint64_t v___x_1785_; uint64_t v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint32_t v___x_1789_; uint8_t v___x_1790_; uint64_t v___x_1791_; lean_object* v___x_1792_; 
v___x_1784_ = 7ULL;
v___x_1785_ = lean_uint64_of_nat(v_deBruijnIndex_1783_);
v___x_1786_ = lean_uint64_mix_hash(v___x_1784_, v___x_1785_);
v___x_1787_ = lean_unsigned_to_nat(1u);
v___x_1788_ = lean_nat_add(v_deBruijnIndex_1783_, v___x_1787_);
v___x_1789_ = 0;
v___x_1790_ = 0;
v___x_1791_ = lean_expr_mk_data(v___x_1786_, v___x_1788_, v___x_1789_, v___x_1790_, v___x_1790_, v___x_1790_, v___x_1790_);
v___x_1792_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1792_, 0, v_deBruijnIndex_1783_);
lean_ctor_set_uint64(v___x_1792_, sizeof(void*)*1, v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* v_fvarId_1793_){
_start:
{
uint64_t v___x_1794_; uint64_t v___x_1795_; uint64_t v___x_1796_; lean_object* v___x_1797_; uint32_t v___x_1798_; uint8_t v___x_1799_; uint8_t v___x_1800_; uint64_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1794_ = 13ULL;
v___x_1795_ = l_Lean_instHashableFVarId_hash(v_fvarId_1793_);
v___x_1796_ = lean_uint64_mix_hash(v___x_1794_, v___x_1795_);
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = 0;
v___x_1799_ = 1;
v___x_1800_ = 0;
v___x_1801_ = lean_expr_mk_data(v___x_1796_, v___x_1797_, v___x_1798_, v___x_1799_, v___x_1800_, v___x_1800_, v___x_1800_);
v___x_1802_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_1802_, 0, v_fvarId_1793_);
lean_ctor_set_uint64(v___x_1802_, sizeof(void*)*1, v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* v_mvarId_1803_){
_start:
{
uint64_t v___x_1804_; uint64_t v___x_1805_; uint64_t v___x_1806_; lean_object* v___x_1807_; uint32_t v___x_1808_; uint8_t v___x_1809_; uint8_t v___x_1810_; uint64_t v___x_1811_; lean_object* v___x_1812_; 
v___x_1804_ = 17ULL;
v___x_1805_ = l_Lean_instHashableMVarId_hash(v_mvarId_1803_);
v___x_1806_ = lean_uint64_mix_hash(v___x_1804_, v___x_1805_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = 0;
v___x_1809_ = 0;
v___x_1810_ = 1;
v___x_1811_ = lean_expr_mk_data(v___x_1806_, v___x_1807_, v___x_1808_, v___x_1809_, v___x_1810_, v___x_1809_, v___x_1809_);
v___x_1812_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_1812_, 0, v_mvarId_1803_);
lean_ctor_set_uint64(v___x_1812_, sizeof(void*)*1, v___x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* v_u_1813_){
_start:
{
uint64_t v___x_1814_; uint64_t v___x_1815_; uint64_t v___x_1816_; lean_object* v___x_1817_; uint32_t v___x_1818_; uint8_t v___x_1819_; uint8_t v___x_1820_; uint8_t v___x_1821_; uint64_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1814_ = 11ULL;
v___x_1815_ = l_Lean_Level_hash(v_u_1813_);
v___x_1816_ = lean_uint64_mix_hash(v___x_1814_, v___x_1815_);
v___x_1817_ = lean_unsigned_to_nat(0u);
v___x_1818_ = 0;
v___x_1819_ = 0;
v___x_1820_ = l_Lean_Level_hasMVar(v_u_1813_);
v___x_1821_ = l_Lean_Level_hasParam(v_u_1813_);
v___x_1822_ = lean_expr_mk_data(v___x_1816_, v___x_1817_, v___x_1818_, v___x_1819_, v___x_1819_, v___x_1820_, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(v___x_1823_, 0, v_u_1813_);
lean_ctor_set_uint64(v___x_1823_, sizeof(void*)*1, v___x_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* v_fn_1824_, lean_object* v_arg_1825_){
_start:
{
uint64_t v___x_1826_; uint64_t v___x_1827_; uint64_t v___x_1828_; lean_object* v___x_1829_; 
v___x_1826_ = lean_expr_data(v_fn_1824_);
v___x_1827_ = lean_expr_data(v_arg_1825_);
v___x_1828_ = lean_expr_mk_app_data(v___x_1826_, v___x_1827_);
v___x_1829_ = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(v___x_1829_, 0, v_fn_1824_);
lean_ctor_set(v___x_1829_, 1, v_arg_1825_);
lean_ctor_set_uint64(v___x_1829_, sizeof(void*)*2, v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object* v_binderName_1830_, lean_object* v_binderType_1831_, lean_object* v_body_1832_, uint8_t v_binderInfo_1833_){
_start:
{
uint32_t v___y_1835_; uint8_t v___y_1836_; lean_object* v___y_1837_; uint8_t v___y_1838_; uint8_t v___y_1839_; uint64_t v___y_1840_; uint8_t v___y_1841_; uint64_t v___x_1844_; uint8_t v___x_1845_; uint32_t v___x_1846_; uint64_t v___x_1847_; uint32_t v___y_1849_; uint8_t v___y_1850_; lean_object* v___y_1851_; uint8_t v___y_1852_; uint64_t v___y_1853_; uint8_t v___y_1854_; uint32_t v___y_1858_; uint8_t v___y_1859_; lean_object* v___y_1860_; uint64_t v___y_1861_; uint8_t v___y_1862_; uint32_t v___y_1866_; lean_object* v___y_1867_; uint64_t v___y_1868_; uint8_t v___y_1869_; uint32_t v___y_1873_; uint64_t v___y_1874_; lean_object* v___y_1875_; uint32_t v___y_1879_; uint8_t v___x_1894_; uint32_t v___x_1895_; uint8_t v___x_1896_; 
v___x_1844_ = lean_expr_data(v_binderType_1831_);
v___x_1845_ = l_Lean_Expr_Data_approxDepth(v___x_1844_);
v___x_1846_ = lean_uint8_to_uint32(v___x_1845_);
v___x_1847_ = lean_expr_data(v_body_1832_);
v___x_1894_ = l_Lean_Expr_Data_approxDepth(v___x_1847_);
v___x_1895_ = lean_uint8_to_uint32(v___x_1894_);
v___x_1896_ = lean_uint32_dec_le(v___x_1846_, v___x_1895_);
if (v___x_1896_ == 0)
{
v___y_1879_ = v___x_1846_;
goto v___jp_1878_;
}
else
{
v___y_1879_ = v___x_1895_;
goto v___jp_1878_;
}
v___jp_1834_:
{
uint64_t v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = lean_expr_mk_data(v___y_1840_, v___y_1837_, v___y_1835_, v___y_1836_, v___y_1839_, v___y_1838_, v___y_1841_);
v___x_1843_ = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(v___x_1843_, 0, v_binderName_1830_);
lean_ctor_set(v___x_1843_, 1, v_binderType_1831_);
lean_ctor_set(v___x_1843_, 2, v_body_1832_);
lean_ctor_set_uint64(v___x_1843_, sizeof(void*)*3, v___x_1842_);
lean_ctor_set_uint8(v___x_1843_, sizeof(void*)*3 + 8, v_binderInfo_1833_);
return v___x_1843_;
}
v___jp_1848_:
{
uint8_t v___x_1855_; 
v___x_1855_ = l_Lean_Expr_Data_hasLevelParam(v___x_1844_);
if (v___x_1855_ == 0)
{
uint8_t v___x_1856_; 
v___x_1856_ = l_Lean_Expr_Data_hasLevelParam(v___x_1847_);
v___y_1835_ = v___y_1849_;
v___y_1836_ = v___y_1850_;
v___y_1837_ = v___y_1851_;
v___y_1838_ = v___y_1854_;
v___y_1839_ = v___y_1852_;
v___y_1840_ = v___y_1853_;
v___y_1841_ = v___x_1856_;
goto v___jp_1834_;
}
else
{
v___y_1835_ = v___y_1849_;
v___y_1836_ = v___y_1850_;
v___y_1837_ = v___y_1851_;
v___y_1838_ = v___y_1854_;
v___y_1839_ = v___y_1852_;
v___y_1840_ = v___y_1853_;
v___y_1841_ = v___x_1855_;
goto v___jp_1834_;
}
}
v___jp_1857_:
{
uint8_t v___x_1863_; 
v___x_1863_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1844_);
if (v___x_1863_ == 0)
{
uint8_t v___x_1864_; 
v___x_1864_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1847_);
v___y_1849_ = v___y_1858_;
v___y_1850_ = v___y_1859_;
v___y_1851_ = v___y_1860_;
v___y_1852_ = v___y_1862_;
v___y_1853_ = v___y_1861_;
v___y_1854_ = v___x_1864_;
goto v___jp_1848_;
}
else
{
v___y_1849_ = v___y_1858_;
v___y_1850_ = v___y_1859_;
v___y_1851_ = v___y_1860_;
v___y_1852_ = v___y_1862_;
v___y_1853_ = v___y_1861_;
v___y_1854_ = v___x_1863_;
goto v___jp_1848_;
}
}
v___jp_1865_:
{
uint8_t v___x_1870_; 
v___x_1870_ = l_Lean_Expr_Data_hasExprMVar(v___x_1844_);
if (v___x_1870_ == 0)
{
uint8_t v___x_1871_; 
v___x_1871_ = l_Lean_Expr_Data_hasExprMVar(v___x_1847_);
v___y_1858_ = v___y_1866_;
v___y_1859_ = v___y_1869_;
v___y_1860_ = v___y_1867_;
v___y_1861_ = v___y_1868_;
v___y_1862_ = v___x_1871_;
goto v___jp_1857_;
}
else
{
v___y_1858_ = v___y_1866_;
v___y_1859_ = v___y_1869_;
v___y_1860_ = v___y_1867_;
v___y_1861_ = v___y_1868_;
v___y_1862_ = v___x_1870_;
goto v___jp_1857_;
}
}
v___jp_1872_:
{
uint8_t v___x_1876_; 
v___x_1876_ = l_Lean_Expr_Data_hasFVar(v___x_1844_);
if (v___x_1876_ == 0)
{
uint8_t v___x_1877_; 
v___x_1877_ = l_Lean_Expr_Data_hasFVar(v___x_1847_);
v___y_1866_ = v___y_1873_;
v___y_1867_ = v___y_1875_;
v___y_1868_ = v___y_1874_;
v___y_1869_ = v___x_1877_;
goto v___jp_1865_;
}
else
{
v___y_1866_ = v___y_1873_;
v___y_1867_ = v___y_1875_;
v___y_1868_ = v___y_1874_;
v___y_1869_ = v___x_1876_;
goto v___jp_1865_;
}
}
v___jp_1878_:
{
lean_object* v___x_1880_; uint32_t v___x_1881_; uint32_t v___x_1882_; uint64_t v___x_1883_; uint64_t v___x_1884_; uint64_t v___x_1885_; uint64_t v___x_1886_; uint64_t v___x_1887_; uint32_t v___x_1888_; lean_object* v___x_1889_; uint32_t v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1880_ = lean_unsigned_to_nat(1u);
v___x_1881_ = 1;
v___x_1882_ = lean_uint32_add(v___y_1879_, v___x_1881_);
v___x_1883_ = lean_uint32_to_uint64(v___x_1882_);
v___x_1884_ = l_Lean_Expr_Data_hash(v___x_1844_);
v___x_1885_ = l_Lean_Expr_Data_hash(v___x_1847_);
v___x_1886_ = lean_uint64_mix_hash(v___x_1884_, v___x_1885_);
v___x_1887_ = lean_uint64_mix_hash(v___x_1883_, v___x_1886_);
v___x_1888_ = l_Lean_Expr_Data_looseBVarRange(v___x_1844_);
v___x_1889_ = lean_uint32_to_nat(v___x_1888_);
v___x_1890_ = l_Lean_Expr_Data_looseBVarRange(v___x_1847_);
v___x_1891_ = lean_uint32_to_nat(v___x_1890_);
v___x_1892_ = lean_nat_sub(v___x_1891_, v___x_1880_);
lean_dec(v___x_1891_);
v___x_1893_ = lean_nat_dec_le(v___x_1889_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_dec(v___x_1892_);
v___y_1873_ = v___x_1882_;
v___y_1874_ = v___x_1887_;
v___y_1875_ = v___x_1889_;
goto v___jp_1872_;
}
else
{
lean_dec(v___x_1889_);
v___y_1873_ = v___x_1882_;
v___y_1874_ = v___x_1887_;
v___y_1875_ = v___x_1892_;
goto v___jp_1872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* v_binderName_1897_, lean_object* v_binderType_1898_, lean_object* v_body_1899_, lean_object* v_binderInfo_1900_){
_start:
{
uint8_t v_binderInfo_boxed_1901_; lean_object* v_res_1902_; 
v_binderInfo_boxed_1901_ = lean_unbox(v_binderInfo_1900_);
v_res_1902_ = l_Lean_Expr_lam___override(v_binderName_1897_, v_binderType_1898_, v_body_1899_, v_binderInfo_boxed_1901_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object* v_binderName_1903_, lean_object* v_binderType_1904_, lean_object* v_body_1905_, uint8_t v_binderInfo_1906_){
_start:
{
uint8_t v___y_1908_; lean_object* v___y_1909_; uint32_t v___y_1910_; uint8_t v___y_1911_; uint64_t v___y_1912_; uint8_t v___y_1913_; uint8_t v___y_1914_; uint64_t v___x_1917_; uint8_t v___x_1918_; uint32_t v___x_1919_; uint64_t v___x_1920_; uint8_t v___y_1922_; lean_object* v___y_1923_; uint32_t v___y_1924_; uint64_t v___y_1925_; uint8_t v___y_1926_; uint8_t v___y_1927_; uint8_t v___y_1931_; lean_object* v___y_1932_; uint32_t v___y_1933_; uint64_t v___y_1934_; uint8_t v___y_1935_; lean_object* v___y_1939_; uint32_t v___y_1940_; uint64_t v___y_1941_; uint8_t v___y_1942_; uint32_t v___y_1946_; uint64_t v___y_1947_; lean_object* v___y_1948_; uint32_t v___y_1952_; uint8_t v___x_1967_; uint32_t v___x_1968_; uint8_t v___x_1969_; 
v___x_1917_ = lean_expr_data(v_binderType_1904_);
v___x_1918_ = l_Lean_Expr_Data_approxDepth(v___x_1917_);
v___x_1919_ = lean_uint8_to_uint32(v___x_1918_);
v___x_1920_ = lean_expr_data(v_body_1905_);
v___x_1967_ = l_Lean_Expr_Data_approxDepth(v___x_1920_);
v___x_1968_ = lean_uint8_to_uint32(v___x_1967_);
v___x_1969_ = lean_uint32_dec_le(v___x_1919_, v___x_1968_);
if (v___x_1969_ == 0)
{
v___y_1952_ = v___x_1919_;
goto v___jp_1951_;
}
else
{
v___y_1952_ = v___x_1968_;
goto v___jp_1951_;
}
v___jp_1907_:
{
uint64_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_expr_mk_data(v___y_1912_, v___y_1909_, v___y_1910_, v___y_1908_, v___y_1913_, v___y_1911_, v___y_1914_);
v___x_1916_ = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(v___x_1916_, 0, v_binderName_1903_);
lean_ctor_set(v___x_1916_, 1, v_binderType_1904_);
lean_ctor_set(v___x_1916_, 2, v_body_1905_);
lean_ctor_set_uint64(v___x_1916_, sizeof(void*)*3, v___x_1915_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*3 + 8, v_binderInfo_1906_);
return v___x_1916_;
}
v___jp_1921_:
{
uint8_t v___x_1928_; 
v___x_1928_ = l_Lean_Expr_Data_hasLevelParam(v___x_1917_);
if (v___x_1928_ == 0)
{
uint8_t v___x_1929_; 
v___x_1929_ = l_Lean_Expr_Data_hasLevelParam(v___x_1920_);
v___y_1908_ = v___y_1922_;
v___y_1909_ = v___y_1923_;
v___y_1910_ = v___y_1924_;
v___y_1911_ = v___y_1927_;
v___y_1912_ = v___y_1925_;
v___y_1913_ = v___y_1926_;
v___y_1914_ = v___x_1929_;
goto v___jp_1907_;
}
else
{
v___y_1908_ = v___y_1922_;
v___y_1909_ = v___y_1923_;
v___y_1910_ = v___y_1924_;
v___y_1911_ = v___y_1927_;
v___y_1912_ = v___y_1925_;
v___y_1913_ = v___y_1926_;
v___y_1914_ = v___x_1928_;
goto v___jp_1907_;
}
}
v___jp_1930_:
{
uint8_t v___x_1936_; 
v___x_1936_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1917_);
if (v___x_1936_ == 0)
{
uint8_t v___x_1937_; 
v___x_1937_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1920_);
v___y_1922_ = v___y_1931_;
v___y_1923_ = v___y_1932_;
v___y_1924_ = v___y_1933_;
v___y_1925_ = v___y_1934_;
v___y_1926_ = v___y_1935_;
v___y_1927_ = v___x_1937_;
goto v___jp_1921_;
}
else
{
v___y_1922_ = v___y_1931_;
v___y_1923_ = v___y_1932_;
v___y_1924_ = v___y_1933_;
v___y_1925_ = v___y_1934_;
v___y_1926_ = v___y_1935_;
v___y_1927_ = v___x_1936_;
goto v___jp_1921_;
}
}
v___jp_1938_:
{
uint8_t v___x_1943_; 
v___x_1943_ = l_Lean_Expr_Data_hasExprMVar(v___x_1917_);
if (v___x_1943_ == 0)
{
uint8_t v___x_1944_; 
v___x_1944_ = l_Lean_Expr_Data_hasExprMVar(v___x_1920_);
v___y_1931_ = v___y_1942_;
v___y_1932_ = v___y_1939_;
v___y_1933_ = v___y_1940_;
v___y_1934_ = v___y_1941_;
v___y_1935_ = v___x_1944_;
goto v___jp_1930_;
}
else
{
v___y_1931_ = v___y_1942_;
v___y_1932_ = v___y_1939_;
v___y_1933_ = v___y_1940_;
v___y_1934_ = v___y_1941_;
v___y_1935_ = v___x_1943_;
goto v___jp_1930_;
}
}
v___jp_1945_:
{
uint8_t v___x_1949_; 
v___x_1949_ = l_Lean_Expr_Data_hasFVar(v___x_1917_);
if (v___x_1949_ == 0)
{
uint8_t v___x_1950_; 
v___x_1950_ = l_Lean_Expr_Data_hasFVar(v___x_1920_);
v___y_1939_ = v___y_1948_;
v___y_1940_ = v___y_1946_;
v___y_1941_ = v___y_1947_;
v___y_1942_ = v___x_1950_;
goto v___jp_1938_;
}
else
{
v___y_1939_ = v___y_1948_;
v___y_1940_ = v___y_1946_;
v___y_1941_ = v___y_1947_;
v___y_1942_ = v___x_1949_;
goto v___jp_1938_;
}
}
v___jp_1951_:
{
lean_object* v___x_1953_; uint32_t v___x_1954_; uint32_t v___x_1955_; uint64_t v___x_1956_; uint64_t v___x_1957_; uint64_t v___x_1958_; uint64_t v___x_1959_; uint64_t v___x_1960_; uint32_t v___x_1961_; lean_object* v___x_1962_; uint32_t v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1953_ = lean_unsigned_to_nat(1u);
v___x_1954_ = 1;
v___x_1955_ = lean_uint32_add(v___y_1952_, v___x_1954_);
v___x_1956_ = lean_uint32_to_uint64(v___x_1955_);
v___x_1957_ = l_Lean_Expr_Data_hash(v___x_1917_);
v___x_1958_ = l_Lean_Expr_Data_hash(v___x_1920_);
v___x_1959_ = lean_uint64_mix_hash(v___x_1957_, v___x_1958_);
v___x_1960_ = lean_uint64_mix_hash(v___x_1956_, v___x_1959_);
v___x_1961_ = l_Lean_Expr_Data_looseBVarRange(v___x_1917_);
v___x_1962_ = lean_uint32_to_nat(v___x_1961_);
v___x_1963_ = l_Lean_Expr_Data_looseBVarRange(v___x_1920_);
v___x_1964_ = lean_uint32_to_nat(v___x_1963_);
v___x_1965_ = lean_nat_sub(v___x_1964_, v___x_1953_);
lean_dec(v___x_1964_);
v___x_1966_ = lean_nat_dec_le(v___x_1962_, v___x_1965_);
if (v___x_1966_ == 0)
{
lean_dec(v___x_1965_);
v___y_1946_ = v___x_1955_;
v___y_1947_ = v___x_1960_;
v___y_1948_ = v___x_1962_;
goto v___jp_1945_;
}
else
{
lean_dec(v___x_1962_);
v___y_1946_ = v___x_1955_;
v___y_1947_ = v___x_1960_;
v___y_1948_ = v___x_1965_;
goto v___jp_1945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* v_binderName_1970_, lean_object* v_binderType_1971_, lean_object* v_body_1972_, lean_object* v_binderInfo_1973_){
_start:
{
uint8_t v_binderInfo_boxed_1974_; lean_object* v_res_1975_; 
v_binderInfo_boxed_1974_ = lean_unbox(v_binderInfo_1973_);
v_res_1975_ = l_Lean_Expr_forallE___override(v_binderName_1970_, v_binderType_1971_, v_body_1972_, v_binderInfo_boxed_1974_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object* v_declName_1976_, lean_object* v_type_1977_, lean_object* v_value_1978_, lean_object* v_body_1979_, uint8_t v_nondep_1980_){
_start:
{
uint8_t v___y_1982_; uint8_t v___y_1983_; uint8_t v___y_1984_; uint32_t v___y_1985_; uint64_t v___y_1986_; lean_object* v___y_1987_; uint8_t v___y_1988_; uint64_t v___y_1992_; uint8_t v___y_1993_; uint8_t v___y_1994_; uint8_t v___y_1995_; uint32_t v___y_1996_; uint64_t v___y_1997_; lean_object* v___y_1998_; uint8_t v___y_1999_; uint64_t v___x_2001_; uint8_t v___x_2002_; uint32_t v___x_2003_; uint64_t v___x_2004_; uint64_t v___y_2006_; uint8_t v___y_2007_; uint8_t v___y_2008_; uint32_t v___y_2009_; uint64_t v___y_2010_; lean_object* v___y_2011_; uint8_t v___y_2012_; uint64_t v___y_2016_; uint8_t v___y_2017_; uint8_t v___y_2018_; uint32_t v___y_2019_; uint64_t v___y_2020_; lean_object* v___y_2021_; uint8_t v___y_2022_; uint64_t v___y_2025_; uint8_t v___y_2026_; uint32_t v___y_2027_; uint64_t v___y_2028_; lean_object* v___y_2029_; uint8_t v___y_2030_; uint64_t v___y_2034_; uint8_t v___y_2035_; uint32_t v___y_2036_; uint64_t v___y_2037_; lean_object* v___y_2038_; uint8_t v___y_2039_; uint64_t v___y_2042_; uint32_t v___y_2043_; uint64_t v___y_2044_; lean_object* v___y_2045_; uint8_t v___y_2046_; uint64_t v___y_2050_; uint32_t v___y_2051_; uint64_t v___y_2052_; lean_object* v___y_2053_; uint8_t v___y_2054_; uint64_t v___y_2057_; uint32_t v___y_2058_; uint64_t v___y_2059_; lean_object* v___y_2060_; uint64_t v___y_2064_; lean_object* v___y_2065_; uint32_t v___y_2066_; uint64_t v___y_2067_; lean_object* v___y_2068_; uint64_t v___y_2074_; uint32_t v___y_2075_; uint32_t v___y_2092_; uint8_t v___x_2097_; uint32_t v___x_2098_; uint8_t v___x_2099_; 
v___x_2001_ = lean_expr_data(v_type_1977_);
v___x_2002_ = l_Lean_Expr_Data_approxDepth(v___x_2001_);
v___x_2003_ = lean_uint8_to_uint32(v___x_2002_);
v___x_2004_ = lean_expr_data(v_value_1978_);
v___x_2097_ = l_Lean_Expr_Data_approxDepth(v___x_2004_);
v___x_2098_ = lean_uint8_to_uint32(v___x_2097_);
v___x_2099_ = lean_uint32_dec_le(v___x_2003_, v___x_2098_);
if (v___x_2099_ == 0)
{
v___y_2092_ = v___x_2003_;
goto v___jp_2091_;
}
else
{
v___y_2092_ = v___x_2098_;
goto v___jp_2091_;
}
v___jp_1981_:
{
uint64_t v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_expr_mk_data(v___y_1986_, v___y_1987_, v___y_1985_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1988_);
v___x_1990_ = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(v___x_1990_, 0, v_declName_1976_);
lean_ctor_set(v___x_1990_, 1, v_type_1977_);
lean_ctor_set(v___x_1990_, 2, v_value_1978_);
lean_ctor_set(v___x_1990_, 3, v_body_1979_);
lean_ctor_set_uint64(v___x_1990_, sizeof(void*)*4, v___x_1989_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*4 + 8, v_nondep_1980_);
return v___x_1990_;
}
v___jp_1991_:
{
if (v___y_1999_ == 0)
{
uint8_t v___x_2000_; 
v___x_2000_ = l_Lean_Expr_Data_hasLevelParam(v___y_1992_);
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v___y_1985_ = v___y_1996_;
v___y_1986_ = v___y_1997_;
v___y_1987_ = v___y_1998_;
v___y_1988_ = v___x_2000_;
goto v___jp_1981_;
}
else
{
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v___y_1985_ = v___y_1996_;
v___y_1986_ = v___y_1997_;
v___y_1987_ = v___y_1998_;
v___y_1988_ = v___y_1999_;
goto v___jp_1981_;
}
}
v___jp_2005_:
{
uint8_t v___x_2013_; 
v___x_2013_ = l_Lean_Expr_Data_hasLevelParam(v___x_2001_);
if (v___x_2013_ == 0)
{
uint8_t v___x_2014_; 
v___x_2014_ = l_Lean_Expr_Data_hasLevelParam(v___x_2004_);
v___y_1992_ = v___y_2006_;
v___y_1993_ = v___y_2007_;
v___y_1994_ = v___y_2008_;
v___y_1995_ = v___y_2012_;
v___y_1996_ = v___y_2009_;
v___y_1997_ = v___y_2010_;
v___y_1998_ = v___y_2011_;
v___y_1999_ = v___x_2014_;
goto v___jp_1991_;
}
else
{
v___y_1992_ = v___y_2006_;
v___y_1993_ = v___y_2007_;
v___y_1994_ = v___y_2008_;
v___y_1995_ = v___y_2012_;
v___y_1996_ = v___y_2009_;
v___y_1997_ = v___y_2010_;
v___y_1998_ = v___y_2011_;
v___y_1999_ = v___x_2013_;
goto v___jp_1991_;
}
}
v___jp_2015_:
{
if (v___y_2022_ == 0)
{
uint8_t v___x_2023_; 
v___x_2023_ = l_Lean_Expr_Data_hasLevelMVar(v___y_2016_);
v___y_2006_ = v___y_2016_;
v___y_2007_ = v___y_2017_;
v___y_2008_ = v___y_2018_;
v___y_2009_ = v___y_2019_;
v___y_2010_ = v___y_2020_;
v___y_2011_ = v___y_2021_;
v___y_2012_ = v___x_2023_;
goto v___jp_2005_;
}
else
{
v___y_2006_ = v___y_2016_;
v___y_2007_ = v___y_2017_;
v___y_2008_ = v___y_2018_;
v___y_2009_ = v___y_2019_;
v___y_2010_ = v___y_2020_;
v___y_2011_ = v___y_2021_;
v___y_2012_ = v___y_2022_;
goto v___jp_2005_;
}
}
v___jp_2024_:
{
uint8_t v___x_2031_; 
v___x_2031_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2001_);
if (v___x_2031_ == 0)
{
uint8_t v___x_2032_; 
v___x_2032_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2004_);
v___y_2016_ = v___y_2025_;
v___y_2017_ = v___y_2026_;
v___y_2018_ = v___y_2030_;
v___y_2019_ = v___y_2027_;
v___y_2020_ = v___y_2028_;
v___y_2021_ = v___y_2029_;
v___y_2022_ = v___x_2032_;
goto v___jp_2015_;
}
else
{
v___y_2016_ = v___y_2025_;
v___y_2017_ = v___y_2026_;
v___y_2018_ = v___y_2030_;
v___y_2019_ = v___y_2027_;
v___y_2020_ = v___y_2028_;
v___y_2021_ = v___y_2029_;
v___y_2022_ = v___x_2031_;
goto v___jp_2015_;
}
}
v___jp_2033_:
{
if (v___y_2039_ == 0)
{
uint8_t v___x_2040_; 
v___x_2040_ = l_Lean_Expr_Data_hasExprMVar(v___y_2034_);
v___y_2025_ = v___y_2034_;
v___y_2026_ = v___y_2035_;
v___y_2027_ = v___y_2036_;
v___y_2028_ = v___y_2037_;
v___y_2029_ = v___y_2038_;
v___y_2030_ = v___x_2040_;
goto v___jp_2024_;
}
else
{
v___y_2025_ = v___y_2034_;
v___y_2026_ = v___y_2035_;
v___y_2027_ = v___y_2036_;
v___y_2028_ = v___y_2037_;
v___y_2029_ = v___y_2038_;
v___y_2030_ = v___y_2039_;
goto v___jp_2024_;
}
}
v___jp_2041_:
{
uint8_t v___x_2047_; 
v___x_2047_ = l_Lean_Expr_Data_hasExprMVar(v___x_2001_);
if (v___x_2047_ == 0)
{
uint8_t v___x_2048_; 
v___x_2048_ = l_Lean_Expr_Data_hasExprMVar(v___x_2004_);
v___y_2034_ = v___y_2042_;
v___y_2035_ = v___y_2046_;
v___y_2036_ = v___y_2043_;
v___y_2037_ = v___y_2044_;
v___y_2038_ = v___y_2045_;
v___y_2039_ = v___x_2048_;
goto v___jp_2033_;
}
else
{
v___y_2034_ = v___y_2042_;
v___y_2035_ = v___y_2046_;
v___y_2036_ = v___y_2043_;
v___y_2037_ = v___y_2044_;
v___y_2038_ = v___y_2045_;
v___y_2039_ = v___x_2047_;
goto v___jp_2033_;
}
}
v___jp_2049_:
{
if (v___y_2054_ == 0)
{
uint8_t v___x_2055_; 
v___x_2055_ = l_Lean_Expr_Data_hasFVar(v___y_2050_);
v___y_2042_ = v___y_2050_;
v___y_2043_ = v___y_2051_;
v___y_2044_ = v___y_2052_;
v___y_2045_ = v___y_2053_;
v___y_2046_ = v___x_2055_;
goto v___jp_2041_;
}
else
{
v___y_2042_ = v___y_2050_;
v___y_2043_ = v___y_2051_;
v___y_2044_ = v___y_2052_;
v___y_2045_ = v___y_2053_;
v___y_2046_ = v___y_2054_;
goto v___jp_2041_;
}
}
v___jp_2056_:
{
uint8_t v___x_2061_; 
v___x_2061_ = l_Lean_Expr_Data_hasFVar(v___x_2001_);
if (v___x_2061_ == 0)
{
uint8_t v___x_2062_; 
v___x_2062_ = l_Lean_Expr_Data_hasFVar(v___x_2004_);
v___y_2050_ = v___y_2057_;
v___y_2051_ = v___y_2058_;
v___y_2052_ = v___y_2059_;
v___y_2053_ = v___y_2060_;
v___y_2054_ = v___x_2062_;
goto v___jp_2049_;
}
else
{
v___y_2050_ = v___y_2057_;
v___y_2051_ = v___y_2058_;
v___y_2052_ = v___y_2059_;
v___y_2053_ = v___y_2060_;
v___y_2054_ = v___x_2061_;
goto v___jp_2049_;
}
}
v___jp_2063_:
{
uint32_t v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2069_ = l_Lean_Expr_Data_looseBVarRange(v___y_2064_);
v___x_2070_ = lean_uint32_to_nat(v___x_2069_);
v___x_2071_ = lean_nat_sub(v___x_2070_, v___y_2065_);
lean_dec(v___x_2070_);
v___x_2072_ = lean_nat_dec_le(v___y_2068_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_dec(v___x_2071_);
v___y_2057_ = v___y_2064_;
v___y_2058_ = v___y_2066_;
v___y_2059_ = v___y_2067_;
v___y_2060_ = v___y_2068_;
goto v___jp_2056_;
}
else
{
lean_dec(v___y_2068_);
v___y_2057_ = v___y_2064_;
v___y_2058_ = v___y_2066_;
v___y_2059_ = v___y_2067_;
v___y_2060_ = v___x_2071_;
goto v___jp_2056_;
}
}
v___jp_2073_:
{
lean_object* v___x_2076_; uint32_t v___x_2077_; uint32_t v___x_2078_; uint64_t v___x_2079_; uint64_t v___x_2080_; uint64_t v___x_2081_; uint64_t v___x_2082_; uint64_t v___x_2083_; uint64_t v___x_2084_; uint64_t v___x_2085_; uint32_t v___x_2086_; lean_object* v___x_2087_; uint32_t v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2076_ = lean_unsigned_to_nat(1u);
v___x_2077_ = 1;
v___x_2078_ = lean_uint32_add(v___y_2075_, v___x_2077_);
v___x_2079_ = lean_uint32_to_uint64(v___x_2078_);
v___x_2080_ = l_Lean_Expr_Data_hash(v___x_2001_);
v___x_2081_ = l_Lean_Expr_Data_hash(v___x_2004_);
v___x_2082_ = l_Lean_Expr_Data_hash(v___y_2074_);
v___x_2083_ = lean_uint64_mix_hash(v___x_2081_, v___x_2082_);
v___x_2084_ = lean_uint64_mix_hash(v___x_2080_, v___x_2083_);
v___x_2085_ = lean_uint64_mix_hash(v___x_2079_, v___x_2084_);
v___x_2086_ = l_Lean_Expr_Data_looseBVarRange(v___x_2001_);
v___x_2087_ = lean_uint32_to_nat(v___x_2086_);
v___x_2088_ = l_Lean_Expr_Data_looseBVarRange(v___x_2004_);
v___x_2089_ = lean_uint32_to_nat(v___x_2088_);
v___x_2090_ = lean_nat_dec_le(v___x_2087_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_dec(v___x_2089_);
v___y_2064_ = v___y_2074_;
v___y_2065_ = v___x_2076_;
v___y_2066_ = v___x_2078_;
v___y_2067_ = v___x_2085_;
v___y_2068_ = v___x_2087_;
goto v___jp_2063_;
}
else
{
lean_dec(v___x_2087_);
v___y_2064_ = v___y_2074_;
v___y_2065_ = v___x_2076_;
v___y_2066_ = v___x_2078_;
v___y_2067_ = v___x_2085_;
v___y_2068_ = v___x_2089_;
goto v___jp_2063_;
}
}
v___jp_2091_:
{
uint64_t v___x_2093_; uint8_t v___x_2094_; uint32_t v___x_2095_; uint8_t v___x_2096_; 
v___x_2093_ = lean_expr_data(v_body_1979_);
v___x_2094_ = l_Lean_Expr_Data_approxDepth(v___x_2093_);
v___x_2095_ = lean_uint8_to_uint32(v___x_2094_);
v___x_2096_ = lean_uint32_dec_le(v___y_2092_, v___x_2095_);
if (v___x_2096_ == 0)
{
v___y_2074_ = v___x_2093_;
v___y_2075_ = v___y_2092_;
goto v___jp_2073_;
}
else
{
v___y_2074_ = v___x_2093_;
v___y_2075_ = v___x_2095_;
goto v___jp_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* v_declName_2100_, lean_object* v_type_2101_, lean_object* v_value_2102_, lean_object* v_body_2103_, lean_object* v_nondep_2104_){
_start:
{
uint8_t v_nondep_boxed_2105_; lean_object* v_res_2106_; 
v_nondep_boxed_2105_ = lean_unbox(v_nondep_2104_);
v_res_2106_ = l_Lean_Expr_letE___override(v_declName_2100_, v_type_2101_, v_value_2102_, v_body_2103_, v_nondep_boxed_2105_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* v_a_2107_){
_start:
{
uint64_t v___x_2108_; uint64_t v___x_2109_; uint64_t v___x_2110_; lean_object* v___x_2111_; uint32_t v___x_2112_; uint8_t v___x_2113_; uint64_t v___x_2114_; lean_object* v___x_2115_; 
v___x_2108_ = 3ULL;
v___x_2109_ = l_Lean_Literal_hash(v_a_2107_);
v___x_2110_ = lean_uint64_mix_hash(v___x_2108_, v___x_2109_);
v___x_2111_ = lean_unsigned_to_nat(0u);
v___x_2112_ = 0;
v___x_2113_ = 0;
v___x_2114_ = lean_expr_mk_data(v___x_2110_, v___x_2111_, v___x_2112_, v___x_2113_, v___x_2113_, v___x_2113_, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(v___x_2115_, 0, v_a_2107_);
lean_ctor_set_uint64(v___x_2115_, sizeof(void*)*1, v___x_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* v_data_2116_, lean_object* v_expr_2117_){
_start:
{
uint64_t v___x_2118_; uint8_t v___x_2119_; uint32_t v___x_2120_; uint32_t v___x_2121_; uint32_t v___x_2122_; uint64_t v___x_2123_; uint64_t v___x_2124_; uint64_t v___x_2125_; uint32_t v___x_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; uint8_t v___x_2129_; uint8_t v___x_2130_; uint8_t v___x_2131_; uint64_t v___x_2132_; lean_object* v___x_2133_; 
v___x_2118_ = lean_expr_data(v_expr_2117_);
v___x_2119_ = l_Lean_Expr_Data_approxDepth(v___x_2118_);
v___x_2120_ = lean_uint8_to_uint32(v___x_2119_);
v___x_2121_ = 1;
v___x_2122_ = lean_uint32_add(v___x_2120_, v___x_2121_);
v___x_2123_ = lean_uint32_to_uint64(v___x_2122_);
v___x_2124_ = l_Lean_Expr_Data_hash(v___x_2118_);
v___x_2125_ = lean_uint64_mix_hash(v___x_2123_, v___x_2124_);
v___x_2126_ = l_Lean_Expr_Data_looseBVarRange(v___x_2118_);
v___x_2127_ = lean_uint32_to_nat(v___x_2126_);
v___x_2128_ = l_Lean_Expr_Data_hasFVar(v___x_2118_);
v___x_2129_ = l_Lean_Expr_Data_hasExprMVar(v___x_2118_);
v___x_2130_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2118_);
v___x_2131_ = l_Lean_Expr_Data_hasLevelParam(v___x_2118_);
v___x_2132_ = lean_expr_mk_data(v___x_2125_, v___x_2127_, v___x_2122_, v___x_2128_, v___x_2129_, v___x_2130_, v___x_2131_);
v___x_2133_ = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(v___x_2133_, 0, v_data_2116_);
lean_ctor_set(v___x_2133_, 1, v_expr_2117_);
lean_ctor_set_uint64(v___x_2133_, sizeof(void*)*2, v___x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* v_typeName_2134_, lean_object* v_idx_2135_, lean_object* v_struct_2136_){
_start:
{
uint64_t v___x_2137_; uint8_t v___x_2138_; uint32_t v___x_2139_; uint32_t v___x_2140_; uint32_t v___x_2141_; uint64_t v___x_2142_; uint64_t v___y_2144_; 
v___x_2137_ = lean_expr_data(v_struct_2136_);
v___x_2138_ = l_Lean_Expr_Data_approxDepth(v___x_2137_);
v___x_2139_ = lean_uint8_to_uint32(v___x_2138_);
v___x_2140_ = 1;
v___x_2141_ = lean_uint32_add(v___x_2139_, v___x_2140_);
v___x_2142_ = lean_uint32_to_uint64(v___x_2141_);
if (lean_obj_tag(v_typeName_2134_) == 0)
{
uint64_t v___x_2158_; 
v___x_2158_ = 1723ULL;
v___y_2144_ = v___x_2158_;
goto v___jp_2143_;
}
else
{
uint64_t v_hash_2159_; 
v_hash_2159_ = lean_ctor_get_uint64(v_typeName_2134_, sizeof(void*)*2);
v___y_2144_ = v_hash_2159_;
goto v___jp_2143_;
}
v___jp_2143_:
{
uint64_t v___x_2145_; uint64_t v___x_2146_; uint64_t v___x_2147_; uint64_t v___x_2148_; uint64_t v___x_2149_; uint32_t v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; uint8_t v___x_2153_; uint8_t v___x_2154_; uint8_t v___x_2155_; uint64_t v___x_2156_; lean_object* v___x_2157_; 
v___x_2145_ = lean_uint64_of_nat(v_idx_2135_);
v___x_2146_ = l_Lean_Expr_Data_hash(v___x_2137_);
v___x_2147_ = lean_uint64_mix_hash(v___x_2145_, v___x_2146_);
v___x_2148_ = lean_uint64_mix_hash(v___y_2144_, v___x_2147_);
v___x_2149_ = lean_uint64_mix_hash(v___x_2142_, v___x_2148_);
v___x_2150_ = l_Lean_Expr_Data_looseBVarRange(v___x_2137_);
v___x_2151_ = lean_uint32_to_nat(v___x_2150_);
v___x_2152_ = l_Lean_Expr_Data_hasFVar(v___x_2137_);
v___x_2153_ = l_Lean_Expr_Data_hasExprMVar(v___x_2137_);
v___x_2154_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2137_);
v___x_2155_ = l_Lean_Expr_Data_hasLevelParam(v___x_2137_);
v___x_2156_ = lean_expr_mk_data(v___x_2149_, v___x_2151_, v___x_2141_, v___x_2152_, v___x_2153_, v___x_2154_, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(v___x_2157_, 0, v_typeName_2134_);
lean_ctor_set(v___x_2157_, 1, v_idx_2135_);
lean_ctor_set(v___x_2157_, 2, v_struct_2136_);
lean_ctor_set_uint64(v___x_2157_, sizeof(void*)*3, v___x_2156_);
return v___x_2157_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__5(lean_object* v_x_2160_){
_start:
{
if (lean_obj_tag(v_x_2160_) == 0)
{
uint8_t v___x_2161_; 
v___x_2161_ = 0;
return v___x_2161_;
}
else
{
lean_object* v_head_2162_; lean_object* v_tail_2163_; uint8_t v___x_2164_; 
v_head_2162_ = lean_ctor_get(v_x_2160_, 0);
v_tail_2163_ = lean_ctor_get(v_x_2160_, 1);
v___x_2164_ = l_Lean_Level_hasMVar(v_head_2162_);
if (v___x_2164_ == 0)
{
v_x_2160_ = v_tail_2163_;
goto _start;
}
else
{
return v___x_2164_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__5___boxed(lean_object* v_x_2166_){
_start:
{
uint8_t v_res_2167_; lean_object* v_r_2168_; 
v_res_2167_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_x_2166_);
lean_dec(v_x_2166_);
v_r_2168_ = lean_box(v_res_2167_);
return v_r_2168_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__6(lean_object* v_x_2169_){
_start:
{
if (lean_obj_tag(v_x_2169_) == 0)
{
uint8_t v___x_2170_; 
v___x_2170_ = 0;
return v___x_2170_;
}
else
{
lean_object* v_head_2171_; lean_object* v_tail_2172_; uint8_t v___x_2173_; 
v_head_2171_ = lean_ctor_get(v_x_2169_, 0);
v_tail_2172_ = lean_ctor_get(v_x_2169_, 1);
v___x_2173_ = l_Lean_Level_hasParam(v_head_2171_);
if (v___x_2173_ == 0)
{
v_x_2169_ = v_tail_2172_;
goto _start;
}
else
{
return v___x_2173_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__6___boxed(lean_object* v_x_2175_){
_start:
{
uint8_t v_res_2176_; lean_object* v_r_2177_; 
v_res_2176_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_x_2175_);
lean_dec(v_x_2175_);
v_r_2177_ = lean_box(v_res_2176_);
return v_r_2177_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t v_x_2178_, lean_object* v_x_2179_){
_start:
{
if (lean_obj_tag(v_x_2179_) == 0)
{
return v_x_2178_;
}
else
{
lean_object* v_head_2180_; lean_object* v_tail_2181_; uint64_t v___x_2182_; uint64_t v___x_2183_; 
v_head_2180_ = lean_ctor_get(v_x_2179_, 0);
v_tail_2181_ = lean_ctor_get(v_x_2179_, 1);
v___x_2182_ = l_Lean_Level_hash(v_head_2180_);
v___x_2183_ = lean_uint64_mix_hash(v_x_2178_, v___x_2182_);
v_x_2178_ = v___x_2183_;
v_x_2179_ = v_tail_2181_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object* v_x_2185_, lean_object* v_x_2186_){
_start:
{
uint64_t v_x_1715__boxed_2187_; uint64_t v_res_2188_; lean_object* v_r_2189_; 
v_x_1715__boxed_2187_ = lean_unbox_uint64(v_x_2185_);
lean_dec_ref(v_x_2185_);
v_res_2188_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_1715__boxed_2187_, v_x_2186_);
lean_dec(v_x_2186_);
v_r_2189_ = lean_box_uint64(v_res_2188_);
return v_r_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* v_declName_2190_, lean_object* v_us_2191_){
_start:
{
uint64_t v___x_2192_; uint64_t v___y_2194_; 
v___x_2192_ = 5ULL;
if (lean_obj_tag(v_declName_2190_) == 0)
{
uint64_t v___x_2206_; 
v___x_2206_ = 1723ULL;
v___y_2194_ = v___x_2206_;
goto v___jp_2193_;
}
else
{
uint64_t v_hash_2207_; 
v_hash_2207_ = lean_ctor_get_uint64(v_declName_2190_, sizeof(void*)*2);
v___y_2194_ = v_hash_2207_;
goto v___jp_2193_;
}
v___jp_2193_:
{
uint64_t v___x_2195_; uint64_t v___x_2196_; uint64_t v___x_2197_; uint64_t v___x_2198_; lean_object* v___x_2199_; uint32_t v___x_2200_; uint8_t v___x_2201_; uint8_t v___x_2202_; uint8_t v___x_2203_; uint64_t v___x_2204_; lean_object* v___x_2205_; 
v___x_2195_ = 7ULL;
v___x_2196_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v___x_2195_, v_us_2191_);
v___x_2197_ = lean_uint64_mix_hash(v___y_2194_, v___x_2196_);
v___x_2198_ = lean_uint64_mix_hash(v___x_2192_, v___x_2197_);
v___x_2199_ = lean_unsigned_to_nat(0u);
v___x_2200_ = 0;
v___x_2201_ = 0;
v___x_2202_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_us_2191_);
v___x_2203_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_us_2191_);
v___x_2204_ = lean_expr_mk_data(v___x_2198_, v___x_2199_, v___x_2200_, v___x_2201_, v___x_2201_, v___x_2202_, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(v___x_2205_, 0, v_declName_2190_);
lean_ctor_set(v___x_2205_, 1, v_us_2191_);
lean_ctor_set_uint64(v___x_2205_, sizeof(void*)*2, v___x_2204_);
return v___x_2205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object* v___y_2208_){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = lean_unsigned_to_nat(0u);
v___x_2210_ = l_Lean_instReprLevel_repr(v___y_2208_, v___x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2211_, lean_object* v_x_2212_, lean_object* v_x_2213_){
_start:
{
if (lean_obj_tag(v_x_2213_) == 0)
{
lean_dec(v_x_2211_);
return v_x_2212_;
}
else
{
lean_object* v_head_2214_; lean_object* v_tail_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2226_; 
v_head_2214_ = lean_ctor_get(v_x_2213_, 0);
v_tail_2215_ = lean_ctor_get(v_x_2213_, 1);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_x_2213_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2217_ = v_x_2213_;
v_isShared_2218_ = v_isSharedCheck_2226_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_tail_2215_);
lean_inc(v_head_2214_);
lean_dec(v_x_2213_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2226_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
lean_inc(v_x_2211_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set_tag(v___x_2217_, 5);
lean_ctor_set(v___x_2217_, 1, v_x_2211_);
lean_ctor_set(v___x_2217_, 0, v_x_2212_);
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_x_2212_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_x_2211_);
v___x_2220_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2222_ = l_Lean_instReprLevel_repr(v_head_2214_, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2220_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v_x_2212_ = v___x_2223_;
v_x_2213_ = v_tail_2215_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object* v_x_2227_, lean_object* v_x_2228_, lean_object* v_x_2229_){
_start:
{
if (lean_obj_tag(v_x_2229_) == 0)
{
lean_dec(v_x_2227_);
return v_x_2228_;
}
else
{
lean_object* v_head_2230_; lean_object* v_tail_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2242_; 
v_head_2230_ = lean_ctor_get(v_x_2229_, 0);
v_tail_2231_ = lean_ctor_get(v_x_2229_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_x_2229_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2233_ = v_x_2229_;
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_tail_2231_);
lean_inc(v_head_2230_);
lean_dec(v_x_2229_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
lean_inc(v_x_2227_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set_tag(v___x_2233_, 5);
lean_ctor_set(v___x_2233_, 1, v_x_2227_);
lean_ctor_set(v___x_2233_, 0, v_x_2228_);
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_x_2228_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_x_2227_);
v___x_2236_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2237_ = lean_unsigned_to_nat(0u);
v___x_2238_ = l_Lean_instReprLevel_repr(v_head_2230_, v___x_2237_);
v___x_2239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2236_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(v_x_2227_, v___x_2239_, v_tail_2231_);
return v___x_2240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object* v_x_2243_, lean_object* v_x_2244_){
_start:
{
if (lean_obj_tag(v_x_2243_) == 0)
{
lean_object* v___x_2245_; 
lean_dec(v_x_2244_);
v___x_2245_ = lean_box(0);
return v___x_2245_;
}
else
{
lean_object* v_tail_2246_; 
v_tail_2246_ = lean_ctor_get(v_x_2243_, 1);
if (lean_obj_tag(v_tail_2246_) == 0)
{
lean_object* v_head_2247_; lean_object* v___x_2248_; 
lean_dec(v_x_2244_);
v_head_2247_ = lean_ctor_get(v_x_2243_, 0);
lean_inc(v_head_2247_);
lean_dec_ref_known(v_x_2243_, 2);
v___x_2248_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2247_);
return v___x_2248_;
}
else
{
lean_object* v_head_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_inc(v_tail_2246_);
v_head_2249_ = lean_ctor_get(v_x_2243_, 0);
lean_inc(v_head_2249_);
lean_dec_ref_known(v_x_2243_, 2);
v___x_2250_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2249_);
v___x_2251_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(v_x_2244_, v___x_2250_, v_tail_2246_);
return v___x_2251_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2));
v___x_2264_ = lean_string_length(v___x_2263_);
return v___x_2264_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7);
v___x_2266_ = lean_nat_to_int(v___x_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object* v_a_2271_){
_start:
{
if (lean_obj_tag(v_a_2271_) == 0)
{
lean_object* v___x_2272_; 
v___x_2272_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1));
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; lean_object* v___x_2282_; 
v___x_2273_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5));
v___x_2274_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(v_a_2271_, v___x_2273_);
v___x_2275_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8);
v___x_2276_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9));
v___x_2277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set(v___x_2277_, 1, v___x_2274_);
v___x_2278_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10));
v___x_2279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2277_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2275_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = 0;
v___x_2282_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*1, v___x_2281_);
return v___x_2282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object* v_x_2355_, lean_object* v_prec_2356_){
_start:
{
switch(lean_obj_tag(v_x_2355_))
{
case 0:
{
lean_object* v_deBruijnIndex_2357_; lean_object* v___y_2359_; lean_object* v___x_2368_; uint8_t v___x_2369_; 
v_deBruijnIndex_2357_ = lean_ctor_get(v_x_2355_, 0);
lean_inc(v_deBruijnIndex_2357_);
lean_dec_ref_known(v_x_2355_, 1);
v___x_2368_ = lean_unsigned_to_nat(1024u);
v___x_2369_ = lean_nat_dec_le(v___x_2368_, v_prec_2356_);
if (v___x_2369_ == 0)
{
lean_object* v___x_2370_; 
v___x_2370_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2359_ = v___x_2370_;
goto v___jp_2358_;
}
else
{
lean_object* v___x_2371_; 
v___x_2371_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2359_ = v___x_2371_;
goto v___jp_2358_;
}
v___jp_2358_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2360_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__2));
v___x_2361_ = l_Nat_reprFast(v_deBruijnIndex_2357_);
v___x_2362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
v___x_2363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2360_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
lean_inc(v___y_2359_);
v___x_2364_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___y_2359_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
v___x_2365_ = 0;
v___x_2366_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set_uint8(v___x_2366_, sizeof(void*)*1, v___x_2365_);
v___x_2367_ = l_Repr_addAppParen(v___x_2366_, v_prec_2356_);
return v___x_2367_;
}
}
case 1:
{
lean_object* v_fvarId_2372_; lean_object* v___y_2374_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v_fvarId_2372_ = lean_ctor_get(v_x_2355_, 0);
lean_inc(v_fvarId_2372_);
lean_dec_ref_known(v_x_2355_, 1);
v___x_2383_ = lean_unsigned_to_nat(1024u);
v___x_2384_ = lean_nat_dec_le(v___x_2383_, v_prec_2356_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2385_; 
v___x_2385_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2374_ = v___x_2385_;
goto v___jp_2373_;
}
else
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2374_ = v___x_2386_;
goto v___jp_2373_;
}
v___jp_2373_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2375_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__5));
v___x_2376_ = lean_unsigned_to_nat(1024u);
v___x_2377_ = l_Lean_Name_reprPrec(v_fvarId_2372_, v___x_2376_);
v___x_2378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2375_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
lean_inc(v___y_2374_);
v___x_2379_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___y_2374_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = 0;
v___x_2381_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2381_, 0, v___x_2379_);
lean_ctor_set_uint8(v___x_2381_, sizeof(void*)*1, v___x_2380_);
v___x_2382_ = l_Repr_addAppParen(v___x_2381_, v_prec_2356_);
return v___x_2382_;
}
}
case 2:
{
lean_object* v_mvarId_2387_; lean_object* v___y_2389_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v_mvarId_2387_ = lean_ctor_get(v_x_2355_, 0);
lean_inc(v_mvarId_2387_);
lean_dec_ref_known(v_x_2355_, 1);
v___x_2398_ = lean_unsigned_to_nat(1024u);
v___x_2399_ = lean_nat_dec_le(v___x_2398_, v_prec_2356_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2389_ = v___x_2400_;
goto v___jp_2388_;
}
else
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2389_ = v___x_2401_;
goto v___jp_2388_;
}
v___jp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2390_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__8));
v___x_2391_ = lean_unsigned_to_nat(1024u);
v___x_2392_ = l_Lean_Name_reprPrec(v_mvarId_2387_, v___x_2391_);
v___x_2393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2390_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
lean_inc(v___y_2389_);
v___x_2394_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___y_2389_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = 0;
v___x_2396_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*1, v___x_2395_);
v___x_2397_ = l_Repr_addAppParen(v___x_2396_, v_prec_2356_);
return v___x_2397_;
}
}
case 3:
{
lean_object* v_u_2402_; lean_object* v___y_2404_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v_u_2402_ = lean_ctor_get(v_x_2355_, 0);
lean_inc(v_u_2402_);
lean_dec_ref_known(v_x_2355_, 1);
v___x_2413_ = lean_unsigned_to_nat(1024u);
v___x_2414_ = lean_nat_dec_le(v___x_2413_, v_prec_2356_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2404_ = v___x_2415_;
goto v___jp_2403_;
}
else
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2404_ = v___x_2416_;
goto v___jp_2403_;
}
v___jp_2403_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2405_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__11));
v___x_2406_ = lean_unsigned_to_nat(1024u);
v___x_2407_ = l_Lean_instReprLevel_repr(v_u_2402_, v___x_2406_);
v___x_2408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2405_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
lean_inc(v___y_2404_);
v___x_2409_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___y_2404_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = 0;
v___x_2411_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set_uint8(v___x_2411_, sizeof(void*)*1, v___x_2410_);
v___x_2412_ = l_Repr_addAppParen(v___x_2411_, v_prec_2356_);
return v___x_2412_;
}
}
case 4:
{
lean_object* v_declName_2417_; lean_object* v_us_2418_; lean_object* v___y_2420_; lean_object* v___x_2433_; uint8_t v___x_2434_; 
v_declName_2417_ = lean_ctor_get(v_x_2355_, 0);
lean_inc(v_declName_2417_);
v_us_2418_ = lean_ctor_get(v_x_2355_, 1);
lean_inc(v_us_2418_);
lean_dec_ref_known(v_x_2355_, 2);
v___x_2433_ = lean_unsigned_to_nat(1024u);
v___x_2434_ = lean_nat_dec_le(v___x_2433_, v_prec_2356_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2420_ = v___x_2435_;
goto v___jp_2419_;
}
else
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2420_ = v___x_2436_;
goto v___jp_2419_;
}
v___jp_2419_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; uint8_t v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2421_ = lean_box(1);
v___x_2422_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__14));
v___x_2423_ = lean_unsigned_to_nat(1024u);
v___x_2424_ = l_Lean_Name_reprPrec(v_declName_2417_, v___x_2423_);
v___x_2425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2422_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
lean_ctor_set(v___x_2426_, 1, v___x_2421_);
v___x_2427_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_us_2418_);
v___x_2428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2426_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
lean_inc(v___y_2420_);
v___x_2429_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___y_2420_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = 0;
v___x_2431_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set_uint8(v___x_2431_, sizeof(void*)*1, v___x_2430_);
v___x_2432_ = l_Repr_addAppParen(v___x_2431_, v_prec_2356_);
return v___x_2432_;
}
}
case 5:
{
lean_object* v_fn_2437_; lean_object* v_arg_2438_; lean_object* v___x_2439_; lean_object* v___y_2441_; uint8_t v___x_2453_; 
v_fn_2437_ = lean_ctor_get(v_x_2355_, 0);
lean_inc_ref(v_fn_2437_);
v_arg_2438_ = lean_ctor_get(v_x_2355_, 1);
lean_inc_ref(v_arg_2438_);
lean_dec_ref_known(v_x_2355_, 2);
v___x_2439_ = lean_unsigned_to_nat(1024u);
v___x_2453_ = lean_nat_dec_le(v___x_2439_, v_prec_2356_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
v___x_2454_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2441_ = v___x_2454_;
goto v___jp_2440_;
}
else
{
lean_object* v___x_2455_; 
v___x_2455_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2441_ = v___x_2455_;
goto v___jp_2440_;
}
v___jp_2440_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2442_ = lean_box(1);
v___x_2443_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__17));
v___x_2444_ = l_Lean_instReprExpr_repr(v_fn_2437_, v___x_2439_);
v___x_2445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2443_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
lean_ctor_set(v___x_2446_, 1, v___x_2442_);
v___x_2447_ = l_Lean_instReprExpr_repr(v_arg_2438_, v___x_2439_);
v___x_2448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
lean_inc(v___y_2441_);
v___x_2449_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___y_2441_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = 0;
v___x_2451_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set_uint8(v___x_2451_, sizeof(void*)*1, v___x_2450_);
v___x_2452_ = l_Repr_addAppParen(v___x_2451_, v_prec_2356_);
return v___x_2452_;
}
}
case 6:
{
lean_object* v_binderName_2456_; lean_object* v_binderType_2457_; lean_object* v_body_2458_; uint8_t v_binderInfo_2459_; lean_object* v___x_2460_; lean_object* v___y_2462_; uint8_t v___x_2480_; 
v_binderName_2456_ = lean_ctor_get(v_x_2355_, 0);
lean_inc(v_binderName_2456_);
v_binderType_2457_ = lean_ctor_get(v_x_2355_, 1);
lean_inc_ref(v_binderType_2457_);
v_body_2458_ = lean_ctor_get(v_x_2355_, 2);
lean_inc_ref(v_body_2458_);
v_binderInfo_2459_ = lean_ctor_get_uint8(v_x_2355_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2355_, 3);
v___x_2460_ = lean_unsigned_to_nat(1024u);
v___x_2480_ = lean_nat_dec_le(v___x_2460_, v_prec_2356_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; 
v___x_2481_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2462_ = v___x_2481_;
goto v___jp_2461_;
}
else
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2462_ = v___x_2482_;
goto v___jp_2461_;
}
v___jp_2461_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2463_ = lean_box(1);
v___x_2464_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__20));
v___x_2465_ = l_Lean_Name_reprPrec(v_binderName_2456_, v___x_2460_);
v___x_2466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
lean_ctor_set(v___x_2467_, 1, v___x_2463_);
v___x_2468_ = l_Lean_instReprExpr_repr(v_binderType_2457_, v___x_2460_);
v___x_2469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
lean_ctor_set(v___x_2470_, 1, v___x_2463_);
v___x_2471_ = l_Lean_instReprExpr_repr(v_body_2458_, v___x_2460_);
v___x_2472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set(v___x_2473_, 1, v___x_2463_);
v___x_2474_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2459_, v___x_2460_);
v___x_2475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
lean_inc(v___y_2462_);
v___x_2476_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___y_2462_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
v___x_2477_ = 0;
v___x_2478_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*1, v___x_2477_);
v___x_2479_ = l_Repr_addAppParen(v___x_2478_, v_prec_2356_);
return v___x_2479_;
}
}
case 7:
{
lean_object* v_binderName_2483_; lean_object* v_binderType_2484_; lean_object* v_body_2485_; uint8_t v_binderInfo_2486_; lean_object* v___x_2487_; lean_object* v___y_2489_; uint8_t v___x_2507_; 
v_binderName_2483_ = lean_ctor_get(v_x_2355_, 0);
lean_inc(v_binderName_2483_);
v_binderType_2484_ = lean_ctor_get(v_x_2355_, 1);
lean_inc_ref(v_binderType_2484_);
v_body_2485_ = lean_ctor_get(v_x_2355_, 2);
lean_inc_ref(v_body_2485_);
v_binderInfo_2486_ = lean_ctor_get_uint8(v_x_2355_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2355_, 3);
v___x_2487_ = lean_unsigned_to_nat(1024u);
v___x_2507_ = lean_nat_dec_le(v___x_2487_, v_prec_2356_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2489_ = v___x_2508_;
goto v___jp_2488_;
}
else
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2489_ = v___x_2509_;
goto v___jp_2488_;
}
v___jp_2488_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; uint8_t v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2490_ = lean_box(1);
v___x_2491_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__23));
v___x_2492_ = l_Lean_Name_reprPrec(v_binderName_2483_, v___x_2487_);
v___x_2493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2491_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
lean_ctor_set(v___x_2494_, 1, v___x_2490_);
v___x_2495_ = l_Lean_instReprExpr_repr(v_binderType_2484_, v___x_2487_);
v___x_2496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2494_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___x_2490_);
v___x_2498_ = l_Lean_instReprExpr_repr(v_body_2485_, v___x_2487_);
v___x_2499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2497_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
lean_ctor_set(v___x_2500_, 1, v___x_2490_);
v___x_2501_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2486_, v___x_2487_);
v___x_2502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2500_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
lean_inc(v___y_2489_);
v___x_2503_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___y_2489_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = 0;
v___x_2505_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set_uint8(v___x_2505_, sizeof(void*)*1, v___x_2504_);
v___x_2506_ = l_Repr_addAppParen(v___x_2505_, v_prec_2356_);
return v___x_2506_;
}
}
case 8:
{
lean_object* v_declName_2510_; lean_object* v_type_2511_; lean_object* v_value_2512_; lean_object* v_body_2513_; uint8_t v_nondep_2514_; lean_object* v___x_2515_; lean_object* v___y_2517_; uint8_t v___x_2538_; 
v_declName_2510_ = lean_ctor_get(v_x_2355_, 0);
lean_inc(v_declName_2510_);
v_type_2511_ = lean_ctor_get(v_x_2355_, 1);
lean_inc_ref(v_type_2511_);
v_value_2512_ = lean_ctor_get(v_x_2355_, 2);
lean_inc_ref(v_value_2512_);
v_body_2513_ = lean_ctor_get(v_x_2355_, 3);
lean_inc_ref(v_body_2513_);
v_nondep_2514_ = lean_ctor_get_uint8(v_x_2355_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_x_2355_, 4);
v___x_2515_ = lean_unsigned_to_nat(1024u);
v___x_2538_ = lean_nat_dec_le(v___x_2515_, v_prec_2356_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; 
v___x_2539_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2517_ = v___x_2539_;
goto v___jp_2516_;
}
else
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2517_ = v___x_2540_;
goto v___jp_2516_;
}
v___jp_2516_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2518_ = lean_box(1);
v___x_2519_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__26));
v___x_2520_ = l_Lean_Name_reprPrec(v_declName_2510_, v___x_2515_);
v___x_2521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v___x_2518_);
v___x_2523_ = l_Lean_instReprExpr_repr(v_type_2511_, v___x_2515_);
v___x_2524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2522_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
lean_ctor_set(v___x_2525_, 1, v___x_2518_);
v___x_2526_ = l_Lean_instReprExpr_repr(v_value_2512_, v___x_2515_);
v___x_2527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
lean_ctor_set(v___x_2528_, 1, v___x_2518_);
v___x_2529_ = l_Lean_instReprExpr_repr(v_body_2513_, v___x_2515_);
v___x_2530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2528_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___x_2531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
lean_ctor_set(v___x_2531_, 1, v___x_2518_);
v___x_2532_ = l_Bool_repr___redArg(v_nondep_2514_);
v___x_2533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2531_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
lean_inc(v___y_2517_);
v___x_2534_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___y_2517_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = 0;
v___x_2536_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set_uint8(v___x_2536_, sizeof(void*)*1, v___x_2535_);
v___x_2537_ = l_Repr_addAppParen(v___x_2536_, v_prec_2356_);
return v___x_2537_;
}
}
case 9:
{
lean_object* v_a_2541_; lean_object* v___y_2543_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v_a_2541_ = lean_ctor_get(v_x_2355_, 0);
lean_inc_ref(v_a_2541_);
lean_dec_ref_known(v_x_2355_, 1);
v___x_2552_ = lean_unsigned_to_nat(1024u);
v___x_2553_ = lean_nat_dec_le(v___x_2552_, v_prec_2356_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2543_ = v___x_2554_;
goto v___jp_2542_;
}
else
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2543_ = v___x_2555_;
goto v___jp_2542_;
}
v___jp_2542_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2544_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__29));
v___x_2545_ = lean_unsigned_to_nat(1024u);
v___x_2546_ = l_Lean_instReprLiteral_repr(v_a_2541_, v___x_2545_);
v___x_2547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2544_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
lean_inc(v___y_2543_);
v___x_2548_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___y_2543_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = 0;
v___x_2550_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set_uint8(v___x_2550_, sizeof(void*)*1, v___x_2549_);
v___x_2551_ = l_Repr_addAppParen(v___x_2550_, v_prec_2356_);
return v___x_2551_;
}
}
case 10:
{
lean_object* v_data_2556_; lean_object* v_expr_2557_; lean_object* v___x_2558_; lean_object* v___y_2560_; uint8_t v___x_2572_; 
v_data_2556_ = lean_ctor_get(v_x_2355_, 0);
lean_inc(v_data_2556_);
v_expr_2557_ = lean_ctor_get(v_x_2355_, 1);
lean_inc_ref(v_expr_2557_);
lean_dec_ref_known(v_x_2355_, 2);
v___x_2558_ = lean_unsigned_to_nat(1024u);
v___x_2572_ = lean_nat_dec_le(v___x_2558_, v_prec_2356_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2560_ = v___x_2573_;
goto v___jp_2559_;
}
else
{
lean_object* v___x_2574_; 
v___x_2574_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2560_ = v___x_2574_;
goto v___jp_2559_;
}
v___jp_2559_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2561_ = lean_box(1);
v___x_2562_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__32));
v___x_2563_ = l_Lean_instReprKVMap_repr___redArg(v_data_2556_);
v___x_2564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2562_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
lean_ctor_set(v___x_2565_, 1, v___x_2561_);
v___x_2566_ = l_Lean_instReprExpr_repr(v_expr_2557_, v___x_2558_);
v___x_2567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
lean_inc(v___y_2560_);
v___x_2568_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___y_2560_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = 0;
v___x_2570_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2570_, 0, v___x_2568_);
lean_ctor_set_uint8(v___x_2570_, sizeof(void*)*1, v___x_2569_);
v___x_2571_ = l_Repr_addAppParen(v___x_2570_, v_prec_2356_);
return v___x_2571_;
}
}
default: 
{
lean_object* v_typeName_2575_; lean_object* v_idx_2576_; lean_object* v_struct_2577_; lean_object* v___x_2578_; lean_object* v___y_2580_; uint8_t v___x_2596_; 
v_typeName_2575_ = lean_ctor_get(v_x_2355_, 0);
lean_inc(v_typeName_2575_);
v_idx_2576_ = lean_ctor_get(v_x_2355_, 1);
lean_inc(v_idx_2576_);
v_struct_2577_ = lean_ctor_get(v_x_2355_, 2);
lean_inc_ref(v_struct_2577_);
lean_dec_ref_known(v_x_2355_, 3);
v___x_2578_ = lean_unsigned_to_nat(1024u);
v___x_2596_ = lean_nat_dec_le(v___x_2578_, v_prec_2356_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2580_ = v___x_2597_;
goto v___jp_2579_;
}
else
{
lean_object* v___x_2598_; 
v___x_2598_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2580_ = v___x_2598_;
goto v___jp_2579_;
}
v___jp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2581_ = lean_box(1);
v___x_2582_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__35));
v___x_2583_ = l_Lean_Name_reprPrec(v_typeName_2575_, v___x_2578_);
v___x_2584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
v___x_2585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
lean_ctor_set(v___x_2585_, 1, v___x_2581_);
v___x_2586_ = l_Nat_reprFast(v_idx_2576_);
v___x_2587_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2585_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
lean_ctor_set(v___x_2589_, 1, v___x_2581_);
v___x_2590_ = l_Lean_instReprExpr_repr(v_struct_2577_, v___x_2578_);
v___x_2591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2589_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
lean_inc(v___y_2580_);
v___x_2592_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___y_2580_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
v___x_2593_ = 0;
v___x_2594_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2594_, 0, v___x_2592_);
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*1, v___x_2593_);
v___x_2595_ = l_Repr_addAppParen(v___x_2594_, v_prec_2356_);
return v___x_2595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object* v_x_2599_, lean_object* v_prec_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_instReprExpr_repr(v_x_2599_, v_prec_2600_);
lean_dec(v_prec_2600_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object* v_a_2602_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = lean_nat_to_int(v_a_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object* v_a_2604_, lean_object* v_n_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_a_2604_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object* v_a_2607_, lean_object* v_n_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0(v_a_2607_, v_n_2608_);
lean_dec(v_n_2608_);
return v_res_2609_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__2(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_box(0);
v___x_2616_ = ((lean_object*)(l_Lean_instInhabitedExpr___closed__1));
v___x_2617_ = l_Lean_Expr_const___override(v___x_2616_, v___x_2615_);
return v___x_2617_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr(void){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* v_x_2631_){
_start:
{
switch(lean_obj_tag(v_x_2631_))
{
case 0:
{
lean_object* v___x_2632_; 
v___x_2632_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__0));
return v___x_2632_;
}
case 1:
{
lean_object* v___x_2633_; 
v___x_2633_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__1));
return v___x_2633_;
}
case 2:
{
lean_object* v___x_2634_; 
v___x_2634_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__2));
return v___x_2634_;
}
case 3:
{
lean_object* v___x_2635_; 
v___x_2635_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__3));
return v___x_2635_;
}
case 4:
{
lean_object* v___x_2636_; 
v___x_2636_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__4));
return v___x_2636_;
}
case 5:
{
lean_object* v___x_2637_; 
v___x_2637_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__5));
return v___x_2637_;
}
case 6:
{
lean_object* v___x_2638_; 
v___x_2638_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__6));
return v___x_2638_;
}
case 7:
{
lean_object* v___x_2639_; 
v___x_2639_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__7));
return v___x_2639_;
}
case 8:
{
lean_object* v___x_2640_; 
v___x_2640_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__8));
return v___x_2640_;
}
case 9:
{
lean_object* v___x_2641_; 
v___x_2641_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__9));
return v___x_2641_;
}
case 10:
{
lean_object* v___x_2642_; 
v___x_2642_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__10));
return v___x_2642_;
}
default: 
{
lean_object* v___x_2643_; 
v___x_2643_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__11));
return v___x_2643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* v_x_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_Expr_ctorName(v_x_2644_);
lean_dec_ref(v_x_2644_);
return v_res_2645_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object* v_e_2646_){
_start:
{
uint64_t v___x_2647_; uint64_t v___x_2648_; 
v___x_2647_ = lean_expr_data(v_e_2646_);
v___x_2648_ = l_Lean_Expr_Data_hash(v___x_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* v_e_2649_){
_start:
{
uint64_t v_res_2650_; lean_object* v_r_2651_; 
v_res_2650_ = l_Lean_Expr_hash(v_e_2649_);
lean_dec_ref(v_e_2649_);
v_r_2651_ = lean_box_uint64(v_res_2650_);
return v_r_2651_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object* v_e_2654_){
_start:
{
uint64_t v___x_2655_; uint8_t v___x_2656_; 
v___x_2655_ = lean_expr_data(v_e_2654_);
v___x_2656_ = l_Lean_Expr_Data_hasFVar(v___x_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* v_e_2657_){
_start:
{
uint8_t v_res_2658_; lean_object* v_r_2659_; 
v_res_2658_ = l_Lean_Expr_hasFVar(v_e_2657_);
lean_dec_ref(v_e_2657_);
v_r_2659_ = lean_box(v_res_2658_);
return v_r_2659_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object* v_e_2660_){
_start:
{
uint64_t v___x_2661_; uint8_t v___x_2662_; 
v___x_2661_ = lean_expr_data(v_e_2660_);
v___x_2662_ = l_Lean_Expr_Data_hasExprMVar(v___x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* v_e_2663_){
_start:
{
uint8_t v_res_2664_; lean_object* v_r_2665_; 
v_res_2664_ = l_Lean_Expr_hasExprMVar(v_e_2663_);
lean_dec_ref(v_e_2663_);
v_r_2665_ = lean_box(v_res_2664_);
return v_r_2665_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object* v_e_2666_){
_start:
{
uint64_t v___x_2667_; uint8_t v___x_2668_; 
v___x_2667_ = lean_expr_data(v_e_2666_);
v___x_2668_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* v_e_2669_){
_start:
{
uint8_t v_res_2670_; lean_object* v_r_2671_; 
v_res_2670_ = l_Lean_Expr_hasLevelMVar(v_e_2669_);
lean_dec_ref(v_e_2669_);
v_r_2671_ = lean_box(v_res_2670_);
return v_r_2671_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object* v_e_2672_){
_start:
{
uint64_t v_d_2673_; uint8_t v___x_2674_; 
v_d_2673_ = lean_expr_data(v_e_2672_);
v___x_2674_ = l_Lean_Expr_Data_hasExprMVar(v_d_2673_);
if (v___x_2674_ == 0)
{
uint8_t v___x_2675_; 
v___x_2675_ = l_Lean_Expr_Data_hasLevelMVar(v_d_2673_);
return v___x_2675_;
}
else
{
return v___x_2674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* v_e_2676_){
_start:
{
uint8_t v_res_2677_; lean_object* v_r_2678_; 
v_res_2677_ = l_Lean_Expr_hasMVar(v_e_2676_);
lean_dec_ref(v_e_2676_);
v_r_2678_ = lean_box(v_res_2677_);
return v_r_2678_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object* v_e_2679_){
_start:
{
uint64_t v___x_2680_; uint8_t v___x_2681_; 
v___x_2680_ = lean_expr_data(v_e_2679_);
v___x_2681_ = l_Lean_Expr_Data_hasLevelParam(v___x_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* v_e_2682_){
_start:
{
uint8_t v_res_2683_; lean_object* v_r_2684_; 
v_res_2683_ = l_Lean_Expr_hasLevelParam(v_e_2682_);
lean_dec_ref(v_e_2682_);
v_r_2684_ = lean_box(v_res_2683_);
return v_r_2684_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object* v_e_2685_){
_start:
{
uint64_t v___x_2686_; uint8_t v___x_2687_; uint32_t v___x_2688_; 
v___x_2686_ = lean_expr_data(v_e_2685_);
v___x_2687_ = l_Lean_Expr_Data_approxDepth(v___x_2686_);
v___x_2688_ = lean_uint8_to_uint32(v___x_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* v_e_2689_){
_start:
{
uint32_t v_res_2690_; lean_object* v_r_2691_; 
v_res_2690_ = l_Lean_Expr_approxDepth(v_e_2689_);
lean_dec_ref(v_e_2689_);
v_r_2691_ = lean_box_uint32(v_res_2690_);
return v_r_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* v_e_2692_){
_start:
{
uint64_t v___x_2693_; uint32_t v___x_2694_; lean_object* v___x_2695_; 
v___x_2693_ = lean_expr_data(v_e_2692_);
v___x_2694_ = l_Lean_Expr_Data_looseBVarRange(v___x_2693_);
v___x_2695_ = lean_uint32_to_nat(v___x_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* v_e_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Lean_Expr_looseBVarRange(v_e_2696_);
lean_dec_ref(v_e_2696_);
return v_res_2697_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object* v_e_2698_){
_start:
{
switch(lean_obj_tag(v_e_2698_))
{
case 7:
{
uint8_t v_binderInfo_2699_; 
v_binderInfo_2699_ = lean_ctor_get_uint8(v_e_2698_, sizeof(void*)*3 + 8);
return v_binderInfo_2699_;
}
case 6:
{
uint8_t v_binderInfo_2700_; 
v_binderInfo_2700_ = lean_ctor_get_uint8(v_e_2698_, sizeof(void*)*3 + 8);
return v_binderInfo_2700_;
}
default: 
{
uint8_t v___x_2701_; 
v___x_2701_ = 0;
return v___x_2701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* v_e_2702_){
_start:
{
uint8_t v_res_2703_; lean_object* v_r_2704_; 
v_res_2703_ = l_Lean_Expr_binderInfo(v_e_2702_);
lean_dec_ref(v_e_2702_);
v_r_2704_ = lean_box(v_res_2703_);
return v_r_2704_;
}
}
LEAN_EXPORT uint64_t lean_expr_hash(lean_object* v_a_2705_){
_start:
{
uint64_t v___x_2706_; 
v___x_2706_ = l_Lean_Expr_hash(v_a_2705_);
lean_dec_ref(v_a_2705_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* v_a_2707_){
_start:
{
uint64_t v_res_2708_; lean_object* v_r_2709_; 
v_res_2708_ = lean_expr_hash(v_a_2707_);
v_r_2709_ = lean_box_uint64(v_res_2708_);
return v_r_2709_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object* v_e_2710_){
_start:
{
uint8_t v___x_2711_; 
v___x_2711_ = l_Lean_Expr_hasFVar(v_e_2710_);
lean_dec_ref(v_e_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* v_e_2712_){
_start:
{
uint8_t v_res_2713_; lean_object* v_r_2714_; 
v_res_2713_ = lean_expr_has_fvar(v_e_2712_);
v_r_2714_ = lean_box(v_res_2713_);
return v_r_2714_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object* v_e_2715_){
_start:
{
uint8_t v___x_2716_; 
v___x_2716_ = l_Lean_Expr_hasExprMVar(v_e_2715_);
lean_dec_ref(v_e_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* v_e_2717_){
_start:
{
uint8_t v_res_2718_; lean_object* v_r_2719_; 
v_res_2718_ = lean_expr_has_expr_mvar(v_e_2717_);
v_r_2719_ = lean_box(v_res_2718_);
return v_r_2719_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object* v_e_2720_){
_start:
{
uint8_t v___x_2721_; 
v___x_2721_ = l_Lean_Expr_hasLevelMVar(v_e_2720_);
lean_dec_ref(v_e_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* v_e_2722_){
_start:
{
uint8_t v_res_2723_; lean_object* v_r_2724_; 
v_res_2723_ = lean_expr_has_level_mvar(v_e_2722_);
v_r_2724_ = lean_box(v_res_2723_);
return v_r_2724_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* v_e_2725_){
_start:
{
uint8_t v___x_2726_; 
v___x_2726_ = l_Lean_Expr_hasLevelParam(v_e_2725_);
lean_dec_ref(v_e_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* v_e_2727_){
_start:
{
uint8_t v_res_2728_; lean_object* v_r_2729_; 
v_res_2728_ = lean_expr_has_level_param(v_e_2727_);
v_r_2729_ = lean_box(v_res_2728_);
return v_r_2729_;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* v_e_2730_){
_start:
{
uint64_t v___x_2731_; uint32_t v___x_2732_; 
v___x_2731_ = lean_expr_data(v_e_2730_);
lean_dec_ref(v_e_2730_);
v___x_2732_ = l_Lean_Expr_Data_looseBVarRange(v___x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* v_e_2733_){
_start:
{
uint32_t v_res_2734_; lean_object* v_r_2735_; 
v_res_2734_ = lean_expr_loose_bvar_range(v_e_2733_);
v_r_2735_ = lean_box_uint32(v_res_2734_);
return v_r_2735_;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* v_e_2736_){
_start:
{
uint8_t v___x_2737_; 
v___x_2737_ = l_Lean_Expr_binderInfo(v_e_2736_);
lean_dec_ref(v_e_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* v_e_2738_){
_start:
{
uint8_t v_res_2739_; lean_object* v_r_2740_; 
v_res_2739_ = lean_expr_binder_info(v_e_2738_);
v_r_2740_ = lean_box(v_res_2739_);
return v_r_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* v_declName_2741_, lean_object* v_us_2742_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_Expr_const___override(v_declName_2741_, v_us_2742_);
return v___x_2743_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2(void){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = lean_box(0);
v___x_2748_ = ((lean_object*)(l_Lean_Literal_type___closed__1));
v___x_2749_ = l_Lean_Expr_const___override(v___x_2748_, v___x_2747_);
return v___x_2749_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = lean_box(0);
v___x_2754_ = ((lean_object*)(l_Lean_Literal_type___closed__4));
v___x_2755_ = l_Lean_Expr_const___override(v___x_2754_, v___x_2753_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* v_x_2756_){
_start:
{
if (lean_obj_tag(v_x_2756_) == 0)
{
lean_object* v___x_2757_; 
v___x_2757_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_2757_;
}
else
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_obj_once(&l_Lean_Literal_type___closed__5, &l_Lean_Literal_type___closed__5_once, _init_l_Lean_Literal_type___closed__5);
return v___x_2758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* v_x_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Lean_Literal_type(v_x_2759_);
lean_dec_ref(v_x_2759_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* v_a_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_Literal_type(v_a_2761_);
lean_dec_ref(v_a_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* v_idx_2763_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_Expr_bvar___override(v_idx_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* v_u_2765_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_Expr_sort___override(v_u_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* v_fvarId_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Lean_Expr_fvar___override(v_fvarId_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* v_mvarId_2769_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l_Lean_Expr_mvar___override(v_mvarId_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* v_m_2771_, lean_object* v_e_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_Expr_mdata___override(v_m_2771_, v_e_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* v_structName_2774_, lean_object* v_idx_2775_, lean_object* v_struct_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Lean_Expr_proj___override(v_structName_2774_, v_idx_2775_, v_struct_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* v_f_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_Expr_app___override(v_f_2778_, v_a_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* v_x_2781_, uint8_t v_bi_2782_, lean_object* v_t_2783_, lean_object* v_b_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Lean_Expr_lam___override(v_x_2781_, v_t_2783_, v_b_2784_, v_bi_2782_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* v_x_2786_, lean_object* v_bi_2787_, lean_object* v_t_2788_, lean_object* v_b_2789_){
_start:
{
uint8_t v_bi_boxed_2790_; lean_object* v_res_2791_; 
v_bi_boxed_2790_ = lean_unbox(v_bi_2787_);
v_res_2791_ = l_Lean_mkLambda(v_x_2786_, v_bi_boxed_2790_, v_t_2788_, v_b_2789_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* v_x_2792_, uint8_t v_bi_2793_, lean_object* v_t_2794_, lean_object* v_b_2795_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_Expr_forallE___override(v_x_2792_, v_t_2794_, v_b_2795_, v_bi_2793_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* v_x_2797_, lean_object* v_bi_2798_, lean_object* v_t_2799_, lean_object* v_b_2800_){
_start:
{
uint8_t v_bi_boxed_2801_; lean_object* v_res_2802_; 
v_bi_boxed_2801_ = lean_unbox(v_bi_2798_);
v_res_2802_ = l_Lean_mkForall(v_x_2797_, v_bi_boxed_2801_, v_t_2799_, v_b_2800_);
return v_res_2802_;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__4(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2809_ = lean_box(0);
v___x_2810_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__3));
v___x_2811_ = l_Lean_Expr_const___override(v___x_2810_, v___x_2809_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* v_type_2812_){
_start:
{
lean_object* v___x_2813_; uint8_t v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2813_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2814_ = 0;
v___x_2815_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2816_ = l_Lean_Expr_forallE___override(v___x_2813_, v___x_2815_, v_type_2812_, v___x_2814_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* v_type_2817_){
_start:
{
lean_object* v___x_2818_; uint8_t v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2818_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2819_ = 0;
v___x_2820_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2821_ = l_Lean_Expr_lam___override(v___x_2818_, v___x_2820_, v_type_2817_, v___x_2819_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* v_x_2822_, lean_object* v_t_2823_, lean_object* v_v_2824_, lean_object* v_b_2825_, uint8_t v_nondep_2826_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_Expr_letE___override(v_x_2822_, v_t_2823_, v_v_2824_, v_b_2825_, v_nondep_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* v_x_2828_, lean_object* v_t_2829_, lean_object* v_v_2830_, lean_object* v_b_2831_, lean_object* v_nondep_2832_){
_start:
{
uint8_t v_nondep_boxed_2833_; lean_object* v_res_2834_; 
v_nondep_boxed_2833_ = lean_unbox(v_nondep_2832_);
v_res_2834_ = l_Lean_mkLet(v_x_2828_, v_t_2829_, v_v_2830_, v_b_2831_, v_nondep_boxed_2833_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object* v_x_2835_, lean_object* v_t_2836_, lean_object* v_v_2837_, lean_object* v_b_2838_){
_start:
{
uint8_t v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = 1;
v___x_2840_ = l_Lean_Expr_letE___override(v_x_2835_, v_t_2836_, v_v_2837_, v_b_2838_, v___x_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* v_f_2841_, lean_object* v_a_2842_, lean_object* v_b_2843_){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = l_Lean_Expr_app___override(v_f_2841_, v_a_2842_);
v___x_2845_ = l_Lean_Expr_app___override(v___x_2844_, v_b_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* v_f_2846_, lean_object* v_a_2847_, lean_object* v_b_2848_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_mkAppB(v_f_2846_, v_a_2847_, v_b_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* v_f_2850_, lean_object* v_a_2851_, lean_object* v_b_2852_, lean_object* v_c_2853_){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = l_Lean_mkAppB(v_f_2850_, v_a_2851_, v_b_2852_);
v___x_2855_ = l_Lean_Expr_app___override(v___x_2854_, v_c_2853_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* v_f_2856_, lean_object* v_a_2857_, lean_object* v_b_2858_, lean_object* v_c_2859_, lean_object* v_d_2860_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = l_Lean_mkAppB(v_f_2856_, v_a_2857_, v_b_2858_);
v___x_2862_ = l_Lean_mkAppB(v___x_2861_, v_c_2859_, v_d_2860_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* v_f_2863_, lean_object* v_a_2864_, lean_object* v_b_2865_, lean_object* v_c_2866_, lean_object* v_d_2867_, lean_object* v_e_2868_){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = l_Lean_mkApp4(v_f_2863_, v_a_2864_, v_b_2865_, v_c_2866_, v_d_2867_);
v___x_2870_ = l_Lean_Expr_app___override(v___x_2869_, v_e_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* v_f_2871_, lean_object* v_a_2872_, lean_object* v_b_2873_, lean_object* v_c_2874_, lean_object* v_d_2875_, lean_object* v_e_u2081_2876_, lean_object* v_e_u2082_2877_){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = l_Lean_mkApp4(v_f_2871_, v_a_2872_, v_b_2873_, v_c_2874_, v_d_2875_);
v___x_2879_ = l_Lean_mkAppB(v___x_2878_, v_e_u2081_2876_, v_e_u2082_2877_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* v_f_2880_, lean_object* v_a_2881_, lean_object* v_b_2882_, lean_object* v_c_2883_, lean_object* v_d_2884_, lean_object* v_e_u2081_2885_, lean_object* v_e_u2082_2886_, lean_object* v_e_u2083_2887_){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = l_Lean_mkApp4(v_f_2880_, v_a_2881_, v_b_2882_, v_c_2883_, v_d_2884_);
v___x_2889_ = l_Lean_mkApp3(v___x_2888_, v_e_u2081_2885_, v_e_u2082_2886_, v_e_u2083_2887_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* v_f_2890_, lean_object* v_a_2891_, lean_object* v_b_2892_, lean_object* v_c_2893_, lean_object* v_d_2894_, lean_object* v_e_u2081_2895_, lean_object* v_e_u2082_2896_, lean_object* v_e_u2083_2897_, lean_object* v_e_u2084_2898_){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = l_Lean_mkApp4(v_f_2890_, v_a_2891_, v_b_2892_, v_c_2893_, v_d_2894_);
v___x_2900_ = l_Lean_mkApp4(v___x_2899_, v_e_u2081_2895_, v_e_u2082_2896_, v_e_u2083_2897_, v_e_u2084_2898_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* v_f_2901_, lean_object* v_a_2902_, lean_object* v_b_2903_, lean_object* v_c_2904_, lean_object* v_d_2905_, lean_object* v_e_u2081_2906_, lean_object* v_e_u2082_2907_, lean_object* v_e_u2083_2908_, lean_object* v_e_u2084_2909_, lean_object* v_e_u2085_2910_){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = l_Lean_mkApp4(v_f_2901_, v_a_2902_, v_b_2903_, v_c_2904_, v_d_2905_);
v___x_2912_ = l_Lean_mkApp5(v___x_2911_, v_e_u2081_2906_, v_e_u2082_2907_, v_e_u2083_2908_, v_e_u2084_2909_, v_e_u2085_2910_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* v_f_2913_, lean_object* v_a_2914_, lean_object* v_b_2915_, lean_object* v_c_2916_, lean_object* v_d_2917_, lean_object* v_e_u2081_2918_, lean_object* v_e_u2082_2919_, lean_object* v_e_u2083_2920_, lean_object* v_e_u2084_2921_, lean_object* v_e_u2085_2922_, lean_object* v_e_u2086_2923_){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = l_Lean_mkApp4(v_f_2913_, v_a_2914_, v_b_2915_, v_c_2916_, v_d_2917_);
v___x_2925_ = l_Lean_mkApp6(v___x_2924_, v_e_u2081_2918_, v_e_u2082_2919_, v_e_u2083_2920_, v_e_u2084_2921_, v_e_u2085_2922_, v_e_u2086_2923_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* v_l_2926_){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Lean_Expr_lit___override(v_l_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* v_n_2928_){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v_n_2928_);
v___x_2930_ = l_Lean_Expr_lit___override(v___x_2929_);
return v___x_2930_;
}
}
static lean_object* _init_l_Lean_mkInstOfNatNat___closed__2(void){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = lean_box(0);
v___x_2935_ = ((lean_object*)(l_Lean_mkInstOfNatNat___closed__1));
v___x_2936_ = l_Lean_Expr_const___override(v___x_2935_, v___x_2934_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object* v_n_2937_){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = lean_obj_once(&l_Lean_mkInstOfNatNat___closed__2, &l_Lean_mkInstOfNatNat___closed__2_once, _init_l_Lean_mkInstOfNatNat___closed__2);
v___x_2939_ = l_Lean_Expr_app___override(v___x_2938_, v_n_2937_);
return v___x_2939_;
}
}
static lean_object* _init_l_Lean_mkNatLitCore___closed__4(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_2949_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_2950_ = l_Lean_Expr_const___override(v___x_2949_, v___x_2948_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object* v_n_2951_){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2952_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_2953_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
lean_inc_ref(v_n_2951_);
v___x_2954_ = l_Lean_mkInstOfNatNat(v_n_2951_);
v___x_2955_ = l_Lean_mkApp3(v___x_2952_, v___x_2953_, v_n_2951_, v___x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* v_n_2956_){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = l_Lean_mkRawNatLit(v_n_2956_);
v___x_2958_ = l_Lean_mkNatLitCore(v___x_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* v_s_2959_){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2960_, 0, v_s_2959_);
v___x_2961_ = l_Lean_Expr_lit___override(v___x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* v_idx_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_Expr_bvar___override(v_idx_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* v_fvarId_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_Expr_fvar___override(v_fvarId_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Lean_Expr_sort___override(v_u_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_2968_, lean_object* v_lvls_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_Expr_const___override(v_c_2968_, v_lvls_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_Lean_Expr_app___override(v_f_2971_, v_a_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* v_n_2974_, lean_object* v_d_2975_, lean_object* v_b_2976_, uint8_t v_bi_2977_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Lean_Expr_lam___override(v_n_2974_, v_d_2975_, v_b_2976_, v_bi_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_2979_, lean_object* v_d_2980_, lean_object* v_b_2981_, lean_object* v_bi_2982_){
_start:
{
uint8_t v_bi_boxed_2983_; lean_object* v_res_2984_; 
v_bi_boxed_2983_ = lean_unbox(v_bi_2982_);
v_res_2984_ = lean_expr_mk_lambda(v_n_2979_, v_d_2980_, v_b_2981_, v_bi_boxed_2983_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* v_n_2985_, lean_object* v_d_2986_, lean_object* v_b_2987_, uint8_t v_bi_2988_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Lean_Expr_forallE___override(v_n_2985_, v_d_2986_, v_b_2987_, v_bi_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_2990_, lean_object* v_d_2991_, lean_object* v_b_2992_, lean_object* v_bi_2993_){
_start:
{
uint8_t v_bi_boxed_2994_; lean_object* v_res_2995_; 
v_bi_boxed_2994_ = lean_unbox(v_bi_2993_);
v_res_2995_ = lean_expr_mk_forall(v_n_2990_, v_d_2991_, v_b_2992_, v_bi_boxed_2994_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* v_n_2996_, lean_object* v_t_2997_, lean_object* v_v_2998_, lean_object* v_b_2999_, uint8_t v_nondep_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lean_Expr_letE___override(v_n_2996_, v_t_2997_, v_v_2998_, v_b_2999_, v_nondep_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_3002_, lean_object* v_t_3003_, lean_object* v_v_3004_, lean_object* v_b_3005_, lean_object* v_nondep_3006_){
_start:
{
uint8_t v_nondep_boxed_3007_; lean_object* v_res_3008_; 
v_nondep_boxed_3007_ = lean_unbox(v_nondep_3006_);
v_res_3008_ = lean_expr_mk_let(v_n_3002_, v_t_3003_, v_v_3004_, v_b_3005_, v_nondep_boxed_3007_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_3009_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_Expr_lit___override(v_l_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_3011_, lean_object* v_e_3012_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Lean_Expr_mdata___override(v_m_3011_, v_e_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_3014_, lean_object* v_idx_3015_, lean_object* v_struct_3016_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Lean_Expr_proj___override(v_structName_3014_, v_idx_3015_, v_struct_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_3018_, size_t v_i_3019_, size_t v_stop_3020_, lean_object* v_b_3021_){
_start:
{
uint8_t v___x_3022_; 
v___x_3022_ = lean_usize_dec_eq(v_i_3019_, v_stop_3020_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; lean_object* v___x_3024_; size_t v___x_3025_; size_t v___x_3026_; 
v___x_3023_ = lean_array_uget_borrowed(v_as_3018_, v_i_3019_);
lean_inc(v___x_3023_);
v___x_3024_ = l_Lean_Expr_app___override(v_b_3021_, v___x_3023_);
v___x_3025_ = ((size_t)1ULL);
v___x_3026_ = lean_usize_add(v_i_3019_, v___x_3025_);
v_i_3019_ = v___x_3026_;
v_b_3021_ = v___x_3024_;
goto _start;
}
else
{
return v_b_3021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_3028_, lean_object* v_i_3029_, lean_object* v_stop_3030_, lean_object* v_b_3031_){
_start:
{
size_t v_i_boxed_3032_; size_t v_stop_boxed_3033_; lean_object* v_res_3034_; 
v_i_boxed_3032_ = lean_unbox_usize(v_i_3029_);
lean_dec(v_i_3029_);
v_stop_boxed_3033_ = lean_unbox_usize(v_stop_3030_);
lean_dec(v_stop_3030_);
v_res_3034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_3028_, v_i_boxed_3032_, v_stop_boxed_3033_, v_b_3031_);
lean_dec_ref(v_as_3028_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_3035_, lean_object* v_args_3036_){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; uint8_t v___x_3039_; 
v___x_3037_ = lean_unsigned_to_nat(0u);
v___x_3038_ = lean_array_get_size(v_args_3036_);
v___x_3039_ = lean_nat_dec_lt(v___x_3037_, v___x_3038_);
if (v___x_3039_ == 0)
{
return v_f_3035_;
}
else
{
uint8_t v___x_3040_; 
v___x_3040_ = lean_nat_dec_le(v___x_3038_, v___x_3038_);
if (v___x_3040_ == 0)
{
if (v___x_3039_ == 0)
{
return v_f_3035_;
}
else
{
size_t v___x_3041_; size_t v___x_3042_; lean_object* v___x_3043_; 
v___x_3041_ = ((size_t)0ULL);
v___x_3042_ = lean_usize_of_nat(v___x_3038_);
v___x_3043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3036_, v___x_3041_, v___x_3042_, v_f_3035_);
return v___x_3043_;
}
}
else
{
size_t v___x_3044_; size_t v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = ((size_t)0ULL);
v___x_3045_ = lean_usize_of_nat(v___x_3038_);
v___x_3046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3036_, v___x_3044_, v___x_3045_, v_f_3035_);
return v___x_3046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_3047_, lean_object* v_args_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_mkAppN(v_f_3047_, v_args_3048_);
lean_dec_ref(v_args_3048_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_3050_, lean_object* v_args_3051_, lean_object* v_i_3052_, lean_object* v_e_3053_){
_start:
{
uint8_t v___x_3054_; 
v___x_3054_ = lean_nat_dec_lt(v_i_3052_, v_n_3050_);
if (v___x_3054_ == 0)
{
lean_dec(v_i_3052_);
return v_e_3053_;
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3055_ = l_Lean_instInhabitedExpr;
v___x_3056_ = lean_unsigned_to_nat(1u);
v___x_3057_ = lean_nat_add(v_i_3052_, v___x_3056_);
v___x_3058_ = lean_array_get_borrowed(v___x_3055_, v_args_3051_, v_i_3052_);
lean_dec(v_i_3052_);
lean_inc(v___x_3058_);
v___x_3059_ = l_Lean_Expr_app___override(v_e_3053_, v___x_3058_);
v_i_3052_ = v___x_3057_;
v_e_3053_ = v___x_3059_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_3061_, lean_object* v_args_3062_, lean_object* v_i_3063_, lean_object* v_e_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_3061_, v_args_3062_, v_i_3063_, v_e_3064_);
lean_dec_ref(v_args_3062_);
lean_dec(v_n_3061_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_3066_, lean_object* v_i_3067_, lean_object* v_j_3068_, lean_object* v_args_3069_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_3068_, v_args_3069_, v_i_3067_, v_f_3066_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_3071_, lean_object* v_i_3072_, lean_object* v_j_3073_, lean_object* v_args_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_mkAppRange(v_f_3071_, v_i_3072_, v_j_3073_, v_args_3074_);
lean_dec_ref(v_args_3074_);
lean_dec(v_j_3073_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_3076_, size_t v_i_3077_, size_t v_stop_3078_, lean_object* v_b_3079_){
_start:
{
uint8_t v___x_3080_; 
v___x_3080_ = lean_usize_dec_eq(v_i_3077_, v_stop_3078_);
if (v___x_3080_ == 0)
{
size_t v___x_3081_; size_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3081_ = ((size_t)1ULL);
v___x_3082_ = lean_usize_sub(v_i_3077_, v___x_3081_);
v___x_3083_ = lean_array_uget_borrowed(v_as_3076_, v___x_3082_);
lean_inc(v___x_3083_);
v___x_3084_ = l_Lean_Expr_app___override(v_b_3079_, v___x_3083_);
v_i_3077_ = v___x_3082_;
v_b_3079_ = v___x_3084_;
goto _start;
}
else
{
return v_b_3079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_3086_, lean_object* v_i_3087_, lean_object* v_stop_3088_, lean_object* v_b_3089_){
_start:
{
size_t v_i_boxed_3090_; size_t v_stop_boxed_3091_; lean_object* v_res_3092_; 
v_i_boxed_3090_ = lean_unbox_usize(v_i_3087_);
lean_dec(v_i_3087_);
v_stop_boxed_3091_ = lean_unbox_usize(v_stop_3088_);
lean_dec(v_stop_3088_);
v_res_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3086_, v_i_boxed_3090_, v_stop_boxed_3091_, v_b_3089_);
lean_dec_ref(v_as_3086_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_3093_, lean_object* v_revArgs_3094_){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3095_ = lean_array_get_size(v_revArgs_3094_);
v___x_3096_ = lean_unsigned_to_nat(0u);
v___x_3097_ = lean_nat_dec_lt(v___x_3096_, v___x_3095_);
if (v___x_3097_ == 0)
{
return v_fn_3093_;
}
else
{
size_t v___x_3098_; size_t v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = lean_usize_of_nat(v___x_3095_);
v___x_3099_ = ((size_t)0ULL);
v___x_3100_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_3094_, v___x_3098_, v___x_3099_, v_fn_3093_);
return v___x_3100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_3101_, lean_object* v_revArgs_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_mkAppRev(v_fn_3101_, v_revArgs_3102_);
lean_dec_ref(v_revArgs_3102_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = lean_expr_dbg_to_string(v_e_3105_);
lean_dec_ref(v_e_3105_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_3109_, lean_object* v_b_3110_){
_start:
{
uint8_t v_res_3111_; lean_object* v_r_3112_; 
v_res_3111_ = lean_expr_quick_lt(v_a_3109_, v_b_3110_);
lean_dec_ref(v_b_3110_);
lean_dec_ref(v_a_3109_);
v_r_3112_ = lean_box(v_res_3111_);
return v_r_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_3115_, lean_object* v_b_3116_){
_start:
{
uint8_t v_res_3117_; lean_object* v_r_3118_; 
v_res_3117_ = lean_expr_lt(v_a_3115_, v_b_3116_);
lean_dec_ref(v_b_3116_);
lean_dec_ref(v_a_3115_);
v_r_3118_ = lean_box(v_res_3117_);
return v_r_3118_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* v_a_3119_, lean_object* v_b_3120_){
_start:
{
uint8_t v___x_3121_; 
v___x_3121_ = lean_expr_quick_lt(v_a_3119_, v_b_3120_);
if (v___x_3121_ == 0)
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_expr_quick_lt(v_b_3120_, v_a_3119_);
if (v___x_3122_ == 0)
{
uint8_t v___x_3123_; 
v___x_3123_ = 1;
return v___x_3123_;
}
else
{
uint8_t v___x_3124_; 
v___x_3124_ = 2;
return v___x_3124_;
}
}
else
{
uint8_t v___x_3125_; 
v___x_3125_ = 0;
return v___x_3125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_3126_, lean_object* v_b_3127_){
_start:
{
uint8_t v_res_3128_; lean_object* v_r_3129_; 
v_res_3128_ = l_Lean_Expr_quickComp(v_a_3126_, v_b_3127_);
lean_dec_ref(v_b_3127_);
lean_dec_ref(v_a_3126_);
v_r_3129_ = lean_box(v_res_3128_);
return v_r_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_3132_, lean_object* v_b_3133_){
_start:
{
uint8_t v_res_3134_; lean_object* v_r_3135_; 
v_res_3134_ = lean_expr_eqv(v_a_3132_, v_b_3133_);
lean_dec_ref(v_b_3133_);
lean_dec_ref(v_a_3132_);
v_r_3135_ = lean_box(v_res_3134_);
return v_r_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3140_, lean_object* v_b_3141_){
_start:
{
uint8_t v_res_3142_; lean_object* v_r_3143_; 
v_res_3142_ = lean_expr_equal(v_a_3140_, v_b_3141_);
lean_dec_ref(v_b_3141_);
lean_dec_ref(v_a_3140_);
v_r_3143_ = lean_box(v_res_3142_);
return v_r_3143_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* v_x_3144_){
_start:
{
if (lean_obj_tag(v_x_3144_) == 3)
{
uint8_t v___x_3145_; 
v___x_3145_ = 1;
return v___x_3145_;
}
else
{
uint8_t v___x_3146_; 
v___x_3146_ = 0;
return v___x_3146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3147_){
_start:
{
uint8_t v_res_3148_; lean_object* v_r_3149_; 
v_res_3148_ = l_Lean_Expr_isSort(v_x_3147_);
lean_dec_ref(v_x_3147_);
v_r_3149_ = lean_box(v_res_3148_);
return v_r_3149_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* v_x_3150_){
_start:
{
if (lean_obj_tag(v_x_3150_) == 3)
{
lean_object* v_u_3151_; 
v_u_3151_ = lean_ctor_get(v_x_3150_, 0);
if (lean_obj_tag(v_u_3151_) == 1)
{
uint8_t v___x_3152_; 
v___x_3152_ = 1;
return v___x_3152_;
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
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3155_){
_start:
{
uint8_t v_res_3156_; lean_object* v_r_3157_; 
v_res_3156_ = l_Lean_Expr_isType(v_x_3155_);
lean_dec_ref(v_x_3155_);
v_r_3157_ = lean_box(v_res_3156_);
return v_r_3157_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* v_x_3158_){
_start:
{
if (lean_obj_tag(v_x_3158_) == 3)
{
lean_object* v_u_3159_; 
v_u_3159_ = lean_ctor_get(v_x_3158_, 0);
if (lean_obj_tag(v_u_3159_) == 1)
{
lean_object* v_a_3160_; 
v_a_3160_ = lean_ctor_get(v_u_3159_, 0);
if (lean_obj_tag(v_a_3160_) == 0)
{
uint8_t v___x_3161_; 
v___x_3161_ = 1;
return v___x_3161_;
}
else
{
uint8_t v___x_3162_; 
v___x_3162_ = 0;
return v___x_3162_;
}
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
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3165_){
_start:
{
uint8_t v_res_3166_; lean_object* v_r_3167_; 
v_res_3166_ = l_Lean_Expr_isType0(v_x_3165_);
lean_dec_ref(v_x_3165_);
v_r_3167_ = lean_box(v_res_3166_);
return v_r_3167_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* v_x_3168_){
_start:
{
if (lean_obj_tag(v_x_3168_) == 3)
{
lean_object* v_u_3169_; 
v_u_3169_ = lean_ctor_get(v_x_3168_, 0);
if (lean_obj_tag(v_u_3169_) == 0)
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
else
{
uint8_t v___x_3172_; 
v___x_3172_ = 0;
return v___x_3172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3173_){
_start:
{
uint8_t v_res_3174_; lean_object* v_r_3175_; 
v_res_3174_ = l_Lean_Expr_isProp(v_x_3173_);
lean_dec_ref(v_x_3173_);
v_r_3175_ = lean_box(v_res_3174_);
return v_r_3175_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3176_){
_start:
{
if (lean_obj_tag(v_x_3176_) == 0)
{
uint8_t v___x_3177_; 
v___x_3177_ = 1;
return v___x_3177_;
}
else
{
uint8_t v___x_3178_; 
v___x_3178_ = 0;
return v___x_3178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3179_){
_start:
{
uint8_t v_res_3180_; lean_object* v_r_3181_; 
v_res_3180_ = l_Lean_Expr_isBVar(v_x_3179_);
lean_dec_ref(v_x_3179_);
v_r_3181_ = lean_box(v_res_3180_);
return v_r_3181_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3182_){
_start:
{
if (lean_obj_tag(v_x_3182_) == 2)
{
uint8_t v___x_3183_; 
v___x_3183_ = 1;
return v___x_3183_;
}
else
{
uint8_t v___x_3184_; 
v___x_3184_ = 0;
return v___x_3184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3185_){
_start:
{
uint8_t v_res_3186_; lean_object* v_r_3187_; 
v_res_3186_ = l_Lean_Expr_isMVar(v_x_3185_);
lean_dec_ref(v_x_3185_);
v_r_3187_ = lean_box(v_res_3186_);
return v_r_3187_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3188_){
_start:
{
if (lean_obj_tag(v_x_3188_) == 1)
{
uint8_t v___x_3189_; 
v___x_3189_ = 1;
return v___x_3189_;
}
else
{
uint8_t v___x_3190_; 
v___x_3190_ = 0;
return v___x_3190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3191_){
_start:
{
uint8_t v_res_3192_; lean_object* v_r_3193_; 
v_res_3192_ = l_Lean_Expr_isFVar(v_x_3191_);
lean_dec_ref(v_x_3191_);
v_r_3193_ = lean_box(v_res_3192_);
return v_r_3193_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* v_x_3194_){
_start:
{
if (lean_obj_tag(v_x_3194_) == 5)
{
uint8_t v___x_3195_; 
v___x_3195_ = 1;
return v___x_3195_;
}
else
{
uint8_t v___x_3196_; 
v___x_3196_ = 0;
return v___x_3196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3197_){
_start:
{
uint8_t v_res_3198_; lean_object* v_r_3199_; 
v_res_3198_ = l_Lean_Expr_isApp(v_x_3197_);
lean_dec_ref(v_x_3197_);
v_r_3199_ = lean_box(v_res_3198_);
return v_r_3199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* v_x_3200_){
_start:
{
if (lean_obj_tag(v_x_3200_) == 11)
{
uint8_t v___x_3201_; 
v___x_3201_ = 1;
return v___x_3201_;
}
else
{
uint8_t v___x_3202_; 
v___x_3202_ = 0;
return v___x_3202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3203_){
_start:
{
uint8_t v_res_3204_; lean_object* v_r_3205_; 
v_res_3204_ = l_Lean_Expr_isProj(v_x_3203_);
lean_dec_ref(v_x_3203_);
v_r_3205_ = lean_box(v_res_3204_);
return v_r_3205_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* v_x_3206_){
_start:
{
if (lean_obj_tag(v_x_3206_) == 4)
{
uint8_t v___x_3207_; 
v___x_3207_ = 1;
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
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3209_){
_start:
{
uint8_t v_res_3210_; lean_object* v_r_3211_; 
v_res_3210_ = l_Lean_Expr_isConst(v_x_3209_);
lean_dec_ref(v_x_3209_);
v_r_3211_ = lean_box(v_res_3210_);
return v_r_3211_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3212_, lean_object* v_x_3213_){
_start:
{
if (lean_obj_tag(v_x_3212_) == 4)
{
lean_object* v_declName_3214_; uint8_t v___x_3215_; 
v_declName_3214_ = lean_ctor_get(v_x_3212_, 0);
v___x_3215_ = lean_name_eq(v_declName_3214_, v_x_3213_);
return v___x_3215_;
}
else
{
uint8_t v___x_3216_; 
v___x_3216_ = 0;
return v___x_3216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3217_, lean_object* v_x_3218_){
_start:
{
uint8_t v_res_3219_; lean_object* v_r_3220_; 
v_res_3219_ = l_Lean_Expr_isConstOf(v_x_3217_, v_x_3218_);
lean_dec(v_x_3218_);
lean_dec_ref(v_x_3217_);
v_r_3220_ = lean_box(v_res_3219_);
return v_r_3220_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3221_, lean_object* v_x_3222_){
_start:
{
if (lean_obj_tag(v_x_3221_) == 1)
{
lean_object* v_fvarId_3223_; uint8_t v___x_3224_; 
v_fvarId_3223_ = lean_ctor_get(v_x_3221_, 0);
v___x_3224_ = lean_name_eq(v_fvarId_3223_, v_x_3222_);
return v___x_3224_;
}
else
{
uint8_t v___x_3225_; 
v___x_3225_ = 0;
return v___x_3225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3226_, lean_object* v_x_3227_){
_start:
{
uint8_t v_res_3228_; lean_object* v_r_3229_; 
v_res_3228_ = l_Lean_Expr_isFVarOf(v_x_3226_, v_x_3227_);
lean_dec(v_x_3227_);
lean_dec_ref(v_x_3226_);
v_r_3229_ = lean_box(v_res_3228_);
return v_r_3229_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* v_x_3230_){
_start:
{
if (lean_obj_tag(v_x_3230_) == 7)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3233_){
_start:
{
uint8_t v_res_3234_; lean_object* v_r_3235_; 
v_res_3234_ = l_Lean_Expr_isForall(v_x_3233_);
lean_dec_ref(v_x_3233_);
v_r_3235_ = lean_box(v_res_3234_);
return v_r_3235_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3236_){
_start:
{
if (lean_obj_tag(v_x_3236_) == 6)
{
uint8_t v___x_3237_; 
v___x_3237_ = 1;
return v___x_3237_;
}
else
{
uint8_t v___x_3238_; 
v___x_3238_ = 0;
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3239_){
_start:
{
uint8_t v_res_3240_; lean_object* v_r_3241_; 
v_res_3240_ = l_Lean_Expr_isLambda(v_x_3239_);
lean_dec_ref(v_x_3239_);
v_r_3241_ = lean_box(v_res_3240_);
return v_r_3241_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3242_){
_start:
{
switch(lean_obj_tag(v_x_3242_))
{
case 6:
{
uint8_t v___x_3243_; 
v___x_3243_ = 1;
return v___x_3243_;
}
case 7:
{
uint8_t v___x_3244_; 
v___x_3244_ = 1;
return v___x_3244_;
}
default: 
{
uint8_t v___x_3245_; 
v___x_3245_ = 0;
return v___x_3245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3246_){
_start:
{
uint8_t v_res_3247_; lean_object* v_r_3248_; 
v_res_3247_ = l_Lean_Expr_isBinding(v_x_3246_);
lean_dec_ref(v_x_3246_);
v_r_3248_ = lean_box(v_res_3247_);
return v_r_3248_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* v_x_3249_){
_start:
{
if (lean_obj_tag(v_x_3249_) == 8)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3252_){
_start:
{
uint8_t v_res_3253_; lean_object* v_r_3254_; 
v_res_3253_ = l_Lean_Expr_isLet(v_x_3252_);
lean_dec_ref(v_x_3252_);
v_r_3254_ = lean_box(v_res_3253_);
return v_r_3254_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object* v_x_3255_){
_start:
{
if (lean_obj_tag(v_x_3255_) == 8)
{
uint8_t v_nondep_3256_; 
v_nondep_3256_ = lean_ctor_get_uint8(v_x_3255_, sizeof(void*)*4 + 8);
return v_nondep_3256_;
}
else
{
uint8_t v___x_3257_; 
v___x_3257_ = 0;
return v___x_3257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3258_){
_start:
{
uint8_t v_res_3259_; lean_object* v_r_3260_; 
v_res_3259_ = l_Lean_Expr_isHave(v_x_3258_);
lean_dec_ref(v_x_3258_);
v_r_3260_ = lean_box(v_res_3259_);
return v_r_3260_;
}
}
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object* v_a_3261_){
_start:
{
uint8_t v___x_3262_; 
v___x_3262_ = l_Lean_Expr_isHave(v_a_3261_);
lean_dec_ref(v_a_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3263_){
_start:
{
uint8_t v_res_3264_; lean_object* v_r_3265_; 
v_res_3264_ = lean_expr_is_have(v_a_3263_);
v_r_3265_ = lean_box(v_res_3264_);
return v_r_3265_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* v_x_3266_){
_start:
{
if (lean_obj_tag(v_x_3266_) == 10)
{
uint8_t v___x_3267_; 
v___x_3267_ = 1;
return v___x_3267_;
}
else
{
uint8_t v___x_3268_; 
v___x_3268_ = 0;
return v___x_3268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3269_){
_start:
{
uint8_t v_res_3270_; lean_object* v_r_3271_; 
v_res_3270_ = l_Lean_Expr_isMData(v_x_3269_);
lean_dec_ref(v_x_3269_);
v_r_3271_ = lean_box(v_res_3270_);
return v_r_3271_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* v_x_3272_){
_start:
{
if (lean_obj_tag(v_x_3272_) == 9)
{
uint8_t v___x_3273_; 
v___x_3273_ = 1;
return v___x_3273_;
}
else
{
uint8_t v___x_3274_; 
v___x_3274_ = 0;
return v___x_3274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3275_){
_start:
{
uint8_t v_res_3276_; lean_object* v_r_3277_; 
v_res_3276_ = l_Lean_Expr_isLit(v_x_3275_);
lean_dec_ref(v_x_3275_);
v_r_3277_ = lean_box(v_res_3276_);
return v_r_3277_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3278_){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = l_Lean_instInhabitedExpr;
v___x_3280_ = lean_panic_fn_borrowed(v___x_3279_, v_msg_3278_);
return v___x_3280_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3284_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3285_ = lean_unsigned_to_nat(15u);
v___x_3286_ = lean_unsigned_to_nat(931u);
v___x_3287_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3288_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3289_ = l_mkPanicMessageWithDecl(v___x_3288_, v___x_3287_, v___x_3286_, v___x_3285_, v___x_3284_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3290_){
_start:
{
if (lean_obj_tag(v_x_3290_) == 5)
{
lean_object* v_fn_3291_; 
v_fn_3291_ = lean_ctor_get(v_x_3290_, 0);
lean_inc_ref(v_fn_3291_);
return v_fn_3291_;
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3293_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3292_);
return v___x_3293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Lean_Expr_appFn_x21(v_x_3294_);
lean_dec_ref(v_x_3294_);
return v_res_3295_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3297_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3298_ = lean_unsigned_to_nat(15u);
v___x_3299_ = lean_unsigned_to_nat(935u);
v___x_3300_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3301_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3302_ = l_mkPanicMessageWithDecl(v___x_3301_, v___x_3300_, v___x_3299_, v___x_3298_, v___x_3297_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3303_){
_start:
{
if (lean_obj_tag(v_x_3303_) == 5)
{
lean_object* v_arg_3304_; 
v_arg_3304_ = lean_ctor_get(v_x_3303_, 1);
lean_inc_ref(v_arg_3304_);
return v_arg_3304_;
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3306_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3305_);
return v___x_3306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_Expr_appArg_x21(v_x_3307_);
lean_dec_ref(v_x_3307_);
return v_res_3308_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3310_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3311_ = lean_unsigned_to_nat(17u);
v___x_3312_ = lean_unsigned_to_nat(940u);
v___x_3313_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3314_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3315_ = l_mkPanicMessageWithDecl(v___x_3314_, v___x_3313_, v___x_3312_, v___x_3311_, v___x_3310_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3316_){
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
lean_object* v_fn_3319_; 
v_fn_3319_ = lean_ctor_get(v_x_3316_, 0);
lean_inc_ref(v_fn_3319_);
return v_fn_3319_;
}
default: 
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3320_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3321_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3320_);
return v___x_3321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_Expr_appFn_x21_x27(v_x_3322_);
lean_dec_ref(v_x_3322_);
return v_res_3323_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3325_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3326_ = lean_unsigned_to_nat(17u);
v___x_3327_ = lean_unsigned_to_nat(945u);
v___x_3328_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3329_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3330_ = l_mkPanicMessageWithDecl(v___x_3329_, v___x_3328_, v___x_3327_, v___x_3326_, v___x_3325_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3331_){
_start:
{
switch(lean_obj_tag(v_x_3331_))
{
case 10:
{
lean_object* v_expr_3332_; 
v_expr_3332_ = lean_ctor_get(v_x_3331_, 1);
v_x_3331_ = v_expr_3332_;
goto _start;
}
case 5:
{
lean_object* v_arg_3334_; 
v_arg_3334_ = lean_ctor_get(v_x_3331_, 1);
lean_inc_ref(v_arg_3334_);
return v_arg_3334_;
}
default: 
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3336_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3335_);
return v___x_3336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Lean_Expr_appArg_x21_x27(v_x_3337_);
lean_dec_ref(v_x_3337_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3339_){
_start:
{
lean_object* v_arg_3340_; 
v_arg_3340_ = lean_ctor_get(v_e_3339_, 1);
lean_inc_ref(v_arg_3340_);
return v_arg_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Expr_appArg___redArg(v_e_3341_);
lean_dec_ref(v_e_3341_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3343_, lean_object* v_h_3344_){
_start:
{
lean_object* v_arg_3345_; 
v_arg_3345_ = lean_ctor_get(v_e_3343_, 1);
lean_inc_ref(v_arg_3345_);
return v_arg_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3346_, lean_object* v_h_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_Expr_appArg(v_e_3346_, v_h_3347_);
lean_dec_ref(v_e_3346_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3349_){
_start:
{
lean_object* v_fn_3350_; 
v_fn_3350_ = lean_ctor_get(v_e_3349_, 0);
lean_inc_ref(v_fn_3350_);
return v_fn_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_Expr_appFn___redArg(v_e_3351_);
lean_dec_ref(v_e_3351_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3353_, lean_object* v_h_3354_){
_start:
{
lean_object* v_fn_3355_; 
v_fn_3355_ = lean_ctor_get(v_e_3353_, 0);
lean_inc_ref(v_fn_3355_);
return v_fn_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3356_, lean_object* v_h_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_Expr_appFn(v_e_3356_, v_h_3357_);
lean_dec_ref(v_e_3356_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3359_){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = lean_box(0);
v___x_3361_ = lean_panic_fn_borrowed(v___x_3360_, v_msg_3359_);
return v___x_3361_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3364_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3365_ = lean_unsigned_to_nat(14u);
v___x_3366_ = lean_unsigned_to_nat(957u);
v___x_3367_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3368_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3369_ = l_mkPanicMessageWithDecl(v___x_3368_, v___x_3367_, v___x_3366_, v___x_3365_, v___x_3364_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3370_){
_start:
{
if (lean_obj_tag(v_x_3370_) == 3)
{
lean_object* v_u_3371_; 
v_u_3371_ = lean_ctor_get(v_x_3370_, 0);
lean_inc(v_u_3371_);
return v_u_3371_;
}
else
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3373_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3372_);
return v___x_3373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Lean_Expr_sortLevel_x21(v_x_3374_);
lean_dec_ref(v_x_3374_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3376_){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3378_ = lean_panic_fn_borrowed(v___x_3377_, v_msg_3376_);
return v___x_3378_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3381_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3382_ = lean_unsigned_to_nat(13u);
v___x_3383_ = lean_unsigned_to_nat(961u);
v___x_3384_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3385_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3386_ = l_mkPanicMessageWithDecl(v___x_3385_, v___x_3384_, v___x_3383_, v___x_3382_, v___x_3381_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3387_){
_start:
{
if (lean_obj_tag(v_x_3387_) == 9)
{
lean_object* v_a_3388_; 
v_a_3388_ = lean_ctor_get(v_x_3387_, 0);
lean_inc_ref(v_a_3388_);
return v_a_3388_;
}
else
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3390_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3389_);
return v___x_3390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_Expr_litValue_x21(v_x_3391_);
lean_dec_ref(v_x_3391_);
return v_res_3392_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3393_){
_start:
{
if (lean_obj_tag(v_x_3393_) == 9)
{
lean_object* v_a_3394_; 
v_a_3394_ = lean_ctor_get(v_x_3393_, 0);
if (lean_obj_tag(v_a_3394_) == 0)
{
uint8_t v___x_3395_; 
v___x_3395_ = 1;
return v___x_3395_;
}
else
{
uint8_t v___x_3396_; 
v___x_3396_ = 0;
return v___x_3396_;
}
}
else
{
uint8_t v___x_3397_; 
v___x_3397_ = 0;
return v___x_3397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3398_){
_start:
{
uint8_t v_res_3399_; lean_object* v_r_3400_; 
v_res_3399_ = l_Lean_Expr_isRawNatLit(v_x_3398_);
lean_dec_ref(v_x_3398_);
v_r_3400_ = lean_box(v_res_3399_);
return v_r_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3401_){
_start:
{
if (lean_obj_tag(v_x_3401_) == 9)
{
lean_object* v_a_3402_; 
v_a_3402_ = lean_ctor_get(v_x_3401_, 0);
lean_inc_ref(v_a_3402_);
lean_dec_ref_known(v_x_3401_, 1);
if (lean_obj_tag(v_a_3402_) == 0)
{
lean_object* v_val_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
v_val_3403_ = lean_ctor_get(v_a_3402_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v_a_3402_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v_a_3402_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_val_3403_);
lean_dec(v_a_3402_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
lean_ctor_set_tag(v___x_3405_, 1);
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_val_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
else
{
lean_object* v___x_3411_; 
lean_dec_ref(v_a_3402_);
v___x_3411_ = lean_box(0);
return v___x_3411_;
}
}
else
{
lean_object* v___x_3412_; 
lean_dec_ref(v_x_3401_);
v___x_3412_ = lean_box(0);
return v___x_3412_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3413_){
_start:
{
if (lean_obj_tag(v_x_3413_) == 9)
{
lean_object* v_a_3414_; 
v_a_3414_ = lean_ctor_get(v_x_3413_, 0);
if (lean_obj_tag(v_a_3414_) == 1)
{
uint8_t v___x_3415_; 
v___x_3415_ = 1;
return v___x_3415_;
}
else
{
uint8_t v___x_3416_; 
v___x_3416_ = 0;
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3418_){
_start:
{
uint8_t v_res_3419_; lean_object* v_r_3420_; 
v_res_3419_ = l_Lean_Expr_isStringLit(v_x_3418_);
lean_dec_ref(v_x_3418_);
v_r_3420_ = lean_box(v_res_3419_);
return v_r_3420_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3425_){
_start:
{
if (lean_obj_tag(v_x_3425_) == 5)
{
lean_object* v_fn_3426_; 
v_fn_3426_ = lean_ctor_get(v_x_3425_, 0);
if (lean_obj_tag(v_fn_3426_) == 4)
{
lean_object* v_arg_3427_; lean_object* v_declName_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; 
v_arg_3427_ = lean_ctor_get(v_x_3425_, 1);
v_declName_3428_ = lean_ctor_get(v_fn_3426_, 0);
v___x_3429_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3430_ = lean_name_eq(v_declName_3428_, v___x_3429_);
if (v___x_3430_ == 0)
{
return v___x_3430_;
}
else
{
uint8_t v___x_3431_; 
v___x_3431_ = l_Lean_Expr_isRawNatLit(v_arg_3427_);
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
else
{
uint8_t v___x_3433_; 
v___x_3433_ = 0;
return v___x_3433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3434_){
_start:
{
uint8_t v_res_3435_; lean_object* v_r_3436_; 
v_res_3435_ = l_Lean_Expr_isCharLit(v_x_3434_);
lean_dec_ref(v_x_3434_);
v_r_3436_ = lean_box(v_res_3435_);
return v_r_3436_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3437_){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = lean_box(0);
v___x_3439_ = lean_panic_fn_borrowed(v___x_3438_, v_msg_3437_);
return v___x_3439_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3442_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3443_ = lean_unsigned_to_nat(17u);
v___x_3444_ = lean_unsigned_to_nat(985u);
v___x_3445_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3446_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3447_ = l_mkPanicMessageWithDecl(v___x_3446_, v___x_3445_, v___x_3444_, v___x_3443_, v___x_3442_);
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3448_){
_start:
{
if (lean_obj_tag(v_x_3448_) == 4)
{
lean_object* v_declName_3449_; 
v_declName_3449_ = lean_ctor_get(v_x_3448_, 0);
lean_inc(v_declName_3449_);
return v_declName_3449_;
}
else
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3451_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3450_);
return v___x_3451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l_Lean_Expr_constName_x21(v_x_3452_);
lean_dec_ref(v_x_3452_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3454_){
_start:
{
if (lean_obj_tag(v_x_3454_) == 4)
{
lean_object* v_declName_3455_; lean_object* v___x_3456_; 
v_declName_3455_ = lean_ctor_get(v_x_3454_, 0);
lean_inc(v_declName_3455_);
v___x_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3456_, 0, v_declName_3455_);
return v___x_3456_;
}
else
{
lean_object* v___x_3457_; 
v___x_3457_ = lean_box(0);
return v___x_3457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_Expr_constName_x3f(v_x_3458_);
lean_dec_ref(v_x_3458_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3460_){
_start:
{
lean_object* v___x_3461_; 
v___x_3461_ = l_Lean_Expr_constName_x3f(v_e_3460_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v___x_3462_; 
v___x_3462_ = lean_box(0);
return v___x_3462_;
}
else
{
lean_object* v_val_3463_; 
v_val_3463_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_val_3463_);
lean_dec_ref_known(v___x_3461_, 1);
return v_val_3463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Lean_Expr_constName(v_e_3464_);
lean_dec_ref(v_e_3464_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3466_){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3467_ = lean_box(0);
v___x_3468_ = lean_panic_fn_borrowed(v___x_3467_, v_msg_3466_);
return v___x_3468_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3470_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3471_ = lean_unsigned_to_nat(18u);
v___x_3472_ = lean_unsigned_to_nat(1005u);
v___x_3473_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3474_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3475_ = l_mkPanicMessageWithDecl(v___x_3474_, v___x_3473_, v___x_3472_, v___x_3471_, v___x_3470_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3476_){
_start:
{
if (lean_obj_tag(v_x_3476_) == 4)
{
lean_object* v_us_3477_; 
v_us_3477_ = lean_ctor_get(v_x_3476_, 1);
lean_inc(v_us_3477_);
return v_us_3477_;
}
else
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3478_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3479_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3478_);
return v___x_3479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_Expr_constLevels_x21(v_x_3480_);
lean_dec_ref(v_x_3480_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3482_){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = lean_unsigned_to_nat(0u);
v___x_3484_ = lean_panic_fn_borrowed(v___x_3483_, v_msg_3482_);
return v___x_3484_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3487_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3488_ = lean_unsigned_to_nat(16u);
v___x_3489_ = lean_unsigned_to_nat(1009u);
v___x_3490_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3491_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3492_ = l_mkPanicMessageWithDecl(v___x_3491_, v___x_3490_, v___x_3489_, v___x_3488_, v___x_3487_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3493_){
_start:
{
if (lean_obj_tag(v_x_3493_) == 0)
{
lean_object* v_deBruijnIndex_3494_; 
v_deBruijnIndex_3494_ = lean_ctor_get(v_x_3493_, 0);
lean_inc(v_deBruijnIndex_3494_);
return v_deBruijnIndex_3494_;
}
else
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3496_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3495_);
return v___x_3496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Lean_Expr_bvarIdx_x21(v_x_3497_);
lean_dec_ref(v_x_3497_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3499_){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = lean_box(0);
v___x_3501_ = lean_panic_fn_borrowed(v___x_3500_, v_msg_3499_);
return v___x_3501_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3504_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3505_ = lean_unsigned_to_nat(14u);
v___x_3506_ = lean_unsigned_to_nat(1013u);
v___x_3507_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3508_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3509_ = l_mkPanicMessageWithDecl(v___x_3508_, v___x_3507_, v___x_3506_, v___x_3505_, v___x_3504_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3510_){
_start:
{
if (lean_obj_tag(v_x_3510_) == 1)
{
lean_object* v_fvarId_3511_; 
v_fvarId_3511_ = lean_ctor_get(v_x_3510_, 0);
lean_inc(v_fvarId_3511_);
return v_fvarId_3511_;
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3512_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3513_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3512_);
return v___x_3513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Lean_Expr_fvarId_x21(v_x_3514_);
lean_dec_ref(v_x_3514_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3516_){
_start:
{
if (lean_obj_tag(v_x_3516_) == 1)
{
lean_object* v_fvarId_3517_; lean_object* v___x_3518_; 
v_fvarId_3517_ = lean_ctor_get(v_x_3516_, 0);
lean_inc(v_fvarId_3517_);
v___x_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3518_, 0, v_fvarId_3517_);
return v___x_3518_;
}
else
{
lean_object* v___x_3519_; 
v___x_3519_ = lean_box(0);
return v___x_3519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_Expr_fvarId_x3f(v_x_3520_);
lean_dec_ref(v_x_3520_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3522_){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3523_ = lean_box(0);
v___x_3524_ = lean_panic_fn_borrowed(v___x_3523_, v_msg_3522_);
return v___x_3524_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3527_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3528_ = lean_unsigned_to_nat(14u);
v___x_3529_ = lean_unsigned_to_nat(1021u);
v___x_3530_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3531_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3532_ = l_mkPanicMessageWithDecl(v___x_3531_, v___x_3530_, v___x_3529_, v___x_3528_, v___x_3527_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3533_){
_start:
{
if (lean_obj_tag(v_x_3533_) == 2)
{
lean_object* v_mvarId_3534_; 
v_mvarId_3534_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_mvarId_3534_);
return v_mvarId_3534_;
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3536_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3535_);
return v___x_3536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Lean_Expr_mvarId_x21(v_x_3537_);
lean_dec_ref(v_x_3537_);
return v_res_3538_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3541_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3542_ = lean_unsigned_to_nat(23u);
v___x_3543_ = lean_unsigned_to_nat(1026u);
v___x_3544_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3545_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3546_ = l_mkPanicMessageWithDecl(v___x_3545_, v___x_3544_, v___x_3543_, v___x_3542_, v___x_3541_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3547_){
_start:
{
switch(lean_obj_tag(v_x_3547_))
{
case 7:
{
lean_object* v_binderName_3548_; 
v_binderName_3548_ = lean_ctor_get(v_x_3547_, 0);
lean_inc(v_binderName_3548_);
return v_binderName_3548_;
}
case 6:
{
lean_object* v_binderName_3549_; 
v_binderName_3549_ = lean_ctor_get(v_x_3547_, 0);
lean_inc(v_binderName_3549_);
return v_binderName_3549_;
}
default: 
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3551_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3550_);
return v___x_3551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_Expr_bindingName_x21(v_x_3552_);
lean_dec_ref(v_x_3552_);
return v_res_3553_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3555_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3556_ = lean_unsigned_to_nat(23u);
v___x_3557_ = lean_unsigned_to_nat(1031u);
v___x_3558_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3559_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3560_ = l_mkPanicMessageWithDecl(v___x_3559_, v___x_3558_, v___x_3557_, v___x_3556_, v___x_3555_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3561_){
_start:
{
switch(lean_obj_tag(v_x_3561_))
{
case 7:
{
lean_object* v_binderType_3562_; 
v_binderType_3562_ = lean_ctor_get(v_x_3561_, 1);
lean_inc_ref(v_binderType_3562_);
return v_binderType_3562_;
}
case 6:
{
lean_object* v_binderType_3563_; 
v_binderType_3563_ = lean_ctor_get(v_x_3561_, 1);
lean_inc_ref(v_binderType_3563_);
return v_binderType_3563_;
}
default: 
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3565_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3564_);
return v___x_3565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_Expr_bindingDomain_x21(v_x_3566_);
lean_dec_ref(v_x_3566_);
return v_res_3567_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3569_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3570_ = lean_unsigned_to_nat(23u);
v___x_3571_ = lean_unsigned_to_nat(1036u);
v___x_3572_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3573_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3574_ = l_mkPanicMessageWithDecl(v___x_3573_, v___x_3572_, v___x_3571_, v___x_3570_, v___x_3569_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3575_){
_start:
{
switch(lean_obj_tag(v_x_3575_))
{
case 7:
{
lean_object* v_body_3576_; 
v_body_3576_ = lean_ctor_get(v_x_3575_, 2);
lean_inc_ref(v_body_3576_);
return v_body_3576_;
}
case 6:
{
lean_object* v_body_3577_; 
v_body_3577_ = lean_ctor_get(v_x_3575_, 2);
lean_inc_ref(v_body_3577_);
return v_body_3577_;
}
default: 
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3579_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3578_);
return v___x_3579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Lean_Expr_bindingBody_x21(v_x_3580_);
lean_dec_ref(v_x_3580_);
return v_res_3581_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3582_){
_start:
{
uint8_t v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; 
v___x_3583_ = 0;
v___x_3584_ = lean_box(v___x_3583_);
v___x_3585_ = lean_panic_fn_borrowed(v___x_3584_, v_msg_3582_);
lean_dec(v___x_3584_);
v___x_3586_ = lean_unbox(v___x_3585_);
lean_dec(v___x_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3587_){
_start:
{
uint8_t v_res_3588_; lean_object* v_r_3589_; 
v_res_3588_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3587_);
v_r_3589_ = lean_box(v_res_3588_);
return v_r_3589_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3591_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3592_ = lean_unsigned_to_nat(24u);
v___x_3593_ = lean_unsigned_to_nat(1041u);
v___x_3594_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3595_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3596_ = l_mkPanicMessageWithDecl(v___x_3595_, v___x_3594_, v___x_3593_, v___x_3592_, v___x_3591_);
return v___x_3596_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3597_){
_start:
{
switch(lean_obj_tag(v_x_3597_))
{
case 7:
{
uint8_t v_binderInfo_3598_; 
v_binderInfo_3598_ = lean_ctor_get_uint8(v_x_3597_, sizeof(void*)*3 + 8);
return v_binderInfo_3598_;
}
case 6:
{
uint8_t v_binderInfo_3599_; 
v_binderInfo_3599_ = lean_ctor_get_uint8(v_x_3597_, sizeof(void*)*3 + 8);
return v_binderInfo_3599_;
}
default: 
{
lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3600_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3601_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3600_);
return v___x_3601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3602_){
_start:
{
uint8_t v_res_3603_; lean_object* v_r_3604_; 
v_res_3603_ = l_Lean_Expr_bindingInfo_x21(v_x_3602_);
lean_dec_ref(v_x_3602_);
v_r_3604_ = lean_box(v_res_3603_);
return v_r_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3605_){
_start:
{
lean_object* v_binderName_3606_; 
v_binderName_3606_ = lean_ctor_get(v_x_3605_, 0);
lean_inc(v_binderName_3606_);
return v_binderName_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Lean_Expr_forallName___redArg(v_x_3607_);
lean_dec_ref(v_x_3607_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3609_, lean_object* v_x_3610_){
_start:
{
lean_object* v_binderName_3611_; 
v_binderName_3611_ = lean_ctor_get(v_x_3609_, 0);
lean_inc(v_binderName_3611_);
return v_binderName_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3612_, lean_object* v_x_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Lean_Expr_forallName(v_x_3612_, v_x_3613_);
lean_dec_ref(v_x_3612_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3615_){
_start:
{
lean_object* v_binderType_3616_; 
v_binderType_3616_ = lean_ctor_get(v_x_3615_, 1);
lean_inc_ref(v_binderType_3616_);
return v_binderType_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Lean_Expr_forallDomain___redArg(v_x_3617_);
lean_dec_ref(v_x_3617_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3619_, lean_object* v_x_3620_){
_start:
{
lean_object* v_binderType_3621_; 
v_binderType_3621_ = lean_ctor_get(v_x_3619_, 1);
lean_inc_ref(v_binderType_3621_);
return v_binderType_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3622_, lean_object* v_x_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_Expr_forallDomain(v_x_3622_, v_x_3623_);
lean_dec_ref(v_x_3622_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3625_){
_start:
{
lean_object* v_body_3626_; 
v_body_3626_ = lean_ctor_get(v_x_3625_, 2);
lean_inc_ref(v_body_3626_);
return v_body_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Expr_forallBody___redArg(v_x_3627_);
lean_dec_ref(v_x_3627_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3629_, lean_object* v_x_3630_){
_start:
{
lean_object* v_body_3631_; 
v_body_3631_ = lean_ctor_get(v_x_3629_, 2);
lean_inc_ref(v_body_3631_);
return v_body_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3632_, lean_object* v_x_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_Lean_Expr_forallBody(v_x_3632_, v_x_3633_);
lean_dec_ref(v_x_3632_);
return v_res_3634_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3635_){
_start:
{
uint8_t v_binderInfo_3636_; 
v_binderInfo_3636_ = lean_ctor_get_uint8(v_x_3635_, sizeof(void*)*3 + 8);
return v_binderInfo_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3637_){
_start:
{
uint8_t v_res_3638_; lean_object* v_r_3639_; 
v_res_3638_ = l_Lean_Expr_forallInfo___redArg(v_x_3637_);
lean_dec_ref(v_x_3637_);
v_r_3639_ = lean_box(v_res_3638_);
return v_r_3639_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3640_, lean_object* v_x_3641_){
_start:
{
uint8_t v_binderInfo_3642_; 
v_binderInfo_3642_ = lean_ctor_get_uint8(v_x_3640_, sizeof(void*)*3 + 8);
return v_binderInfo_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3643_, lean_object* v_x_3644_){
_start:
{
uint8_t v_res_3645_; lean_object* v_r_3646_; 
v_res_3645_ = l_Lean_Expr_forallInfo(v_x_3643_, v_x_3644_);
lean_dec_ref(v_x_3643_);
v_r_3646_ = lean_box(v_res_3645_);
return v_r_3646_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3649_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3650_ = lean_unsigned_to_nat(17u);
v___x_3651_ = lean_unsigned_to_nat(1057u);
v___x_3652_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3653_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3654_ = l_mkPanicMessageWithDecl(v___x_3653_, v___x_3652_, v___x_3651_, v___x_3650_, v___x_3649_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3655_){
_start:
{
if (lean_obj_tag(v_x_3655_) == 8)
{
lean_object* v_declName_3656_; 
v_declName_3656_ = lean_ctor_get(v_x_3655_, 0);
lean_inc(v_declName_3656_);
return v_declName_3656_;
}
else
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3658_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3657_);
return v___x_3658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l_Lean_Expr_letName_x21(v_x_3659_);
lean_dec_ref(v_x_3659_);
return v_res_3660_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3662_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3663_ = lean_unsigned_to_nat(19u);
v___x_3664_ = lean_unsigned_to_nat(1061u);
v___x_3665_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3666_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3667_ = l_mkPanicMessageWithDecl(v___x_3666_, v___x_3665_, v___x_3664_, v___x_3663_, v___x_3662_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3668_){
_start:
{
if (lean_obj_tag(v_x_3668_) == 8)
{
lean_object* v_type_3669_; 
v_type_3669_ = lean_ctor_get(v_x_3668_, 1);
lean_inc_ref(v_type_3669_);
return v_type_3669_;
}
else
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3671_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3670_);
return v___x_3671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l_Lean_Expr_letType_x21(v_x_3672_);
lean_dec_ref(v_x_3672_);
return v_res_3673_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3675_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3676_ = lean_unsigned_to_nat(21u);
v___x_3677_ = lean_unsigned_to_nat(1065u);
v___x_3678_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3679_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3680_ = l_mkPanicMessageWithDecl(v___x_3679_, v___x_3678_, v___x_3677_, v___x_3676_, v___x_3675_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3681_){
_start:
{
if (lean_obj_tag(v_x_3681_) == 8)
{
lean_object* v_value_3682_; 
v_value_3682_ = lean_ctor_get(v_x_3681_, 2);
lean_inc_ref(v_value_3682_);
return v_value_3682_;
}
else
{
lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3683_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3684_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3683_);
return v___x_3684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_Lean_Expr_letValue_x21(v_x_3685_);
lean_dec_ref(v_x_3685_);
return v_res_3686_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3688_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3689_ = lean_unsigned_to_nat(23u);
v___x_3690_ = lean_unsigned_to_nat(1069u);
v___x_3691_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3692_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3693_ = l_mkPanicMessageWithDecl(v___x_3692_, v___x_3691_, v___x_3690_, v___x_3689_, v___x_3688_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3694_){
_start:
{
if (lean_obj_tag(v_x_3694_) == 8)
{
lean_object* v_body_3695_; 
v_body_3695_ = lean_ctor_get(v_x_3694_, 3);
lean_inc_ref(v_body_3695_);
return v_body_3695_;
}
else
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3696_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3697_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3696_);
return v___x_3697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Lean_Expr_letBody_x21(v_x_3698_);
lean_dec_ref(v_x_3698_);
return v_res_3699_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3700_){
_start:
{
uint8_t v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; 
v___x_3701_ = 0;
v___x_3702_ = lean_box(v___x_3701_);
v___x_3703_ = lean_panic_fn_borrowed(v___x_3702_, v_msg_3700_);
lean_dec(v___x_3702_);
v___x_3704_ = lean_unbox(v___x_3703_);
lean_dec(v___x_3703_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3705_){
_start:
{
uint8_t v_res_3706_; lean_object* v_r_3707_; 
v_res_3706_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3705_);
v_r_3707_ = lean_box(v_res_3706_);
return v_r_3707_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3709_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3710_ = lean_unsigned_to_nat(27u);
v___x_3711_ = lean_unsigned_to_nat(1073u);
v___x_3712_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3713_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3714_ = l_mkPanicMessageWithDecl(v___x_3713_, v___x_3712_, v___x_3711_, v___x_3710_, v___x_3709_);
return v___x_3714_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3715_){
_start:
{
if (lean_obj_tag(v_x_3715_) == 8)
{
uint8_t v_nondep_3716_; 
v_nondep_3716_ = lean_ctor_get_uint8(v_x_3715_, sizeof(void*)*4 + 8);
return v_nondep_3716_;
}
else
{
lean_object* v___x_3717_; uint8_t v___x_3718_; 
v___x_3717_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3718_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3717_);
return v___x_3718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3719_){
_start:
{
uint8_t v_res_3720_; lean_object* v_r_3721_; 
v_res_3720_ = l_Lean_Expr_letNondep_x21(v_x_3719_);
lean_dec_ref(v_x_3719_);
v_r_3721_ = lean_box(v_res_3720_);
return v_r_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3722_){
_start:
{
if (lean_obj_tag(v_x_3722_) == 10)
{
lean_object* v_expr_3723_; 
v_expr_3723_ = lean_ctor_get(v_x_3722_, 1);
v_x_3722_ = v_expr_3723_;
goto _start;
}
else
{
lean_inc_ref(v_x_3722_);
return v_x_3722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_Expr_consumeMData(v_x_3725_);
lean_dec_ref(v_x_3725_);
return v_res_3726_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3729_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3730_ = lean_unsigned_to_nat(17u);
v___x_3731_ = lean_unsigned_to_nat(1081u);
v___x_3732_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3733_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3734_ = l_mkPanicMessageWithDecl(v___x_3733_, v___x_3732_, v___x_3731_, v___x_3730_, v___x_3729_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3735_){
_start:
{
if (lean_obj_tag(v_x_3735_) == 10)
{
lean_object* v_expr_3736_; 
v_expr_3736_ = lean_ctor_get(v_x_3735_, 1);
lean_inc_ref(v_expr_3736_);
return v_expr_3736_;
}
else
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3737_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3738_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3737_);
return v___x_3738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_Expr_mdataExpr_x21(v_x_3739_);
lean_dec_ref(v_x_3739_);
return v_res_3740_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3743_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3744_ = lean_unsigned_to_nat(18u);
v___x_3745_ = lean_unsigned_to_nat(1085u);
v___x_3746_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3747_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3748_ = l_mkPanicMessageWithDecl(v___x_3747_, v___x_3746_, v___x_3745_, v___x_3744_, v___x_3743_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3749_){
_start:
{
if (lean_obj_tag(v_x_3749_) == 11)
{
lean_object* v_struct_3750_; 
v_struct_3750_ = lean_ctor_get(v_x_3749_, 2);
lean_inc_ref(v_struct_3750_);
return v_struct_3750_;
}
else
{
lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3751_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3752_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3751_);
return v___x_3752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l_Lean_Expr_projExpr_x21(v_x_3753_);
lean_dec_ref(v_x_3753_);
return v_res_3754_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3756_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3757_ = lean_unsigned_to_nat(18u);
v___x_3758_ = lean_unsigned_to_nat(1089u);
v___x_3759_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3760_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3761_ = l_mkPanicMessageWithDecl(v___x_3760_, v___x_3759_, v___x_3758_, v___x_3757_, v___x_3756_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3762_){
_start:
{
if (lean_obj_tag(v_x_3762_) == 11)
{
lean_object* v_idx_3763_; 
v_idx_3763_ = lean_ctor_get(v_x_3762_, 1);
lean_inc(v_idx_3763_);
return v_idx_3763_;
}
else
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3764_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3765_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3764_);
return v___x_3765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_Expr_projIdx_x21(v_x_3766_);
lean_dec_ref(v_x_3766_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3768_){
_start:
{
if (lean_obj_tag(v_x_3768_) == 7)
{
lean_object* v_body_3769_; 
v_body_3769_ = lean_ctor_get(v_x_3768_, 2);
v_x_3768_ = v_body_3769_;
goto _start;
}
else
{
lean_inc_ref(v_x_3768_);
return v_x_3768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_Expr_getForallBody(v_x_3771_);
lean_dec_ref(v_x_3771_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3773_, lean_object* v_x_3774_){
_start:
{
lean_object* v_zero_3775_; uint8_t v_isZero_3776_; 
v_zero_3775_ = lean_unsigned_to_nat(0u);
v_isZero_3776_ = lean_nat_dec_eq(v_x_3773_, v_zero_3775_);
if (v_isZero_3776_ == 1)
{
lean_dec(v_x_3773_);
lean_inc_ref(v_x_3774_);
return v_x_3774_;
}
else
{
if (lean_obj_tag(v_x_3774_) == 7)
{
lean_object* v_body_3777_; lean_object* v_one_3778_; lean_object* v_n_3779_; 
v_body_3777_ = lean_ctor_get(v_x_3774_, 2);
v_one_3778_ = lean_unsigned_to_nat(1u);
v_n_3779_ = lean_nat_sub(v_x_3773_, v_one_3778_);
lean_dec(v_x_3773_);
v_x_3773_ = v_n_3779_;
v_x_3774_ = v_body_3777_;
goto _start;
}
else
{
lean_dec(v_x_3773_);
lean_inc_ref(v_x_3774_);
return v_x_3774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3781_, lean_object* v_x_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3781_, v_x_3782_);
lean_dec_ref(v_x_3782_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3784_){
_start:
{
if (lean_obj_tag(v_x_3784_) == 7)
{
lean_object* v_binderName_3785_; lean_object* v_body_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v_binderName_3785_ = lean_ctor_get(v_x_3784_, 0);
v_body_3786_ = lean_ctor_get(v_x_3784_, 2);
v___x_3787_ = l_Lean_Expr_getForallBinderNames(v_body_3786_);
lean_inc(v_binderName_3785_);
v___x_3788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3788_, 0, v_binderName_3785_);
lean_ctor_set(v___x_3788_, 1, v___x_3787_);
return v___x_3788_;
}
else
{
lean_object* v___x_3789_; 
v___x_3789_ = lean_box(0);
return v___x_3789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l_Lean_Expr_getForallBinderNames(v_x_3790_);
lean_dec_ref(v_x_3790_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3792_){
_start:
{
switch(lean_obj_tag(v_x_3792_))
{
case 10:
{
lean_object* v_expr_3793_; 
v_expr_3793_ = lean_ctor_get(v_x_3792_, 1);
v_x_3792_ = v_expr_3793_;
goto _start;
}
case 7:
{
lean_object* v_body_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v_body_3795_ = lean_ctor_get(v_x_3792_, 2);
v___x_3796_ = l_Lean_Expr_getNumHeadForalls(v_body_3795_);
v___x_3797_ = lean_unsigned_to_nat(1u);
v___x_3798_ = lean_nat_add(v___x_3796_, v___x_3797_);
lean_dec(v___x_3796_);
return v___x_3798_;
}
default: 
{
lean_object* v___x_3799_; 
v___x_3799_ = lean_unsigned_to_nat(0u);
return v___x_3799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_Expr_getNumHeadForalls(v_x_3800_);
lean_dec_ref(v_x_3800_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3802_){
_start:
{
if (lean_obj_tag(v_x_3802_) == 5)
{
lean_object* v_fn_3803_; 
v_fn_3803_ = lean_ctor_get(v_x_3802_, 0);
v_x_3802_ = v_fn_3803_;
goto _start;
}
else
{
lean_inc_ref(v_x_3802_);
return v_x_3802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Lean_Expr_getAppFn(v_x_3805_);
lean_dec_ref(v_x_3805_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3807_){
_start:
{
switch(lean_obj_tag(v_x_3807_))
{
case 5:
{
lean_object* v_fn_3808_; 
v_fn_3808_ = lean_ctor_get(v_x_3807_, 0);
v_x_3807_ = v_fn_3808_;
goto _start;
}
case 10:
{
lean_object* v_expr_3810_; 
v_expr_3810_ = lean_ctor_get(v_x_3807_, 1);
v_x_3807_ = v_expr_3810_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3807_);
return v_x_3807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3812_){
_start:
{
lean_object* v_res_3813_; 
v_res_3813_ = l_Lean_Expr_getAppFn_x27(v_x_3812_);
lean_dec_ref(v_x_3812_);
return v_res_3813_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3814_, lean_object* v_n_3815_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l_Lean_Expr_getAppFn(v_e_3814_);
if (lean_obj_tag(v___x_3816_) == 4)
{
lean_object* v_declName_3817_; uint8_t v___x_3818_; 
v_declName_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_declName_3817_);
lean_dec_ref_known(v___x_3816_, 2);
v___x_3818_ = lean_name_eq(v_declName_3817_, v_n_3815_);
lean_dec(v_declName_3817_);
return v___x_3818_;
}
else
{
uint8_t v___x_3819_; 
lean_dec_ref(v___x_3816_);
v___x_3819_ = 0;
return v___x_3819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3820_, lean_object* v_n_3821_){
_start:
{
uint8_t v_res_3822_; lean_object* v_r_3823_; 
v_res_3822_ = l_Lean_Expr_isAppOf(v_e_3820_, v_n_3821_);
lean_dec(v_n_3821_);
lean_dec_ref(v_e_3820_);
v_r_3823_ = lean_box(v_res_3822_);
return v_r_3823_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3824_, lean_object* v_x_3825_, lean_object* v_x_3826_){
_start:
{
switch(lean_obj_tag(v_x_3824_))
{
case 4:
{
lean_object* v_declName_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; 
v_declName_3827_ = lean_ctor_get(v_x_3824_, 0);
v___x_3828_ = lean_unsigned_to_nat(0u);
v___x_3829_ = lean_nat_dec_eq(v_x_3826_, v___x_3828_);
lean_dec(v_x_3826_);
if (v___x_3829_ == 0)
{
return v___x_3829_;
}
else
{
uint8_t v___x_3830_; 
v___x_3830_ = lean_name_eq(v_declName_3827_, v_x_3825_);
return v___x_3830_;
}
}
case 5:
{
lean_object* v_fn_3831_; lean_object* v_zero_3832_; uint8_t v_isZero_3833_; 
v_fn_3831_ = lean_ctor_get(v_x_3824_, 0);
v_zero_3832_ = lean_unsigned_to_nat(0u);
v_isZero_3833_ = lean_nat_dec_eq(v_x_3826_, v_zero_3832_);
if (v_isZero_3833_ == 0)
{
lean_object* v_one_3834_; lean_object* v_n_3835_; 
v_one_3834_ = lean_unsigned_to_nat(1u);
v_n_3835_ = lean_nat_sub(v_x_3826_, v_one_3834_);
lean_dec(v_x_3826_);
v_x_3824_ = v_fn_3831_;
v_x_3826_ = v_n_3835_;
goto _start;
}
else
{
uint8_t v___x_3837_; 
lean_dec(v_x_3826_);
v___x_3837_ = 0;
return v___x_3837_;
}
}
default: 
{
uint8_t v___x_3838_; 
lean_dec(v_x_3826_);
v___x_3838_ = 0;
return v___x_3838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3839_, lean_object* v_x_3840_, lean_object* v_x_3841_){
_start:
{
uint8_t v_res_3842_; lean_object* v_r_3843_; 
v_res_3842_ = l_Lean_Expr_isAppOfArity(v_x_3839_, v_x_3840_, v_x_3841_);
lean_dec(v_x_3840_);
lean_dec_ref(v_x_3839_);
v_r_3843_ = lean_box(v_res_3842_);
return v_r_3843_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3844_, lean_object* v_x_3845_, lean_object* v_x_3846_){
_start:
{
switch(lean_obj_tag(v_x_3844_))
{
case 10:
{
lean_object* v_expr_3847_; 
v_expr_3847_ = lean_ctor_get(v_x_3844_, 1);
v_x_3844_ = v_expr_3847_;
goto _start;
}
case 4:
{
lean_object* v_declName_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; 
v_declName_3849_ = lean_ctor_get(v_x_3844_, 0);
v___x_3850_ = lean_unsigned_to_nat(0u);
v___x_3851_ = lean_nat_dec_eq(v_x_3846_, v___x_3850_);
lean_dec(v_x_3846_);
if (v___x_3851_ == 0)
{
return v___x_3851_;
}
else
{
uint8_t v___x_3852_; 
v___x_3852_ = lean_name_eq(v_declName_3849_, v_x_3845_);
return v___x_3852_;
}
}
case 5:
{
lean_object* v_fn_3853_; lean_object* v_zero_3854_; uint8_t v_isZero_3855_; 
v_fn_3853_ = lean_ctor_get(v_x_3844_, 0);
v_zero_3854_ = lean_unsigned_to_nat(0u);
v_isZero_3855_ = lean_nat_dec_eq(v_x_3846_, v_zero_3854_);
if (v_isZero_3855_ == 0)
{
lean_object* v_one_3856_; lean_object* v_n_3857_; 
v_one_3856_ = lean_unsigned_to_nat(1u);
v_n_3857_ = lean_nat_sub(v_x_3846_, v_one_3856_);
lean_dec(v_x_3846_);
v_x_3844_ = v_fn_3853_;
v_x_3846_ = v_n_3857_;
goto _start;
}
else
{
uint8_t v___x_3859_; 
lean_dec(v_x_3846_);
v___x_3859_ = 0;
return v___x_3859_;
}
}
default: 
{
uint8_t v___x_3860_; 
lean_dec(v_x_3846_);
v___x_3860_ = 0;
return v___x_3860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3861_, lean_object* v_x_3862_, lean_object* v_x_3863_){
_start:
{
uint8_t v_res_3864_; lean_object* v_r_3865_; 
v_res_3864_ = l_Lean_Expr_isAppOfArity_x27(v_x_3861_, v_x_3862_, v_x_3863_);
lean_dec(v_x_3862_);
lean_dec_ref(v_x_3861_);
v_r_3865_ = lean_box(v_res_3864_);
return v_r_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3866_, lean_object* v_x_3867_){
_start:
{
if (lean_obj_tag(v_x_3866_) == 5)
{
lean_object* v_fn_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v_fn_3868_ = lean_ctor_get(v_x_3866_, 0);
v___x_3869_ = lean_unsigned_to_nat(1u);
v___x_3870_ = lean_nat_add(v_x_3867_, v___x_3869_);
lean_dec(v_x_3867_);
v_x_3866_ = v_fn_3868_;
v_x_3867_ = v___x_3870_;
goto _start;
}
else
{
return v_x_3867_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3872_, lean_object* v_x_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3872_, v_x_3873_);
lean_dec_ref(v_x_3872_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3875_){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3876_ = lean_unsigned_to_nat(0u);
v___x_3877_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3875_, v___x_3876_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_Lean_Expr_getAppNumArgs(v_e_3878_);
lean_dec_ref(v_e_3878_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3880_, lean_object* v_a_3881_){
_start:
{
switch(lean_obj_tag(v_a_3880_))
{
case 10:
{
lean_object* v_expr_3882_; 
v_expr_3882_ = lean_ctor_get(v_a_3880_, 1);
v_a_3880_ = v_expr_3882_;
goto _start;
}
case 5:
{
lean_object* v_fn_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v_fn_3884_ = lean_ctor_get(v_a_3880_, 0);
v___x_3885_ = lean_unsigned_to_nat(1u);
v___x_3886_ = lean_nat_add(v_a_3881_, v___x_3885_);
lean_dec(v_a_3881_);
v_a_3880_ = v_fn_3884_;
v_a_3881_ = v___x_3886_;
goto _start;
}
default: 
{
return v_a_3881_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3888_, v_a_3889_);
lean_dec_ref(v_a_3888_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3891_){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = lean_unsigned_to_nat(0u);
v___x_3893_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3891_, v___x_3892_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3894_);
lean_dec_ref(v_e_3894_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3896_, lean_object* v_x_3897_){
_start:
{
lean_object* v_zero_3898_; uint8_t v_isZero_3899_; 
v_zero_3898_ = lean_unsigned_to_nat(0u);
v_isZero_3899_ = lean_nat_dec_eq(v_x_3896_, v_zero_3898_);
if (v_isZero_3899_ == 0)
{
if (lean_obj_tag(v_x_3897_) == 5)
{
lean_object* v_fn_3900_; lean_object* v_one_3901_; lean_object* v_n_3902_; 
v_fn_3900_ = lean_ctor_get(v_x_3897_, 0);
v_one_3901_ = lean_unsigned_to_nat(1u);
v_n_3902_ = lean_nat_sub(v_x_3896_, v_one_3901_);
lean_dec(v_x_3896_);
v_x_3896_ = v_n_3902_;
v_x_3897_ = v_fn_3900_;
goto _start;
}
else
{
lean_dec(v_x_3896_);
lean_inc_ref(v_x_3897_);
return v_x_3897_;
}
}
else
{
lean_dec(v_x_3896_);
lean_inc_ref(v_x_3897_);
return v_x_3897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_3904_, lean_object* v_x_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l_Lean_Expr_getBoundedAppFn(v_x_3904_, v_x_3905_);
lean_dec_ref(v_x_3905_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_3907_, lean_object* v_x_3908_, lean_object* v_x_3909_){
_start:
{
if (lean_obj_tag(v_x_3907_) == 5)
{
lean_object* v_fn_3910_; lean_object* v_arg_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_fn_3910_ = lean_ctor_get(v_x_3907_, 0);
lean_inc_ref(v_fn_3910_);
v_arg_3911_ = lean_ctor_get(v_x_3907_, 1);
lean_inc_ref(v_arg_3911_);
lean_dec_ref_known(v_x_3907_, 2);
v___x_3912_ = lean_array_set(v_x_3908_, v_x_3909_, v_arg_3911_);
v___x_3913_ = lean_unsigned_to_nat(1u);
v___x_3914_ = lean_nat_sub(v_x_3909_, v___x_3913_);
lean_dec(v_x_3909_);
v_x_3907_ = v_fn_3910_;
v_x_3908_ = v___x_3912_;
v_x_3909_ = v___x_3914_;
goto _start;
}
else
{
lean_dec(v_x_3909_);
lean_dec_ref(v_x_3907_);
return v_x_3908_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_3916_; lean_object* v_dummy_3917_; 
v___x_3916_ = lean_box(0);
v_dummy_3917_ = l_Lean_Expr_sort___override(v___x_3916_);
return v_dummy_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_3918_){
_start:
{
lean_object* v_dummy_3919_; lean_object* v_nargs_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v_dummy_3919_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3920_ = l_Lean_Expr_getAppNumArgs(v_e_3918_);
lean_inc(v_nargs_3920_);
v___x_3921_ = lean_mk_array(v_nargs_3920_, v_dummy_3919_);
v___x_3922_ = lean_unsigned_to_nat(1u);
v___x_3923_ = lean_nat_sub(v_nargs_3920_, v___x_3922_);
lean_dec(v_nargs_3920_);
v___x_3924_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3918_, v___x_3921_, v___x_3923_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_3925_, lean_object* v_x_3926_, lean_object* v_x_3927_){
_start:
{
if (lean_obj_tag(v_x_3925_) == 5)
{
lean_object* v_fn_3928_; lean_object* v_arg_3929_; lean_object* v_zero_3930_; uint8_t v_isZero_3931_; 
v_fn_3928_ = lean_ctor_get(v_x_3925_, 0);
lean_inc_ref(v_fn_3928_);
v_arg_3929_ = lean_ctor_get(v_x_3925_, 1);
lean_inc_ref(v_arg_3929_);
lean_dec_ref_known(v_x_3925_, 2);
v_zero_3930_ = lean_unsigned_to_nat(0u);
v_isZero_3931_ = lean_nat_dec_eq(v_x_3927_, v_zero_3930_);
if (v_isZero_3931_ == 0)
{
lean_object* v_one_3932_; lean_object* v_n_3933_; lean_object* v___x_3934_; 
v_one_3932_ = lean_unsigned_to_nat(1u);
v_n_3933_ = lean_nat_sub(v_x_3927_, v_one_3932_);
lean_dec(v_x_3927_);
v___x_3934_ = lean_array_set(v_x_3926_, v_n_3933_, v_arg_3929_);
v_x_3925_ = v_fn_3928_;
v_x_3926_ = v___x_3934_;
v_x_3927_ = v_n_3933_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3929_);
lean_dec_ref(v_fn_3928_);
lean_dec(v_x_3927_);
return v_x_3926_;
}
}
else
{
lean_dec(v_x_3927_);
lean_dec_ref(v_x_3925_);
return v_x_3926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_3936_, lean_object* v_e_3937_){
_start:
{
lean_object* v_dummy_3938_; lean_object* v___y_3940_; lean_object* v___x_3943_; uint8_t v___x_3944_; 
v_dummy_3938_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_3943_ = l_Lean_Expr_getAppNumArgs(v_e_3937_);
v___x_3944_ = lean_nat_dec_le(v_maxArgs_3936_, v___x_3943_);
if (v___x_3944_ == 0)
{
lean_dec(v_maxArgs_3936_);
v___y_3940_ = v___x_3943_;
goto v___jp_3939_;
}
else
{
lean_dec(v___x_3943_);
v___y_3940_ = v_maxArgs_3936_;
goto v___jp_3939_;
}
v___jp_3939_:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
lean_inc(v___y_3940_);
v___x_3941_ = lean_mk_array(v___y_3940_, v_dummy_3938_);
v___x_3942_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_3937_, v___x_3941_, v___y_3940_);
return v___x_3942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_3945_, lean_object* v_x_3946_){
_start:
{
if (lean_obj_tag(v_x_3945_) == 5)
{
lean_object* v_fn_3947_; lean_object* v_arg_3948_; lean_object* v___x_3949_; 
v_fn_3947_ = lean_ctor_get(v_x_3945_, 0);
lean_inc_ref(v_fn_3947_);
v_arg_3948_ = lean_ctor_get(v_x_3945_, 1);
lean_inc_ref(v_arg_3948_);
lean_dec_ref_known(v_x_3945_, 2);
v___x_3949_ = lean_array_push(v_x_3946_, v_arg_3948_);
v_x_3945_ = v_fn_3947_;
v_x_3946_ = v___x_3949_;
goto _start;
}
else
{
lean_dec_ref(v_x_3945_);
return v_x_3946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_3951_){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3952_ = l_Lean_Expr_getAppNumArgs(v_e_3951_);
v___x_3953_ = lean_mk_empty_array_with_capacity(v___x_3952_);
lean_dec(v___x_3952_);
v___x_3954_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3951_, v___x_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_3955_, lean_object* v_x_3956_, lean_object* v_x_3957_, lean_object* v_x_3958_){
_start:
{
if (lean_obj_tag(v_x_3956_) == 5)
{
lean_object* v_fn_3959_; lean_object* v_arg_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v_fn_3959_ = lean_ctor_get(v_x_3956_, 0);
lean_inc_ref(v_fn_3959_);
v_arg_3960_ = lean_ctor_get(v_x_3956_, 1);
lean_inc_ref(v_arg_3960_);
lean_dec_ref_known(v_x_3956_, 2);
v___x_3961_ = lean_array_set(v_x_3957_, v_x_3958_, v_arg_3960_);
v___x_3962_ = lean_unsigned_to_nat(1u);
v___x_3963_ = lean_nat_sub(v_x_3958_, v___x_3962_);
lean_dec(v_x_3958_);
v_x_3956_ = v_fn_3959_;
v_x_3957_ = v___x_3961_;
v_x_3958_ = v___x_3963_;
goto _start;
}
else
{
lean_object* v___x_3965_; 
lean_dec(v_x_3958_);
v___x_3965_ = lean_apply_2(v_k_3955_, v_x_3956_, v_x_3957_);
return v___x_3965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_3966_, lean_object* v_k_3967_, lean_object* v_x_3968_, lean_object* v_x_3969_, lean_object* v_x_3970_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Lean_Expr_withAppAux___redArg(v_k_3967_, v_x_3968_, v_x_3969_, v_x_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_3972_, lean_object* v_k_3973_){
_start:
{
lean_object* v_dummy_3974_; lean_object* v_nargs_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v_dummy_3974_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3975_ = l_Lean_Expr_getAppNumArgs(v_e_3972_);
lean_inc(v_nargs_3975_);
v___x_3976_ = lean_mk_array(v_nargs_3975_, v_dummy_3974_);
v___x_3977_ = lean_unsigned_to_nat(1u);
v___x_3978_ = lean_nat_sub(v_nargs_3975_, v___x_3977_);
lean_dec(v_nargs_3975_);
v___x_3979_ = l_Lean_Expr_withAppAux___redArg(v_k_3973_, v_e_3972_, v___x_3976_, v___x_3978_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_3980_, lean_object* v_e_3981_, lean_object* v_k_3982_){
_start:
{
lean_object* v_dummy_3983_; lean_object* v_nargs_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v_dummy_3983_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3984_ = l_Lean_Expr_getAppNumArgs(v_e_3981_);
lean_inc(v_nargs_3984_);
v___x_3985_ = lean_mk_array(v_nargs_3984_, v_dummy_3983_);
v___x_3986_ = lean_unsigned_to_nat(1u);
v___x_3987_ = lean_nat_sub(v_nargs_3984_, v___x_3986_);
lean_dec(v_nargs_3984_);
v___x_3988_ = l_Lean_Expr_withAppAux___redArg(v_k_3982_, v_e_3981_, v___x_3985_, v___x_3987_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_3989_, lean_object* v_x_3990_, lean_object* v_x_3991_){
_start:
{
if (lean_obj_tag(v_x_3989_) == 5)
{
lean_object* v_fn_3992_; lean_object* v_arg_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v_fn_3992_ = lean_ctor_get(v_x_3989_, 0);
lean_inc_ref(v_fn_3992_);
v_arg_3993_ = lean_ctor_get(v_x_3989_, 1);
lean_inc_ref(v_arg_3993_);
lean_dec_ref_known(v_x_3989_, 2);
v___x_3994_ = lean_array_set(v_x_3990_, v_x_3991_, v_arg_3993_);
v___x_3995_ = lean_unsigned_to_nat(1u);
v___x_3996_ = lean_nat_sub(v_x_3991_, v___x_3995_);
lean_dec(v_x_3991_);
v_x_3989_ = v_fn_3992_;
v_x_3990_ = v___x_3994_;
v_x_3991_ = v___x_3996_;
goto _start;
}
else
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
lean_dec(v_x_3991_);
v___x_3998_ = l_Lean_Expr_constName(v_x_3989_);
lean_dec_ref(v_x_3989_);
v___x_3999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
lean_ctor_set(v___x_3999_, 1, v_x_3990_);
return v___x_3999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_4000_){
_start:
{
lean_object* v_dummy_4001_; lean_object* v_nargs_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v_dummy_4001_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4002_ = l_Lean_Expr_getAppNumArgs(v_e_4000_);
lean_inc(v_nargs_4002_);
v___x_4003_ = lean_mk_array(v_nargs_4002_, v_dummy_4001_);
v___x_4004_ = lean_unsigned_to_nat(1u);
v___x_4005_ = lean_nat_sub(v_nargs_4002_, v___x_4004_);
lean_dec(v_nargs_4002_);
v___x_4006_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_4000_, v___x_4003_, v___x_4005_);
return v___x_4006_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = l_Array_instInhabited___redArg();
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_4008_){
_start:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4009_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_4010_ = lean_panic_fn_borrowed(v___x_4009_, v_msg_4008_);
return v___x_4010_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4013_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_4014_ = lean_unsigned_to_nat(27u);
v___x_4015_ = lean_unsigned_to_nat(1246u);
v___x_4016_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_4017_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4018_ = l_mkPanicMessageWithDecl(v___x_4017_, v___x_4016_, v___x_4015_, v___x_4014_, v___x_4013_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v_zero_4022_; uint8_t v_isZero_4023_; 
v_zero_4022_ = lean_unsigned_to_nat(0u);
v_isZero_4023_ = lean_nat_dec_eq(v_a_4019_, v_zero_4022_);
if (v_isZero_4023_ == 1)
{
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
return v_a_4021_;
}
else
{
if (lean_obj_tag(v_a_4020_) == 5)
{
lean_object* v_fn_4024_; lean_object* v_arg_4025_; lean_object* v_one_4026_; lean_object* v_n_4027_; lean_object* v___x_4028_; 
v_fn_4024_ = lean_ctor_get(v_a_4020_, 0);
lean_inc_ref(v_fn_4024_);
v_arg_4025_ = lean_ctor_get(v_a_4020_, 1);
lean_inc_ref(v_arg_4025_);
lean_dec_ref_known(v_a_4020_, 2);
v_one_4026_ = lean_unsigned_to_nat(1u);
v_n_4027_ = lean_nat_sub(v_a_4019_, v_one_4026_);
lean_dec(v_a_4019_);
v___x_4028_ = lean_array_set(v_a_4021_, v_n_4027_, v_arg_4025_);
v_a_4019_ = v_n_4027_;
v_a_4020_ = v_fn_4024_;
v_a_4021_ = v___x_4028_;
goto _start;
}
else
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
lean_dec_ref(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
v___x_4030_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_4031_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_4030_);
return v___x_4031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_4032_, lean_object* v_n_4033_){
_start:
{
lean_object* v_dummy_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v_dummy_4034_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_4033_);
v___x_4035_ = lean_mk_array(v_n_4033_, v_dummy_4034_);
v___x_4036_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_4033_, v_e_4032_, v___x_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_4037_, lean_object* v_n_4038_){
_start:
{
lean_object* v_zero_4039_; uint8_t v_isZero_4040_; 
v_zero_4039_ = lean_unsigned_to_nat(0u);
v_isZero_4040_ = lean_nat_dec_eq(v_n_4038_, v_zero_4039_);
if (v_isZero_4040_ == 1)
{
lean_dec(v_n_4038_);
lean_inc_ref(v_e_4037_);
return v_e_4037_;
}
else
{
if (lean_obj_tag(v_e_4037_) == 5)
{
lean_object* v_fn_4041_; lean_object* v_one_4042_; lean_object* v_n_4043_; 
v_fn_4041_ = lean_ctor_get(v_e_4037_, 0);
v_one_4042_ = lean_unsigned_to_nat(1u);
v_n_4043_ = lean_nat_sub(v_n_4038_, v_one_4042_);
lean_dec(v_n_4038_);
v_e_4037_ = v_fn_4041_;
v_n_4038_ = v_n_4043_;
goto _start;
}
else
{
lean_dec(v_n_4038_);
lean_inc_ref(v_e_4037_);
return v_e_4037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_4045_, lean_object* v_n_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_Lean_Expr_stripArgsN(v_e_4045_, v_n_4046_);
lean_dec_ref(v_e_4045_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_4048_, lean_object* v_n_4049_){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4050_ = l_Lean_Expr_getAppNumArgs(v_e_4048_);
v___x_4051_ = lean_nat_sub(v___x_4050_, v_n_4049_);
lean_dec(v___x_4050_);
v___x_4052_ = l_Lean_Expr_stripArgsN(v_e_4048_, v___x_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_4053_, lean_object* v_n_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l_Lean_Expr_getAppPrefix(v_e_4053_, v_n_4054_);
lean_dec(v_n_4054_);
lean_dec_ref(v_e_4053_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_4056_, lean_object* v_inst_4057_, lean_object* v_f_4058_, lean_object* v_x_4059_){
_start:
{
size_t v_sz_4060_; size_t v___x_4061_; lean_object* v___x_4062_; 
v_sz_4060_ = lean_array_size(v_args_4056_);
v___x_4061_ = ((size_t)0ULL);
v___x_4062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4057_, v_f_4058_, v_sz_4060_, v___x_4061_, v_args_4056_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_4064_, lean_object* v_inst_4065_, lean_object* v_f_4066_, lean_object* v_toSeq_4067_, lean_object* v_fn_4068_, lean_object* v_args_4069_){
_start:
{
lean_object* v_map_4070_; lean_object* v___f_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v_map_4070_ = lean_ctor_get(v_toFunctor_4064_, 0);
lean_inc(v_map_4070_);
lean_dec_ref(v_toFunctor_4064_);
lean_inc(v_f_4066_);
v___f_4071_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4071_, 0, v_args_4069_);
lean_closure_set(v___f_4071_, 1, v_inst_4065_);
lean_closure_set(v___f_4071_, 2, v_f_4066_);
v___x_4072_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_4073_ = lean_apply_1(v_f_4066_, v_fn_4068_);
v___x_4074_ = lean_apply_4(v_map_4070_, lean_box(0), lean_box(0), v___x_4072_, v___x_4073_);
v___x_4075_ = lean_apply_4(v_toSeq_4067_, lean_box(0), lean_box(0), v___x_4074_, v___f_4071_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_4076_, lean_object* v_f_4077_, lean_object* v_e_4078_){
_start:
{
lean_object* v_toApplicative_4079_; lean_object* v_toFunctor_4080_; lean_object* v_toSeq_4081_; lean_object* v___f_4082_; lean_object* v_dummy_4083_; lean_object* v_nargs_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v_toApplicative_4079_ = lean_ctor_get(v_inst_4076_, 0);
v_toFunctor_4080_ = lean_ctor_get(v_toApplicative_4079_, 0);
lean_inc_ref(v_toFunctor_4080_);
v_toSeq_4081_ = lean_ctor_get(v_toApplicative_4079_, 2);
lean_inc(v_toSeq_4081_);
v___f_4082_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_4082_, 0, v_toFunctor_4080_);
lean_closure_set(v___f_4082_, 1, v_inst_4076_);
lean_closure_set(v___f_4082_, 2, v_f_4077_);
lean_closure_set(v___f_4082_, 3, v_toSeq_4081_);
v_dummy_4083_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4084_ = l_Lean_Expr_getAppNumArgs(v_e_4078_);
lean_inc(v_nargs_4084_);
v___x_4085_ = lean_mk_array(v_nargs_4084_, v_dummy_4083_);
v___x_4086_ = lean_unsigned_to_nat(1u);
v___x_4087_ = lean_nat_sub(v_nargs_4084_, v___x_4086_);
lean_dec(v_nargs_4084_);
v___x_4088_ = l_Lean_Expr_withAppAux___redArg(v___f_4082_, v_e_4078_, v___x_4085_, v___x_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_4089_, lean_object* v_inst_4090_, lean_object* v_f_4091_, lean_object* v_e_4092_){
_start:
{
lean_object* v___x_4093_; 
v___x_4093_ = l_Lean_Expr_traverseApp___redArg(v_inst_4090_, v_f_4091_, v_e_4092_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_4094_, lean_object* v_x_4095_, lean_object* v_x_4096_){
_start:
{
if (lean_obj_tag(v_x_4095_) == 5)
{
lean_object* v_fn_4097_; lean_object* v_arg_4098_; lean_object* v___x_4099_; 
v_fn_4097_ = lean_ctor_get(v_x_4095_, 0);
lean_inc_ref(v_fn_4097_);
v_arg_4098_ = lean_ctor_get(v_x_4095_, 1);
lean_inc_ref(v_arg_4098_);
lean_dec_ref_known(v_x_4095_, 2);
v___x_4099_ = lean_array_push(v_x_4096_, v_arg_4098_);
v_x_4095_ = v_fn_4097_;
v_x_4096_ = v___x_4099_;
goto _start;
}
else
{
lean_object* v___x_4101_; 
v___x_4101_ = lean_apply_2(v_k_4094_, v_x_4095_, v_x_4096_);
return v___x_4101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_4102_, lean_object* v_k_4103_, lean_object* v_x_4104_, lean_object* v_x_4105_){
_start:
{
lean_object* v___x_4106_; 
v___x_4106_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4103_, v_x_4104_, v_x_4105_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_4107_, lean_object* v_k_4108_){
_start:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4109_ = l_Lean_Expr_getAppNumArgs(v_e_4107_);
v___x_4110_ = lean_mk_empty_array_with_capacity(v___x_4109_);
lean_dec(v___x_4109_);
v___x_4111_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4108_, v_e_4107_, v___x_4110_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_4112_, lean_object* v_e_4113_, lean_object* v_k_4114_){
_start:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4115_ = l_Lean_Expr_getAppNumArgs(v_e_4113_);
v___x_4116_ = lean_mk_empty_array_with_capacity(v___x_4115_);
lean_dec(v___x_4115_);
v___x_4117_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4114_, v_e_4113_, v___x_4116_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_4118_, lean_object* v_x_4119_, lean_object* v_x_4120_){
_start:
{
if (lean_obj_tag(v_x_4118_) == 5)
{
lean_object* v_fn_4121_; lean_object* v_arg_4122_; lean_object* v_zero_4123_; uint8_t v_isZero_4124_; 
v_fn_4121_ = lean_ctor_get(v_x_4118_, 0);
v_arg_4122_ = lean_ctor_get(v_x_4118_, 1);
v_zero_4123_ = lean_unsigned_to_nat(0u);
v_isZero_4124_ = lean_nat_dec_eq(v_x_4119_, v_zero_4123_);
if (v_isZero_4124_ == 1)
{
lean_dec(v_x_4119_);
lean_inc_ref(v_arg_4122_);
return v_arg_4122_;
}
else
{
lean_object* v_one_4125_; lean_object* v_n_4126_; 
v_one_4125_ = lean_unsigned_to_nat(1u);
v_n_4126_ = lean_nat_sub(v_x_4119_, v_one_4125_);
lean_dec(v_x_4119_);
v_x_4118_ = v_fn_4121_;
v_x_4119_ = v_n_4126_;
goto _start;
}
}
else
{
lean_dec(v_x_4119_);
lean_inc_ref(v_x_4120_);
return v_x_4120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_4128_, lean_object* v_x_4129_, lean_object* v_x_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l_Lean_Expr_getRevArgD(v_x_4128_, v_x_4129_, v_x_4130_);
lean_dec_ref(v_x_4130_);
lean_dec_ref(v_x_4128_);
return v_res_4131_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4134_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4135_ = lean_unsigned_to_nat(20u);
v___x_4136_ = lean_unsigned_to_nat(1287u);
v___x_4137_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4138_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4139_ = l_mkPanicMessageWithDecl(v___x_4138_, v___x_4137_, v___x_4136_, v___x_4135_, v___x_4134_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4140_, lean_object* v_x_4141_){
_start:
{
if (lean_obj_tag(v_x_4140_) == 5)
{
lean_object* v_fn_4142_; lean_object* v_arg_4143_; lean_object* v_zero_4144_; uint8_t v_isZero_4145_; 
v_fn_4142_ = lean_ctor_get(v_x_4140_, 0);
v_arg_4143_ = lean_ctor_get(v_x_4140_, 1);
v_zero_4144_ = lean_unsigned_to_nat(0u);
v_isZero_4145_ = lean_nat_dec_eq(v_x_4141_, v_zero_4144_);
if (v_isZero_4145_ == 1)
{
lean_dec(v_x_4141_);
lean_inc_ref(v_arg_4143_);
return v_arg_4143_;
}
else
{
lean_object* v_one_4146_; lean_object* v_n_4147_; 
v_one_4146_ = lean_unsigned_to_nat(1u);
v_n_4147_ = lean_nat_sub(v_x_4141_, v_one_4146_);
lean_dec(v_x_4141_);
v_x_4140_ = v_fn_4142_;
v_x_4141_ = v_n_4147_;
goto _start;
}
}
else
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
lean_dec(v_x_4141_);
v___x_4149_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4150_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4149_);
return v___x_4150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4151_, lean_object* v_x_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l_Lean_Expr_getRevArg_x21(v_x_4151_, v_x_4152_);
lean_dec_ref(v_x_4151_);
return v_res_4153_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4155_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4156_ = lean_unsigned_to_nat(20u);
v___x_4157_ = lean_unsigned_to_nat(1294u);
v___x_4158_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4159_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4160_ = l_mkPanicMessageWithDecl(v___x_4159_, v___x_4158_, v___x_4157_, v___x_4156_, v___x_4155_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4161_, lean_object* v_x_4162_){
_start:
{
switch(lean_obj_tag(v_x_4161_))
{
case 10:
{
lean_object* v_expr_4163_; 
v_expr_4163_ = lean_ctor_get(v_x_4161_, 1);
v_x_4161_ = v_expr_4163_;
goto _start;
}
case 5:
{
lean_object* v_fn_4165_; lean_object* v_arg_4166_; lean_object* v_zero_4167_; uint8_t v_isZero_4168_; 
v_fn_4165_ = lean_ctor_get(v_x_4161_, 0);
v_arg_4166_ = lean_ctor_get(v_x_4161_, 1);
v_zero_4167_ = lean_unsigned_to_nat(0u);
v_isZero_4168_ = lean_nat_dec_eq(v_x_4162_, v_zero_4167_);
if (v_isZero_4168_ == 1)
{
lean_dec(v_x_4162_);
lean_inc_ref(v_arg_4166_);
return v_arg_4166_;
}
else
{
lean_object* v_one_4169_; lean_object* v_n_4170_; 
v_one_4169_ = lean_unsigned_to_nat(1u);
v_n_4170_ = lean_nat_sub(v_x_4162_, v_one_4169_);
lean_dec(v_x_4162_);
v_x_4161_ = v_fn_4165_;
v_x_4162_ = v_n_4170_;
goto _start;
}
}
default: 
{
lean_object* v___x_4172_; lean_object* v___x_4173_; 
lean_dec(v_x_4162_);
v___x_4172_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4173_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4172_);
return v___x_4173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4174_, lean_object* v_x_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4174_, v_x_4175_);
lean_dec_ref(v_x_4174_);
return v_res_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4177_, lean_object* v_i_4178_, lean_object* v_n_4179_){
_start:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4180_ = lean_nat_sub(v_n_4179_, v_i_4178_);
v___x_4181_ = lean_unsigned_to_nat(1u);
v___x_4182_ = lean_nat_sub(v___x_4180_, v___x_4181_);
lean_dec(v___x_4180_);
v___x_4183_ = l_Lean_Expr_getRevArg_x21(v_e_4177_, v___x_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4184_, lean_object* v_i_4185_, lean_object* v_n_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l_Lean_Expr_getArg_x21(v_e_4184_, v_i_4185_, v_n_4186_);
lean_dec(v_n_4186_);
lean_dec(v_i_4185_);
lean_dec_ref(v_e_4184_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4188_, lean_object* v_i_4189_, lean_object* v_n_4190_){
_start:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4191_ = lean_nat_sub(v_n_4190_, v_i_4189_);
v___x_4192_ = lean_unsigned_to_nat(1u);
v___x_4193_ = lean_nat_sub(v___x_4191_, v___x_4192_);
lean_dec(v___x_4191_);
v___x_4194_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4188_, v___x_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4195_, lean_object* v_i_4196_, lean_object* v_n_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l_Lean_Expr_getArg_x21_x27(v_e_4195_, v_i_4196_, v_n_4197_);
lean_dec(v_n_4197_);
lean_dec(v_i_4196_);
lean_dec_ref(v_e_4195_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4199_, lean_object* v_i_4200_, lean_object* v_v_u2080_4201_, lean_object* v_n_4202_){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4203_ = lean_nat_sub(v_n_4202_, v_i_4200_);
v___x_4204_ = lean_unsigned_to_nat(1u);
v___x_4205_ = lean_nat_sub(v___x_4203_, v___x_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = l_Lean_Expr_getRevArgD(v_e_4199_, v___x_4205_, v_v_u2080_4201_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4207_, lean_object* v_i_4208_, lean_object* v_v_u2080_4209_, lean_object* v_n_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Lean_Expr_getArgD(v_e_4207_, v_i_4208_, v_v_u2080_4209_, v_n_4210_);
lean_dec(v_n_4210_);
lean_dec_ref(v_v_u2080_4209_);
lean_dec(v_i_4208_);
lean_dec_ref(v_e_4207_);
return v_res_4211_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4212_){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; uint8_t v___x_4215_; 
v___x_4213_ = lean_unsigned_to_nat(0u);
v___x_4214_ = l_Lean_Expr_looseBVarRange(v_e_4212_);
v___x_4215_ = lean_nat_dec_lt(v___x_4213_, v___x_4214_);
lean_dec(v___x_4214_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4216_){
_start:
{
uint8_t v_res_4217_; lean_object* v_r_4218_; 
v_res_4217_ = l_Lean_Expr_hasLooseBVars(v_e_4216_);
lean_dec_ref(v_e_4216_);
v_r_4218_ = lean_box(v_res_4217_);
return v_r_4218_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4219_){
_start:
{
if (lean_obj_tag(v_e_4219_) == 7)
{
lean_object* v_body_4220_; uint8_t v___x_4221_; 
v_body_4220_ = lean_ctor_get(v_e_4219_, 2);
v___x_4221_ = l_Lean_Expr_hasLooseBVars(v_body_4220_);
if (v___x_4221_ == 0)
{
uint8_t v___x_4222_; 
v___x_4222_ = 1;
return v___x_4222_;
}
else
{
uint8_t v___x_4223_; 
v___x_4223_ = 0;
return v___x_4223_;
}
}
else
{
uint8_t v___x_4224_; 
v___x_4224_ = 0;
return v___x_4224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4225_){
_start:
{
uint8_t v_res_4226_; lean_object* v_r_4227_; 
v_res_4226_ = l_Lean_Expr_isArrow(v_e_4225_);
lean_dec_ref(v_e_4225_);
v_r_4227_ = lean_box(v_res_4226_);
return v_r_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4230_, lean_object* v_bvarIdx_4231_){
_start:
{
uint8_t v_res_4232_; lean_object* v_r_4233_; 
v_res_4232_ = lean_expr_has_loose_bvar(v_e_4230_, v_bvarIdx_4231_);
lean_dec(v_bvarIdx_4231_);
lean_dec_ref(v_e_4230_);
v_r_4233_ = lean_box(v_res_4232_);
return v_r_4233_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4234_, lean_object* v_bvarIdx_4235_, uint8_t v_considerRange_4236_){
_start:
{
if (lean_obj_tag(v_e_4234_) == 7)
{
lean_object* v_binderType_4237_; lean_object* v_body_4238_; uint8_t v_binderInfo_4239_; uint8_t v___y_4241_; uint8_t v___x_4245_; 
v_binderType_4237_ = lean_ctor_get(v_e_4234_, 1);
v_body_4238_ = lean_ctor_get(v_e_4234_, 2);
v_binderInfo_4239_ = lean_ctor_get_uint8(v_e_4234_, sizeof(void*)*3 + 8);
v___x_4245_ = lean_expr_has_loose_bvar(v_binderType_4237_, v_bvarIdx_4235_);
if (v___x_4245_ == 0)
{
v___y_4241_ = v___x_4245_;
goto v___jp_4240_;
}
else
{
uint8_t v___x_4246_; 
v___x_4246_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4239_);
if (v___x_4246_ == 0)
{
lean_object* v___x_4247_; uint8_t v___x_4248_; 
v___x_4247_ = lean_unsigned_to_nat(0u);
v___x_4248_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4238_, v___x_4247_, v_considerRange_4236_);
v___y_4241_ = v___x_4248_;
goto v___jp_4240_;
}
else
{
v___y_4241_ = v___x_4246_;
goto v___jp_4240_;
}
}
v___jp_4240_:
{
if (v___y_4241_ == 0)
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = lean_unsigned_to_nat(1u);
v___x_4243_ = lean_nat_add(v_bvarIdx_4235_, v___x_4242_);
lean_dec(v_bvarIdx_4235_);
v_e_4234_ = v_body_4238_;
v_bvarIdx_4235_ = v___x_4243_;
goto _start;
}
else
{
lean_dec(v_bvarIdx_4235_);
return v___y_4241_;
}
}
}
else
{
if (v_considerRange_4236_ == 0)
{
lean_dec(v_bvarIdx_4235_);
return v_considerRange_4236_;
}
else
{
uint8_t v___x_4249_; 
v___x_4249_ = lean_expr_has_loose_bvar(v_e_4234_, v_bvarIdx_4235_);
lean_dec(v_bvarIdx_4235_);
return v___x_4249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4250_, lean_object* v_bvarIdx_4251_, lean_object* v_considerRange_4252_){
_start:
{
uint8_t v_considerRange_boxed_4253_; uint8_t v_res_4254_; lean_object* v_r_4255_; 
v_considerRange_boxed_4253_ = lean_unbox(v_considerRange_4252_);
v_res_4254_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4250_, v_bvarIdx_4251_, v_considerRange_boxed_4253_);
lean_dec_ref(v_e_4250_);
v_r_4255_ = lean_box(v_res_4254_);
return v_r_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4259_, lean_object* v_s_4260_, lean_object* v_d_4261_){
_start:
{
lean_object* v_res_4262_; 
v_res_4262_ = lean_expr_lower_loose_bvars(v_e_4259_, v_s_4260_, v_d_4261_);
lean_dec(v_d_4261_);
lean_dec(v_s_4260_);
lean_dec_ref(v_e_4259_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4266_, lean_object* v_s_4267_, lean_object* v_d_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = lean_expr_lift_loose_bvars(v_e_4266_, v_s_4267_, v_d_4268_);
lean_dec(v_d_4268_);
lean_dec(v_s_4267_);
lean_dec_ref(v_e_4266_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4270_, lean_object* v_numParams_4271_, uint8_t v_considerRange_4272_){
_start:
{
if (lean_obj_tag(v_e_4270_) == 7)
{
lean_object* v_binderName_4273_; lean_object* v_binderType_4274_; lean_object* v_body_4275_; uint8_t v_binderInfo_4276_; lean_object* v_zero_4277_; uint8_t v_isZero_4278_; 
v_binderName_4273_ = lean_ctor_get(v_e_4270_, 0);
v_binderType_4274_ = lean_ctor_get(v_e_4270_, 1);
v_body_4275_ = lean_ctor_get(v_e_4270_, 2);
v_binderInfo_4276_ = lean_ctor_get_uint8(v_e_4270_, sizeof(void*)*3 + 8);
v_zero_4277_ = lean_unsigned_to_nat(0u);
v_isZero_4278_ = lean_nat_dec_eq(v_numParams_4271_, v_zero_4277_);
if (v_isZero_4278_ == 0)
{
lean_object* v_one_4279_; lean_object* v_n_4280_; lean_object* v_b_4281_; uint8_t v___y_4283_; uint8_t v___x_4287_; 
lean_inc_ref(v_body_4275_);
lean_inc_ref(v_binderType_4274_);
lean_inc(v_binderName_4273_);
lean_dec_ref_known(v_e_4270_, 3);
v_one_4279_ = lean_unsigned_to_nat(1u);
v_n_4280_ = lean_nat_sub(v_numParams_4271_, v_one_4279_);
v_b_4281_ = l_Lean_Expr_inferImplicit(v_body_4275_, v_n_4280_, v_considerRange_4272_);
lean_dec(v_n_4280_);
v___x_4287_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4276_);
if (v___x_4287_ == 0)
{
v___y_4283_ = v___x_4287_;
goto v___jp_4282_;
}
else
{
uint8_t v___x_4288_; 
v___x_4288_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4281_, v_zero_4277_, v_considerRange_4272_);
v___y_4283_ = v___x_4288_;
goto v___jp_4282_;
}
v___jp_4282_:
{
if (v___y_4283_ == 0)
{
lean_object* v___x_4284_; 
v___x_4284_ = l_Lean_Expr_forallE___override(v_binderName_4273_, v_binderType_4274_, v_b_4281_, v_binderInfo_4276_);
return v___x_4284_;
}
else
{
uint8_t v___x_4285_; lean_object* v___x_4286_; 
v___x_4285_ = 1;
v___x_4286_ = l_Lean_Expr_forallE___override(v_binderName_4273_, v_binderType_4274_, v_b_4281_, v___x_4285_);
return v___x_4286_;
}
}
}
else
{
return v_e_4270_;
}
}
else
{
return v_e_4270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4289_, lean_object* v_numParams_4290_, lean_object* v_considerRange_4291_){
_start:
{
uint8_t v_considerRange_boxed_4292_; lean_object* v_res_4293_; 
v_considerRange_boxed_4292_ = lean_unbox(v_considerRange_4291_);
v_res_4293_ = l_Lean_Expr_inferImplicit(v_e_4289_, v_numParams_4290_, v_considerRange_boxed_4292_);
lean_dec(v_numParams_4290_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4294_, lean_object* v_binderInfos_x3f_4295_){
_start:
{
if (lean_obj_tag(v_e_4294_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4295_) == 1)
{
lean_object* v_binderName_4296_; lean_object* v_binderType_4297_; lean_object* v_body_4298_; uint8_t v_binderInfo_4299_; lean_object* v_head_4300_; lean_object* v_tail_4301_; lean_object* v_b_4302_; 
v_binderName_4296_ = lean_ctor_get(v_e_4294_, 0);
lean_inc(v_binderName_4296_);
v_binderType_4297_ = lean_ctor_get(v_e_4294_, 1);
lean_inc_ref(v_binderType_4297_);
v_body_4298_ = lean_ctor_get(v_e_4294_, 2);
lean_inc_ref(v_body_4298_);
v_binderInfo_4299_ = lean_ctor_get_uint8(v_e_4294_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4294_, 3);
v_head_4300_ = lean_ctor_get(v_binderInfos_x3f_4295_, 0);
v_tail_4301_ = lean_ctor_get(v_binderInfos_x3f_4295_, 1);
v_b_4302_ = l_Lean_Expr_updateForallBinderInfos(v_body_4298_, v_tail_4301_);
if (lean_obj_tag(v_head_4300_) == 0)
{
lean_object* v___x_4303_; 
v___x_4303_ = l_Lean_Expr_forallE___override(v_binderName_4296_, v_binderType_4297_, v_b_4302_, v_binderInfo_4299_);
return v___x_4303_;
}
else
{
lean_object* v_val_4304_; uint8_t v___x_4305_; lean_object* v___x_4306_; 
v_val_4304_ = lean_ctor_get(v_head_4300_, 0);
v___x_4305_ = lean_unbox(v_val_4304_);
v___x_4306_ = l_Lean_Expr_forallE___override(v_binderName_4296_, v_binderType_4297_, v_b_4302_, v___x_4305_);
return v___x_4306_;
}
}
else
{
return v_e_4294_;
}
}
else
{
return v_e_4294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4307_, lean_object* v_binderInfos_x3f_4308_){
_start:
{
lean_object* v_res_4309_; 
v_res_4309_ = l_Lean_Expr_updateForallBinderInfos(v_e_4307_, v_binderInfos_x3f_4308_);
lean_dec(v_binderInfos_x3f_4308_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4310_, lean_object* v_binderNames_x3f_4311_){
_start:
{
switch(lean_obj_tag(v_e_4310_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4311_) == 1)
{
lean_object* v_binderName_4312_; lean_object* v_binderType_4313_; lean_object* v_body_4314_; uint8_t v_binderInfo_4315_; lean_object* v_head_4316_; lean_object* v_tail_4317_; lean_object* v_b_4318_; 
v_binderName_4312_ = lean_ctor_get(v_e_4310_, 0);
lean_inc(v_binderName_4312_);
v_binderType_4313_ = lean_ctor_get(v_e_4310_, 1);
lean_inc_ref(v_binderType_4313_);
v_body_4314_ = lean_ctor_get(v_e_4310_, 2);
lean_inc_ref(v_body_4314_);
v_binderInfo_4315_ = lean_ctor_get_uint8(v_e_4310_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4310_, 3);
v_head_4316_ = lean_ctor_get(v_binderNames_x3f_4311_, 0);
lean_inc(v_head_4316_);
v_tail_4317_ = lean_ctor_get(v_binderNames_x3f_4311_, 1);
lean_inc(v_tail_4317_);
lean_dec_ref_known(v_binderNames_x3f_4311_, 2);
v_b_4318_ = l_Lean_Expr_updateBinderNames(v_body_4314_, v_tail_4317_);
if (lean_obj_tag(v_head_4316_) == 0)
{
lean_object* v___x_4319_; 
v___x_4319_ = l_Lean_Expr_forallE___override(v_binderName_4312_, v_binderType_4313_, v_b_4318_, v_binderInfo_4315_);
return v___x_4319_;
}
else
{
lean_object* v_val_4320_; lean_object* v___x_4321_; 
lean_dec(v_binderName_4312_);
v_val_4320_ = lean_ctor_get(v_head_4316_, 0);
lean_inc(v_val_4320_);
lean_dec_ref_known(v_head_4316_, 1);
v___x_4321_ = l_Lean_Expr_forallE___override(v_val_4320_, v_binderType_4313_, v_b_4318_, v_binderInfo_4315_);
return v___x_4321_;
}
}
else
{
lean_dec(v_binderNames_x3f_4311_);
return v_e_4310_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4311_) == 1)
{
lean_object* v_binderName_4322_; lean_object* v_binderType_4323_; lean_object* v_body_4324_; uint8_t v_binderInfo_4325_; lean_object* v_head_4326_; lean_object* v_tail_4327_; lean_object* v_b_4328_; 
v_binderName_4322_ = lean_ctor_get(v_e_4310_, 0);
lean_inc(v_binderName_4322_);
v_binderType_4323_ = lean_ctor_get(v_e_4310_, 1);
lean_inc_ref(v_binderType_4323_);
v_body_4324_ = lean_ctor_get(v_e_4310_, 2);
lean_inc_ref(v_body_4324_);
v_binderInfo_4325_ = lean_ctor_get_uint8(v_e_4310_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4310_, 3);
v_head_4326_ = lean_ctor_get(v_binderNames_x3f_4311_, 0);
lean_inc(v_head_4326_);
v_tail_4327_ = lean_ctor_get(v_binderNames_x3f_4311_, 1);
lean_inc(v_tail_4327_);
lean_dec_ref_known(v_binderNames_x3f_4311_, 2);
v_b_4328_ = l_Lean_Expr_updateBinderNames(v_body_4324_, v_tail_4327_);
if (lean_obj_tag(v_head_4326_) == 0)
{
lean_object* v___x_4329_; 
v___x_4329_ = l_Lean_Expr_lam___override(v_binderName_4322_, v_binderType_4323_, v_b_4328_, v_binderInfo_4325_);
return v___x_4329_;
}
else
{
lean_object* v_val_4330_; lean_object* v___x_4331_; 
lean_dec(v_binderName_4322_);
v_val_4330_ = lean_ctor_get(v_head_4326_, 0);
lean_inc(v_val_4330_);
lean_dec_ref_known(v_head_4326_, 1);
v___x_4331_ = l_Lean_Expr_lam___override(v_val_4330_, v_binderType_4323_, v_b_4328_, v_binderInfo_4325_);
return v___x_4331_;
}
}
else
{
lean_dec(v_binderNames_x3f_4311_);
return v_e_4310_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4311_);
return v_e_4310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4334_, lean_object* v_subst_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = lean_expr_instantiate(v_e_4334_, v_subst_4335_);
lean_dec_ref(v_subst_4335_);
lean_dec_ref(v_e_4334_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4339_, lean_object* v_subst_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = lean_expr_instantiate1(v_e_4339_, v_subst_4340_);
lean_dec_ref(v_subst_4340_);
lean_dec_ref(v_e_4339_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4344_, lean_object* v_subst_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = lean_expr_instantiate_rev(v_e_4344_, v_subst_4345_);
lean_dec_ref(v_subst_4345_);
lean_dec_ref(v_e_4344_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4351_, lean_object* v_beginIdx_4352_, lean_object* v_endIdx_4353_, lean_object* v_subst_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = lean_expr_instantiate_range(v_e_4351_, v_beginIdx_4352_, v_endIdx_4353_, v_subst_4354_);
lean_dec_ref(v_subst_4354_);
lean_dec(v_endIdx_4353_);
lean_dec(v_beginIdx_4352_);
lean_dec_ref(v_e_4351_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4360_, lean_object* v_beginIdx_4361_, lean_object* v_endIdx_4362_, lean_object* v_subst_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = lean_expr_instantiate_rev_range(v_e_4360_, v_beginIdx_4361_, v_endIdx_4362_, v_subst_4363_);
lean_dec_ref(v_subst_4363_);
lean_dec(v_endIdx_4362_);
lean_dec(v_beginIdx_4361_);
lean_dec_ref(v_e_4360_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4367_, lean_object* v_xs_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = lean_expr_abstract(v_e_4367_, v_xs_4368_);
lean_dec_ref(v_xs_4368_);
lean_dec_ref(v_e_4367_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4373_, lean_object* v_n_4374_, lean_object* v_xs_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = lean_expr_abstract_range(v_e_4373_, v_n_4374_, v_xs_4375_);
lean_dec_ref(v_xs_4375_);
lean_dec(v_n_4374_);
lean_dec_ref(v_e_4373_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4377_, lean_object* v_fvar_4378_, lean_object* v_v_4379_){
_start:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4380_ = lean_unsigned_to_nat(1u);
v___x_4381_ = lean_mk_empty_array_with_capacity(v___x_4380_);
v___x_4382_ = lean_array_push(v___x_4381_, v_fvar_4378_);
v___x_4383_ = lean_expr_abstract(v_e_4377_, v___x_4382_);
lean_dec_ref(v___x_4382_);
v___x_4384_ = lean_expr_instantiate1(v___x_4383_, v_v_4379_);
lean_dec_ref(v___x_4383_);
return v___x_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4385_, lean_object* v_fvar_4386_, lean_object* v_v_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l_Lean_Expr_replaceFVar(v_e_4385_, v_fvar_4386_, v_v_4387_);
lean_dec_ref(v_v_4387_);
lean_dec_ref(v_e_4385_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4389_, lean_object* v_fvarId_4390_, lean_object* v_v_4391_){
_start:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4392_ = l_Lean_Expr_fvar___override(v_fvarId_4390_);
v___x_4393_ = l_Lean_Expr_replaceFVar(v_e_4389_, v___x_4392_, v_v_4391_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4394_, lean_object* v_fvarId_4395_, lean_object* v_v_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l_Lean_Expr_replaceFVarId(v_e_4394_, v_fvarId_4395_, v_v_4396_);
lean_dec_ref(v_v_4396_);
lean_dec_ref(v_e_4394_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4398_, lean_object* v_fvars_4399_, lean_object* v_vs_4400_){
_start:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = lean_expr_abstract(v_e_4398_, v_fvars_4399_);
v___x_4402_ = lean_expr_instantiate_rev(v___x_4401_, v_vs_4400_);
lean_dec_ref(v___x_4401_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4403_, lean_object* v_fvars_4404_, lean_object* v_vs_4405_){
_start:
{
lean_object* v_res_4406_; 
v_res_4406_ = l_Lean_Expr_replaceFVars(v_e_4403_, v_fvars_4404_, v_vs_4405_);
lean_dec_ref(v_vs_4405_);
lean_dec_ref(v_fvars_4404_);
lean_dec_ref(v_e_4403_);
return v_res_4406_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4409_){
_start:
{
switch(lean_obj_tag(v_x_4409_))
{
case 4:
{
uint8_t v___x_4410_; 
v___x_4410_ = 1;
return v___x_4410_;
}
case 3:
{
uint8_t v___x_4411_; 
v___x_4411_ = 1;
return v___x_4411_;
}
case 0:
{
uint8_t v___x_4412_; 
v___x_4412_ = 1;
return v___x_4412_;
}
case 9:
{
uint8_t v___x_4413_; 
v___x_4413_ = 1;
return v___x_4413_;
}
case 2:
{
uint8_t v___x_4414_; 
v___x_4414_ = 1;
return v___x_4414_;
}
case 1:
{
uint8_t v___x_4415_; 
v___x_4415_ = 1;
return v___x_4415_;
}
default: 
{
uint8_t v___x_4416_; 
v___x_4416_ = 0;
return v___x_4416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4417_){
_start:
{
uint8_t v_res_4418_; lean_object* v_r_4419_; 
v_res_4418_ = l_Lean_Expr_isAtomic(v_x_4417_);
lean_dec_ref(v_x_4417_);
v_r_4419_ = lean_box(v_res_4418_);
return v_r_4419_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4425_ = lean_box(0);
v___x_4426_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4427_ = l_Lean_Expr_const___override(v___x_4426_, v___x_4425_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4428_, lean_object* v_proof_4429_){
_start:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4430_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4431_ = l_Lean_mkAppB(v___x_4430_, v_pred_4428_, v_proof_4429_);
return v___x_4431_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4436_ = lean_box(0);
v___x_4437_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4438_ = l_Lean_Expr_const___override(v___x_4437_, v___x_4436_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4439_, lean_object* v_proof_4440_){
_start:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4441_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4442_ = l_Lean_mkAppB(v___x_4441_, v_pred_4439_, v_proof_4440_);
return v___x_4442_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4443_; 
v___x_4443_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4443_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4444_; 
v___x_4444_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4445_){
_start:
{
lean_inc_ref(v_val_4445_);
return v_val_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4446_);
lean_dec_ref(v_val_4446_);
return v_res_4447_;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4450_, lean_object* v_x_4451_){
_start:
{
uint8_t v___x_4452_; 
v___x_4452_ = lean_expr_equal(v_x_4450_, v_x_4451_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4453_, lean_object* v_x_4454_){
_start:
{
uint8_t v_res_4455_; lean_object* v_r_4456_; 
v_res_4455_ = l_Lean_ExprStructEq_beq(v_x_4453_, v_x_4454_);
lean_dec_ref(v_x_4454_);
lean_dec_ref(v_x_4453_);
v_r_4456_ = lean_box(v_res_4455_);
return v_r_4456_;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4457_){
_start:
{
uint64_t v___x_4458_; 
v___x_4458_ = l_Lean_Expr_hash(v_x_4457_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4459_){
_start:
{
uint64_t v_res_4460_; lean_object* v_r_4461_; 
v_res_4460_ = l_Lean_ExprStructEq_hash(v_x_4459_);
lean_dec_ref(v_x_4459_);
v_r_4461_ = lean_box_uint64(v_res_4460_);
return v_r_4461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4468_, lean_object* v_start_4469_, lean_object* v_b_4470_, lean_object* v_i_4471_){
_start:
{
uint8_t v___x_4472_; 
v___x_4472_ = lean_nat_dec_le(v_i_4471_, v_start_4469_);
if (v___x_4472_ == 0)
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v_i_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4473_ = l_Lean_instInhabitedExpr;
v___x_4474_ = lean_unsigned_to_nat(1u);
v_i_4475_ = lean_nat_sub(v_i_4471_, v___x_4474_);
lean_dec(v_i_4471_);
v___x_4476_ = lean_array_get_borrowed(v___x_4473_, v_revArgs_4468_, v_i_4475_);
lean_inc(v___x_4476_);
v___x_4477_ = l_Lean_Expr_app___override(v_b_4470_, v___x_4476_);
v_b_4470_ = v___x_4477_;
v_i_4471_ = v_i_4475_;
goto _start;
}
else
{
lean_dec(v_i_4471_);
return v_b_4470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4479_, lean_object* v_start_4480_, lean_object* v_b_4481_, lean_object* v_i_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4479_, v_start_4480_, v_b_4481_, v_i_4482_);
lean_dec(v_start_4480_);
lean_dec_ref(v_revArgs_4479_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4484_, lean_object* v_beginIdx_4485_, lean_object* v_endIdx_4486_, lean_object* v_revArgs_4487_){
_start:
{
lean_object* v___x_4488_; 
v___x_4488_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4487_, v_beginIdx_4485_, v_f_4484_, v_endIdx_4486_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4489_, lean_object* v_beginIdx_4490_, lean_object* v_endIdx_4491_, lean_object* v_revArgs_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l_Lean_Expr_mkAppRevRange(v_f_4489_, v_beginIdx_4490_, v_endIdx_4491_, v_revArgs_4492_);
lean_dec_ref(v_revArgs_4492_);
lean_dec(v_beginIdx_4490_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4494_, uint8_t v_useZeta_4495_, uint8_t v_preserveMData_4496_, lean_object* v_sz_4497_, lean_object* v_e_4498_, lean_object* v_i_4499_){
_start:
{
switch(lean_obj_tag(v_e_4498_))
{
case 6:
{
lean_object* v_body_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; uint8_t v___x_4508_; 
v_body_4505_ = lean_ctor_get(v_e_4498_, 2);
lean_inc_ref(v_body_4505_);
lean_dec_ref_known(v_e_4498_, 3);
v___x_4506_ = lean_unsigned_to_nat(1u);
v___x_4507_ = lean_nat_add(v_i_4499_, v___x_4506_);
lean_dec(v_i_4499_);
v___x_4508_ = lean_nat_dec_lt(v___x_4507_, v_sz_4497_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; 
lean_dec(v___x_4507_);
v___x_4509_ = lean_expr_instantiate(v_body_4505_, v_revArgs_4494_);
lean_dec_ref(v_body_4505_);
return v___x_4509_;
}
else
{
v_e_4498_ = v_body_4505_;
v_i_4499_ = v___x_4507_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4495_ == 0)
{
goto v___jp_4500_;
}
else
{
lean_object* v_value_4511_; lean_object* v_body_4512_; uint8_t v___x_4513_; 
v_value_4511_ = lean_ctor_get(v_e_4498_, 2);
v_body_4512_ = lean_ctor_get(v_e_4498_, 3);
v___x_4513_ = lean_nat_dec_lt(v_i_4499_, v_sz_4497_);
if (v___x_4513_ == 0)
{
goto v___jp_4500_;
}
else
{
lean_object* v___x_4514_; 
lean_inc_ref(v_body_4512_);
lean_inc_ref(v_value_4511_);
lean_dec_ref_known(v_e_4498_, 4);
v___x_4514_ = lean_expr_instantiate1(v_body_4512_, v_value_4511_);
lean_dec_ref(v_value_4511_);
lean_dec_ref(v_body_4512_);
v_e_4498_ = v___x_4514_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4496_ == 0)
{
lean_object* v_expr_4516_; 
v_expr_4516_ = lean_ctor_get(v_e_4498_, 1);
lean_inc_ref(v_expr_4516_);
lean_dec_ref_known(v_e_4498_, 2);
v_e_4498_ = v_expr_4516_;
goto _start;
}
else
{
goto v___jp_4500_;
}
}
default: 
{
goto v___jp_4500_;
}
}
v___jp_4500_:
{
lean_object* v_n_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v_n_4501_ = lean_nat_sub(v_sz_4497_, v_i_4499_);
lean_dec(v_i_4499_);
v___x_4502_ = lean_expr_instantiate_range(v_e_4498_, v_n_4501_, v_sz_4497_, v_revArgs_4494_);
lean_dec_ref(v_e_4498_);
v___x_4503_ = lean_unsigned_to_nat(0u);
v___x_4504_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4494_, v___x_4503_, v___x_4502_, v_n_4501_);
return v___x_4504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4518_, lean_object* v_useZeta_4519_, lean_object* v_preserveMData_4520_, lean_object* v_sz_4521_, lean_object* v_e_4522_, lean_object* v_i_4523_){
_start:
{
uint8_t v_useZeta_boxed_4524_; uint8_t v_preserveMData_boxed_4525_; lean_object* v_res_4526_; 
v_useZeta_boxed_4524_ = lean_unbox(v_useZeta_4519_);
v_preserveMData_boxed_4525_ = lean_unbox(v_preserveMData_4520_);
v_res_4526_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4518_, v_useZeta_boxed_4524_, v_preserveMData_boxed_4525_, v_sz_4521_, v_e_4522_, v_i_4523_);
lean_dec(v_sz_4521_);
lean_dec_ref(v_revArgs_4518_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4527_, lean_object* v_revArgs_4528_, uint8_t v_useZeta_4529_, uint8_t v_preserveMData_4530_){
_start:
{
lean_object* v_sz_4531_; lean_object* v___x_4532_; uint8_t v___x_4533_; 
v_sz_4531_ = lean_array_get_size(v_revArgs_4528_);
v___x_4532_ = lean_unsigned_to_nat(0u);
v___x_4533_ = lean_nat_dec_eq(v_sz_4531_, v___x_4532_);
if (v___x_4533_ == 0)
{
lean_object* v___x_4534_; 
v___x_4534_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4528_, v_useZeta_4529_, v_preserveMData_4530_, v_sz_4531_, v_f_4527_, v___x_4532_);
return v___x_4534_;
}
else
{
return v_f_4527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4535_, lean_object* v_revArgs_4536_, lean_object* v_useZeta_4537_, lean_object* v_preserveMData_4538_){
_start:
{
uint8_t v_useZeta_boxed_4539_; uint8_t v_preserveMData_boxed_4540_; lean_object* v_res_4541_; 
v_useZeta_boxed_4539_ = lean_unbox(v_useZeta_4537_);
v_preserveMData_boxed_4540_ = lean_unbox(v_preserveMData_4538_);
v_res_4541_ = l_Lean_Expr_betaRev(v_f_4535_, v_revArgs_4536_, v_useZeta_boxed_4539_, v_preserveMData_boxed_4540_);
lean_dec_ref(v_revArgs_4536_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4542_, lean_object* v_args_4543_){
_start:
{
lean_object* v___x_4544_; uint8_t v___x_4545_; lean_object* v___x_4546_; 
v___x_4544_ = l_Array_reverse___redArg(v_args_4543_);
v___x_4545_ = 0;
v___x_4546_ = l_Lean_Expr_betaRev(v_f_4542_, v___x_4544_, v___x_4545_, v___x_4545_);
lean_dec_ref(v___x_4544_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4547_){
_start:
{
switch(lean_obj_tag(v_x_4547_))
{
case 6:
{
lean_object* v_body_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; 
v_body_4548_ = lean_ctor_get(v_x_4547_, 2);
v___x_4549_ = l_Lean_Expr_getNumHeadLambdas(v_body_4548_);
v___x_4550_ = lean_unsigned_to_nat(1u);
v___x_4551_ = lean_nat_add(v___x_4549_, v___x_4550_);
lean_dec(v___x_4549_);
return v___x_4551_;
}
case 10:
{
lean_object* v_expr_4552_; 
v_expr_4552_ = lean_ctor_get(v_x_4547_, 1);
v_x_4547_ = v_expr_4552_;
goto _start;
}
default: 
{
lean_object* v___x_4554_; 
v___x_4554_ = lean_unsigned_to_nat(0u);
return v___x_4554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Lean_Expr_getNumHeadLambdas(v_x_4555_);
lean_dec_ref(v_x_4555_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object* v_x_4557_){
_start:
{
switch(lean_obj_tag(v_x_4557_))
{
case 6:
{
lean_object* v_body_4558_; 
v_body_4558_ = lean_ctor_get(v_x_4557_, 2);
v_x_4557_ = v_body_4558_;
goto _start;
}
case 10:
{
lean_object* v_expr_4560_; 
v_expr_4560_ = lean_ctor_get(v_x_4557_, 1);
v_x_4557_ = v_expr_4560_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_4557_);
return v_x_4557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object* v_x_4562_){
_start:
{
lean_object* v_res_4563_; 
v_res_4563_ = l_Lean_Expr_getLambdaBody(v_x_4562_);
lean_dec_ref(v_x_4562_);
return v_res_4563_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4564_, lean_object* v_x_4565_){
_start:
{
switch(lean_obj_tag(v_x_4565_))
{
case 6:
{
uint8_t v___x_4566_; 
v___x_4566_ = 1;
return v___x_4566_;
}
case 8:
{
if (v_useZeta_4564_ == 0)
{
return v_useZeta_4564_;
}
else
{
lean_object* v_body_4567_; 
v_body_4567_ = lean_ctor_get(v_x_4565_, 3);
v_x_4565_ = v_body_4567_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4569_; 
v_expr_4569_ = lean_ctor_get(v_x_4565_, 1);
v_x_4565_ = v_expr_4569_;
goto _start;
}
default: 
{
uint8_t v___x_4571_; 
v___x_4571_ = 0;
return v___x_4571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4572_, lean_object* v_x_4573_){
_start:
{
uint8_t v_useZeta_boxed_4574_; uint8_t v_res_4575_; lean_object* v_r_4576_; 
v_useZeta_boxed_4574_ = lean_unbox(v_useZeta_4572_);
v_res_4575_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4574_, v_x_4573_);
lean_dec_ref(v_x_4573_);
v_r_4576_ = lean_box(v_res_4575_);
return v_r_4576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4577_){
_start:
{
lean_object* v_f_4578_; uint8_t v___x_4579_; uint8_t v___x_4580_; 
v_f_4578_ = l_Lean_Expr_getAppFn(v_e_4577_);
v___x_4579_ = 0;
v___x_4580_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4579_, v_f_4578_);
if (v___x_4580_ == 0)
{
lean_dec_ref(v_f_4578_);
return v_e_4577_;
}
else
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4581_ = l_Lean_Expr_getAppNumArgs(v_e_4577_);
v___x_4582_ = lean_mk_empty_array_with_capacity(v___x_4581_);
lean_dec(v___x_4581_);
v___x_4583_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4577_, v___x_4582_);
v___x_4584_ = l_Lean_Expr_betaRev(v_f_4578_, v___x_4583_, v___x_4579_, v___x_4579_);
lean_dec_ref(v___x_4583_);
return v___x_4584_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4585_, uint8_t v_useZeta_4586_){
_start:
{
uint8_t v___x_4587_; 
v___x_4587_ = l_Lean_Expr_isApp(v_e_4585_);
if (v___x_4587_ == 0)
{
return v___x_4587_;
}
else
{
lean_object* v___x_4588_; uint8_t v___x_4589_; 
v___x_4588_ = l_Lean_Expr_getAppFn(v_e_4585_);
v___x_4589_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4586_, v___x_4588_);
lean_dec_ref(v___x_4588_);
return v___x_4589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4590_, lean_object* v_useZeta_4591_){
_start:
{
uint8_t v_useZeta_boxed_4592_; uint8_t v_res_4593_; lean_object* v_r_4594_; 
v_useZeta_boxed_4592_ = lean_unbox(v_useZeta_4591_);
v_res_4593_ = l_Lean_Expr_isHeadBetaTarget(v_e_4590_, v_useZeta_boxed_4592_);
lean_dec_ref(v_e_4590_);
v_r_4594_ = lean_box(v_res_4593_);
return v_r_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4595_, lean_object* v_x_4596_, lean_object* v_x_4597_){
_start:
{
lean_object* v_f_4599_; 
if (lean_obj_tag(v_x_4595_) == 5)
{
lean_object* v_arg_4603_; 
v_arg_4603_ = lean_ctor_get(v_x_4595_, 1);
if (lean_obj_tag(v_arg_4603_) == 0)
{
lean_object* v_fn_4604_; lean_object* v_deBruijnIndex_4605_; lean_object* v_zero_4606_; uint8_t v_isZero_4607_; 
v_fn_4604_ = lean_ctor_get(v_x_4595_, 0);
v_deBruijnIndex_4605_ = lean_ctor_get(v_arg_4603_, 0);
v_zero_4606_ = lean_unsigned_to_nat(0u);
v_isZero_4607_ = lean_nat_dec_eq(v_x_4596_, v_zero_4606_);
if (v_isZero_4607_ == 1)
{
lean_dec(v_x_4597_);
lean_dec(v_x_4596_);
v_f_4599_ = v_x_4595_;
goto v___jp_4598_;
}
else
{
uint8_t v___x_4608_; 
lean_inc(v_deBruijnIndex_4605_);
lean_inc_ref(v_fn_4604_);
lean_dec_ref_known(v_x_4595_, 2);
v___x_4608_ = lean_nat_dec_eq(v_deBruijnIndex_4605_, v_x_4597_);
lean_dec(v_deBruijnIndex_4605_);
if (v___x_4608_ == 0)
{
lean_object* v___x_4609_; 
lean_dec_ref(v_fn_4604_);
lean_dec(v_x_4597_);
lean_dec(v_x_4596_);
v___x_4609_ = lean_box(0);
return v___x_4609_;
}
else
{
lean_object* v_one_4610_; lean_object* v_n_4611_; lean_object* v___x_4612_; 
v_one_4610_ = lean_unsigned_to_nat(1u);
v_n_4611_ = lean_nat_sub(v_x_4596_, v_one_4610_);
lean_dec(v_x_4596_);
v___x_4612_ = lean_nat_add(v_x_4597_, v_one_4610_);
lean_dec(v_x_4597_);
v_x_4595_ = v_fn_4604_;
v_x_4596_ = v_n_4611_;
v_x_4597_ = v___x_4612_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4614_; uint8_t v_isZero_4615_; 
lean_dec(v_x_4597_);
v_zero_4614_ = lean_unsigned_to_nat(0u);
v_isZero_4615_ = lean_nat_dec_eq(v_x_4596_, v_zero_4614_);
lean_dec(v_x_4596_);
if (v_isZero_4615_ == 1)
{
v_f_4599_ = v_x_4595_;
goto v___jp_4598_;
}
else
{
lean_object* v___x_4616_; 
lean_dec_ref_known(v_x_4595_, 2);
v___x_4616_ = lean_box(0);
return v___x_4616_;
}
}
}
else
{
lean_object* v_zero_4617_; uint8_t v_isZero_4618_; 
lean_dec(v_x_4597_);
v_zero_4617_ = lean_unsigned_to_nat(0u);
v_isZero_4618_ = lean_nat_dec_eq(v_x_4596_, v_zero_4617_);
lean_dec(v_x_4596_);
if (v_isZero_4618_ == 1)
{
v_f_4599_ = v_x_4595_;
goto v___jp_4598_;
}
else
{
lean_object* v___x_4619_; 
lean_dec_ref(v_x_4595_);
v___x_4619_ = lean_box(0);
return v___x_4619_;
}
}
v___jp_4598_:
{
uint8_t v___x_4600_; 
v___x_4600_ = l_Lean_Expr_hasLooseBVars(v_f_4599_);
if (v___x_4600_ == 0)
{
lean_object* v___x_4601_; 
v___x_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4601_, 0, v_f_4599_);
return v___x_4601_;
}
else
{
lean_object* v___x_4602_; 
lean_dec_ref(v_f_4599_);
v___x_4602_ = lean_box(0);
return v___x_4602_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4620_, lean_object* v_x_4621_){
_start:
{
if (lean_obj_tag(v_x_4620_) == 6)
{
lean_object* v_body_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v_body_4622_ = lean_ctor_get(v_x_4620_, 2);
lean_inc_ref(v_body_4622_);
lean_dec_ref_known(v_x_4620_, 3);
v___x_4623_ = lean_unsigned_to_nat(1u);
v___x_4624_ = lean_nat_add(v_x_4621_, v___x_4623_);
lean_dec(v_x_4621_);
v_x_4620_ = v_body_4622_;
v_x_4621_ = v___x_4624_;
goto _start;
}
else
{
lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___x_4626_ = lean_unsigned_to_nat(0u);
v___x_4627_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4620_, v_x_4621_, v___x_4626_);
return v___x_4627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4628_){
_start:
{
lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4629_ = lean_unsigned_to_nat(0u);
v___x_4630_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4628_, v___x_4629_);
return v___x_4630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4631_){
_start:
{
if (lean_obj_tag(v_x_4631_) == 6)
{
lean_object* v_body_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
v_body_4632_ = lean_ctor_get(v_x_4631_, 2);
lean_inc_ref(v_body_4632_);
lean_dec_ref_known(v_x_4631_, 3);
v___x_4633_ = lean_unsigned_to_nat(1u);
v___x_4634_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4632_, v___x_4633_);
return v___x_4634_;
}
else
{
lean_object* v___x_4635_; 
lean_dec_ref(v_x_4631_);
v___x_4635_ = lean_box(0);
return v___x_4635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4639_){
_start:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; uint8_t v___x_4642_; 
v___x_4640_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4641_ = lean_unsigned_to_nat(2u);
v___x_4642_ = l_Lean_Expr_isAppOfArity(v_e_4639_, v___x_4640_, v___x_4641_);
if (v___x_4642_ == 0)
{
lean_object* v___x_4643_; 
v___x_4643_ = lean_box(0);
return v___x_4643_;
}
else
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = l_Lean_Expr_appArg_x21(v_e_4639_);
v___x_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4644_);
return v___x_4645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4646_);
lean_dec_ref(v_e_4646_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4651_){
_start:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; uint8_t v___x_4654_; 
v___x_4652_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4653_ = lean_unsigned_to_nat(2u);
v___x_4654_ = l_Lean_Expr_isAppOfArity(v_e_4651_, v___x_4652_, v___x_4653_);
if (v___x_4654_ == 0)
{
lean_object* v___x_4655_; 
v___x_4655_ = lean_box(0);
return v___x_4655_;
}
else
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = l_Lean_Expr_appArg_x21(v_e_4651_);
v___x_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4656_);
return v___x_4657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4658_);
lean_dec_ref(v_e_4658_);
return v_res_4659_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOutParam(lean_object* v_e_4663_){
_start:
{
lean_object* v___x_4664_; lean_object* v___x_4665_; uint8_t v___x_4666_; 
v___x_4664_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4665_ = lean_unsigned_to_nat(1u);
v___x_4666_ = l_Lean_Expr_isAppOfArity(v_e_4663_, v___x_4664_, v___x_4665_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4667_){
_start:
{
uint8_t v_res_4668_; lean_object* v_r_4669_; 
v_res_4668_ = l_Lean_Expr_isOutParam(v_e_4667_);
lean_dec_ref(v_e_4667_);
v_r_4669_ = lean_box(v_res_4668_);
return v_r_4669_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4673_){
_start:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; uint8_t v___x_4676_; 
v___x_4674_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4675_ = lean_unsigned_to_nat(1u);
v___x_4676_ = l_Lean_Expr_isAppOfArity(v_e_4673_, v___x_4674_, v___x_4675_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4677_){
_start:
{
uint8_t v_res_4678_; lean_object* v_r_4679_; 
v_res_4678_ = l_Lean_Expr_isSemiOutParam(v_e_4677_);
lean_dec_ref(v_e_4677_);
v_r_4679_ = lean_box(v_res_4678_);
return v_r_4679_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4680_){
_start:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; uint8_t v___x_4683_; 
v___x_4681_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4682_ = lean_unsigned_to_nat(2u);
v___x_4683_ = l_Lean_Expr_isAppOfArity(v_e_4680_, v___x_4681_, v___x_4682_);
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4684_){
_start:
{
uint8_t v_res_4685_; lean_object* v_r_4686_; 
v_res_4685_ = l_Lean_Expr_isOptParam(v_e_4684_);
lean_dec_ref(v_e_4684_);
v_r_4686_ = lean_box(v_res_4685_);
return v_r_4686_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4687_){
_start:
{
lean_object* v___x_4688_; lean_object* v___x_4689_; uint8_t v___x_4690_; 
v___x_4688_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4689_ = lean_unsigned_to_nat(2u);
v___x_4690_ = l_Lean_Expr_isAppOfArity(v_e_4687_, v___x_4688_, v___x_4689_);
return v___x_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4691_){
_start:
{
uint8_t v_res_4692_; lean_object* v_r_4693_; 
v_res_4692_ = l_Lean_Expr_isAutoParam(v_e_4691_);
lean_dec_ref(v_e_4691_);
v_r_4693_ = lean_box(v_res_4692_);
return v_r_4693_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4694_){
_start:
{
lean_object* v___x_4695_; 
v___x_4695_ = l_Lean_Expr_getAppFn(v_e_4694_);
if (lean_obj_tag(v___x_4695_) == 4)
{
lean_object* v_declName_4696_; uint8_t v___y_4698_; lean_object* v___x_4703_; uint8_t v___x_4704_; 
v_declName_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_declName_4696_);
lean_dec_ref_known(v___x_4695_, 2);
v___x_4703_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4704_ = lean_name_eq(v_declName_4696_, v___x_4703_);
if (v___x_4704_ == 0)
{
lean_object* v___x_4705_; uint8_t v___x_4706_; 
v___x_4705_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4706_ = lean_name_eq(v_declName_4696_, v___x_4705_);
v___y_4698_ = v___x_4706_;
goto v___jp_4697_;
}
else
{
v___y_4698_ = v___x_4704_;
goto v___jp_4697_;
}
v___jp_4697_:
{
if (v___y_4698_ == 0)
{
lean_object* v___x_4699_; uint8_t v___x_4700_; 
v___x_4699_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4700_ = lean_name_eq(v_declName_4696_, v___x_4699_);
if (v___x_4700_ == 0)
{
lean_object* v___x_4701_; uint8_t v___x_4702_; 
v___x_4701_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4702_ = lean_name_eq(v_declName_4696_, v___x_4701_);
lean_dec(v_declName_4696_);
return v___x_4702_;
}
else
{
lean_dec(v_declName_4696_);
return v___x_4700_;
}
}
else
{
lean_dec(v_declName_4696_);
return v___y_4698_;
}
}
}
else
{
uint8_t v___x_4707_; 
lean_dec_ref(v___x_4695_);
v___x_4707_ = 0;
return v___x_4707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4708_){
_start:
{
uint8_t v_res_4709_; lean_object* v_r_4710_; 
v_res_4709_ = l_Lean_Expr_isTypeAnnotation(v_e_4708_);
lean_dec_ref(v_e_4708_);
v_r_4710_ = lean_box(v_res_4709_);
return v_r_4710_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4711_){
_start:
{
uint8_t v___y_4713_; uint8_t v___y_4717_; uint8_t v___x_4723_; 
v___x_4723_ = l_Lean_Expr_isOptParam(v_e_4711_);
if (v___x_4723_ == 0)
{
uint8_t v___x_4724_; 
v___x_4724_ = l_Lean_Expr_isAutoParam(v_e_4711_);
v___y_4717_ = v___x_4724_;
goto v___jp_4716_;
}
else
{
v___y_4717_ = v___x_4723_;
goto v___jp_4716_;
}
v___jp_4712_:
{
if (v___y_4713_ == 0)
{
return v_e_4711_;
}
else
{
lean_object* v___x_4714_; 
v___x_4714_ = l_Lean_Expr_appArg_x21(v_e_4711_);
lean_dec_ref(v_e_4711_);
v_e_4711_ = v___x_4714_;
goto _start;
}
}
v___jp_4716_:
{
if (v___y_4717_ == 0)
{
uint8_t v___x_4718_; 
v___x_4718_ = l_Lean_Expr_isOutParam(v_e_4711_);
if (v___x_4718_ == 0)
{
uint8_t v___x_4719_; 
v___x_4719_ = l_Lean_Expr_isSemiOutParam(v_e_4711_);
v___y_4713_ = v___x_4719_;
goto v___jp_4712_;
}
else
{
v___y_4713_ = v___x_4718_;
goto v___jp_4712_;
}
}
else
{
lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4720_ = l_Lean_Expr_appFn_x21(v_e_4711_);
lean_dec_ref(v_e_4711_);
v___x_4721_ = l_Lean_Expr_appArg_x21(v___x_4720_);
lean_dec_ref(v___x_4720_);
v_e_4711_ = v___x_4721_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4725_){
_start:
{
lean_object* v___x_4726_; lean_object* v_e_x27_4727_; uint8_t v___x_4728_; 
v___x_4726_ = l_Lean_Expr_consumeMData(v_e_4725_);
v_e_x27_4727_ = lean_expr_consume_type_annotations(v___x_4726_);
v___x_4728_ = lean_expr_eqv(v_e_x27_4727_, v_e_4725_);
if (v___x_4728_ == 0)
{
lean_dec_ref(v_e_4725_);
v_e_4725_ = v_e_x27_4727_;
goto _start;
}
else
{
lean_dec_ref(v_e_x27_4727_);
return v_e_4725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4730_){
_start:
{
lean_object* v_fn_4731_; lean_object* v___x_4732_; 
v_fn_4731_ = lean_ctor_get(v_e_4730_, 0);
lean_inc_ref(v_fn_4731_);
lean_dec_ref(v_e_4730_);
v___x_4732_ = l_Lean_Expr_cleanupAnnotations(v_fn_4731_);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* v_e_4733_, lean_object* v_h_4734_){
_start:
{
lean_object* v___x_4735_; 
v___x_4735_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4733_);
return v___x_4735_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4739_){
_start:
{
lean_object* v___x_4740_; lean_object* v___x_4741_; uint8_t v___x_4742_; 
v___x_4740_ = l_Lean_Expr_cleanupAnnotations(v_e_4739_);
v___x_4741_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4742_ = l_Lean_Expr_isConstOf(v___x_4740_, v___x_4741_);
lean_dec_ref(v___x_4740_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4743_){
_start:
{
uint8_t v_res_4744_; lean_object* v_r_4745_; 
v_res_4744_ = l_Lean_Expr_isFalse(v_e_4743_);
v_r_4745_ = lean_box(v_res_4744_);
return v_r_4745_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4749_){
_start:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; uint8_t v___x_4752_; 
v___x_4750_ = l_Lean_Expr_cleanupAnnotations(v_e_4749_);
v___x_4751_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4752_ = l_Lean_Expr_isConstOf(v___x_4750_, v___x_4751_);
lean_dec_ref(v___x_4750_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4753_){
_start:
{
uint8_t v_res_4754_; lean_object* v_r_4755_; 
v_res_4754_ = l_Lean_Expr_isTrue(v_e_4753_);
v_r_4755_ = lean_box(v_res_4754_);
return v_r_4755_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object* v_e_4760_){
_start:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; uint8_t v___x_4763_; 
v___x_4761_ = l_Lean_Expr_cleanupAnnotations(v_e_4760_);
v___x_4762_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_4763_ = l_Lean_Expr_isConstOf(v___x_4761_, v___x_4762_);
lean_dec_ref(v___x_4761_);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object* v_e_4764_){
_start:
{
uint8_t v_res_4765_; lean_object* v_r_4766_; 
v_res_4765_ = l_Lean_Expr_isBoolFalse(v_e_4764_);
v_r_4766_ = lean_box(v_res_4765_);
return v_r_4766_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object* v_e_4770_){
_start:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; uint8_t v___x_4773_; 
v___x_4771_ = l_Lean_Expr_cleanupAnnotations(v_e_4770_);
v___x_4772_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_4773_ = l_Lean_Expr_isConstOf(v___x_4771_, v___x_4772_);
lean_dec_ref(v___x_4771_);
return v___x_4773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object* v_e_4774_){
_start:
{
uint8_t v_res_4775_; lean_object* v_r_4776_; 
v_res_4775_ = l_Lean_Expr_isBoolTrue(v_e_4774_);
v_r_4776_ = lean_box(v_res_4775_);
return v_r_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* v_x_4777_){
_start:
{
switch(lean_obj_tag(v_x_4777_))
{
case 10:
{
lean_object* v_expr_4778_; 
v_expr_4778_ = lean_ctor_get(v_x_4777_, 1);
lean_inc_ref(v_expr_4778_);
lean_dec_ref_known(v_x_4777_, 2);
v_x_4777_ = v_expr_4778_;
goto _start;
}
case 7:
{
lean_object* v_body_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v_body_4780_ = lean_ctor_get(v_x_4777_, 2);
lean_inc_ref(v_body_4780_);
lean_dec_ref_known(v_x_4777_, 3);
v___x_4781_ = l_Lean_Expr_getForallArity(v_body_4780_);
v___x_4782_ = lean_unsigned_to_nat(1u);
v___x_4783_ = lean_nat_add(v___x_4781_, v___x_4782_);
lean_dec(v___x_4781_);
return v___x_4783_;
}
default: 
{
uint8_t v___x_4784_; uint8_t v___x_4785_; 
v___x_4784_ = 0;
v___x_4785_ = l_Lean_Expr_isHeadBetaTarget(v_x_4777_, v___x_4784_);
if (v___x_4785_ == 0)
{
lean_object* v_e_x27_4786_; uint8_t v___x_4787_; 
lean_inc_ref(v_x_4777_);
v_e_x27_4786_ = l_Lean_Expr_cleanupAnnotations(v_x_4777_);
v___x_4787_ = lean_expr_eqv(v_x_4777_, v_e_x27_4786_);
lean_dec_ref(v_x_4777_);
if (v___x_4787_ == 0)
{
v_x_4777_ = v_e_x27_4786_;
goto _start;
}
else
{
if (v___x_4785_ == 0)
{
lean_object* v___x_4789_; 
lean_dec_ref(v_e_x27_4786_);
v___x_4789_ = lean_unsigned_to_nat(0u);
return v___x_4789_;
}
else
{
v_x_4777_ = v_e_x27_4786_;
goto _start;
}
}
}
else
{
lean_object* v___x_4791_; 
v___x_4791_ = l_Lean_Expr_headBeta(v_x_4777_);
v_x_4777_ = v___x_4791_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4793_){
_start:
{
lean_object* v___x_4794_; uint8_t v___x_4795_; 
v___x_4794_ = l_Lean_Expr_cleanupAnnotations(v_e_4793_);
v___x_4795_ = l_Lean_Expr_isApp(v___x_4794_);
if (v___x_4795_ == 0)
{
lean_object* v___x_4796_; 
lean_dec_ref(v___x_4794_);
v___x_4796_ = lean_box(0);
return v___x_4796_;
}
else
{
lean_object* v___x_4797_; uint8_t v___x_4798_; 
v___x_4797_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4794_);
v___x_4798_ = l_Lean_Expr_isApp(v___x_4797_);
if (v___x_4798_ == 0)
{
lean_object* v___x_4799_; 
lean_dec_ref(v___x_4797_);
v___x_4799_ = lean_box(0);
return v___x_4799_;
}
else
{
lean_object* v_arg_4800_; lean_object* v___x_4801_; uint8_t v___x_4802_; 
v_arg_4800_ = lean_ctor_get(v___x_4797_, 1);
lean_inc_ref(v_arg_4800_);
v___x_4801_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4797_);
v___x_4802_ = l_Lean_Expr_isApp(v___x_4801_);
if (v___x_4802_ == 0)
{
lean_object* v___x_4803_; 
lean_dec_ref(v___x_4801_);
lean_dec_ref(v_arg_4800_);
v___x_4803_ = lean_box(0);
return v___x_4803_;
}
else
{
lean_object* v___x_4804_; lean_object* v___x_4805_; uint8_t v___x_4806_; 
v___x_4804_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4801_);
v___x_4805_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4806_ = l_Lean_Expr_isConstOf(v___x_4804_, v___x_4805_);
lean_dec_ref(v___x_4804_);
if (v___x_4806_ == 0)
{
lean_object* v___x_4807_; 
lean_dec_ref(v_arg_4800_);
v___x_4807_ = lean_box(0);
return v___x_4807_;
}
else
{
if (lean_obj_tag(v_arg_4800_) == 9)
{
lean_object* v_a_4808_; 
v_a_4808_ = lean_ctor_get(v_arg_4800_, 0);
lean_inc_ref(v_a_4808_);
lean_dec_ref_known(v_arg_4800_, 1);
if (lean_obj_tag(v_a_4808_) == 0)
{
lean_object* v_val_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4816_; 
v_val_4809_ = lean_ctor_get(v_a_4808_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v_a_4808_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4811_ = v_a_4808_;
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_val_4809_);
lean_dec(v_a_4808_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___x_4814_; 
if (v_isShared_4812_ == 0)
{
lean_ctor_set_tag(v___x_4811_, 1);
v___x_4814_ = v___x_4811_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_val_4809_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
}
else
{
lean_object* v___x_4817_; 
lean_dec_ref(v_a_4808_);
v___x_4817_ = lean_box(0);
return v___x_4817_;
}
}
else
{
lean_object* v___x_4818_; 
lean_dec_ref(v_arg_4800_);
v___x_4818_ = lean_box(0);
return v___x_4818_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4824_){
_start:
{
lean_object* v___x_4837_; uint8_t v___x_4838_; 
lean_inc_ref(v_e_4824_);
v___x_4837_ = l_Lean_Expr_cleanupAnnotations(v_e_4824_);
v___x_4838_ = l_Lean_Expr_isApp(v___x_4837_);
if (v___x_4838_ == 0)
{
lean_dec_ref(v___x_4837_);
goto v___jp_4825_;
}
else
{
lean_object* v_arg_4839_; lean_object* v___x_4840_; uint8_t v___x_4841_; 
v_arg_4839_ = lean_ctor_get(v___x_4837_, 1);
lean_inc_ref(v_arg_4839_);
v___x_4840_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4837_);
v___x_4841_ = l_Lean_Expr_isApp(v___x_4840_);
if (v___x_4841_ == 0)
{
lean_dec_ref(v___x_4840_);
lean_dec_ref(v_arg_4839_);
goto v___jp_4825_;
}
else
{
lean_object* v___x_4842_; uint8_t v___x_4843_; 
v___x_4842_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4840_);
v___x_4843_ = l_Lean_Expr_isApp(v___x_4842_);
if (v___x_4843_ == 0)
{
lean_dec_ref(v___x_4842_);
lean_dec_ref(v_arg_4839_);
goto v___jp_4825_;
}
else
{
lean_object* v___x_4844_; lean_object* v___x_4845_; uint8_t v___x_4846_; 
v___x_4844_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4842_);
v___x_4845_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4846_ = l_Lean_Expr_isConstOf(v___x_4844_, v___x_4845_);
lean_dec_ref(v___x_4844_);
if (v___x_4846_ == 0)
{
lean_dec_ref(v_arg_4839_);
goto v___jp_4825_;
}
else
{
lean_object* v___x_4847_; 
lean_dec_ref(v_e_4824_);
v___x_4847_ = l_Lean_Expr_nat_x3f(v_arg_4839_);
if (lean_obj_tag(v___x_4847_) == 0)
{
lean_object* v___x_4848_; 
v___x_4848_ = lean_box(0);
return v___x_4848_;
}
else
{
lean_object* v_val_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4861_; 
v_val_4849_ = lean_ctor_get(v___x_4847_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4851_ = v___x_4847_;
v_isShared_4852_ = v_isSharedCheck_4861_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_val_4849_);
lean_dec(v___x_4847_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4861_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4853_; uint8_t v___x_4854_; 
v___x_4853_ = lean_unsigned_to_nat(0u);
v___x_4854_ = lean_nat_dec_eq(v_val_4849_, v___x_4853_);
if (v___x_4854_ == 0)
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4858_; 
v___x_4855_ = lean_nat_to_int(v_val_4849_);
v___x_4856_ = lean_int_neg(v___x_4855_);
lean_dec(v___x_4855_);
if (v_isShared_4852_ == 0)
{
lean_ctor_set(v___x_4851_, 0, v___x_4856_);
v___x_4858_ = v___x_4851_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4856_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
else
{
lean_object* v___x_4860_; 
lean_del_object(v___x_4851_);
lean_dec(v_val_4849_);
v___x_4860_ = lean_box(0);
return v___x_4860_;
}
}
}
}
}
}
}
v___jp_4825_:
{
lean_object* v___x_4826_; 
v___x_4826_ = l_Lean_Expr_nat_x3f(v_e_4824_);
if (lean_obj_tag(v___x_4826_) == 0)
{
lean_object* v___x_4827_; 
v___x_4827_ = lean_box(0);
return v___x_4827_;
}
else
{
lean_object* v_val_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4836_; 
v_val_4828_ = lean_ctor_get(v___x_4826_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4826_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4830_ = v___x_4826_;
v_isShared_4831_ = v_isSharedCheck_4836_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_val_4828_);
lean_dec(v___x_4826_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4836_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4832_; lean_object* v___x_4834_; 
v___x_4832_ = lean_nat_to_int(v_val_4828_);
if (v_isShared_4831_ == 0)
{
lean_ctor_set(v___x_4830_, 0, v___x_4832_);
v___x_4834_ = v___x_4830_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v___x_4832_);
v___x_4834_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
return v___x_4834_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4862_, lean_object* v_e_4863_){
_start:
{
uint8_t v___x_4864_; lean_object* v_d_4866_; lean_object* v_b_4867_; 
v___x_4864_ = l_Lean_Expr_hasFVar(v_e_4863_);
if (v___x_4864_ == 0)
{
lean_dec_ref(v_e_4863_);
lean_dec_ref(v_p_4862_);
return v___x_4864_;
}
else
{
switch(lean_obj_tag(v_e_4863_))
{
case 7:
{
lean_object* v_binderType_4870_; lean_object* v_body_4871_; 
v_binderType_4870_ = lean_ctor_get(v_e_4863_, 1);
lean_inc_ref(v_binderType_4870_);
v_body_4871_ = lean_ctor_get(v_e_4863_, 2);
lean_inc_ref(v_body_4871_);
lean_dec_ref_known(v_e_4863_, 3);
v_d_4866_ = v_binderType_4870_;
v_b_4867_ = v_body_4871_;
goto v___jp_4865_;
}
case 6:
{
lean_object* v_binderType_4872_; lean_object* v_body_4873_; 
v_binderType_4872_ = lean_ctor_get(v_e_4863_, 1);
lean_inc_ref(v_binderType_4872_);
v_body_4873_ = lean_ctor_get(v_e_4863_, 2);
lean_inc_ref(v_body_4873_);
lean_dec_ref_known(v_e_4863_, 3);
v_d_4866_ = v_binderType_4872_;
v_b_4867_ = v_body_4873_;
goto v___jp_4865_;
}
case 10:
{
lean_object* v_expr_4874_; 
v_expr_4874_ = lean_ctor_get(v_e_4863_, 1);
lean_inc_ref(v_expr_4874_);
lean_dec_ref_known(v_e_4863_, 2);
v_e_4863_ = v_expr_4874_;
goto _start;
}
case 8:
{
lean_object* v_type_4876_; lean_object* v_value_4877_; lean_object* v_body_4878_; uint8_t v___x_4879_; 
v_type_4876_ = lean_ctor_get(v_e_4863_, 1);
lean_inc_ref(v_type_4876_);
v_value_4877_ = lean_ctor_get(v_e_4863_, 2);
lean_inc_ref(v_value_4877_);
v_body_4878_ = lean_ctor_get(v_e_4863_, 3);
lean_inc_ref(v_body_4878_);
lean_dec_ref_known(v_e_4863_, 4);
lean_inc_ref(v_p_4862_);
v___x_4879_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4862_, v_type_4876_);
if (v___x_4879_ == 0)
{
uint8_t v___x_4880_; 
lean_inc_ref(v_p_4862_);
v___x_4880_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4862_, v_value_4877_);
if (v___x_4880_ == 0)
{
v_e_4863_ = v_body_4878_;
goto _start;
}
else
{
lean_dec_ref(v_body_4878_);
lean_dec_ref(v_p_4862_);
return v___x_4864_;
}
}
else
{
lean_dec_ref(v_body_4878_);
lean_dec_ref(v_value_4877_);
lean_dec_ref(v_p_4862_);
return v___x_4864_;
}
}
case 5:
{
lean_object* v_fn_4882_; lean_object* v_arg_4883_; uint8_t v___x_4884_; 
v_fn_4882_ = lean_ctor_get(v_e_4863_, 0);
lean_inc_ref(v_fn_4882_);
v_arg_4883_ = lean_ctor_get(v_e_4863_, 1);
lean_inc_ref(v_arg_4883_);
lean_dec_ref_known(v_e_4863_, 2);
lean_inc_ref(v_p_4862_);
v___x_4884_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4862_, v_fn_4882_);
if (v___x_4884_ == 0)
{
v_e_4863_ = v_arg_4883_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4883_);
lean_dec_ref(v_p_4862_);
return v___x_4864_;
}
}
case 11:
{
lean_object* v_struct_4886_; 
v_struct_4886_ = lean_ctor_get(v_e_4863_, 2);
lean_inc_ref(v_struct_4886_);
lean_dec_ref_known(v_e_4863_, 3);
v_e_4863_ = v_struct_4886_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4888_; lean_object* v___x_4889_; uint8_t v___x_4890_; 
v_fvarId_4888_ = lean_ctor_get(v_e_4863_, 0);
lean_inc(v_fvarId_4888_);
lean_dec_ref_known(v_e_4863_, 1);
v___x_4889_ = lean_apply_1(v_p_4862_, v_fvarId_4888_);
v___x_4890_ = lean_unbox(v___x_4889_);
return v___x_4890_;
}
default: 
{
uint8_t v___x_4891_; 
lean_dec_ref(v_e_4863_);
lean_dec_ref(v_p_4862_);
v___x_4891_ = 0;
return v___x_4891_;
}
}
}
v___jp_4865_:
{
uint8_t v___x_4868_; 
lean_inc_ref(v_p_4862_);
v___x_4868_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4862_, v_d_4866_);
if (v___x_4868_ == 0)
{
v_e_4863_ = v_b_4867_;
goto _start;
}
else
{
lean_dec_ref(v_b_4867_);
lean_dec_ref(v_p_4862_);
return v___x_4864_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_4892_, lean_object* v_e_4893_){
_start:
{
uint8_t v_res_4894_; lean_object* v_r_4895_; 
v_res_4894_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4892_, v_e_4893_);
v_r_4895_ = lean_box(v_res_4894_);
return v_r_4895_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_4896_, lean_object* v_p_4897_){
_start:
{
uint8_t v___x_4898_; 
v___x_4898_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4897_, v_e_4896_);
return v___x_4898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_4899_, lean_object* v_p_4900_){
_start:
{
uint8_t v_res_4901_; lean_object* v_r_4902_; 
v_res_4901_ = l_Lean_Expr_hasAnyFVar(v_e_4899_, v_p_4900_);
v_r_4902_ = lean_box(v_res_4901_);
return v_r_4902_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_4903_, lean_object* v_e_4904_){
_start:
{
uint8_t v___x_4905_; lean_object* v_d_4907_; lean_object* v_b_4908_; 
v___x_4905_ = l_Lean_Expr_hasFVar(v_e_4904_);
if (v___x_4905_ == 0)
{
return v___x_4905_;
}
else
{
switch(lean_obj_tag(v_e_4904_))
{
case 7:
{
lean_object* v_binderType_4911_; lean_object* v_body_4912_; 
v_binderType_4911_ = lean_ctor_get(v_e_4904_, 1);
v_body_4912_ = lean_ctor_get(v_e_4904_, 2);
v_d_4907_ = v_binderType_4911_;
v_b_4908_ = v_body_4912_;
goto v___jp_4906_;
}
case 6:
{
lean_object* v_binderType_4913_; lean_object* v_body_4914_; 
v_binderType_4913_ = lean_ctor_get(v_e_4904_, 1);
v_body_4914_ = lean_ctor_get(v_e_4904_, 2);
v_d_4907_ = v_binderType_4913_;
v_b_4908_ = v_body_4914_;
goto v___jp_4906_;
}
case 10:
{
lean_object* v_expr_4915_; 
v_expr_4915_ = lean_ctor_get(v_e_4904_, 1);
v_e_4904_ = v_expr_4915_;
goto _start;
}
case 8:
{
lean_object* v_type_4917_; lean_object* v_value_4918_; lean_object* v_body_4919_; uint8_t v___x_4920_; 
v_type_4917_ = lean_ctor_get(v_e_4904_, 1);
v_value_4918_ = lean_ctor_get(v_e_4904_, 2);
v_body_4919_ = lean_ctor_get(v_e_4904_, 3);
v___x_4920_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4903_, v_type_4917_);
if (v___x_4920_ == 0)
{
uint8_t v___x_4921_; 
v___x_4921_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4903_, v_value_4918_);
if (v___x_4921_ == 0)
{
v_e_4904_ = v_body_4919_;
goto _start;
}
else
{
return v___x_4905_;
}
}
else
{
return v___x_4905_;
}
}
case 5:
{
lean_object* v_fn_4923_; lean_object* v_arg_4924_; uint8_t v___x_4925_; 
v_fn_4923_ = lean_ctor_get(v_e_4904_, 0);
v_arg_4924_ = lean_ctor_get(v_e_4904_, 1);
v___x_4925_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4903_, v_fn_4923_);
if (v___x_4925_ == 0)
{
v_e_4904_ = v_arg_4924_;
goto _start;
}
else
{
return v___x_4905_;
}
}
case 11:
{
lean_object* v_struct_4927_; 
v_struct_4927_ = lean_ctor_get(v_e_4904_, 2);
v_e_4904_ = v_struct_4927_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4929_; uint8_t v___x_4930_; 
v_fvarId_4929_ = lean_ctor_get(v_e_4904_, 0);
v___x_4930_ = lean_name_eq(v_fvarId_4929_, v_fvarId_4903_);
return v___x_4930_;
}
default: 
{
uint8_t v___x_4931_; 
v___x_4931_ = 0;
return v___x_4931_;
}
}
}
v___jp_4906_:
{
uint8_t v___x_4909_; 
v___x_4909_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4903_, v_d_4907_);
if (v___x_4909_ == 0)
{
v_e_4904_ = v_b_4908_;
goto _start;
}
else
{
return v___x_4905_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_4932_, lean_object* v_e_4933_){
_start:
{
uint8_t v_res_4934_; lean_object* v_r_4935_; 
v_res_4934_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4932_, v_e_4933_);
lean_dec_ref(v_e_4933_);
lean_dec(v_fvarId_4932_);
v_r_4935_ = lean_box(v_res_4934_);
return v_r_4935_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_4936_, lean_object* v_fvarId_4937_){
_start:
{
uint8_t v___x_4938_; 
v___x_4938_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4937_, v_e_4936_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_4939_, lean_object* v_fvarId_4940_){
_start:
{
uint8_t v_res_4941_; lean_object* v_r_4942_; 
v_res_4941_ = l_Lean_Expr_containsFVar(v_e_4939_, v_fvarId_4940_);
lean_dec(v_fvarId_4940_);
lean_dec_ref(v_e_4939_);
v_r_4942_ = lean_box(v_res_4941_);
return v_r_4942_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(lean_object* v_p_4943_, lean_object* v_e_4944_){
_start:
{
uint8_t v___x_4945_; lean_object* v_d_4947_; lean_object* v_b_4948_; 
v___x_4945_ = l_Lean_Expr_hasExprMVar(v_e_4944_);
if (v___x_4945_ == 0)
{
lean_dec_ref(v_e_4944_);
lean_dec_ref(v_p_4943_);
return v___x_4945_;
}
else
{
switch(lean_obj_tag(v_e_4944_))
{
case 7:
{
lean_object* v_binderType_4951_; lean_object* v_body_4952_; 
v_binderType_4951_ = lean_ctor_get(v_e_4944_, 1);
lean_inc_ref(v_binderType_4951_);
v_body_4952_ = lean_ctor_get(v_e_4944_, 2);
lean_inc_ref(v_body_4952_);
lean_dec_ref_known(v_e_4944_, 3);
v_d_4947_ = v_binderType_4951_;
v_b_4948_ = v_body_4952_;
goto v___jp_4946_;
}
case 6:
{
lean_object* v_binderType_4953_; lean_object* v_body_4954_; 
v_binderType_4953_ = lean_ctor_get(v_e_4944_, 1);
lean_inc_ref(v_binderType_4953_);
v_body_4954_ = lean_ctor_get(v_e_4944_, 2);
lean_inc_ref(v_body_4954_);
lean_dec_ref_known(v_e_4944_, 3);
v_d_4947_ = v_binderType_4953_;
v_b_4948_ = v_body_4954_;
goto v___jp_4946_;
}
case 10:
{
lean_object* v_expr_4955_; 
v_expr_4955_ = lean_ctor_get(v_e_4944_, 1);
lean_inc_ref(v_expr_4955_);
lean_dec_ref_known(v_e_4944_, 2);
v_e_4944_ = v_expr_4955_;
goto _start;
}
case 8:
{
lean_object* v_type_4957_; lean_object* v_value_4958_; lean_object* v_body_4959_; uint8_t v___x_4960_; 
v_type_4957_ = lean_ctor_get(v_e_4944_, 1);
lean_inc_ref(v_type_4957_);
v_value_4958_ = lean_ctor_get(v_e_4944_, 2);
lean_inc_ref(v_value_4958_);
v_body_4959_ = lean_ctor_get(v_e_4944_, 3);
lean_inc_ref(v_body_4959_);
lean_dec_ref_known(v_e_4944_, 4);
lean_inc_ref(v_p_4943_);
v___x_4960_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4943_, v_type_4957_);
if (v___x_4960_ == 0)
{
uint8_t v___x_4961_; 
lean_inc_ref(v_p_4943_);
v___x_4961_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4943_, v_value_4958_);
if (v___x_4961_ == 0)
{
v_e_4944_ = v_body_4959_;
goto _start;
}
else
{
lean_dec_ref(v_body_4959_);
lean_dec_ref(v_p_4943_);
return v___x_4945_;
}
}
else
{
lean_dec_ref(v_body_4959_);
lean_dec_ref(v_value_4958_);
lean_dec_ref(v_p_4943_);
return v___x_4945_;
}
}
case 5:
{
lean_object* v_fn_4963_; lean_object* v_arg_4964_; uint8_t v___x_4965_; 
v_fn_4963_ = lean_ctor_get(v_e_4944_, 0);
lean_inc_ref(v_fn_4963_);
v_arg_4964_ = lean_ctor_get(v_e_4944_, 1);
lean_inc_ref(v_arg_4964_);
lean_dec_ref_known(v_e_4944_, 2);
lean_inc_ref(v_p_4943_);
v___x_4965_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4943_, v_fn_4963_);
if (v___x_4965_ == 0)
{
v_e_4944_ = v_arg_4964_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4964_);
lean_dec_ref(v_p_4943_);
return v___x_4945_;
}
}
case 11:
{
lean_object* v_struct_4967_; 
v_struct_4967_ = lean_ctor_get(v_e_4944_, 2);
lean_inc_ref(v_struct_4967_);
lean_dec_ref_known(v_e_4944_, 3);
v_e_4944_ = v_struct_4967_;
goto _start;
}
case 2:
{
lean_object* v_mvarId_4969_; lean_object* v___x_4970_; uint8_t v___x_4971_; 
v_mvarId_4969_ = lean_ctor_get(v_e_4944_, 0);
lean_inc(v_mvarId_4969_);
lean_dec_ref_known(v_e_4944_, 1);
v___x_4970_ = lean_apply_1(v_p_4943_, v_mvarId_4969_);
v___x_4971_ = lean_unbox(v___x_4970_);
return v___x_4971_;
}
default: 
{
uint8_t v___x_4972_; 
lean_dec_ref(v_e_4944_);
lean_dec_ref(v_p_4943_);
v___x_4972_ = 0;
return v___x_4972_;
}
}
}
v___jp_4946_:
{
uint8_t v___x_4949_; 
lean_inc_ref(v_p_4943_);
v___x_4949_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4943_, v_d_4947_);
if (v___x_4949_ == 0)
{
v_e_4944_ = v_b_4948_;
goto _start;
}
else
{
lean_dec_ref(v_b_4948_);
lean_dec_ref(v_p_4943_);
return v___x_4945_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___boxed(lean_object* v_p_4973_, lean_object* v_e_4974_){
_start:
{
uint8_t v_res_4975_; lean_object* v_r_4976_; 
v_res_4975_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4973_, v_e_4974_);
v_r_4976_ = lean_box(v_res_4975_);
return v_r_4976_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyMVar(lean_object* v_e_4977_, lean_object* v_p_4978_){
_start:
{
uint8_t v___x_4979_; 
v___x_4979_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4978_, v_e_4977_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyMVar___boxed(lean_object* v_e_4980_, lean_object* v_p_4981_){
_start:
{
uint8_t v_res_4982_; lean_object* v_r_4983_; 
v_res_4982_ = l_Lean_Expr_hasAnyMVar(v_e_4980_, v_p_4981_);
v_r_4983_ = lean_box(v_res_4982_);
return v_r_4983_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(lean_object* v_mvarId_4984_, lean_object* v_e_4985_){
_start:
{
uint8_t v___x_4986_; lean_object* v_d_4988_; lean_object* v_b_4989_; 
v___x_4986_ = l_Lean_Expr_hasExprMVar(v_e_4985_);
if (v___x_4986_ == 0)
{
return v___x_4986_;
}
else
{
switch(lean_obj_tag(v_e_4985_))
{
case 7:
{
lean_object* v_binderType_4992_; lean_object* v_body_4993_; 
v_binderType_4992_ = lean_ctor_get(v_e_4985_, 1);
v_body_4993_ = lean_ctor_get(v_e_4985_, 2);
v_d_4988_ = v_binderType_4992_;
v_b_4989_ = v_body_4993_;
goto v___jp_4987_;
}
case 6:
{
lean_object* v_binderType_4994_; lean_object* v_body_4995_; 
v_binderType_4994_ = lean_ctor_get(v_e_4985_, 1);
v_body_4995_ = lean_ctor_get(v_e_4985_, 2);
v_d_4988_ = v_binderType_4994_;
v_b_4989_ = v_body_4995_;
goto v___jp_4987_;
}
case 10:
{
lean_object* v_expr_4996_; 
v_expr_4996_ = lean_ctor_get(v_e_4985_, 1);
v_e_4985_ = v_expr_4996_;
goto _start;
}
case 8:
{
lean_object* v_type_4998_; lean_object* v_value_4999_; lean_object* v_body_5000_; uint8_t v___x_5001_; 
v_type_4998_ = lean_ctor_get(v_e_4985_, 1);
v_value_4999_ = lean_ctor_get(v_e_4985_, 2);
v_body_5000_ = lean_ctor_get(v_e_4985_, 3);
v___x_5001_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4984_, v_type_4998_);
if (v___x_5001_ == 0)
{
uint8_t v___x_5002_; 
v___x_5002_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4984_, v_value_4999_);
if (v___x_5002_ == 0)
{
v_e_4985_ = v_body_5000_;
goto _start;
}
else
{
return v___x_4986_;
}
}
else
{
return v___x_4986_;
}
}
case 5:
{
lean_object* v_fn_5004_; lean_object* v_arg_5005_; uint8_t v___x_5006_; 
v_fn_5004_ = lean_ctor_get(v_e_4985_, 0);
v_arg_5005_ = lean_ctor_get(v_e_4985_, 1);
v___x_5006_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4984_, v_fn_5004_);
if (v___x_5006_ == 0)
{
v_e_4985_ = v_arg_5005_;
goto _start;
}
else
{
return v___x_4986_;
}
}
case 11:
{
lean_object* v_struct_5008_; 
v_struct_5008_ = lean_ctor_get(v_e_4985_, 2);
v_e_4985_ = v_struct_5008_;
goto _start;
}
case 2:
{
lean_object* v_mvarId_5010_; uint8_t v___x_5011_; 
v_mvarId_5010_ = lean_ctor_get(v_e_4985_, 0);
v___x_5011_ = lean_name_eq(v_mvarId_5010_, v_mvarId_4984_);
return v___x_5011_;
}
default: 
{
uint8_t v___x_5012_; 
v___x_5012_ = 0;
return v___x_5012_;
}
}
}
v___jp_4987_:
{
uint8_t v___x_4990_; 
v___x_4990_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4984_, v_d_4988_);
if (v___x_4990_ == 0)
{
v_e_4985_ = v_b_4989_;
goto _start;
}
else
{
return v___x_4986_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0___boxed(lean_object* v_mvarId_5013_, lean_object* v_e_5014_){
_start:
{
uint8_t v_res_5015_; lean_object* v_r_5016_; 
v_res_5015_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5013_, v_e_5014_);
lean_dec_ref(v_e_5014_);
lean_dec(v_mvarId_5013_);
v_r_5016_ = lean_box(v_res_5015_);
return v_r_5016_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsMVar(lean_object* v_e_5017_, lean_object* v_mvarId_5018_){
_start:
{
uint8_t v___x_5019_; 
v___x_5019_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5018_, v_e_5017_);
return v___x_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsMVar___boxed(lean_object* v_e_5020_, lean_object* v_mvarId_5021_){
_start:
{
uint8_t v_res_5022_; lean_object* v_r_5023_; 
v_res_5022_ = l_Lean_Expr_containsMVar(v_e_5020_, v_mvarId_5021_);
lean_dec(v_mvarId_5021_);
lean_dec_ref(v_e_5020_);
v_r_5023_ = lean_box(v_res_5022_);
return v_r_5023_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5025_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_5026_ = lean_unsigned_to_nat(18u);
v___x_5027_ = lean_unsigned_to_nat(1864u);
v___x_5028_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_5029_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5030_ = l_mkPanicMessageWithDecl(v___x_5029_, v___x_5028_, v___x_5027_, v___x_5026_, v___x_5025_);
return v___x_5030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_5031_, lean_object* v_newFn_5032_, lean_object* v_newArg_5033_){
_start:
{
if (lean_obj_tag(v_e_5031_) == 5)
{
lean_object* v_fn_5034_; lean_object* v_arg_5035_; size_t v___x_5036_; size_t v___x_5037_; uint8_t v___x_5038_; 
v_fn_5034_ = lean_ctor_get(v_e_5031_, 0);
v_arg_5035_ = lean_ctor_get(v_e_5031_, 1);
v___x_5036_ = lean_ptr_addr(v_fn_5034_);
v___x_5037_ = lean_ptr_addr(v_newFn_5032_);
v___x_5038_ = lean_usize_dec_eq(v___x_5036_, v___x_5037_);
if (v___x_5038_ == 0)
{
lean_object* v___x_5039_; 
v___x_5039_ = l_Lean_Expr_app___override(v_newFn_5032_, v_newArg_5033_);
return v___x_5039_;
}
else
{
size_t v___x_5040_; size_t v___x_5041_; uint8_t v___x_5042_; 
v___x_5040_ = lean_ptr_addr(v_arg_5035_);
v___x_5041_ = lean_ptr_addr(v_newArg_5033_);
v___x_5042_ = lean_usize_dec_eq(v___x_5040_, v___x_5041_);
if (v___x_5042_ == 0)
{
lean_object* v___x_5043_; 
v___x_5043_ = l_Lean_Expr_app___override(v_newFn_5032_, v_newArg_5033_);
return v___x_5043_;
}
else
{
lean_dec_ref(v_newArg_5033_);
lean_dec_ref(v_newFn_5032_);
lean_inc_ref(v_e_5031_);
return v_e_5031_;
}
}
}
else
{
lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
lean_dec_ref(v_newArg_5033_);
lean_dec_ref(v_newFn_5032_);
v___x_5044_ = l_Lean_instInhabitedExpr;
v___x_5045_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_5046_ = l_panic___redArg(v___x_5044_, v___x_5045_);
return v___x_5046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_5047_, lean_object* v_newFn_5048_, lean_object* v_newArg_5049_){
_start:
{
lean_object* v_res_5050_; 
v_res_5050_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_5047_, v_newFn_5048_, v_newArg_5049_);
lean_dec_ref(v_e_5047_);
return v_res_5050_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5052_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_5053_ = lean_unsigned_to_nat(20u);
v___x_5054_ = lean_unsigned_to_nat(1875u);
v___x_5055_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_5056_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5057_ = l_mkPanicMessageWithDecl(v___x_5056_, v___x_5055_, v___x_5054_, v___x_5053_, v___x_5052_);
return v___x_5057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_5058_, lean_object* v_fvarIdNew_5059_){
_start:
{
if (lean_obj_tag(v_e_5058_) == 1)
{
lean_object* v_fvarId_5060_; uint8_t v___x_5061_; 
v_fvarId_5060_ = lean_ctor_get(v_e_5058_, 0);
v___x_5061_ = lean_name_eq(v_fvarId_5060_, v_fvarIdNew_5059_);
if (v___x_5061_ == 0)
{
lean_object* v___x_5062_; 
v___x_5062_ = l_Lean_Expr_fvar___override(v_fvarIdNew_5059_);
return v___x_5062_;
}
else
{
lean_dec(v_fvarIdNew_5059_);
lean_inc_ref(v_e_5058_);
return v_e_5058_;
}
}
else
{
lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
lean_dec(v_fvarIdNew_5059_);
v___x_5063_ = l_Lean_instInhabitedExpr;
v___x_5064_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_5065_ = l_panic___redArg(v___x_5063_, v___x_5064_);
return v___x_5065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_5066_, lean_object* v_fvarIdNew_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l_Lean_Expr_updateFVar_x21(v_e_5066_, v_fvarIdNew_5067_);
lean_dec_ref(v_e_5066_);
return v_res_5068_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; 
v___x_5070_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_5071_ = lean_unsigned_to_nat(18u);
v___x_5072_ = lean_unsigned_to_nat(1880u);
v___x_5073_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_5074_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5075_ = l_mkPanicMessageWithDecl(v___x_5074_, v___x_5073_, v___x_5072_, v___x_5071_, v___x_5070_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_5076_, lean_object* v_newLevels_5077_){
_start:
{
if (lean_obj_tag(v_e_5076_) == 4)
{
lean_object* v_declName_5078_; lean_object* v_us_5079_; uint8_t v___x_5080_; 
v_declName_5078_ = lean_ctor_get(v_e_5076_, 0);
v_us_5079_ = lean_ctor_get(v_e_5076_, 1);
v___x_5080_ = l_ptrEqList___redArg(v_us_5079_, v_newLevels_5077_);
if (v___x_5080_ == 0)
{
lean_object* v___x_5081_; 
lean_inc(v_declName_5078_);
lean_dec_ref_known(v_e_5076_, 2);
v___x_5081_ = l_Lean_Expr_const___override(v_declName_5078_, v_newLevels_5077_);
return v___x_5081_;
}
else
{
lean_dec(v_newLevels_5077_);
return v_e_5076_;
}
}
else
{
lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
lean_dec(v_newLevels_5077_);
lean_dec_ref(v_e_5076_);
v___x_5082_ = l_Lean_instInhabitedExpr;
v___x_5083_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_5084_ = l_panic___redArg(v___x_5082_, v___x_5083_);
return v___x_5084_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; 
v___x_5087_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_5088_ = lean_unsigned_to_nat(14u);
v___x_5089_ = lean_unsigned_to_nat(1891u);
v___x_5090_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_5091_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5092_ = l_mkPanicMessageWithDecl(v___x_5091_, v___x_5090_, v___x_5089_, v___x_5088_, v___x_5087_);
return v___x_5092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_5093_, lean_object* v_u_x27_5094_){
_start:
{
if (lean_obj_tag(v_e_5093_) == 3)
{
lean_object* v_u_5095_; size_t v___x_5096_; size_t v___x_5097_; uint8_t v___x_5098_; 
v_u_5095_ = lean_ctor_get(v_e_5093_, 0);
v___x_5096_ = lean_ptr_addr(v_u_5095_);
v___x_5097_ = lean_ptr_addr(v_u_x27_5094_);
v___x_5098_ = lean_usize_dec_eq(v___x_5096_, v___x_5097_);
if (v___x_5098_ == 0)
{
lean_object* v___x_5099_; 
v___x_5099_ = l_Lean_Expr_sort___override(v_u_x27_5094_);
return v___x_5099_;
}
else
{
lean_dec(v_u_x27_5094_);
lean_inc_ref(v_e_5093_);
return v_e_5093_;
}
}
else
{
lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; 
lean_dec(v_u_x27_5094_);
v___x_5100_ = l_Lean_instInhabitedExpr;
v___x_5101_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_5102_ = l_panic___redArg(v___x_5100_, v___x_5101_);
return v___x_5102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_5103_, lean_object* v_u_x27_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_5103_, v_u_x27_5104_);
lean_dec_ref(v_e_5103_);
return v_res_5105_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; 
v___x_5108_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_5109_ = lean_unsigned_to_nat(17u);
v___x_5110_ = lean_unsigned_to_nat(1902u);
v___x_5111_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_5112_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5113_ = l_mkPanicMessageWithDecl(v___x_5112_, v___x_5111_, v___x_5110_, v___x_5109_, v___x_5108_);
return v___x_5113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_5114_, lean_object* v_newExpr_5115_){
_start:
{
if (lean_obj_tag(v_e_5114_) == 10)
{
lean_object* v_data_5116_; lean_object* v_expr_5117_; size_t v___x_5118_; size_t v___x_5119_; uint8_t v___x_5120_; 
v_data_5116_ = lean_ctor_get(v_e_5114_, 0);
v_expr_5117_ = lean_ctor_get(v_e_5114_, 1);
v___x_5118_ = lean_ptr_addr(v_expr_5117_);
v___x_5119_ = lean_ptr_addr(v_newExpr_5115_);
v___x_5120_ = lean_usize_dec_eq(v___x_5118_, v___x_5119_);
if (v___x_5120_ == 0)
{
lean_object* v___x_5121_; 
lean_inc(v_data_5116_);
lean_dec_ref_known(v_e_5114_, 2);
v___x_5121_ = l_Lean_Expr_mdata___override(v_data_5116_, v_newExpr_5115_);
return v___x_5121_;
}
else
{
lean_dec_ref(v_newExpr_5115_);
return v_e_5114_;
}
}
else
{
lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; 
lean_dec_ref(v_newExpr_5115_);
lean_dec_ref(v_e_5114_);
v___x_5122_ = l_Lean_instInhabitedExpr;
v___x_5123_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_5124_ = l_panic___redArg(v___x_5122_, v___x_5123_);
return v___x_5124_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; 
v___x_5127_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_5128_ = lean_unsigned_to_nat(18u);
v___x_5129_ = lean_unsigned_to_nat(1913u);
v___x_5130_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_5131_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5132_ = l_mkPanicMessageWithDecl(v___x_5131_, v___x_5130_, v___x_5129_, v___x_5128_, v___x_5127_);
return v___x_5132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_5133_, lean_object* v_newExpr_5134_){
_start:
{
if (lean_obj_tag(v_e_5133_) == 11)
{
lean_object* v_typeName_5135_; lean_object* v_idx_5136_; lean_object* v_struct_5137_; size_t v___x_5138_; size_t v___x_5139_; uint8_t v___x_5140_; 
v_typeName_5135_ = lean_ctor_get(v_e_5133_, 0);
v_idx_5136_ = lean_ctor_get(v_e_5133_, 1);
v_struct_5137_ = lean_ctor_get(v_e_5133_, 2);
v___x_5138_ = lean_ptr_addr(v_struct_5137_);
v___x_5139_ = lean_ptr_addr(v_newExpr_5134_);
v___x_5140_ = lean_usize_dec_eq(v___x_5138_, v___x_5139_);
if (v___x_5140_ == 0)
{
lean_object* v___x_5141_; 
lean_inc(v_idx_5136_);
lean_inc(v_typeName_5135_);
lean_dec_ref_known(v_e_5133_, 3);
v___x_5141_ = l_Lean_Expr_proj___override(v_typeName_5135_, v_idx_5136_, v_newExpr_5134_);
return v___x_5141_;
}
else
{
lean_dec_ref(v_newExpr_5134_);
return v_e_5133_;
}
}
else
{
lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; 
lean_dec_ref(v_newExpr_5134_);
lean_dec_ref(v_e_5133_);
v___x_5142_ = l_Lean_instInhabitedExpr;
v___x_5143_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_5144_ = l_panic___redArg(v___x_5142_, v___x_5143_);
return v___x_5144_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; 
v___x_5147_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5148_ = lean_unsigned_to_nat(23u);
v___x_5149_ = lean_unsigned_to_nat(1928u);
v___x_5150_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_5151_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5152_ = l_mkPanicMessageWithDecl(v___x_5151_, v___x_5150_, v___x_5149_, v___x_5148_, v___x_5147_);
return v___x_5152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_5153_, uint8_t v_newBinfo_5154_, lean_object* v_newDomain_5155_, lean_object* v_newBody_5156_){
_start:
{
if (lean_obj_tag(v_e_5153_) == 7)
{
lean_object* v_binderName_5157_; lean_object* v_binderType_5158_; lean_object* v_body_5159_; uint8_t v_binderInfo_5160_; size_t v___x_5161_; size_t v___x_5162_; uint8_t v___x_5163_; 
v_binderName_5157_ = lean_ctor_get(v_e_5153_, 0);
v_binderType_5158_ = lean_ctor_get(v_e_5153_, 1);
v_body_5159_ = lean_ctor_get(v_e_5153_, 2);
v_binderInfo_5160_ = lean_ctor_get_uint8(v_e_5153_, sizeof(void*)*3 + 8);
v___x_5161_ = lean_ptr_addr(v_binderType_5158_);
v___x_5162_ = lean_ptr_addr(v_newDomain_5155_);
v___x_5163_ = lean_usize_dec_eq(v___x_5161_, v___x_5162_);
if (v___x_5163_ == 0)
{
lean_object* v___x_5164_; 
lean_inc(v_binderName_5157_);
lean_dec_ref_known(v_e_5153_, 3);
v___x_5164_ = l_Lean_Expr_forallE___override(v_binderName_5157_, v_newDomain_5155_, v_newBody_5156_, v_newBinfo_5154_);
return v___x_5164_;
}
else
{
size_t v___x_5165_; size_t v___x_5166_; uint8_t v___x_5167_; 
v___x_5165_ = lean_ptr_addr(v_body_5159_);
v___x_5166_ = lean_ptr_addr(v_newBody_5156_);
v___x_5167_ = lean_usize_dec_eq(v___x_5165_, v___x_5166_);
if (v___x_5167_ == 0)
{
lean_object* v___x_5168_; 
lean_inc(v_binderName_5157_);
lean_dec_ref_known(v_e_5153_, 3);
v___x_5168_ = l_Lean_Expr_forallE___override(v_binderName_5157_, v_newDomain_5155_, v_newBody_5156_, v_newBinfo_5154_);
return v___x_5168_;
}
else
{
uint8_t v___x_5169_; 
v___x_5169_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5160_, v_newBinfo_5154_);
if (v___x_5169_ == 0)
{
lean_object* v___x_5170_; 
lean_inc(v_binderName_5157_);
lean_dec_ref_known(v_e_5153_, 3);
v___x_5170_ = l_Lean_Expr_forallE___override(v_binderName_5157_, v_newDomain_5155_, v_newBody_5156_, v_newBinfo_5154_);
return v___x_5170_;
}
else
{
lean_dec_ref(v_newBody_5156_);
lean_dec_ref(v_newDomain_5155_);
return v_e_5153_;
}
}
}
}
else
{
lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; 
lean_dec_ref(v_newBody_5156_);
lean_dec_ref(v_newDomain_5155_);
lean_dec_ref(v_e_5153_);
v___x_5171_ = l_Lean_instInhabitedExpr;
v___x_5172_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_5173_ = l_panic___redArg(v___x_5171_, v___x_5172_);
return v___x_5173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_5174_, lean_object* v_newBinfo_5175_, lean_object* v_newDomain_5176_, lean_object* v_newBody_5177_){
_start:
{
uint8_t v_newBinfo_boxed_5178_; lean_object* v_res_5179_; 
v_newBinfo_boxed_5178_ = lean_unbox(v_newBinfo_5175_);
v_res_5179_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5174_, v_newBinfo_boxed_5178_, v_newDomain_5176_, v_newBody_5177_);
return v_res_5179_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; 
v___x_5181_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5182_ = lean_unsigned_to_nat(24u);
v___x_5183_ = lean_unsigned_to_nat(1939u);
v___x_5184_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_5185_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5186_ = l_mkPanicMessageWithDecl(v___x_5185_, v___x_5184_, v___x_5183_, v___x_5182_, v___x_5181_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_5187_, lean_object* v_newDomain_5188_, lean_object* v_newBody_5189_){
_start:
{
if (lean_obj_tag(v_e_5187_) == 7)
{
lean_object* v_binderName_5190_; lean_object* v_binderType_5191_; lean_object* v_body_5192_; uint8_t v_binderInfo_5193_; size_t v___x_5194_; size_t v___x_5195_; uint8_t v___x_5196_; 
v_binderName_5190_ = lean_ctor_get(v_e_5187_, 0);
v_binderType_5191_ = lean_ctor_get(v_e_5187_, 1);
v_body_5192_ = lean_ctor_get(v_e_5187_, 2);
v_binderInfo_5193_ = lean_ctor_get_uint8(v_e_5187_, sizeof(void*)*3 + 8);
v___x_5194_ = lean_ptr_addr(v_binderType_5191_);
v___x_5195_ = lean_ptr_addr(v_newDomain_5188_);
v___x_5196_ = lean_usize_dec_eq(v___x_5194_, v___x_5195_);
if (v___x_5196_ == 0)
{
lean_object* v___x_5197_; 
lean_inc(v_binderName_5190_);
lean_dec_ref_known(v_e_5187_, 3);
v___x_5197_ = l_Lean_Expr_forallE___override(v_binderName_5190_, v_newDomain_5188_, v_newBody_5189_, v_binderInfo_5193_);
return v___x_5197_;
}
else
{
size_t v___x_5198_; size_t v___x_5199_; uint8_t v___x_5200_; 
v___x_5198_ = lean_ptr_addr(v_body_5192_);
v___x_5199_ = lean_ptr_addr(v_newBody_5189_);
v___x_5200_ = lean_usize_dec_eq(v___x_5198_, v___x_5199_);
if (v___x_5200_ == 0)
{
lean_object* v___x_5201_; 
lean_inc(v_binderName_5190_);
lean_dec_ref_known(v_e_5187_, 3);
v___x_5201_ = l_Lean_Expr_forallE___override(v_binderName_5190_, v_newDomain_5188_, v_newBody_5189_, v_binderInfo_5193_);
return v___x_5201_;
}
else
{
uint8_t v___x_5202_; 
v___x_5202_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5193_, v_binderInfo_5193_);
if (v___x_5202_ == 0)
{
lean_object* v___x_5203_; 
lean_inc(v_binderName_5190_);
lean_dec_ref_known(v_e_5187_, 3);
v___x_5203_ = l_Lean_Expr_forallE___override(v_binderName_5190_, v_newDomain_5188_, v_newBody_5189_, v_binderInfo_5193_);
return v___x_5203_;
}
else
{
lean_dec_ref(v_newBody_5189_);
lean_dec_ref(v_newDomain_5188_);
return v_e_5187_;
}
}
}
}
else
{
lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; 
lean_dec_ref(v_newBody_5189_);
lean_dec_ref(v_newDomain_5188_);
lean_dec_ref(v_e_5187_);
v___x_5204_ = l_Lean_instInhabitedExpr;
v___x_5205_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_5206_ = l_panic___redArg(v___x_5204_, v___x_5205_);
return v___x_5206_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; 
v___x_5209_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5210_ = lean_unsigned_to_nat(19u);
v___x_5211_ = lean_unsigned_to_nat(1948u);
v___x_5212_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_5213_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5214_ = l_mkPanicMessageWithDecl(v___x_5213_, v___x_5212_, v___x_5211_, v___x_5210_, v___x_5209_);
return v___x_5214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_5215_, uint8_t v_newBinfo_5216_, lean_object* v_newDomain_5217_, lean_object* v_newBody_5218_){
_start:
{
if (lean_obj_tag(v_e_5215_) == 6)
{
lean_object* v_binderName_5219_; lean_object* v_binderType_5220_; lean_object* v_body_5221_; uint8_t v_binderInfo_5222_; size_t v___x_5223_; size_t v___x_5224_; uint8_t v___x_5225_; 
v_binderName_5219_ = lean_ctor_get(v_e_5215_, 0);
v_binderType_5220_ = lean_ctor_get(v_e_5215_, 1);
v_body_5221_ = lean_ctor_get(v_e_5215_, 2);
v_binderInfo_5222_ = lean_ctor_get_uint8(v_e_5215_, sizeof(void*)*3 + 8);
v___x_5223_ = lean_ptr_addr(v_binderType_5220_);
v___x_5224_ = lean_ptr_addr(v_newDomain_5217_);
v___x_5225_ = lean_usize_dec_eq(v___x_5223_, v___x_5224_);
if (v___x_5225_ == 0)
{
lean_object* v___x_5226_; 
lean_inc(v_binderName_5219_);
lean_dec_ref_known(v_e_5215_, 3);
v___x_5226_ = l_Lean_Expr_lam___override(v_binderName_5219_, v_newDomain_5217_, v_newBody_5218_, v_newBinfo_5216_);
return v___x_5226_;
}
else
{
size_t v___x_5227_; size_t v___x_5228_; uint8_t v___x_5229_; 
v___x_5227_ = lean_ptr_addr(v_body_5221_);
v___x_5228_ = lean_ptr_addr(v_newBody_5218_);
v___x_5229_ = lean_usize_dec_eq(v___x_5227_, v___x_5228_);
if (v___x_5229_ == 0)
{
lean_object* v___x_5230_; 
lean_inc(v_binderName_5219_);
lean_dec_ref_known(v_e_5215_, 3);
v___x_5230_ = l_Lean_Expr_lam___override(v_binderName_5219_, v_newDomain_5217_, v_newBody_5218_, v_newBinfo_5216_);
return v___x_5230_;
}
else
{
uint8_t v___x_5231_; 
v___x_5231_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5222_, v_newBinfo_5216_);
if (v___x_5231_ == 0)
{
lean_object* v___x_5232_; 
lean_inc(v_binderName_5219_);
lean_dec_ref_known(v_e_5215_, 3);
v___x_5232_ = l_Lean_Expr_lam___override(v_binderName_5219_, v_newDomain_5217_, v_newBody_5218_, v_newBinfo_5216_);
return v___x_5232_;
}
else
{
lean_dec_ref(v_newBody_5218_);
lean_dec_ref(v_newDomain_5217_);
return v_e_5215_;
}
}
}
}
else
{
lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; 
lean_dec_ref(v_newBody_5218_);
lean_dec_ref(v_newDomain_5217_);
lean_dec_ref(v_e_5215_);
v___x_5233_ = l_Lean_instInhabitedExpr;
v___x_5234_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_5235_ = l_panic___redArg(v___x_5233_, v___x_5234_);
return v___x_5235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_5236_, lean_object* v_newBinfo_5237_, lean_object* v_newDomain_5238_, lean_object* v_newBody_5239_){
_start:
{
uint8_t v_newBinfo_boxed_5240_; lean_object* v_res_5241_; 
v_newBinfo_boxed_5240_ = lean_unbox(v_newBinfo_5237_);
v_res_5241_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5236_, v_newBinfo_boxed_5240_, v_newDomain_5238_, v_newBody_5239_);
return v_res_5241_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; 
v___x_5243_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5244_ = lean_unsigned_to_nat(20u);
v___x_5245_ = lean_unsigned_to_nat(1959u);
v___x_5246_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5247_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5248_ = l_mkPanicMessageWithDecl(v___x_5247_, v___x_5246_, v___x_5245_, v___x_5244_, v___x_5243_);
return v___x_5248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5249_, lean_object* v_newDomain_5250_, lean_object* v_newBody_5251_){
_start:
{
if (lean_obj_tag(v_e_5249_) == 6)
{
lean_object* v_binderName_5252_; lean_object* v_binderType_5253_; lean_object* v_body_5254_; uint8_t v_binderInfo_5255_; size_t v___x_5256_; size_t v___x_5257_; uint8_t v___x_5258_; 
v_binderName_5252_ = lean_ctor_get(v_e_5249_, 0);
v_binderType_5253_ = lean_ctor_get(v_e_5249_, 1);
v_body_5254_ = lean_ctor_get(v_e_5249_, 2);
v_binderInfo_5255_ = lean_ctor_get_uint8(v_e_5249_, sizeof(void*)*3 + 8);
v___x_5256_ = lean_ptr_addr(v_binderType_5253_);
v___x_5257_ = lean_ptr_addr(v_newDomain_5250_);
v___x_5258_ = lean_usize_dec_eq(v___x_5256_, v___x_5257_);
if (v___x_5258_ == 0)
{
lean_object* v___x_5259_; 
lean_inc(v_binderName_5252_);
lean_dec_ref_known(v_e_5249_, 3);
v___x_5259_ = l_Lean_Expr_lam___override(v_binderName_5252_, v_newDomain_5250_, v_newBody_5251_, v_binderInfo_5255_);
return v___x_5259_;
}
else
{
size_t v___x_5260_; size_t v___x_5261_; uint8_t v___x_5262_; 
v___x_5260_ = lean_ptr_addr(v_body_5254_);
v___x_5261_ = lean_ptr_addr(v_newBody_5251_);
v___x_5262_ = lean_usize_dec_eq(v___x_5260_, v___x_5261_);
if (v___x_5262_ == 0)
{
lean_object* v___x_5263_; 
lean_inc(v_binderName_5252_);
lean_dec_ref_known(v_e_5249_, 3);
v___x_5263_ = l_Lean_Expr_lam___override(v_binderName_5252_, v_newDomain_5250_, v_newBody_5251_, v_binderInfo_5255_);
return v___x_5263_;
}
else
{
uint8_t v___x_5264_; 
v___x_5264_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5255_, v_binderInfo_5255_);
if (v___x_5264_ == 0)
{
lean_object* v___x_5265_; 
lean_inc(v_binderName_5252_);
lean_dec_ref_known(v_e_5249_, 3);
v___x_5265_ = l_Lean_Expr_lam___override(v_binderName_5252_, v_newDomain_5250_, v_newBody_5251_, v_binderInfo_5255_);
return v___x_5265_;
}
else
{
lean_dec_ref(v_newBody_5251_);
lean_dec_ref(v_newDomain_5250_);
return v_e_5249_;
}
}
}
}
else
{
lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; 
lean_dec_ref(v_newBody_5251_);
lean_dec_ref(v_newDomain_5250_);
lean_dec_ref(v_e_5249_);
v___x_5266_ = l_Lean_instInhabitedExpr;
v___x_5267_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5268_ = l_panic___redArg(v___x_5266_, v___x_5267_);
return v___x_5268_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; 
v___x_5270_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5271_ = lean_unsigned_to_nat(22u);
v___x_5272_ = lean_unsigned_to_nat(1968u);
v___x_5273_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5274_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5275_ = l_mkPanicMessageWithDecl(v___x_5274_, v___x_5273_, v___x_5272_, v___x_5271_, v___x_5270_);
return v___x_5275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5276_, lean_object* v_newType_5277_, lean_object* v_newVal_5278_, lean_object* v_newBody_5279_, uint8_t v_newNondep_5280_){
_start:
{
if (lean_obj_tag(v_e_5276_) == 8)
{
lean_object* v_declName_5281_; lean_object* v_type_5282_; lean_object* v_value_5283_; lean_object* v_body_5284_; uint8_t v_nondep_5285_; size_t v___x_5286_; size_t v___x_5287_; uint8_t v___x_5288_; 
v_declName_5281_ = lean_ctor_get(v_e_5276_, 0);
v_type_5282_ = lean_ctor_get(v_e_5276_, 1);
v_value_5283_ = lean_ctor_get(v_e_5276_, 2);
v_body_5284_ = lean_ctor_get(v_e_5276_, 3);
v_nondep_5285_ = lean_ctor_get_uint8(v_e_5276_, sizeof(void*)*4 + 8);
v___x_5286_ = lean_ptr_addr(v_type_5282_);
v___x_5287_ = lean_ptr_addr(v_newType_5277_);
v___x_5288_ = lean_usize_dec_eq(v___x_5286_, v___x_5287_);
if (v___x_5288_ == 0)
{
lean_object* v___x_5289_; 
lean_inc(v_declName_5281_);
lean_dec_ref_known(v_e_5276_, 4);
v___x_5289_ = l_Lean_Expr_letE___override(v_declName_5281_, v_newType_5277_, v_newVal_5278_, v_newBody_5279_, v_newNondep_5280_);
return v___x_5289_;
}
else
{
size_t v___x_5290_; size_t v___x_5291_; uint8_t v___x_5292_; 
v___x_5290_ = lean_ptr_addr(v_value_5283_);
v___x_5291_ = lean_ptr_addr(v_newVal_5278_);
v___x_5292_ = lean_usize_dec_eq(v___x_5290_, v___x_5291_);
if (v___x_5292_ == 0)
{
lean_object* v___x_5293_; 
lean_inc(v_declName_5281_);
lean_dec_ref_known(v_e_5276_, 4);
v___x_5293_ = l_Lean_Expr_letE___override(v_declName_5281_, v_newType_5277_, v_newVal_5278_, v_newBody_5279_, v_newNondep_5280_);
return v___x_5293_;
}
else
{
size_t v___x_5294_; size_t v___x_5295_; uint8_t v___x_5296_; 
v___x_5294_ = lean_ptr_addr(v_body_5284_);
v___x_5295_ = lean_ptr_addr(v_newBody_5279_);
v___x_5296_ = lean_usize_dec_eq(v___x_5294_, v___x_5295_);
if (v___x_5296_ == 0)
{
lean_object* v___x_5297_; 
lean_inc(v_declName_5281_);
lean_dec_ref_known(v_e_5276_, 4);
v___x_5297_ = l_Lean_Expr_letE___override(v_declName_5281_, v_newType_5277_, v_newVal_5278_, v_newBody_5279_, v_newNondep_5280_);
return v___x_5297_;
}
else
{
if (v_newNondep_5280_ == 0)
{
if (v_nondep_5285_ == 0)
{
lean_dec_ref(v_newBody_5279_);
lean_dec_ref(v_newVal_5278_);
lean_dec_ref(v_newType_5277_);
return v_e_5276_;
}
else
{
lean_object* v___x_5298_; 
lean_inc(v_declName_5281_);
lean_dec_ref_known(v_e_5276_, 4);
v___x_5298_ = l_Lean_Expr_letE___override(v_declName_5281_, v_newType_5277_, v_newVal_5278_, v_newBody_5279_, v_newNondep_5280_);
return v___x_5298_;
}
}
else
{
if (v_nondep_5285_ == 0)
{
lean_object* v___x_5299_; 
lean_inc(v_declName_5281_);
lean_dec_ref_known(v_e_5276_, 4);
v___x_5299_ = l_Lean_Expr_letE___override(v_declName_5281_, v_newType_5277_, v_newVal_5278_, v_newBody_5279_, v_newNondep_5280_);
return v___x_5299_;
}
else
{
lean_dec_ref(v_newBody_5279_);
lean_dec_ref(v_newVal_5278_);
lean_dec_ref(v_newType_5277_);
return v_e_5276_;
}
}
}
}
}
}
else
{
lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; 
lean_dec_ref(v_newBody_5279_);
lean_dec_ref(v_newVal_5278_);
lean_dec_ref(v_newType_5277_);
lean_dec_ref(v_e_5276_);
v___x_5300_ = l_Lean_instInhabitedExpr;
v___x_5301_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5302_ = l_panic___redArg(v___x_5300_, v___x_5301_);
return v___x_5302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5303_, lean_object* v_newType_5304_, lean_object* v_newVal_5305_, lean_object* v_newBody_5306_, lean_object* v_newNondep_5307_){
_start:
{
uint8_t v_newNondep_boxed_5308_; lean_object* v_res_5309_; 
v_newNondep_boxed_5308_ = lean_unbox(v_newNondep_5307_);
v_res_5309_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5303_, v_newType_5304_, v_newVal_5305_, v_newBody_5306_, v_newNondep_boxed_5308_);
return v_res_5309_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; 
v___x_5311_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5312_ = lean_unsigned_to_nat(27u);
v___x_5313_ = lean_unsigned_to_nat(1981u);
v___x_5314_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5315_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5316_ = l_mkPanicMessageWithDecl(v___x_5315_, v___x_5314_, v___x_5313_, v___x_5312_, v___x_5311_);
return v___x_5316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5317_, lean_object* v_newType_5318_, lean_object* v_newVal_5319_, lean_object* v_newBody_5320_){
_start:
{
if (lean_obj_tag(v_e_5317_) == 8)
{
lean_object* v_declName_5321_; lean_object* v_type_5322_; lean_object* v_value_5323_; lean_object* v_body_5324_; uint8_t v_nondep_5325_; size_t v___x_5326_; size_t v___x_5327_; uint8_t v___x_5328_; 
v_declName_5321_ = lean_ctor_get(v_e_5317_, 0);
v_type_5322_ = lean_ctor_get(v_e_5317_, 1);
v_value_5323_ = lean_ctor_get(v_e_5317_, 2);
v_body_5324_ = lean_ctor_get(v_e_5317_, 3);
v_nondep_5325_ = lean_ctor_get_uint8(v_e_5317_, sizeof(void*)*4 + 8);
v___x_5326_ = lean_ptr_addr(v_type_5322_);
v___x_5327_ = lean_ptr_addr(v_newType_5318_);
v___x_5328_ = lean_usize_dec_eq(v___x_5326_, v___x_5327_);
if (v___x_5328_ == 0)
{
lean_object* v___x_5329_; 
lean_inc(v_declName_5321_);
lean_dec_ref_known(v_e_5317_, 4);
v___x_5329_ = l_Lean_Expr_letE___override(v_declName_5321_, v_newType_5318_, v_newVal_5319_, v_newBody_5320_, v_nondep_5325_);
return v___x_5329_;
}
else
{
size_t v___x_5330_; size_t v___x_5331_; uint8_t v___x_5332_; 
v___x_5330_ = lean_ptr_addr(v_value_5323_);
v___x_5331_ = lean_ptr_addr(v_newVal_5319_);
v___x_5332_ = lean_usize_dec_eq(v___x_5330_, v___x_5331_);
if (v___x_5332_ == 0)
{
lean_object* v___x_5333_; 
lean_inc(v_declName_5321_);
lean_dec_ref_known(v_e_5317_, 4);
v___x_5333_ = l_Lean_Expr_letE___override(v_declName_5321_, v_newType_5318_, v_newVal_5319_, v_newBody_5320_, v_nondep_5325_);
return v___x_5333_;
}
else
{
size_t v___x_5334_; size_t v___x_5335_; uint8_t v___x_5336_; 
v___x_5334_ = lean_ptr_addr(v_body_5324_);
v___x_5335_ = lean_ptr_addr(v_newBody_5320_);
v___x_5336_ = lean_usize_dec_eq(v___x_5334_, v___x_5335_);
if (v___x_5336_ == 0)
{
lean_object* v___x_5337_; 
lean_inc(v_declName_5321_);
lean_dec_ref_known(v_e_5317_, 4);
v___x_5337_ = l_Lean_Expr_letE___override(v_declName_5321_, v_newType_5318_, v_newVal_5319_, v_newBody_5320_, v_nondep_5325_);
return v___x_5337_;
}
else
{
lean_dec_ref(v_newBody_5320_);
lean_dec_ref(v_newVal_5319_);
lean_dec_ref(v_newType_5318_);
return v_e_5317_;
}
}
}
}
else
{
lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; 
lean_dec_ref(v_newBody_5320_);
lean_dec_ref(v_newVal_5319_);
lean_dec_ref(v_newType_5318_);
lean_dec_ref(v_e_5317_);
v___x_5338_ = l_Lean_instInhabitedExpr;
v___x_5339_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5340_ = l_panic___redArg(v___x_5338_, v___x_5339_);
return v___x_5340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5341_, lean_object* v_x_5342_){
_start:
{
if (lean_obj_tag(v_x_5341_) == 5)
{
lean_object* v_fn_5343_; lean_object* v_arg_5344_; lean_object* v___x_5345_; size_t v___x_5346_; size_t v___x_5347_; uint8_t v___x_5348_; 
v_fn_5343_ = lean_ctor_get(v_x_5341_, 0);
v_arg_5344_ = lean_ctor_get(v_x_5341_, 1);
lean_inc_ref(v_fn_5343_);
v___x_5345_ = l_Lean_Expr_updateFn(v_fn_5343_, v_x_5342_);
v___x_5346_ = lean_ptr_addr(v_fn_5343_);
v___x_5347_ = lean_ptr_addr(v___x_5345_);
v___x_5348_ = lean_usize_dec_eq(v___x_5346_, v___x_5347_);
if (v___x_5348_ == 0)
{
lean_object* v___x_5349_; 
lean_inc_ref(v_arg_5344_);
lean_dec_ref_known(v_x_5341_, 2);
v___x_5349_ = l_Lean_Expr_app___override(v___x_5345_, v_arg_5344_);
return v___x_5349_;
}
else
{
size_t v___x_5350_; uint8_t v___x_5351_; 
v___x_5350_ = lean_ptr_addr(v_arg_5344_);
v___x_5351_ = lean_usize_dec_eq(v___x_5350_, v___x_5350_);
if (v___x_5351_ == 0)
{
lean_object* v___x_5352_; 
lean_inc_ref(v_arg_5344_);
lean_dec_ref_known(v_x_5341_, 2);
v___x_5352_ = l_Lean_Expr_app___override(v___x_5345_, v_arg_5344_);
return v___x_5352_;
}
else
{
lean_dec_ref(v___x_5345_);
return v_x_5341_;
}
}
}
else
{
lean_dec_ref(v_x_5341_);
lean_inc_ref(v_x_5342_);
return v_x_5342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5353_, lean_object* v_x_5354_){
_start:
{
lean_object* v_res_5355_; 
v_res_5355_ = l_Lean_Expr_updateFn(v_x_5353_, v_x_5354_);
lean_dec_ref(v_x_5354_);
return v_res_5355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5356_){
_start:
{
if (lean_obj_tag(v_e_5356_) == 6)
{
lean_object* v_binderName_5357_; lean_object* v_binderType_5358_; lean_object* v_body_5359_; uint8_t v_binderInfo_5360_; lean_object* v_b_x27_5361_; 
v_binderName_5357_ = lean_ctor_get(v_e_5356_, 0);
v_binderType_5358_ = lean_ctor_get(v_e_5356_, 1);
v_body_5359_ = lean_ctor_get(v_e_5356_, 2);
v_binderInfo_5360_ = lean_ctor_get_uint8(v_e_5356_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5359_);
v_b_x27_5361_ = l_Lean_Expr_eta(v_body_5359_);
if (lean_obj_tag(v_b_x27_5361_) == 5)
{
lean_object* v_arg_5372_; 
v_arg_5372_ = lean_ctor_get(v_b_x27_5361_, 1);
if (lean_obj_tag(v_arg_5372_) == 0)
{
lean_object* v_fn_5373_; lean_object* v_deBruijnIndex_5374_; lean_object* v___x_5375_; uint8_t v___x_5376_; 
v_fn_5373_ = lean_ctor_get(v_b_x27_5361_, 0);
v_deBruijnIndex_5374_ = lean_ctor_get(v_arg_5372_, 0);
v___x_5375_ = lean_unsigned_to_nat(0u);
v___x_5376_ = lean_nat_dec_eq(v_deBruijnIndex_5374_, v___x_5375_);
if (v___x_5376_ == 0)
{
goto v___jp_5362_;
}
else
{
uint8_t v___x_5377_; 
v___x_5377_ = lean_expr_has_loose_bvar(v_fn_5373_, v___x_5375_);
if (v___x_5377_ == 0)
{
lean_object* v___x_5378_; lean_object* v___x_5379_; 
lean_inc_ref(v_fn_5373_);
lean_dec_ref_known(v_b_x27_5361_, 2);
lean_dec_ref_known(v_e_5356_, 3);
v___x_5378_ = lean_unsigned_to_nat(1u);
v___x_5379_ = lean_expr_lower_loose_bvars(v_fn_5373_, v___x_5378_, v___x_5378_);
lean_dec_ref(v_fn_5373_);
return v___x_5379_;
}
else
{
size_t v___x_5380_; uint8_t v___x_5381_; 
v___x_5380_ = lean_ptr_addr(v_binderType_5358_);
v___x_5381_ = lean_usize_dec_eq(v___x_5380_, v___x_5380_);
if (v___x_5381_ == 0)
{
lean_object* v___x_5382_; 
lean_inc_ref(v_binderType_5358_);
lean_inc(v_binderName_5357_);
lean_dec_ref_known(v_e_5356_, 3);
v___x_5382_ = l_Lean_Expr_lam___override(v_binderName_5357_, v_binderType_5358_, v_b_x27_5361_, v_binderInfo_5360_);
return v___x_5382_;
}
else
{
size_t v___x_5383_; size_t v___x_5384_; uint8_t v___x_5385_; 
v___x_5383_ = lean_ptr_addr(v_body_5359_);
v___x_5384_ = lean_ptr_addr(v_b_x27_5361_);
v___x_5385_ = lean_usize_dec_eq(v___x_5383_, v___x_5384_);
if (v___x_5385_ == 0)
{
lean_object* v___x_5386_; 
lean_inc_ref(v_binderType_5358_);
lean_inc(v_binderName_5357_);
lean_dec_ref_known(v_e_5356_, 3);
v___x_5386_ = l_Lean_Expr_lam___override(v_binderName_5357_, v_binderType_5358_, v_b_x27_5361_, v_binderInfo_5360_);
return v___x_5386_;
}
else
{
uint8_t v___x_5387_; 
v___x_5387_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5360_, v_binderInfo_5360_);
if (v___x_5387_ == 0)
{
lean_object* v___x_5388_; 
lean_inc_ref(v_binderType_5358_);
lean_inc(v_binderName_5357_);
lean_dec_ref_known(v_e_5356_, 3);
v___x_5388_ = l_Lean_Expr_lam___override(v_binderName_5357_, v_binderType_5358_, v_b_x27_5361_, v_binderInfo_5360_);
return v___x_5388_;
}
else
{
lean_dec_ref_known(v_b_x27_5361_, 2);
return v_e_5356_;
}
}
}
}
}
}
else
{
goto v___jp_5362_;
}
}
else
{
goto v___jp_5362_;
}
v___jp_5362_:
{
size_t v___x_5363_; uint8_t v___x_5364_; 
v___x_5363_ = lean_ptr_addr(v_binderType_5358_);
v___x_5364_ = lean_usize_dec_eq(v___x_5363_, v___x_5363_);
if (v___x_5364_ == 0)
{
lean_object* v___x_5365_; 
lean_inc_ref(v_binderType_5358_);
lean_inc(v_binderName_5357_);
lean_dec_ref_known(v_e_5356_, 3);
v___x_5365_ = l_Lean_Expr_lam___override(v_binderName_5357_, v_binderType_5358_, v_b_x27_5361_, v_binderInfo_5360_);
return v___x_5365_;
}
else
{
size_t v___x_5366_; size_t v___x_5367_; uint8_t v___x_5368_; 
v___x_5366_ = lean_ptr_addr(v_body_5359_);
v___x_5367_ = lean_ptr_addr(v_b_x27_5361_);
v___x_5368_ = lean_usize_dec_eq(v___x_5366_, v___x_5367_);
if (v___x_5368_ == 0)
{
lean_object* v___x_5369_; 
lean_inc_ref(v_binderType_5358_);
lean_inc(v_binderName_5357_);
lean_dec_ref_known(v_e_5356_, 3);
v___x_5369_ = l_Lean_Expr_lam___override(v_binderName_5357_, v_binderType_5358_, v_b_x27_5361_, v_binderInfo_5360_);
return v___x_5369_;
}
else
{
uint8_t v___x_5370_; 
v___x_5370_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5360_, v_binderInfo_5360_);
if (v___x_5370_ == 0)
{
lean_object* v___x_5371_; 
lean_inc_ref(v_binderType_5358_);
lean_inc(v_binderName_5357_);
lean_dec_ref_known(v_e_5356_, 3);
v___x_5371_ = l_Lean_Expr_lam___override(v_binderName_5357_, v_binderType_5358_, v_b_x27_5361_, v_binderInfo_5360_);
return v___x_5371_;
}
else
{
lean_dec_ref(v_b_x27_5361_);
return v_e_5356_;
}
}
}
}
}
else
{
return v_e_5356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5389_, lean_object* v_optionName_5390_, lean_object* v_inst_5391_, lean_object* v_val_5392_){
_start:
{
lean_object* v_toDataValue_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; 
v_toDataValue_5393_ = lean_ctor_get(v_inst_5391_, 0);
lean_inc_ref(v_toDataValue_5393_);
lean_dec_ref(v_inst_5391_);
v___x_5394_ = lean_box(0);
v___x_5395_ = lean_apply_1(v_toDataValue_5393_, v_val_5392_);
v___x_5396_ = l_Lean_KVMap_insert(v___x_5394_, v_optionName_5390_, v___x_5395_);
v___x_5397_ = l_Lean_Expr_mdata___override(v___x_5396_, v_e_5389_);
return v___x_5397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5398_, lean_object* v_e_5399_, lean_object* v_optionName_5400_, lean_object* v_inst_5401_, lean_object* v_val_5402_){
_start:
{
lean_object* v___x_5403_; 
v___x_5403_ = l_Lean_Expr_setOption___redArg(v_e_5399_, v_optionName_5400_, v_inst_5401_, v_val_5402_);
return v___x_5403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5404_, lean_object* v_optionName_5405_, uint8_t v_val_5406_){
_start:
{
lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; 
v___x_5407_ = lean_box(0);
v___x_5408_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5408_, 0, v_val_5406_);
v___x_5409_ = l_Lean_KVMap_insert(v___x_5407_, v_optionName_5405_, v___x_5408_);
v___x_5410_ = l_Lean_Expr_mdata___override(v___x_5409_, v_e_5404_);
return v___x_5410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5411_, lean_object* v_optionName_5412_, lean_object* v_val_5413_){
_start:
{
uint8_t v_val_boxed_5414_; lean_object* v_res_5415_; 
v_val_boxed_5414_ = lean_unbox(v_val_5413_);
v_res_5415_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5411_, v_optionName_5412_, v_val_boxed_5414_);
return v_res_5415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5421_, uint8_t v_flag_5422_){
_start:
{
lean_object* v___x_5423_; lean_object* v___x_5424_; 
v___x_5423_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5424_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5421_, v___x_5423_, v_flag_5422_);
return v___x_5424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5425_, lean_object* v_flag_5426_){
_start:
{
uint8_t v_flag_boxed_5427_; lean_object* v_res_5428_; 
v_flag_boxed_5427_ = lean_unbox(v_flag_5426_);
v_res_5428_ = l_Lean_Expr_setPPExplicit(v_e_5425_, v_flag_boxed_5427_);
return v_res_5428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5433_, uint8_t v_flag_5434_){
_start:
{
lean_object* v___x_5435_; lean_object* v___x_5436_; 
v___x_5435_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5436_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5433_, v___x_5435_, v_flag_5434_);
return v___x_5436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5437_, lean_object* v_flag_5438_){
_start:
{
uint8_t v_flag_boxed_5439_; lean_object* v_res_5440_; 
v_flag_boxed_5439_ = lean_unbox(v_flag_5438_);
v_res_5440_ = l_Lean_Expr_setPPUniverses(v_e_5437_, v_flag_boxed_5439_);
return v_res_5440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5445_, uint8_t v_flag_5446_){
_start:
{
lean_object* v___x_5447_; lean_object* v___x_5448_; 
v___x_5447_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5448_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5445_, v___x_5447_, v_flag_5446_);
return v___x_5448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5449_, lean_object* v_flag_5450_){
_start:
{
uint8_t v_flag_boxed_5451_; lean_object* v_res_5452_; 
v_flag_boxed_5451_ = lean_unbox(v_flag_5450_);
v_res_5452_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5449_, v_flag_boxed_5451_);
return v_res_5452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5457_, uint8_t v_flag_5458_){
_start:
{
lean_object* v___x_5459_; lean_object* v___x_5460_; 
v___x_5459_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5460_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5457_, v___x_5459_, v_flag_5458_);
return v___x_5460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5461_, lean_object* v_flag_5462_){
_start:
{
uint8_t v_flag_boxed_5463_; lean_object* v_res_5464_; 
v_flag_boxed_5463_ = lean_unbox(v_flag_5462_);
v_res_5464_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5461_, v_flag_boxed_5463_);
return v_res_5464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5469_, uint8_t v_flag_5470_){
_start:
{
lean_object* v___x_5471_; lean_object* v___x_5472_; 
v___x_5471_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5472_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5469_, v___x_5471_, v_flag_5470_);
return v___x_5472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5473_, lean_object* v_flag_5474_){
_start:
{
uint8_t v_flag_boxed_5475_; lean_object* v_res_5476_; 
v_flag_boxed_5475_ = lean_unbox(v_flag_5474_);
v_res_5476_ = l_Lean_Expr_setPPNumericTypes(v_e_5473_, v_flag_boxed_5475_);
return v_res_5476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5477_, size_t v_i_5478_, lean_object* v_bs_5479_){
_start:
{
uint8_t v___x_5480_; 
v___x_5480_ = lean_usize_dec_lt(v_i_5478_, v_sz_5477_);
if (v___x_5480_ == 0)
{
return v_bs_5479_;
}
else
{
uint8_t v___x_5481_; lean_object* v_v_5482_; lean_object* v___x_5483_; lean_object* v_bs_x27_5484_; lean_object* v___x_5485_; size_t v___x_5486_; size_t v___x_5487_; lean_object* v___x_5488_; 
v___x_5481_ = 0;
v_v_5482_ = lean_array_uget(v_bs_5479_, v_i_5478_);
v___x_5483_ = lean_unsigned_to_nat(0u);
v_bs_x27_5484_ = lean_array_uset(v_bs_5479_, v_i_5478_, v___x_5483_);
v___x_5485_ = l_Lean_Expr_setPPExplicit(v_v_5482_, v___x_5481_);
v___x_5486_ = ((size_t)1ULL);
v___x_5487_ = lean_usize_add(v_i_5478_, v___x_5486_);
v___x_5488_ = lean_array_uset(v_bs_x27_5484_, v_i_5478_, v___x_5485_);
v_i_5478_ = v___x_5487_;
v_bs_5479_ = v___x_5488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5490_, lean_object* v_i_5491_, lean_object* v_bs_5492_){
_start:
{
size_t v_sz_boxed_5493_; size_t v_i_boxed_5494_; lean_object* v_res_5495_; 
v_sz_boxed_5493_ = lean_unbox_usize(v_sz_5490_);
lean_dec(v_sz_5490_);
v_i_boxed_5494_ = lean_unbox_usize(v_i_5491_);
lean_dec(v_i_5491_);
v_res_5495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5493_, v_i_boxed_5494_, v_bs_5492_);
return v_res_5495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5496_){
_start:
{
if (lean_obj_tag(v_e_5496_) == 5)
{
lean_object* v___x_5497_; uint8_t v___x_5498_; lean_object* v_f_5499_; lean_object* v_dummy_5500_; lean_object* v_nargs_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; size_t v_sz_5506_; size_t v___x_5507_; lean_object* v_args_5508_; lean_object* v___x_5509_; uint8_t v___x_5510_; lean_object* v___x_5511_; 
v___x_5497_ = l_Lean_Expr_getAppFn(v_e_5496_);
v___x_5498_ = 0;
v_f_5499_ = l_Lean_Expr_setPPExplicit(v___x_5497_, v___x_5498_);
v_dummy_5500_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5501_ = l_Lean_Expr_getAppNumArgs(v_e_5496_);
lean_inc(v_nargs_5501_);
v___x_5502_ = lean_mk_array(v_nargs_5501_, v_dummy_5500_);
v___x_5503_ = lean_unsigned_to_nat(1u);
v___x_5504_ = lean_nat_sub(v_nargs_5501_, v___x_5503_);
lean_dec(v_nargs_5501_);
v___x_5505_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5496_, v___x_5502_, v___x_5504_);
v_sz_5506_ = lean_array_size(v___x_5505_);
v___x_5507_ = ((size_t)0ULL);
v_args_5508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5506_, v___x_5507_, v___x_5505_);
v___x_5509_ = l_Lean_mkAppN(v_f_5499_, v_args_5508_);
lean_dec_ref(v_args_5508_);
v___x_5510_ = 1;
v___x_5511_ = l_Lean_Expr_setPPExplicit(v___x_5509_, v___x_5510_);
return v___x_5511_;
}
else
{
return v_e_5496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5512_, size_t v_i_5513_, lean_object* v_bs_5514_){
_start:
{
uint8_t v___x_5515_; 
v___x_5515_ = lean_usize_dec_lt(v_i_5513_, v_sz_5512_);
if (v___x_5515_ == 0)
{
return v_bs_5514_;
}
else
{
lean_object* v_v_5516_; lean_object* v___x_5517_; lean_object* v_bs_x27_5518_; lean_object* v___y_5520_; uint8_t v___x_5525_; 
v_v_5516_ = lean_array_uget(v_bs_5514_, v_i_5513_);
v___x_5517_ = lean_unsigned_to_nat(0u);
v_bs_x27_5518_ = lean_array_uset(v_bs_5514_, v_i_5513_, v___x_5517_);
v___x_5525_ = l_Lean_Expr_hasMVar(v_v_5516_);
if (v___x_5525_ == 0)
{
lean_object* v___x_5526_; 
v___x_5526_ = l_Lean_Expr_setPPExplicit(v_v_5516_, v___x_5525_);
v___y_5520_ = v___x_5526_;
goto v___jp_5519_;
}
else
{
v___y_5520_ = v_v_5516_;
goto v___jp_5519_;
}
v___jp_5519_:
{
size_t v___x_5521_; size_t v___x_5522_; lean_object* v___x_5523_; 
v___x_5521_ = ((size_t)1ULL);
v___x_5522_ = lean_usize_add(v_i_5513_, v___x_5521_);
v___x_5523_ = lean_array_uset(v_bs_x27_5518_, v_i_5513_, v___y_5520_);
v_i_5513_ = v___x_5522_;
v_bs_5514_ = v___x_5523_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5527_, lean_object* v_i_5528_, lean_object* v_bs_5529_){
_start:
{
size_t v_sz_boxed_5530_; size_t v_i_boxed_5531_; lean_object* v_res_5532_; 
v_sz_boxed_5530_ = lean_unbox_usize(v_sz_5527_);
lean_dec(v_sz_5527_);
v_i_boxed_5531_ = lean_unbox_usize(v_i_5528_);
lean_dec(v_i_5528_);
v_res_5532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5530_, v_i_boxed_5531_, v_bs_5529_);
return v_res_5532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5533_){
_start:
{
if (lean_obj_tag(v_e_5533_) == 5)
{
lean_object* v___x_5534_; uint8_t v___x_5535_; lean_object* v_f_5536_; lean_object* v_dummy_5537_; lean_object* v_nargs_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; size_t v_sz_5543_; size_t v___x_5544_; lean_object* v_args_5545_; lean_object* v___x_5546_; uint8_t v___x_5547_; lean_object* v___x_5548_; 
v___x_5534_ = l_Lean_Expr_getAppFn(v_e_5533_);
v___x_5535_ = 0;
v_f_5536_ = l_Lean_Expr_setPPExplicit(v___x_5534_, v___x_5535_);
v_dummy_5537_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5538_ = l_Lean_Expr_getAppNumArgs(v_e_5533_);
lean_inc(v_nargs_5538_);
v___x_5539_ = lean_mk_array(v_nargs_5538_, v_dummy_5537_);
v___x_5540_ = lean_unsigned_to_nat(1u);
v___x_5541_ = lean_nat_sub(v_nargs_5538_, v___x_5540_);
lean_dec(v_nargs_5538_);
v___x_5542_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5533_, v___x_5539_, v___x_5541_);
v_sz_5543_ = lean_array_size(v___x_5542_);
v___x_5544_ = ((size_t)0ULL);
v_args_5545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5543_, v___x_5544_, v___x_5542_);
v___x_5546_ = l_Lean_mkAppN(v_f_5536_, v_args_5545_);
lean_dec_ref(v_args_5545_);
v___x_5547_ = 1;
v___x_5548_ = l_Lean_Expr_setPPExplicit(v___x_5546_, v___x_5547_);
return v___x_5548_;
}
else
{
return v_e_5533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5549_, lean_object* v_body_5550_, lean_object* v_x_5551_){
_start:
{
lean_object* v___x_5552_; 
v___x_5552_ = lean_apply_1(v_f_5549_, v_body_5550_);
return v___x_5552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5553_, lean_object* v_binderType_5554_, lean_object* v_x_5555_){
_start:
{
lean_object* v___x_5556_; 
v___x_5556_ = lean_apply_1(v_f_5553_, v_binderType_5554_);
return v___x_5556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5557_, lean_object* v_value_5558_, lean_object* v_x_5559_){
_start:
{
lean_object* v___x_5560_; 
v___x_5560_ = lean_apply_1(v_f_5557_, v_value_5558_);
return v___x_5560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5561_, lean_object* v_type_5562_, lean_object* v_x_5563_){
_start:
{
lean_object* v___x_5564_; 
v___x_5564_ = lean_apply_1(v_f_5561_, v_type_5562_);
return v___x_5564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5565_, lean_object* v_arg_5566_, lean_object* v_x_5567_){
_start:
{
lean_object* v___x_5568_; 
v___x_5568_ = lean_apply_1(v_f_5565_, v_arg_5566_);
return v___x_5568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5569_, lean_object* v_fn_5570_, lean_object* v_x_5571_){
_start:
{
lean_object* v___x_5572_; 
v___x_5572_ = lean_apply_1(v_f_5569_, v_fn_5570_);
return v___x_5572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5573_, lean_object* v_f_5574_, lean_object* v_x_5575_){
_start:
{
switch(lean_obj_tag(v_x_5575_))
{
case 7:
{
lean_object* v_toPure_5576_; lean_object* v_toSeq_5577_; lean_object* v_binderType_5578_; lean_object* v_body_5579_; lean_object* v___f_5580_; lean_object* v___f_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; 
v_toPure_5576_ = lean_ctor_get(v_inst_5573_, 1);
lean_inc(v_toPure_5576_);
v_toSeq_5577_ = lean_ctor_get(v_inst_5573_, 2);
lean_inc_n(v_toSeq_5577_, 2);
lean_dec_ref(v_inst_5573_);
v_binderType_5578_ = lean_ctor_get(v_x_5575_, 1);
v_body_5579_ = lean_ctor_get(v_x_5575_, 2);
lean_inc_ref(v_body_5579_);
lean_inc(v_f_5574_);
v___f_5580_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5580_, 0, v_f_5574_);
lean_closure_set(v___f_5580_, 1, v_body_5579_);
lean_inc_ref(v_binderType_5578_);
v___f_5581_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5581_, 0, v_f_5574_);
lean_closure_set(v___f_5581_, 1, v_binderType_5578_);
v___x_5582_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5582_, 0, v_x_5575_);
v___x_5583_ = lean_apply_2(v_toPure_5576_, lean_box(0), v___x_5582_);
v___x_5584_ = lean_apply_4(v_toSeq_5577_, lean_box(0), lean_box(0), v___x_5583_, v___f_5581_);
v___x_5585_ = lean_apply_4(v_toSeq_5577_, lean_box(0), lean_box(0), v___x_5584_, v___f_5580_);
return v___x_5585_;
}
case 6:
{
lean_object* v_toPure_5586_; lean_object* v_toSeq_5587_; lean_object* v_binderType_5588_; lean_object* v_body_5589_; lean_object* v___f_5590_; lean_object* v___f_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; 
v_toPure_5586_ = lean_ctor_get(v_inst_5573_, 1);
lean_inc(v_toPure_5586_);
v_toSeq_5587_ = lean_ctor_get(v_inst_5573_, 2);
lean_inc_n(v_toSeq_5587_, 2);
lean_dec_ref(v_inst_5573_);
v_binderType_5588_ = lean_ctor_get(v_x_5575_, 1);
v_body_5589_ = lean_ctor_get(v_x_5575_, 2);
lean_inc_ref(v_body_5589_);
lean_inc(v_f_5574_);
v___f_5590_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5590_, 0, v_f_5574_);
lean_closure_set(v___f_5590_, 1, v_body_5589_);
lean_inc_ref(v_binderType_5588_);
v___f_5591_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5591_, 0, v_f_5574_);
lean_closure_set(v___f_5591_, 1, v_binderType_5588_);
v___x_5592_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5592_, 0, v_x_5575_);
v___x_5593_ = lean_apply_2(v_toPure_5586_, lean_box(0), v___x_5592_);
v___x_5594_ = lean_apply_4(v_toSeq_5587_, lean_box(0), lean_box(0), v___x_5593_, v___f_5591_);
v___x_5595_ = lean_apply_4(v_toSeq_5587_, lean_box(0), lean_box(0), v___x_5594_, v___f_5590_);
return v___x_5595_;
}
case 10:
{
lean_object* v_toFunctor_5596_; lean_object* v_expr_5597_; lean_object* v_map_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; 
v_toFunctor_5596_ = lean_ctor_get(v_inst_5573_, 0);
lean_inc_ref(v_toFunctor_5596_);
lean_dec_ref(v_inst_5573_);
v_expr_5597_ = lean_ctor_get(v_x_5575_, 1);
lean_inc_ref(v_expr_5597_);
v_map_5598_ = lean_ctor_get(v_toFunctor_5596_, 0);
lean_inc(v_map_5598_);
lean_dec_ref(v_toFunctor_5596_);
v___x_5599_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5599_, 0, v_x_5575_);
v___x_5600_ = lean_apply_1(v_f_5574_, v_expr_5597_);
v___x_5601_ = lean_apply_4(v_map_5598_, lean_box(0), lean_box(0), v___x_5599_, v___x_5600_);
return v___x_5601_;
}
case 8:
{
lean_object* v_toPure_5602_; lean_object* v_toSeq_5603_; lean_object* v_type_5604_; lean_object* v_value_5605_; lean_object* v_body_5606_; lean_object* v___f_5607_; lean_object* v___f_5608_; lean_object* v___f_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; 
v_toPure_5602_ = lean_ctor_get(v_inst_5573_, 1);
lean_inc(v_toPure_5602_);
v_toSeq_5603_ = lean_ctor_get(v_inst_5573_, 2);
lean_inc_n(v_toSeq_5603_, 3);
lean_dec_ref(v_inst_5573_);
v_type_5604_ = lean_ctor_get(v_x_5575_, 1);
v_value_5605_ = lean_ctor_get(v_x_5575_, 2);
v_body_5606_ = lean_ctor_get(v_x_5575_, 3);
lean_inc_ref(v_body_5606_);
lean_inc_n(v_f_5574_, 2);
v___f_5607_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5607_, 0, v_f_5574_);
lean_closure_set(v___f_5607_, 1, v_body_5606_);
lean_inc_ref(v_value_5605_);
v___f_5608_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5608_, 0, v_f_5574_);
lean_closure_set(v___f_5608_, 1, v_value_5605_);
lean_inc_ref(v_type_5604_);
v___f_5609_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5609_, 0, v_f_5574_);
lean_closure_set(v___f_5609_, 1, v_type_5604_);
v___x_5610_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5610_, 0, v_x_5575_);
v___x_5611_ = lean_apply_2(v_toPure_5602_, lean_box(0), v___x_5610_);
v___x_5612_ = lean_apply_4(v_toSeq_5603_, lean_box(0), lean_box(0), v___x_5611_, v___f_5609_);
v___x_5613_ = lean_apply_4(v_toSeq_5603_, lean_box(0), lean_box(0), v___x_5612_, v___f_5608_);
v___x_5614_ = lean_apply_4(v_toSeq_5603_, lean_box(0), lean_box(0), v___x_5613_, v___f_5607_);
return v___x_5614_;
}
case 5:
{
lean_object* v_toPure_5615_; lean_object* v_toSeq_5616_; lean_object* v_fn_5617_; lean_object* v_arg_5618_; lean_object* v___f_5619_; lean_object* v___f_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; 
v_toPure_5615_ = lean_ctor_get(v_inst_5573_, 1);
lean_inc(v_toPure_5615_);
v_toSeq_5616_ = lean_ctor_get(v_inst_5573_, 2);
lean_inc_n(v_toSeq_5616_, 2);
lean_dec_ref(v_inst_5573_);
v_fn_5617_ = lean_ctor_get(v_x_5575_, 0);
v_arg_5618_ = lean_ctor_get(v_x_5575_, 1);
lean_inc_ref(v_arg_5618_);
lean_inc(v_f_5574_);
v___f_5619_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5619_, 0, v_f_5574_);
lean_closure_set(v___f_5619_, 1, v_arg_5618_);
lean_inc_ref(v_fn_5617_);
v___f_5620_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5620_, 0, v_f_5574_);
lean_closure_set(v___f_5620_, 1, v_fn_5617_);
v___x_5621_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5621_, 0, v_x_5575_);
v___x_5622_ = lean_apply_2(v_toPure_5615_, lean_box(0), v___x_5621_);
v___x_5623_ = lean_apply_4(v_toSeq_5616_, lean_box(0), lean_box(0), v___x_5622_, v___f_5620_);
v___x_5624_ = lean_apply_4(v_toSeq_5616_, lean_box(0), lean_box(0), v___x_5623_, v___f_5619_);
return v___x_5624_;
}
case 11:
{
lean_object* v_toFunctor_5625_; lean_object* v_struct_5626_; lean_object* v_map_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; 
v_toFunctor_5625_ = lean_ctor_get(v_inst_5573_, 0);
lean_inc_ref(v_toFunctor_5625_);
lean_dec_ref(v_inst_5573_);
v_struct_5626_ = lean_ctor_get(v_x_5575_, 2);
lean_inc_ref(v_struct_5626_);
v_map_5627_ = lean_ctor_get(v_toFunctor_5625_, 0);
lean_inc(v_map_5627_);
lean_dec_ref(v_toFunctor_5625_);
v___x_5628_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5628_, 0, v_x_5575_);
v___x_5629_ = lean_apply_1(v_f_5574_, v_struct_5626_);
v___x_5630_ = lean_apply_4(v_map_5627_, lean_box(0), lean_box(0), v___x_5628_, v___x_5629_);
return v___x_5630_;
}
default: 
{
lean_object* v_toPure_5631_; lean_object* v___x_5632_; 
lean_dec(v_f_5574_);
v_toPure_5631_ = lean_ctor_get(v_inst_5573_, 1);
lean_inc(v_toPure_5631_);
lean_dec_ref(v_inst_5573_);
v___x_5632_ = lean_apply_2(v_toPure_5631_, lean_box(0), v_x_5575_);
return v___x_5632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5633_, lean_object* v_inst_5634_, lean_object* v_f_5635_, lean_object* v_x_5636_){
_start:
{
lean_object* v___x_5637_; 
v___x_5637_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5634_, v_f_5635_, v_x_5636_);
return v___x_5637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5638_){
_start:
{
lean_object* v_snd_5639_; 
v_snd_5639_ = lean_ctor_get(v_self_5638_, 1);
lean_inc(v_snd_5639_);
return v_snd_5639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5640_){
_start:
{
lean_object* v_res_5641_; 
v_res_5641_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5640_);
lean_dec_ref(v_self_5640_);
return v_res_5641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5642_, lean_object* v_snd_5643_){
_start:
{
lean_object* v___x_5644_; 
v___x_5644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5644_, 0, v_e_x27_5642_);
lean_ctor_set(v___x_5644_, 1, v_snd_5643_);
return v___x_5644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5645_, lean_object* v_map_5646_, lean_object* v_e_x27_5647_, lean_object* v_a_5648_){
_start:
{
lean_object* v___f_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; 
lean_inc_ref(v_e_x27_5647_);
v___f_5649_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5649_, 0, v_e_x27_5647_);
v___x_5650_ = lean_apply_2(v_f_5645_, v_a_5648_, v_e_x27_5647_);
v___x_5651_ = lean_apply_4(v_map_5646_, lean_box(0), lean_box(0), v___f_5649_, v___x_5650_);
return v___x_5651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5653_, lean_object* v_f_5654_, lean_object* v_init_5655_, lean_object* v_e_5656_){
_start:
{
lean_object* v_toApplicative_5657_; lean_object* v_toFunctor_5658_; lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5685_; 
v_toApplicative_5657_ = lean_ctor_get(v_inst_5653_, 0);
lean_inc_ref(v_toApplicative_5657_);
v_toFunctor_5658_ = lean_ctor_get(v_toApplicative_5657_, 0);
v_isSharedCheck_5685_ = !lean_is_exclusive(v_toApplicative_5657_);
if (v_isSharedCheck_5685_ == 0)
{
lean_object* v_unused_5686_; lean_object* v_unused_5687_; lean_object* v_unused_5688_; lean_object* v_unused_5689_; 
v_unused_5686_ = lean_ctor_get(v_toApplicative_5657_, 4);
lean_dec(v_unused_5686_);
v_unused_5687_ = lean_ctor_get(v_toApplicative_5657_, 3);
lean_dec(v_unused_5687_);
v_unused_5688_ = lean_ctor_get(v_toApplicative_5657_, 2);
lean_dec(v_unused_5688_);
v_unused_5689_ = lean_ctor_get(v_toApplicative_5657_, 1);
lean_dec(v_unused_5689_);
v___x_5660_ = v_toApplicative_5657_;
v_isShared_5661_ = v_isSharedCheck_5685_;
goto v_resetjp_5659_;
}
else
{
lean_inc(v_toFunctor_5658_);
lean_dec(v_toApplicative_5657_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5685_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
lean_object* v_map_5662_; lean_object* v___x_5664_; uint8_t v_isShared_5665_; uint8_t v_isSharedCheck_5683_; 
v_map_5662_ = lean_ctor_get(v_toFunctor_5658_, 0);
v_isSharedCheck_5683_ = !lean_is_exclusive(v_toFunctor_5658_);
if (v_isSharedCheck_5683_ == 0)
{
lean_object* v_unused_5684_; 
v_unused_5684_ = lean_ctor_get(v_toFunctor_5658_, 1);
lean_dec(v_unused_5684_);
v___x_5664_ = v_toFunctor_5658_;
v_isShared_5665_ = v_isSharedCheck_5683_;
goto v_resetjp_5663_;
}
else
{
lean_inc(v_map_5662_);
lean_dec(v_toFunctor_5658_);
v___x_5664_ = lean_box(0);
v_isShared_5665_ = v_isSharedCheck_5683_;
goto v_resetjp_5663_;
}
v_resetjp_5663_:
{
lean_object* v___f_5666_; lean_object* v___f_5667_; lean_object* v___f_5668_; lean_object* v___f_5669_; lean_object* v___f_5670_; lean_object* v___f_5671_; lean_object* v___x_5672_; lean_object* v___x_5674_; 
v___f_5666_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5662_);
v___f_5667_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5667_, 0, v_f_5654_);
lean_closure_set(v___f_5667_, 1, v_map_5662_);
lean_inc_ref_n(v_inst_5653_, 5);
v___f_5668_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5668_, 0, v_inst_5653_);
v___f_5669_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5669_, 0, v_inst_5653_);
v___f_5670_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5670_, 0, v_inst_5653_);
v___f_5671_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5671_, 0, v_inst_5653_);
v___x_5672_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5672_, 0, lean_box(0));
lean_closure_set(v___x_5672_, 1, lean_box(0));
lean_closure_set(v___x_5672_, 2, v_inst_5653_);
if (v_isShared_5665_ == 0)
{
lean_ctor_set(v___x_5664_, 1, v___f_5668_);
lean_ctor_set(v___x_5664_, 0, v___x_5672_);
v___x_5674_ = v___x_5664_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5682_; 
v_reuseFailAlloc_5682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5682_, 0, v___x_5672_);
lean_ctor_set(v_reuseFailAlloc_5682_, 1, v___f_5668_);
v___x_5674_ = v_reuseFailAlloc_5682_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
lean_object* v___x_5675_; lean_object* v___x_5677_; 
v___x_5675_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5675_, 0, lean_box(0));
lean_closure_set(v___x_5675_, 1, lean_box(0));
lean_closure_set(v___x_5675_, 2, v_inst_5653_);
if (v_isShared_5661_ == 0)
{
lean_ctor_set(v___x_5660_, 4, v___f_5671_);
lean_ctor_set(v___x_5660_, 3, v___f_5670_);
lean_ctor_set(v___x_5660_, 2, v___f_5669_);
lean_ctor_set(v___x_5660_, 1, v___x_5675_);
lean_ctor_set(v___x_5660_, 0, v___x_5674_);
v___x_5677_ = v___x_5660_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5681_; 
v_reuseFailAlloc_5681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5681_, 0, v___x_5674_);
lean_ctor_set(v_reuseFailAlloc_5681_, 1, v___x_5675_);
lean_ctor_set(v_reuseFailAlloc_5681_, 2, v___f_5669_);
lean_ctor_set(v_reuseFailAlloc_5681_, 3, v___f_5670_);
lean_ctor_set(v_reuseFailAlloc_5681_, 4, v___f_5671_);
v___x_5677_ = v_reuseFailAlloc_5681_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
lean_object* v___x_30__overap_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; 
v___x_30__overap_5678_ = l_Lean_Expr_traverseChildren___redArg(v___x_5677_, v___f_5667_, v_e_5656_);
v___x_5679_ = lean_apply_1(v___x_30__overap_5678_, v_init_5655_);
v___x_5680_ = lean_apply_4(v_map_5662_, lean_box(0), lean_box(0), v___f_5666_, v___x_5679_);
return v___x_5680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5690_, lean_object* v_m_5691_, lean_object* v_inst_5692_, lean_object* v_f_5693_, lean_object* v_init_5694_, lean_object* v_e_5695_){
_start:
{
lean_object* v___x_5696_; 
v___x_5696_ = l_Lean_Expr_foldlM___redArg(v_inst_5692_, v_f_5693_, v_init_5694_, v_e_5695_);
return v___x_5696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5697_){
_start:
{
lean_object* v_d_5699_; lean_object* v_b_5700_; 
switch(lean_obj_tag(v_x_5697_))
{
case 5:
{
lean_object* v_fn_5706_; lean_object* v_arg_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; 
v_fn_5706_ = lean_ctor_get(v_x_5697_, 0);
v_arg_5707_ = lean_ctor_get(v_x_5697_, 1);
v___x_5708_ = lean_unsigned_to_nat(1u);
v___x_5709_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5706_);
v___x_5710_ = lean_nat_add(v___x_5708_, v___x_5709_);
lean_dec(v___x_5709_);
v___x_5711_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5707_);
v___x_5712_ = lean_nat_add(v___x_5710_, v___x_5711_);
lean_dec(v___x_5711_);
lean_dec(v___x_5710_);
return v___x_5712_;
}
case 6:
{
lean_object* v_binderType_5713_; lean_object* v_body_5714_; 
v_binderType_5713_ = lean_ctor_get(v_x_5697_, 1);
v_body_5714_ = lean_ctor_get(v_x_5697_, 2);
v_d_5699_ = v_binderType_5713_;
v_b_5700_ = v_body_5714_;
goto v___jp_5698_;
}
case 7:
{
lean_object* v_binderType_5715_; lean_object* v_body_5716_; 
v_binderType_5715_ = lean_ctor_get(v_x_5697_, 1);
v_body_5716_ = lean_ctor_get(v_x_5697_, 2);
v_d_5699_ = v_binderType_5715_;
v_b_5700_ = v_body_5716_;
goto v___jp_5698_;
}
case 8:
{
lean_object* v_type_5717_; lean_object* v_value_5718_; lean_object* v_body_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; 
v_type_5717_ = lean_ctor_get(v_x_5697_, 1);
v_value_5718_ = lean_ctor_get(v_x_5697_, 2);
v_body_5719_ = lean_ctor_get(v_x_5697_, 3);
v___x_5720_ = lean_unsigned_to_nat(1u);
v___x_5721_ = l_Lean_Expr_sizeWithoutSharing(v_type_5717_);
v___x_5722_ = lean_nat_add(v___x_5720_, v___x_5721_);
lean_dec(v___x_5721_);
v___x_5723_ = l_Lean_Expr_sizeWithoutSharing(v_value_5718_);
v___x_5724_ = lean_nat_add(v___x_5722_, v___x_5723_);
lean_dec(v___x_5723_);
lean_dec(v___x_5722_);
v___x_5725_ = l_Lean_Expr_sizeWithoutSharing(v_body_5719_);
v___x_5726_ = lean_nat_add(v___x_5724_, v___x_5725_);
lean_dec(v___x_5725_);
lean_dec(v___x_5724_);
return v___x_5726_;
}
case 10:
{
lean_object* v_expr_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; 
v_expr_5727_ = lean_ctor_get(v_x_5697_, 1);
v___x_5728_ = lean_unsigned_to_nat(1u);
v___x_5729_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5727_);
v___x_5730_ = lean_nat_add(v___x_5728_, v___x_5729_);
lean_dec(v___x_5729_);
return v___x_5730_;
}
case 11:
{
lean_object* v_struct_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; 
v_struct_5731_ = lean_ctor_get(v_x_5697_, 2);
v___x_5732_ = lean_unsigned_to_nat(1u);
v___x_5733_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5731_);
v___x_5734_ = lean_nat_add(v___x_5732_, v___x_5733_);
lean_dec(v___x_5733_);
return v___x_5734_;
}
default: 
{
lean_object* v___x_5735_; 
v___x_5735_ = lean_unsigned_to_nat(1u);
return v___x_5735_;
}
}
v___jp_5698_:
{
lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; 
v___x_5701_ = lean_unsigned_to_nat(1u);
v___x_5702_ = l_Lean_Expr_sizeWithoutSharing(v_d_5699_);
v___x_5703_ = lean_nat_add(v___x_5701_, v___x_5702_);
lean_dec(v___x_5702_);
v___x_5704_ = l_Lean_Expr_sizeWithoutSharing(v_b_5700_);
v___x_5705_ = lean_nat_add(v___x_5703_, v___x_5704_);
lean_dec(v___x_5704_);
lean_dec(v___x_5703_);
return v___x_5705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5736_){
_start:
{
lean_object* v_res_5737_; 
v_res_5737_ = l_Lean_Expr_sizeWithoutSharing(v_x_5736_);
lean_dec_ref(v_x_5736_);
return v_res_5737_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5740_, lean_object* v_e_5741_){
_start:
{
lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; 
v___x_5742_ = l_Lean_KVMap_empty;
v___x_5743_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5744_ = l_Lean_KVMap_insert(v___x_5742_, v_kind_5740_, v___x_5743_);
v___x_5745_ = l_Lean_Expr_mdata___override(v___x_5744_, v_e_5741_);
return v___x_5745_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5746_, lean_object* v_e_5747_){
_start:
{
if (lean_obj_tag(v_e_5747_) == 10)
{
lean_object* v_data_5748_; lean_object* v_expr_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; uint8_t v___x_5752_; 
v_data_5748_ = lean_ctor_get(v_e_5747_, 0);
v_expr_5749_ = lean_ctor_get(v_e_5747_, 1);
v___x_5750_ = l_Lean_KVMap_size(v_data_5748_);
v___x_5751_ = lean_unsigned_to_nat(1u);
v___x_5752_ = lean_nat_dec_eq(v___x_5750_, v___x_5751_);
lean_dec(v___x_5750_);
if (v___x_5752_ == 0)
{
lean_object* v___x_5753_; 
v___x_5753_ = lean_box(0);
return v___x_5753_;
}
else
{
uint8_t v___x_5754_; uint8_t v___x_5755_; 
v___x_5754_ = 0;
v___x_5755_ = l_Lean_KVMap_getBool(v_data_5748_, v_kind_5746_, v___x_5754_);
if (v___x_5755_ == 0)
{
lean_object* v___x_5756_; 
v___x_5756_ = lean_box(0);
return v___x_5756_;
}
else
{
lean_object* v___x_5757_; 
lean_inc_ref(v_expr_5749_);
v___x_5757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5757_, 0, v_expr_5749_);
return v___x_5757_;
}
}
}
else
{
lean_object* v___x_5758_; 
v___x_5758_ = lean_box(0);
return v___x_5758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* v_kind_5759_, lean_object* v_e_5760_){
_start:
{
lean_object* v_res_5761_; 
v_res_5761_ = l_Lean_annotation_x3f(v_kind_5759_, v_e_5760_);
lean_dec_ref(v_e_5760_);
lean_dec(v_kind_5759_);
return v_res_5761_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* v_e_5765_){
_start:
{
lean_object* v___x_5766_; lean_object* v___x_5767_; 
v___x_5766_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5767_ = l_Lean_mkAnnotation(v___x_5766_, v_e_5765_);
return v___x_5767_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* v_e_5768_){
_start:
{
lean_object* v___x_5769_; lean_object* v___x_5770_; 
v___x_5769_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5770_ = l_Lean_annotation_x3f(v___x_5769_, v_e_5768_);
return v___x_5770_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* v_e_5771_){
_start:
{
lean_object* v_res_5772_; 
v_res_5772_ = l_Lean_inaccessible_x3f(v_e_5771_);
lean_dec_ref(v_e_5771_);
return v_res_5772_;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* v_p_5777_){
_start:
{
if (lean_obj_tag(v_p_5777_) == 10)
{
lean_object* v_data_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; 
v_data_5778_ = lean_ctor_get(v_p_5777_, 0);
v___x_5779_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5780_ = l_Lean_KVMap_find(v_data_5778_, v___x_5779_);
if (lean_obj_tag(v___x_5780_) == 1)
{
lean_object* v_val_5781_; lean_object* v___x_5783_; uint8_t v_isShared_5784_; uint8_t v_isSharedCheck_5792_; 
v_val_5781_ = lean_ctor_get(v___x_5780_, 0);
v_isSharedCheck_5792_ = !lean_is_exclusive(v___x_5780_);
if (v_isSharedCheck_5792_ == 0)
{
v___x_5783_ = v___x_5780_;
v_isShared_5784_ = v_isSharedCheck_5792_;
goto v_resetjp_5782_;
}
else
{
lean_inc(v_val_5781_);
lean_dec(v___x_5780_);
v___x_5783_ = lean_box(0);
v_isShared_5784_ = v_isSharedCheck_5792_;
goto v_resetjp_5782_;
}
v_resetjp_5782_:
{
if (lean_obj_tag(v_val_5781_) == 5)
{
lean_object* v_v_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5789_; 
v_v_5785_ = lean_ctor_get(v_val_5781_, 0);
lean_inc(v_v_5785_);
lean_dec_ref_known(v_val_5781_, 1);
v___x_5786_ = l_Lean_Expr_mdataExpr_x21(v_p_5777_);
v___x_5787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5787_, 0, v_v_5785_);
lean_ctor_set(v___x_5787_, 1, v___x_5786_);
if (v_isShared_5784_ == 0)
{
lean_ctor_set(v___x_5783_, 0, v___x_5787_);
v___x_5789_ = v___x_5783_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5790_; 
v_reuseFailAlloc_5790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5790_, 0, v___x_5787_);
v___x_5789_ = v_reuseFailAlloc_5790_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
return v___x_5789_;
}
}
else
{
lean_object* v___x_5791_; 
lean_del_object(v___x_5783_);
lean_dec(v_val_5781_);
v___x_5791_ = lean_box(0);
return v___x_5791_;
}
}
}
else
{
lean_object* v___x_5793_; 
lean_dec(v___x_5780_);
v___x_5793_ = lean_box(0);
return v___x_5793_;
}
}
else
{
lean_object* v___x_5794_; 
v___x_5794_ = lean_box(0);
return v___x_5794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* v_p_5795_){
_start:
{
lean_object* v_res_5796_; 
v_res_5796_ = l_Lean_patternWithRef_x3f(v_p_5795_);
lean_dec_ref(v_p_5795_);
return v_res_5796_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object* v_p_5797_){
_start:
{
lean_object* v___x_5798_; 
v___x_5798_ = l_Lean_patternWithRef_x3f(v_p_5797_);
if (lean_obj_tag(v___x_5798_) == 0)
{
uint8_t v___x_5799_; 
v___x_5799_ = 0;
return v___x_5799_;
}
else
{
uint8_t v___x_5800_; 
lean_dec_ref_known(v___x_5798_, 1);
v___x_5800_ = 1;
return v___x_5800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* v_p_5801_){
_start:
{
uint8_t v_res_5802_; lean_object* v_r_5803_; 
v_res_5802_ = l_Lean_isPatternWithRef(v_p_5801_);
lean_dec_ref(v_p_5801_);
v_r_5803_ = lean_box(v_res_5802_);
return v_r_5803_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* v_p_5804_, lean_object* v_stx_5805_){
_start:
{
lean_object* v___x_5806_; 
v___x_5806_ = l_Lean_patternWithRef_x3f(v_p_5804_);
if (lean_obj_tag(v___x_5806_) == 0)
{
lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; 
v___x_5807_ = l_Lean_KVMap_empty;
v___x_5808_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5809_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_5809_, 0, v_stx_5805_);
v___x_5810_ = l_Lean_KVMap_insert(v___x_5807_, v___x_5808_, v___x_5809_);
v___x_5811_ = l_Lean_Expr_mdata___override(v___x_5810_, v_p_5804_);
return v___x_5811_;
}
else
{
lean_dec_ref_known(v___x_5806_, 1);
lean_dec(v_stx_5805_);
return v_p_5804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* v_e_5812_){
_start:
{
lean_object* v___x_5813_; 
v___x_5813_ = l_Lean_inaccessible_x3f(v_e_5812_);
if (lean_obj_tag(v___x_5813_) == 1)
{
return v___x_5813_;
}
else
{
lean_object* v___x_5814_; 
lean_dec(v___x_5813_);
v___x_5814_ = l_Lean_patternWithRef_x3f(v_e_5812_);
if (lean_obj_tag(v___x_5814_) == 1)
{
lean_object* v_val_5815_; lean_object* v___x_5817_; uint8_t v_isShared_5818_; uint8_t v_isSharedCheck_5823_; 
v_val_5815_ = lean_ctor_get(v___x_5814_, 0);
v_isSharedCheck_5823_ = !lean_is_exclusive(v___x_5814_);
if (v_isSharedCheck_5823_ == 0)
{
v___x_5817_ = v___x_5814_;
v_isShared_5818_ = v_isSharedCheck_5823_;
goto v_resetjp_5816_;
}
else
{
lean_inc(v_val_5815_);
lean_dec(v___x_5814_);
v___x_5817_ = lean_box(0);
v_isShared_5818_ = v_isSharedCheck_5823_;
goto v_resetjp_5816_;
}
v_resetjp_5816_:
{
lean_object* v_snd_5819_; lean_object* v___x_5821_; 
v_snd_5819_ = lean_ctor_get(v_val_5815_, 1);
lean_inc(v_snd_5819_);
lean_dec(v_val_5815_);
if (v_isShared_5818_ == 0)
{
lean_ctor_set(v___x_5817_, 0, v_snd_5819_);
v___x_5821_ = v___x_5817_;
goto v_reusejp_5820_;
}
else
{
lean_object* v_reuseFailAlloc_5822_; 
v_reuseFailAlloc_5822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5822_, 0, v_snd_5819_);
v___x_5821_ = v_reuseFailAlloc_5822_;
goto v_reusejp_5820_;
}
v_reusejp_5820_:
{
return v___x_5821_;
}
}
}
else
{
lean_object* v___x_5824_; 
lean_dec(v___x_5814_);
v___x_5824_ = lean_box(0);
return v___x_5824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* v_e_5825_){
_start:
{
lean_object* v_res_5826_; 
v_res_5826_ = l_Lean_patternAnnotation_x3f(v_e_5825_);
lean_dec_ref(v_e_5825_);
return v_res_5826_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* v_e_5830_){
_start:
{
lean_object* v___x_5831_; lean_object* v___x_5832_; 
v___x_5831_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5832_ = l_Lean_mkAnnotation(v___x_5831_, v_e_5830_);
return v___x_5832_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* v_e_5836_){
_start:
{
lean_object* v___x_5837_; lean_object* v___x_5838_; 
v___x_5837_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5838_ = l_Lean_annotation_x3f(v___x_5837_, v_e_5836_);
if (lean_obj_tag(v___x_5838_) == 0)
{
return v___x_5838_;
}
else
{
lean_object* v_val_5839_; lean_object* v___x_5841_; uint8_t v_isShared_5842_; uint8_t v_isSharedCheck_5852_; 
v_val_5839_ = lean_ctor_get(v___x_5838_, 0);
v_isSharedCheck_5852_ = !lean_is_exclusive(v___x_5838_);
if (v_isSharedCheck_5852_ == 0)
{
v___x_5841_ = v___x_5838_;
v_isShared_5842_ = v_isSharedCheck_5852_;
goto v_resetjp_5840_;
}
else
{
lean_inc(v_val_5839_);
lean_dec(v___x_5838_);
v___x_5841_ = lean_box(0);
v_isShared_5842_ = v_isSharedCheck_5852_;
goto v_resetjp_5840_;
}
v_resetjp_5840_:
{
lean_object* v___x_5843_; lean_object* v___x_5844_; uint8_t v___x_5845_; 
v___x_5843_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5844_ = lean_unsigned_to_nat(3u);
v___x_5845_ = l_Lean_Expr_isAppOfArity(v_val_5839_, v___x_5843_, v___x_5844_);
if (v___x_5845_ == 0)
{
lean_object* v___x_5846_; 
lean_del_object(v___x_5841_);
lean_dec(v_val_5839_);
v___x_5846_ = lean_box(0);
return v___x_5846_;
}
else
{
lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5850_; 
v___x_5847_ = l_Lean_Expr_appFn_x21(v_val_5839_);
lean_dec(v_val_5839_);
v___x_5848_ = l_Lean_Expr_appArg_x21(v___x_5847_);
lean_dec_ref(v___x_5847_);
if (v_isShared_5842_ == 0)
{
lean_ctor_set(v___x_5841_, 0, v___x_5848_);
v___x_5850_ = v___x_5841_;
goto v_reusejp_5849_;
}
else
{
lean_object* v_reuseFailAlloc_5851_; 
v_reuseFailAlloc_5851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5851_, 0, v___x_5848_);
v___x_5850_ = v_reuseFailAlloc_5851_;
goto v_reusejp_5849_;
}
v_reusejp_5849_:
{
return v___x_5850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* v_e_5853_){
_start:
{
lean_object* v_res_5854_; 
v_res_5854_ = l_Lean_isLHSGoal_x3f(v_e_5853_);
lean_dec_ref(v_e_5853_);
return v_res_5854_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* v_toPure_5855_, lean_object* v_____do__lift_5856_){
_start:
{
lean_object* v___x_5857_; 
v___x_5857_ = lean_apply_2(v_toPure_5855_, lean_box(0), v_____do__lift_5856_);
return v___x_5857_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* v_inst_5858_, lean_object* v_inst_5859_){
_start:
{
lean_object* v_toApplicative_5860_; lean_object* v_toBind_5861_; lean_object* v_toPure_5862_; lean_object* v___x_5863_; lean_object* v___f_5864_; lean_object* v___x_5865_; 
v_toApplicative_5860_ = lean_ctor_get(v_inst_5858_, 0);
v_toBind_5861_ = lean_ctor_get(v_inst_5858_, 1);
lean_inc(v_toBind_5861_);
v_toPure_5862_ = lean_ctor_get(v_toApplicative_5860_, 1);
lean_inc(v_toPure_5862_);
v___x_5863_ = l_Lean_mkFreshId___redArg(v_inst_5858_, v_inst_5859_);
v___f_5864_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5864_, 0, v_toPure_5862_);
v___x_5865_ = lean_apply_4(v_toBind_5861_, lean_box(0), lean_box(0), v___x_5863_, v___f_5864_);
return v___x_5865_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* v_m_5866_, lean_object* v_inst_5867_, lean_object* v_inst_5868_){
_start:
{
lean_object* v___x_5869_; 
v___x_5869_ = l_Lean_mkFreshFVarId___redArg(v_inst_5867_, v_inst_5868_);
return v___x_5869_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* v_inst_5870_, lean_object* v_inst_5871_){
_start:
{
lean_object* v_toApplicative_5872_; lean_object* v_toBind_5873_; lean_object* v_toPure_5874_; lean_object* v___x_5875_; lean_object* v___f_5876_; lean_object* v___x_5877_; 
v_toApplicative_5872_ = lean_ctor_get(v_inst_5870_, 0);
v_toBind_5873_ = lean_ctor_get(v_inst_5870_, 1);
lean_inc(v_toBind_5873_);
v_toPure_5874_ = lean_ctor_get(v_toApplicative_5872_, 1);
lean_inc(v_toPure_5874_);
v___x_5875_ = l_Lean_mkFreshId___redArg(v_inst_5870_, v_inst_5871_);
v___f_5876_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5876_, 0, v_toPure_5874_);
v___x_5877_ = lean_apply_4(v_toBind_5873_, lean_box(0), lean_box(0), v___x_5875_, v___f_5876_);
return v___x_5877_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* v_m_5878_, lean_object* v_inst_5879_, lean_object* v_inst_5880_){
_start:
{
lean_object* v___x_5881_; 
v___x_5881_ = l_Lean_mkFreshMVarId___redArg(v_inst_5879_, v_inst_5880_);
return v___x_5881_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* v_inst_5882_, lean_object* v_inst_5883_){
_start:
{
lean_object* v_toApplicative_5884_; lean_object* v_toBind_5885_; lean_object* v_toPure_5886_; lean_object* v___x_5887_; lean_object* v___f_5888_; lean_object* v___x_5889_; 
v_toApplicative_5884_ = lean_ctor_get(v_inst_5882_, 0);
v_toBind_5885_ = lean_ctor_get(v_inst_5882_, 1);
lean_inc(v_toBind_5885_);
v_toPure_5886_ = lean_ctor_get(v_toApplicative_5884_, 1);
lean_inc(v_toPure_5886_);
v___x_5887_ = l_Lean_mkFreshId___redArg(v_inst_5882_, v_inst_5883_);
v___f_5888_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5888_, 0, v_toPure_5886_);
v___x_5889_ = lean_apply_4(v_toBind_5885_, lean_box(0), lean_box(0), v___x_5887_, v___f_5888_);
return v___x_5889_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* v_m_5890_, lean_object* v_inst_5891_, lean_object* v_inst_5892_){
_start:
{
lean_object* v___x_5893_; 
v___x_5893_ = l_Lean_mkFreshLMVarId___redArg(v_inst_5891_, v_inst_5892_);
return v___x_5893_;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2(void){
_start:
{
lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; 
v___x_5897_ = lean_box(0);
v___x_5898_ = ((lean_object*)(l_Lean_mkNot___closed__1));
v___x_5899_ = l_Lean_Expr_const___override(v___x_5898_, v___x_5897_);
return v___x_5899_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* v_p_5900_){
_start:
{
lean_object* v___x_5901_; lean_object* v___x_5902_; 
v___x_5901_ = lean_obj_once(&l_Lean_mkNot___closed__2, &l_Lean_mkNot___closed__2_once, _init_l_Lean_mkNot___closed__2);
v___x_5902_ = l_Lean_Expr_app___override(v___x_5901_, v_p_5900_);
return v___x_5902_;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2(void){
_start:
{
lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; 
v___x_5906_ = lean_box(0);
v___x_5907_ = ((lean_object*)(l_Lean_mkOr___closed__1));
v___x_5908_ = l_Lean_Expr_const___override(v___x_5907_, v___x_5906_);
return v___x_5908_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* v_p_5909_, lean_object* v_q_5910_){
_start:
{
lean_object* v___x_5911_; lean_object* v___x_5912_; 
v___x_5911_ = lean_obj_once(&l_Lean_mkOr___closed__2, &l_Lean_mkOr___closed__2_once, _init_l_Lean_mkOr___closed__2);
v___x_5912_ = l_Lean_mkAppB(v___x_5911_, v_p_5909_, v_q_5910_);
return v___x_5912_;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2(void){
_start:
{
lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; 
v___x_5916_ = lean_box(0);
v___x_5917_ = ((lean_object*)(l_Lean_mkAnd___closed__1));
v___x_5918_ = l_Lean_Expr_const___override(v___x_5917_, v___x_5916_);
return v___x_5918_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* v_p_5919_, lean_object* v_q_5920_){
_start:
{
lean_object* v___x_5921_; lean_object* v___x_5922_; 
v___x_5921_ = lean_obj_once(&l_Lean_mkAnd___closed__2, &l_Lean_mkAnd___closed__2_once, _init_l_Lean_mkAnd___closed__2);
v___x_5922_ = l_Lean_mkAppB(v___x_5921_, v_p_5919_, v_q_5920_);
return v___x_5922_;
}
}
static lean_object* _init_l_Lean_mkAndN___closed__0(void){
_start:
{
lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; 
v___x_5923_ = lean_box(0);
v___x_5924_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_5925_ = l_Lean_Expr_const___override(v___x_5924_, v___x_5923_);
return v___x_5925_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* v_x_5926_){
_start:
{
if (lean_obj_tag(v_x_5926_) == 0)
{
lean_object* v___x_5927_; 
v___x_5927_ = lean_obj_once(&l_Lean_mkAndN___closed__0, &l_Lean_mkAndN___closed__0_once, _init_l_Lean_mkAndN___closed__0);
return v___x_5927_;
}
else
{
lean_object* v_tail_5928_; 
v_tail_5928_ = lean_ctor_get(v_x_5926_, 1);
if (lean_obj_tag(v_tail_5928_) == 0)
{
lean_object* v_head_5929_; 
v_head_5929_ = lean_ctor_get(v_x_5926_, 0);
lean_inc(v_head_5929_);
lean_dec_ref_known(v_x_5926_, 2);
return v_head_5929_;
}
else
{
lean_object* v_head_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; 
lean_inc(v_tail_5928_);
v_head_5930_ = lean_ctor_get(v_x_5926_, 0);
lean_inc(v_head_5930_);
lean_dec_ref_known(v_x_5926_, 2);
v___x_5931_ = l_Lean_mkAndN(v_tail_5928_);
v___x_5932_ = l_Lean_mkAnd(v_head_5930_, v___x_5931_);
return v___x_5932_;
}
}
}
}
static lean_object* _init_l_Lean_mkEM___closed__3(void){
_start:
{
lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; 
v___x_5938_ = lean_box(0);
v___x_5939_ = ((lean_object*)(l_Lean_mkEM___closed__2));
v___x_5940_ = l_Lean_Expr_const___override(v___x_5939_, v___x_5938_);
return v___x_5940_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* v_p_5941_){
_start:
{
lean_object* v___x_5942_; lean_object* v___x_5943_; 
v___x_5942_ = lean_obj_once(&l_Lean_mkEM___closed__3, &l_Lean_mkEM___closed__3_once, _init_l_Lean_mkEM___closed__3);
v___x_5943_ = l_Lean_Expr_app___override(v___x_5942_, v_p_5941_);
return v___x_5943_;
}
}
static lean_object* _init_l_Lean_mkIff___closed__2(void){
_start:
{
lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; 
v___x_5947_ = lean_box(0);
v___x_5948_ = ((lean_object*)(l_Lean_mkIff___closed__1));
v___x_5949_ = l_Lean_Expr_const___override(v___x_5948_, v___x_5947_);
return v___x_5949_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* v_p_5950_, lean_object* v_q_5951_){
_start:
{
lean_object* v___x_5952_; lean_object* v___x_5953_; 
v___x_5952_ = lean_obj_once(&l_Lean_mkIff___closed__2, &l_Lean_mkIff___closed__2_once, _init_l_Lean_mkIff___closed__2);
v___x_5953_ = l_Lean_mkAppB(v___x_5952_, v_p_5950_, v_q_5951_);
return v___x_5953_;
}
}
static lean_object* _init_l_Lean_Nat_mkType(void){
_start:
{
lean_object* v___x_5954_; 
v___x_5954_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_5954_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; 
v___x_5958_ = lean_box(0);
v___x_5959_ = ((lean_object*)(l_Lean_Nat_mkInstAdd___closed__1));
v___x_5960_ = l_Lean_Expr_const___override(v___x_5959_, v___x_5958_);
return v___x_5960_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd(void){
_start:
{
lean_object* v___x_5961_; 
v___x_5961_ = lean_obj_once(&l_Lean_Nat_mkInstAdd___closed__2, &l_Lean_Nat_mkInstAdd___closed__2_once, _init_l_Lean_Nat_mkInstAdd___closed__2);
return v___x_5961_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__2(void){
_start:
{
lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; 
v___x_5965_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5966_ = ((lean_object*)(l_Lean_Nat_mkInstHAdd___closed__1));
v___x_5967_ = l_Lean_Expr_const___override(v___x_5966_, v___x_5965_);
return v___x_5967_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__3(void){
_start:
{
lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; 
v___x_5968_ = l_Lean_Nat_mkInstAdd;
v___x_5969_ = l_Lean_Nat_mkType;
v___x_5970_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_5971_ = l_Lean_mkAppB(v___x_5970_, v___x_5969_, v___x_5968_);
return v___x_5971_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd(void){
_start:
{
lean_object* v___x_5972_; 
v___x_5972_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__3, &l_Lean_Nat_mkInstHAdd___closed__3_once, _init_l_Lean_Nat_mkInstHAdd___closed__3);
return v___x_5972_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; 
v___x_5976_ = lean_box(0);
v___x_5977_ = ((lean_object*)(l_Lean_Nat_mkInstSub___closed__1));
v___x_5978_ = l_Lean_Expr_const___override(v___x_5977_, v___x_5976_);
return v___x_5978_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub(void){
_start:
{
lean_object* v___x_5979_; 
v___x_5979_ = lean_obj_once(&l_Lean_Nat_mkInstSub___closed__2, &l_Lean_Nat_mkInstSub___closed__2_once, _init_l_Lean_Nat_mkInstSub___closed__2);
return v___x_5979_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__2(void){
_start:
{
lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; 
v___x_5983_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5984_ = ((lean_object*)(l_Lean_Nat_mkInstHSub___closed__1));
v___x_5985_ = l_Lean_Expr_const___override(v___x_5984_, v___x_5983_);
return v___x_5985_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__3(void){
_start:
{
lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; 
v___x_5986_ = l_Lean_Nat_mkInstSub;
v___x_5987_ = l_Lean_Nat_mkType;
v___x_5988_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_5989_ = l_Lean_mkAppB(v___x_5988_, v___x_5987_, v___x_5986_);
return v___x_5989_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub(void){
_start:
{
lean_object* v___x_5990_; 
v___x_5990_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__3, &l_Lean_Nat_mkInstHSub___closed__3_once, _init_l_Lean_Nat_mkInstHSub___closed__3);
return v___x_5990_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; 
v___x_5994_ = lean_box(0);
v___x_5995_ = ((lean_object*)(l_Lean_Nat_mkInstMul___closed__1));
v___x_5996_ = l_Lean_Expr_const___override(v___x_5995_, v___x_5994_);
return v___x_5996_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul(void){
_start:
{
lean_object* v___x_5997_; 
v___x_5997_ = lean_obj_once(&l_Lean_Nat_mkInstMul___closed__2, &l_Lean_Nat_mkInstMul___closed__2_once, _init_l_Lean_Nat_mkInstMul___closed__2);
return v___x_5997_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__2(void){
_start:
{
lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; 
v___x_6001_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6002_ = ((lean_object*)(l_Lean_Nat_mkInstHMul___closed__1));
v___x_6003_ = l_Lean_Expr_const___override(v___x_6002_, v___x_6001_);
return v___x_6003_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; 
v___x_6004_ = l_Lean_Nat_mkInstMul;
v___x_6005_ = l_Lean_Nat_mkType;
v___x_6006_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6007_ = l_Lean_mkAppB(v___x_6006_, v___x_6005_, v___x_6004_);
return v___x_6007_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul(void){
_start:
{
lean_object* v___x_6008_; 
v___x_6008_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__3, &l_Lean_Nat_mkInstHMul___closed__3_once, _init_l_Lean_Nat_mkInstHMul___closed__3);
return v___x_6008_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv___closed__2(void){
_start:
{
lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; 
v___x_6013_ = lean_box(0);
v___x_6014_ = ((lean_object*)(l_Lean_Nat_mkInstDiv___closed__1));
v___x_6015_ = l_Lean_Expr_const___override(v___x_6014_, v___x_6013_);
return v___x_6015_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv(void){
_start:
{
lean_object* v___x_6016_; 
v___x_6016_ = lean_obj_once(&l_Lean_Nat_mkInstDiv___closed__2, &l_Lean_Nat_mkInstDiv___closed__2_once, _init_l_Lean_Nat_mkInstDiv___closed__2);
return v___x_6016_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__2(void){
_start:
{
lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; 
v___x_6020_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6021_ = ((lean_object*)(l_Lean_Nat_mkInstHDiv___closed__1));
v___x_6022_ = l_Lean_Expr_const___override(v___x_6021_, v___x_6020_);
return v___x_6022_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__3(void){
_start:
{
lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; 
v___x_6023_ = l_Lean_Nat_mkInstDiv;
v___x_6024_ = l_Lean_Nat_mkType;
v___x_6025_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6026_ = l_Lean_mkAppB(v___x_6025_, v___x_6024_, v___x_6023_);
return v___x_6026_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv(void){
_start:
{
lean_object* v___x_6027_; 
v___x_6027_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__3, &l_Lean_Nat_mkInstHDiv___closed__3_once, _init_l_Lean_Nat_mkInstHDiv___closed__3);
return v___x_6027_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod___closed__2(void){
_start:
{
lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; 
v___x_6032_ = lean_box(0);
v___x_6033_ = ((lean_object*)(l_Lean_Nat_mkInstMod___closed__1));
v___x_6034_ = l_Lean_Expr_const___override(v___x_6033_, v___x_6032_);
return v___x_6034_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod(void){
_start:
{
lean_object* v___x_6035_; 
v___x_6035_ = lean_obj_once(&l_Lean_Nat_mkInstMod___closed__2, &l_Lean_Nat_mkInstMod___closed__2_once, _init_l_Lean_Nat_mkInstMod___closed__2);
return v___x_6035_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__2(void){
_start:
{
lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; 
v___x_6039_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6040_ = ((lean_object*)(l_Lean_Nat_mkInstHMod___closed__1));
v___x_6041_ = l_Lean_Expr_const___override(v___x_6040_, v___x_6039_);
return v___x_6041_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__3(void){
_start:
{
lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; 
v___x_6042_ = l_Lean_Nat_mkInstMod;
v___x_6043_ = l_Lean_Nat_mkType;
v___x_6044_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6045_ = l_Lean_mkAppB(v___x_6044_, v___x_6043_, v___x_6042_);
return v___x_6045_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod(void){
_start:
{
lean_object* v___x_6046_; 
v___x_6046_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__3, &l_Lean_Nat_mkInstHMod___closed__3_once, _init_l_Lean_Nat_mkInstHMod___closed__3);
return v___x_6046_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow___closed__2(void){
_start:
{
lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; 
v___x_6050_ = lean_box(0);
v___x_6051_ = ((lean_object*)(l_Lean_Nat_mkInstNatPow___closed__1));
v___x_6052_ = l_Lean_Expr_const___override(v___x_6051_, v___x_6050_);
return v___x_6052_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow(void){
_start:
{
lean_object* v___x_6053_; 
v___x_6053_ = lean_obj_once(&l_Lean_Nat_mkInstNatPow___closed__2, &l_Lean_Nat_mkInstNatPow___closed__2_once, _init_l_Lean_Nat_mkInstNatPow___closed__2);
return v___x_6053_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; 
v___x_6057_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6058_ = ((lean_object*)(l_Lean_Nat_mkInstPow___closed__1));
v___x_6059_ = l_Lean_Expr_const___override(v___x_6058_, v___x_6057_);
return v___x_6059_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__3(void){
_start:
{
lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; 
v___x_6060_ = l_Lean_Nat_mkInstNatPow;
v___x_6061_ = l_Lean_Nat_mkType;
v___x_6062_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6063_ = l_Lean_mkAppB(v___x_6062_, v___x_6061_, v___x_6060_);
return v___x_6063_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow(void){
_start:
{
lean_object* v___x_6064_; 
v___x_6064_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__3, &l_Lean_Nat_mkInstPow___closed__3_once, _init_l_Lean_Nat_mkInstPow___closed__3);
return v___x_6064_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__3(void){
_start:
{
lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; 
v___x_6071_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__2));
v___x_6072_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__1));
v___x_6073_ = l_Lean_Expr_const___override(v___x_6072_, v___x_6071_);
return v___x_6073_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__4(void){
_start:
{
lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; 
v___x_6074_ = l_Lean_Nat_mkInstPow;
v___x_6075_ = l_Lean_Nat_mkType;
v___x_6076_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6077_ = l_Lean_mkApp3(v___x_6076_, v___x_6075_, v___x_6075_, v___x_6074_);
return v___x_6077_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow(void){
_start:
{
lean_object* v___x_6078_; 
v___x_6078_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__4, &l_Lean_Nat_mkInstHPow___closed__4_once, _init_l_Lean_Nat_mkInstHPow___closed__4);
return v___x_6078_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; 
v___x_6082_ = lean_box(0);
v___x_6083_ = ((lean_object*)(l_Lean_Nat_mkInstLT___closed__1));
v___x_6084_ = l_Lean_Expr_const___override(v___x_6083_, v___x_6082_);
return v___x_6084_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT(void){
_start:
{
lean_object* v___x_6085_; 
v___x_6085_ = lean_obj_once(&l_Lean_Nat_mkInstLT___closed__2, &l_Lean_Nat_mkInstLT___closed__2_once, _init_l_Lean_Nat_mkInstLT___closed__2);
return v___x_6085_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; 
v___x_6089_ = lean_box(0);
v___x_6090_ = ((lean_object*)(l_Lean_Nat_mkInstLE___closed__1));
v___x_6091_ = l_Lean_Expr_const___override(v___x_6090_, v___x_6089_);
return v___x_6091_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE(void){
_start:
{
lean_object* v___x_6092_; 
v___x_6092_ = lean_obj_once(&l_Lean_Nat_mkInstLE___closed__2, &l_Lean_Nat_mkInstLE___closed__2_once, _init_l_Lean_Nat_mkInstLE___closed__2);
return v___x_6092_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3(void){
_start:
{
lean_object* v___x_6098_; lean_object* v___x_6099_; 
v___x_6098_ = lean_unsigned_to_nat(0u);
v___x_6099_ = l_Lean_Level_ofNat(v___x_6098_);
return v___x_6099_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4(void){
_start:
{
lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; 
v___x_6100_ = lean_box(0);
v___x_6101_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
lean_ctor_set(v___x_6102_, 1, v___x_6100_);
return v___x_6102_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5(void){
_start:
{
lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; 
v___x_6103_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6104_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6105_, 0, v___x_6104_);
lean_ctor_set(v___x_6105_, 1, v___x_6103_);
return v___x_6105_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6(void){
_start:
{
lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; 
v___x_6106_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__5, &l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5);
v___x_6107_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6108_, 0, v___x_6107_);
lean_ctor_set(v___x_6108_, 1, v___x_6106_);
return v___x_6108_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7(void){
_start:
{
lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; 
v___x_6109_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6110_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natAddFn___closed__2));
v___x_6111_ = l_Lean_Expr_const___override(v___x_6110_, v___x_6109_);
return v___x_6111_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8(void){
_start:
{
lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; 
v___x_6112_ = l_Lean_Nat_mkInstHAdd;
v___x_6113_ = l_Lean_Nat_mkType;
v___x_6114_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6115_ = l_Lean_mkApp4(v___x_6114_, v___x_6113_, v___x_6113_, v___x_6113_, v___x_6112_);
return v___x_6115_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn(void){
_start:
{
lean_object* v___x_6116_; 
v___x_6116_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__8, &l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8);
return v___x_6116_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3(void){
_start:
{
lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; 
v___x_6122_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6123_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natSubFn___closed__2));
v___x_6124_ = l_Lean_Expr_const___override(v___x_6123_, v___x_6122_);
return v___x_6124_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4(void){
_start:
{
lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; 
v___x_6125_ = l_Lean_Nat_mkInstHSub;
v___x_6126_ = l_Lean_Nat_mkType;
v___x_6127_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6128_ = l_Lean_mkApp4(v___x_6127_, v___x_6126_, v___x_6126_, v___x_6126_, v___x_6125_);
return v___x_6128_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn(void){
_start:
{
lean_object* v___x_6129_; 
v___x_6129_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__4, &l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4);
return v___x_6129_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3(void){
_start:
{
lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; 
v___x_6135_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6136_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natMulFn___closed__2));
v___x_6137_ = l_Lean_Expr_const___override(v___x_6136_, v___x_6135_);
return v___x_6137_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4(void){
_start:
{
lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; 
v___x_6138_ = l_Lean_Nat_mkInstHMul;
v___x_6139_ = l_Lean_Nat_mkType;
v___x_6140_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6141_ = l_Lean_mkApp4(v___x_6140_, v___x_6139_, v___x_6139_, v___x_6139_, v___x_6138_);
return v___x_6141_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn(void){
_start:
{
lean_object* v___x_6142_; 
v___x_6142_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__4, &l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4);
return v___x_6142_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3(void){
_start:
{
lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; 
v___x_6148_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6149_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natPowFn___closed__2));
v___x_6150_ = l_Lean_Expr_const___override(v___x_6149_, v___x_6148_);
return v___x_6150_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4(void){
_start:
{
lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; 
v___x_6151_ = l_Lean_Nat_mkInstHPow;
v___x_6152_ = l_Lean_Nat_mkType;
v___x_6153_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6154_ = l_Lean_mkApp4(v___x_6153_, v___x_6152_, v___x_6152_, v___x_6152_, v___x_6151_);
return v___x_6154_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn(void){
_start:
{
lean_object* v___x_6155_; 
v___x_6155_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__4, &l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4);
return v___x_6155_;
}
}
static lean_object* _init_l_Lean_mkNatSucc___closed__2(void){
_start:
{
lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; 
v___x_6160_ = lean_box(0);
v___x_6161_ = ((lean_object*)(l_Lean_mkNatSucc___closed__1));
v___x_6162_ = l_Lean_Expr_const___override(v___x_6161_, v___x_6160_);
return v___x_6162_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* v_a_6163_){
_start:
{
lean_object* v___x_6164_; lean_object* v___x_6165_; 
v___x_6164_ = lean_obj_once(&l_Lean_mkNatSucc___closed__2, &l_Lean_mkNatSucc___closed__2_once, _init_l_Lean_mkNatSucc___closed__2);
v___x_6165_ = l_Lean_Expr_app___override(v___x_6164_, v_a_6163_);
return v___x_6165_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* v_a_6166_, lean_object* v_b_6167_){
_start:
{
lean_object* v___x_6168_; lean_object* v___x_6169_; 
v___x_6168_ = l___private_Lean_Expr_0__Lean_natAddFn;
v___x_6169_ = l_Lean_mkAppB(v___x_6168_, v_a_6166_, v_b_6167_);
return v___x_6169_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* v_a_6170_, lean_object* v_b_6171_){
_start:
{
lean_object* v___x_6172_; lean_object* v___x_6173_; 
v___x_6172_ = l___private_Lean_Expr_0__Lean_natSubFn;
v___x_6173_ = l_Lean_mkAppB(v___x_6172_, v_a_6170_, v_b_6171_);
return v___x_6173_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* v_a_6174_, lean_object* v_b_6175_){
_start:
{
lean_object* v___x_6176_; lean_object* v___x_6177_; 
v___x_6176_ = l___private_Lean_Expr_0__Lean_natMulFn;
v___x_6177_ = l_Lean_mkAppB(v___x_6176_, v_a_6174_, v_b_6175_);
return v___x_6177_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object* v_a_6178_, lean_object* v_b_6179_){
_start:
{
lean_object* v___x_6180_; lean_object* v___x_6181_; 
v___x_6180_ = l___private_Lean_Expr_0__Lean_natPowFn;
v___x_6181_ = l_Lean_mkAppB(v___x_6180_, v_a_6178_, v_b_6179_);
return v___x_6181_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3(void){
_start:
{
lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; 
v___x_6187_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6188_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natLEPred___closed__2));
v___x_6189_ = l_Lean_Expr_const___override(v___x_6188_, v___x_6187_);
return v___x_6189_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4(void){
_start:
{
lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; 
v___x_6190_ = l_Lean_Nat_mkInstLE;
v___x_6191_ = l_Lean_Nat_mkType;
v___x_6192_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6193_ = l_Lean_mkAppB(v___x_6192_, v___x_6191_, v___x_6190_);
return v___x_6193_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred(void){
_start:
{
lean_object* v___x_6194_; 
v___x_6194_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__4, &l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4);
return v___x_6194_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* v_a_6195_, lean_object* v_b_6196_){
_start:
{
lean_object* v___x_6197_; lean_object* v___x_6198_; 
v___x_6197_ = l___private_Lean_Expr_0__Lean_natLEPred;
v___x_6198_ = l_Lean_mkAppB(v___x_6197_, v_a_6195_, v_b_6196_);
return v___x_6198_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0(void){
_start:
{
lean_object* v___x_6199_; lean_object* v___x_6200_; 
v___x_6199_ = lean_unsigned_to_nat(1u);
v___x_6200_ = l_Lean_Level_ofNat(v___x_6199_);
return v___x_6200_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1(void){
_start:
{
lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; 
v___x_6201_ = lean_box(0);
v___x_6202_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__0, &l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0);
v___x_6203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6203_, 0, v___x_6202_);
lean_ctor_set(v___x_6203_, 1, v___x_6201_);
return v___x_6203_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2(void){
_start:
{
lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; 
v___x_6204_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__1, &l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1);
v___x_6205_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_6206_ = l_Lean_Expr_const___override(v___x_6205_, v___x_6204_);
return v___x_6206_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3(void){
_start:
{
lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; 
v___x_6207_ = l_Lean_Nat_mkType;
v___x_6208_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6209_ = l_Lean_Expr_app___override(v___x_6208_, v___x_6207_);
return v___x_6209_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred(void){
_start:
{
lean_object* v___x_6210_; 
v___x_6210_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__3, &l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3);
return v___x_6210_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* v_a_6211_, lean_object* v_b_6212_){
_start:
{
lean_object* v___x_6213_; lean_object* v___x_6214_; 
v___x_6213_ = l___private_Lean_Expr_0__Lean_natEqPred;
v___x_6214_ = l_Lean_mkAppB(v___x_6213_, v_a_6211_, v_b_6212_);
return v___x_6214_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__0(void){
_start:
{
lean_object* v___x_6215_; lean_object* v___x_6216_; 
v___x_6215_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6216_ = l_Lean_Expr_sort___override(v___x_6215_);
return v___x_6216_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__1(void){
_start:
{
lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; 
v___x_6217_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__0, &l___private_Lean_Expr_0__Lean_propEq___closed__0_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__0);
v___x_6218_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6219_ = l_Lean_Expr_app___override(v___x_6218_, v___x_6217_);
return v___x_6219_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq(void){
_start:
{
lean_object* v___x_6220_; 
v___x_6220_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__1, &l___private_Lean_Expr_0__Lean_propEq___closed__1_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__1);
return v___x_6220_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* v_a_6221_, lean_object* v_b_6222_){
_start:
{
lean_object* v___x_6223_; lean_object* v___x_6224_; 
v___x_6223_ = l___private_Lean_Expr_0__Lean_propEq;
v___x_6224_ = l_Lean_mkAppB(v___x_6223_, v_a_6221_, v_b_6222_);
return v___x_6224_;
}
}
static lean_object* _init_l_Lean_Int_mkType___closed__2(void){
_start:
{
lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; 
v___x_6228_ = lean_box(0);
v___x_6229_ = ((lean_object*)(l_Lean_Int_mkType___closed__1));
v___x_6230_ = l_Lean_Expr_const___override(v___x_6229_, v___x_6228_);
return v___x_6230_;
}
}
static lean_object* _init_l_Lean_Int_mkType(void){
_start:
{
lean_object* v___x_6231_; 
v___x_6231_ = lean_obj_once(&l_Lean_Int_mkType___closed__2, &l_Lean_Int_mkType___closed__2_once, _init_l_Lean_Int_mkType___closed__2);
return v___x_6231_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg___closed__2(void){
_start:
{
lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; 
v___x_6236_ = lean_box(0);
v___x_6237_ = ((lean_object*)(l_Lean_Int_mkInstNeg___closed__1));
v___x_6238_ = l_Lean_Expr_const___override(v___x_6237_, v___x_6236_);
return v___x_6238_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg(void){
_start:
{
lean_object* v___x_6239_; 
v___x_6239_ = lean_obj_once(&l_Lean_Int_mkInstNeg___closed__2, &l_Lean_Int_mkInstNeg___closed__2_once, _init_l_Lean_Int_mkInstNeg___closed__2);
return v___x_6239_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; 
v___x_6244_ = lean_box(0);
v___x_6245_ = ((lean_object*)(l_Lean_Int_mkInstAdd___closed__1));
v___x_6246_ = l_Lean_Expr_const___override(v___x_6245_, v___x_6244_);
return v___x_6246_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd(void){
_start:
{
lean_object* v___x_6247_; 
v___x_6247_ = lean_obj_once(&l_Lean_Int_mkInstAdd___closed__2, &l_Lean_Int_mkInstAdd___closed__2_once, _init_l_Lean_Int_mkInstAdd___closed__2);
return v___x_6247_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd___closed__0(void){
_start:
{
lean_object* v___x_6248_; lean_object* v___x_6249_; lean_object* v___x_6250_; lean_object* v___x_6251_; 
v___x_6248_ = l_Lean_Int_mkInstAdd;
v___x_6249_ = l_Lean_Int_mkType;
v___x_6250_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6251_ = l_Lean_mkAppB(v___x_6250_, v___x_6249_, v___x_6248_);
return v___x_6251_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd(void){
_start:
{
lean_object* v___x_6252_; 
v___x_6252_ = lean_obj_once(&l_Lean_Int_mkInstHAdd___closed__0, &l_Lean_Int_mkInstHAdd___closed__0_once, _init_l_Lean_Int_mkInstHAdd___closed__0);
return v___x_6252_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6257_; lean_object* v___x_6258_; lean_object* v___x_6259_; 
v___x_6257_ = lean_box(0);
v___x_6258_ = ((lean_object*)(l_Lean_Int_mkInstSub___closed__1));
v___x_6259_ = l_Lean_Expr_const___override(v___x_6258_, v___x_6257_);
return v___x_6259_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub(void){
_start:
{
lean_object* v___x_6260_; 
v___x_6260_ = lean_obj_once(&l_Lean_Int_mkInstSub___closed__2, &l_Lean_Int_mkInstSub___closed__2_once, _init_l_Lean_Int_mkInstSub___closed__2);
return v___x_6260_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub___closed__0(void){
_start:
{
lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; 
v___x_6261_ = l_Lean_Int_mkInstSub;
v___x_6262_ = l_Lean_Int_mkType;
v___x_6263_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6264_ = l_Lean_mkAppB(v___x_6263_, v___x_6262_, v___x_6261_);
return v___x_6264_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub(void){
_start:
{
lean_object* v___x_6265_; 
v___x_6265_ = lean_obj_once(&l_Lean_Int_mkInstHSub___closed__0, &l_Lean_Int_mkInstHSub___closed__0_once, _init_l_Lean_Int_mkInstHSub___closed__0);
return v___x_6265_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6270_; lean_object* v___x_6271_; lean_object* v___x_6272_; 
v___x_6270_ = lean_box(0);
v___x_6271_ = ((lean_object*)(l_Lean_Int_mkInstMul___closed__1));
v___x_6272_ = l_Lean_Expr_const___override(v___x_6271_, v___x_6270_);
return v___x_6272_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul(void){
_start:
{
lean_object* v___x_6273_; 
v___x_6273_ = lean_obj_once(&l_Lean_Int_mkInstMul___closed__2, &l_Lean_Int_mkInstMul___closed__2_once, _init_l_Lean_Int_mkInstMul___closed__2);
return v___x_6273_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul___closed__0(void){
_start:
{
lean_object* v___x_6274_; lean_object* v___x_6275_; lean_object* v___x_6276_; lean_object* v___x_6277_; 
v___x_6274_ = l_Lean_Int_mkInstMul;
v___x_6275_ = l_Lean_Int_mkType;
v___x_6276_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6277_ = l_Lean_mkAppB(v___x_6276_, v___x_6275_, v___x_6274_);
return v___x_6277_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul(void){
_start:
{
lean_object* v___x_6278_; 
v___x_6278_ = lean_obj_once(&l_Lean_Int_mkInstHMul___closed__0, &l_Lean_Int_mkInstHMul___closed__0_once, _init_l_Lean_Int_mkInstHMul___closed__0);
return v___x_6278_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv___closed__1(void){
_start:
{
lean_object* v___x_6282_; lean_object* v___x_6283_; lean_object* v___x_6284_; 
v___x_6282_ = lean_box(0);
v___x_6283_ = ((lean_object*)(l_Lean_Int_mkInstDiv___closed__0));
v___x_6284_ = l_Lean_Expr_const___override(v___x_6283_, v___x_6282_);
return v___x_6284_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv(void){
_start:
{
lean_object* v___x_6285_; 
v___x_6285_ = lean_obj_once(&l_Lean_Int_mkInstDiv___closed__1, &l_Lean_Int_mkInstDiv___closed__1_once, _init_l_Lean_Int_mkInstDiv___closed__1);
return v___x_6285_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv___closed__0(void){
_start:
{
lean_object* v___x_6286_; lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; 
v___x_6286_ = l_Lean_Int_mkInstDiv;
v___x_6287_ = l_Lean_Int_mkType;
v___x_6288_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6289_ = l_Lean_mkAppB(v___x_6288_, v___x_6287_, v___x_6286_);
return v___x_6289_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv(void){
_start:
{
lean_object* v___x_6290_; 
v___x_6290_ = lean_obj_once(&l_Lean_Int_mkInstHDiv___closed__0, &l_Lean_Int_mkInstHDiv___closed__0_once, _init_l_Lean_Int_mkInstHDiv___closed__0);
return v___x_6290_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod___closed__1(void){
_start:
{
lean_object* v___x_6294_; lean_object* v___x_6295_; lean_object* v___x_6296_; 
v___x_6294_ = lean_box(0);
v___x_6295_ = ((lean_object*)(l_Lean_Int_mkInstMod___closed__0));
v___x_6296_ = l_Lean_Expr_const___override(v___x_6295_, v___x_6294_);
return v___x_6296_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod(void){
_start:
{
lean_object* v___x_6297_; 
v___x_6297_ = lean_obj_once(&l_Lean_Int_mkInstMod___closed__1, &l_Lean_Int_mkInstMod___closed__1_once, _init_l_Lean_Int_mkInstMod___closed__1);
return v___x_6297_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod___closed__0(void){
_start:
{
lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; 
v___x_6298_ = l_Lean_Int_mkInstMod;
v___x_6299_ = l_Lean_Int_mkType;
v___x_6300_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6301_ = l_Lean_mkAppB(v___x_6300_, v___x_6299_, v___x_6298_);
return v___x_6301_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod(void){
_start:
{
lean_object* v___x_6302_; 
v___x_6302_ = lean_obj_once(&l_Lean_Int_mkInstHMod___closed__0, &l_Lean_Int_mkInstHMod___closed__0_once, _init_l_Lean_Int_mkInstHMod___closed__0);
return v___x_6302_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6307_; lean_object* v___x_6308_; lean_object* v___x_6309_; 
v___x_6307_ = lean_box(0);
v___x_6308_ = ((lean_object*)(l_Lean_Int_mkInstPow___closed__1));
v___x_6309_ = l_Lean_Expr_const___override(v___x_6308_, v___x_6307_);
return v___x_6309_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow(void){
_start:
{
lean_object* v___x_6310_; 
v___x_6310_ = lean_obj_once(&l_Lean_Int_mkInstPow___closed__2, &l_Lean_Int_mkInstPow___closed__2_once, _init_l_Lean_Int_mkInstPow___closed__2);
return v___x_6310_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat___closed__0(void){
_start:
{
lean_object* v___x_6311_; lean_object* v___x_6312_; lean_object* v___x_6313_; lean_object* v___x_6314_; 
v___x_6311_ = l_Lean_Int_mkInstPow;
v___x_6312_ = l_Lean_Int_mkType;
v___x_6313_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6314_ = l_Lean_mkAppB(v___x_6313_, v___x_6312_, v___x_6311_);
return v___x_6314_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat(void){
_start:
{
lean_object* v___x_6315_; 
v___x_6315_ = lean_obj_once(&l_Lean_Int_mkInstPowNat___closed__0, &l_Lean_Int_mkInstPowNat___closed__0_once, _init_l_Lean_Int_mkInstPowNat___closed__0);
return v___x_6315_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow___closed__0(void){
_start:
{
lean_object* v___x_6316_; lean_object* v___x_6317_; lean_object* v___x_6318_; lean_object* v___x_6319_; lean_object* v___x_6320_; 
v___x_6316_ = l_Lean_Int_mkInstPowNat;
v___x_6317_ = l_Lean_Nat_mkType;
v___x_6318_ = l_Lean_Int_mkType;
v___x_6319_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6320_ = l_Lean_mkApp3(v___x_6319_, v___x_6318_, v___x_6317_, v___x_6316_);
return v___x_6320_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow(void){
_start:
{
lean_object* v___x_6321_; 
v___x_6321_ = lean_obj_once(&l_Lean_Int_mkInstHPow___closed__0, &l_Lean_Int_mkInstHPow___closed__0_once, _init_l_Lean_Int_mkInstHPow___closed__0);
return v___x_6321_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6326_; lean_object* v___x_6327_; lean_object* v___x_6328_; 
v___x_6326_ = lean_box(0);
v___x_6327_ = ((lean_object*)(l_Lean_Int_mkInstLT___closed__1));
v___x_6328_ = l_Lean_Expr_const___override(v___x_6327_, v___x_6326_);
return v___x_6328_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT(void){
_start:
{
lean_object* v___x_6329_; 
v___x_6329_ = lean_obj_once(&l_Lean_Int_mkInstLT___closed__2, &l_Lean_Int_mkInstLT___closed__2_once, _init_l_Lean_Int_mkInstLT___closed__2);
return v___x_6329_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6334_; lean_object* v___x_6335_; lean_object* v___x_6336_; 
v___x_6334_ = lean_box(0);
v___x_6335_ = ((lean_object*)(l_Lean_Int_mkInstLE___closed__1));
v___x_6336_ = l_Lean_Expr_const___override(v___x_6335_, v___x_6334_);
return v___x_6336_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE(void){
_start:
{
lean_object* v___x_6337_; 
v___x_6337_ = lean_obj_once(&l_Lean_Int_mkInstLE___closed__2, &l_Lean_Int_mkInstLE___closed__2_once, _init_l_Lean_Int_mkInstLE___closed__2);
return v___x_6337_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast___closed__2(void){
_start:
{
lean_object* v___x_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; 
v___x_6341_ = lean_box(0);
v___x_6342_ = ((lean_object*)(l_Lean_Int_mkInstNatCast___closed__1));
v___x_6343_ = l_Lean_Expr_const___override(v___x_6342_, v___x_6341_);
return v___x_6343_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast(void){
_start:
{
lean_object* v___x_6344_; 
v___x_6344_ = lean_obj_once(&l_Lean_Int_mkInstNatCast___closed__2, &l_Lean_Int_mkInstNatCast___closed__2_once, _init_l_Lean_Int_mkInstNatCast___closed__2);
return v___x_6344_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0(void){
_start:
{
lean_object* v___x_6345_; lean_object* v___x_6346_; lean_object* v___x_6347_; 
v___x_6345_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6346_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_6347_ = l_Lean_Expr_const___override(v___x_6346_, v___x_6345_);
return v___x_6347_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1(void){
_start:
{
lean_object* v___x_6348_; lean_object* v___x_6349_; lean_object* v___x_6350_; lean_object* v___x_6351_; 
v___x_6348_ = l_Lean_Int_mkInstNeg;
v___x_6349_ = l_Lean_Int_mkType;
v___x_6350_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__0, &l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0);
v___x_6351_ = l_Lean_mkAppB(v___x_6350_, v___x_6349_, v___x_6348_);
return v___x_6351_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn(void){
_start:
{
lean_object* v___x_6352_; 
v___x_6352_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__1, &l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1);
return v___x_6352_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0(void){
_start:
{
lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6356_; 
v___x_6353_ = l_Lean_Int_mkInstHAdd;
v___x_6354_ = l_Lean_Int_mkType;
v___x_6355_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6356_ = l_Lean_mkApp4(v___x_6355_, v___x_6354_, v___x_6354_, v___x_6354_, v___x_6353_);
return v___x_6356_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn(void){
_start:
{
lean_object* v___x_6357_; 
v___x_6357_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intAddFn___closed__0, &l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0);
return v___x_6357_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0(void){
_start:
{
lean_object* v___x_6358_; lean_object* v___x_6359_; lean_object* v___x_6360_; lean_object* v___x_6361_; 
v___x_6358_ = l_Lean_Int_mkInstHSub;
v___x_6359_ = l_Lean_Int_mkType;
v___x_6360_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6361_ = l_Lean_mkApp4(v___x_6360_, v___x_6359_, v___x_6359_, v___x_6359_, v___x_6358_);
return v___x_6361_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn(void){
_start:
{
lean_object* v___x_6362_; 
v___x_6362_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intSubFn___closed__0, &l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0);
return v___x_6362_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0(void){
_start:
{
lean_object* v___x_6363_; lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; 
v___x_6363_ = l_Lean_Int_mkInstHMul;
v___x_6364_ = l_Lean_Int_mkType;
v___x_6365_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6366_ = l_Lean_mkApp4(v___x_6365_, v___x_6364_, v___x_6364_, v___x_6364_, v___x_6363_);
return v___x_6366_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn(void){
_start:
{
lean_object* v___x_6367_; 
v___x_6367_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intMulFn___closed__0, &l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0);
return v___x_6367_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3(void){
_start:
{
lean_object* v___x_6373_; lean_object* v___x_6374_; lean_object* v___x_6375_; 
v___x_6373_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6374_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intDivFn___closed__2));
v___x_6375_ = l_Lean_Expr_const___override(v___x_6374_, v___x_6373_);
return v___x_6375_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4(void){
_start:
{
lean_object* v___x_6376_; lean_object* v___x_6377_; lean_object* v___x_6378_; lean_object* v___x_6379_; 
v___x_6376_ = l_Lean_Int_mkInstHDiv;
v___x_6377_ = l_Lean_Int_mkType;
v___x_6378_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__3, &l___private_Lean_Expr_0__Lean_intDivFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3);
v___x_6379_ = l_Lean_mkApp4(v___x_6378_, v___x_6377_, v___x_6377_, v___x_6377_, v___x_6376_);
return v___x_6379_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn(void){
_start:
{
lean_object* v___x_6380_; 
v___x_6380_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__4, &l___private_Lean_Expr_0__Lean_intDivFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4);
return v___x_6380_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3(void){
_start:
{
lean_object* v___x_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; 
v___x_6386_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6387_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intModFn___closed__2));
v___x_6388_ = l_Lean_Expr_const___override(v___x_6387_, v___x_6386_);
return v___x_6388_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4(void){
_start:
{
lean_object* v___x_6389_; lean_object* v___x_6390_; lean_object* v___x_6391_; lean_object* v___x_6392_; 
v___x_6389_ = l_Lean_Int_mkInstHMod;
v___x_6390_ = l_Lean_Int_mkType;
v___x_6391_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__3, &l___private_Lean_Expr_0__Lean_intModFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3);
v___x_6392_ = l_Lean_mkApp4(v___x_6391_, v___x_6390_, v___x_6390_, v___x_6390_, v___x_6389_);
return v___x_6392_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn(void){
_start:
{
lean_object* v___x_6393_; 
v___x_6393_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__4, &l___private_Lean_Expr_0__Lean_intModFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4);
return v___x_6393_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0(void){
_start:
{
lean_object* v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; lean_object* v___x_6397_; lean_object* v___x_6398_; 
v___x_6394_ = l_Lean_Int_mkInstHPow;
v___x_6395_ = l_Lean_Nat_mkType;
v___x_6396_ = l_Lean_Int_mkType;
v___x_6397_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6398_ = l_Lean_mkApp4(v___x_6397_, v___x_6396_, v___x_6395_, v___x_6396_, v___x_6394_);
return v___x_6398_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn(void){
_start:
{
lean_object* v___x_6399_; 
v___x_6399_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0, &l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0);
return v___x_6399_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3(void){
_start:
{
lean_object* v___x_6405_; lean_object* v___x_6406_; lean_object* v___x_6407_; 
v___x_6405_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6406_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2));
v___x_6407_ = l_Lean_Expr_const___override(v___x_6406_, v___x_6405_);
return v___x_6407_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4(void){
_start:
{
lean_object* v___x_6408_; lean_object* v___x_6409_; lean_object* v___x_6410_; lean_object* v___x_6411_; 
v___x_6408_ = l_Lean_Int_mkInstNatCast;
v___x_6409_ = l_Lean_Int_mkType;
v___x_6410_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3);
v___x_6411_ = l_Lean_mkAppB(v___x_6410_, v___x_6409_, v___x_6408_);
return v___x_6411_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn(void){
_start:
{
lean_object* v___x_6412_; 
v___x_6412_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4);
return v___x_6412_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* v_a_6413_){
_start:
{
lean_object* v___x_6414_; lean_object* v___x_6415_; 
v___x_6414_ = l___private_Lean_Expr_0__Lean_intNegFn;
v___x_6415_ = l_Lean_Expr_app___override(v___x_6414_, v_a_6413_);
return v___x_6415_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* v_a_6416_, lean_object* v_b_6417_){
_start:
{
lean_object* v___x_6418_; lean_object* v___x_6419_; 
v___x_6418_ = l___private_Lean_Expr_0__Lean_intAddFn;
v___x_6419_ = l_Lean_mkAppB(v___x_6418_, v_a_6416_, v_b_6417_);
return v___x_6419_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* v_a_6420_, lean_object* v_b_6421_){
_start:
{
lean_object* v___x_6422_; lean_object* v___x_6423_; 
v___x_6422_ = l___private_Lean_Expr_0__Lean_intSubFn;
v___x_6423_ = l_Lean_mkAppB(v___x_6422_, v_a_6420_, v_b_6421_);
return v___x_6423_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* v_a_6424_, lean_object* v_b_6425_){
_start:
{
lean_object* v___x_6426_; lean_object* v___x_6427_; 
v___x_6426_ = l___private_Lean_Expr_0__Lean_intMulFn;
v___x_6427_ = l_Lean_mkAppB(v___x_6426_, v_a_6424_, v_b_6425_);
return v___x_6427_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* v_a_6428_, lean_object* v_b_6429_){
_start:
{
lean_object* v___x_6430_; lean_object* v___x_6431_; 
v___x_6430_ = l___private_Lean_Expr_0__Lean_intDivFn;
v___x_6431_ = l_Lean_mkAppB(v___x_6430_, v_a_6428_, v_b_6429_);
return v___x_6431_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* v_a_6432_, lean_object* v_b_6433_){
_start:
{
lean_object* v___x_6434_; lean_object* v___x_6435_; 
v___x_6434_ = l___private_Lean_Expr_0__Lean_intModFn;
v___x_6435_ = l_Lean_mkAppB(v___x_6434_, v_a_6432_, v_b_6433_);
return v___x_6435_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* v_a_6436_){
_start:
{
lean_object* v___x_6437_; lean_object* v___x_6438_; 
v___x_6437_ = l___private_Lean_Expr_0__Lean_intNatCastFn;
v___x_6438_ = l_Lean_Expr_app___override(v___x_6437_, v_a_6436_);
return v___x_6438_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object* v_a_6439_, lean_object* v_b_6440_){
_start:
{
lean_object* v___x_6441_; lean_object* v___x_6442_; 
v___x_6441_ = l___private_Lean_Expr_0__Lean_intPowNatFn;
v___x_6442_ = l_Lean_mkAppB(v___x_6441_, v_a_6439_, v_b_6440_);
return v___x_6442_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0(void){
_start:
{
lean_object* v___x_6443_; lean_object* v___x_6444_; lean_object* v___x_6445_; lean_object* v___x_6446_; 
v___x_6443_ = l_Lean_Int_mkInstLE;
v___x_6444_ = l_Lean_Int_mkType;
v___x_6445_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6446_ = l_Lean_mkAppB(v___x_6445_, v___x_6444_, v___x_6443_);
return v___x_6446_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred(void){
_start:
{
lean_object* v___x_6447_; 
v___x_6447_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLEPred___closed__0, &l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0);
return v___x_6447_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* v_a_6448_, lean_object* v_b_6449_){
_start:
{
lean_object* v___x_6450_; lean_object* v___x_6451_; 
v___x_6450_ = l___private_Lean_Expr_0__Lean_intLEPred;
v___x_6451_ = l_Lean_mkAppB(v___x_6450_, v_a_6448_, v_b_6449_);
return v___x_6451_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3(void){
_start:
{
lean_object* v___x_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; 
v___x_6457_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6458_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intLTPred___closed__2));
v___x_6459_ = l_Lean_Expr_const___override(v___x_6458_, v___x_6457_);
return v___x_6459_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4(void){
_start:
{
lean_object* v___x_6460_; lean_object* v___x_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; 
v___x_6460_ = l_Lean_Int_mkInstLT;
v___x_6461_ = l_Lean_Int_mkType;
v___x_6462_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__3, &l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3);
v___x_6463_ = l_Lean_mkAppB(v___x_6462_, v___x_6461_, v___x_6460_);
return v___x_6463_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred(void){
_start:
{
lean_object* v___x_6464_; 
v___x_6464_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__4, &l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4);
return v___x_6464_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object* v_a_6465_, lean_object* v_b_6466_){
_start:
{
lean_object* v___x_6467_; lean_object* v___x_6468_; 
v___x_6467_ = l___private_Lean_Expr_0__Lean_intLTPred;
v___x_6468_ = l_Lean_mkAppB(v___x_6467_, v_a_6465_, v_b_6466_);
return v___x_6468_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0(void){
_start:
{
lean_object* v___x_6469_; lean_object* v___x_6470_; lean_object* v___x_6471_; 
v___x_6469_ = l_Lean_Int_mkType;
v___x_6470_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6471_ = l_Lean_Expr_app___override(v___x_6470_, v___x_6469_);
return v___x_6471_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred(void){
_start:
{
lean_object* v___x_6472_; 
v___x_6472_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intEqPred___closed__0, &l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0);
return v___x_6472_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* v_a_6473_, lean_object* v_b_6474_){
_start:
{
lean_object* v___x_6475_; lean_object* v___x_6476_; 
v___x_6475_ = l___private_Lean_Expr_0__Lean_intEqPred;
v___x_6476_ = l_Lean_mkAppB(v___x_6475_, v_a_6473_, v_b_6474_);
return v___x_6476_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__3(void){
_start:
{
lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; 
v___x_6482_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6483_ = ((lean_object*)(l_Lean_mkIntDvd___closed__2));
v___x_6484_ = l_Lean_Expr_const___override(v___x_6483_, v___x_6482_);
return v___x_6484_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__6(void){
_start:
{
lean_object* v___x_6489_; lean_object* v___x_6490_; lean_object* v___x_6491_; 
v___x_6489_ = lean_box(0);
v___x_6490_ = ((lean_object*)(l_Lean_mkIntDvd___closed__5));
v___x_6491_ = l_Lean_Expr_const___override(v___x_6490_, v___x_6489_);
return v___x_6491_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* v_a_6492_, lean_object* v_b_6493_){
_start:
{
lean_object* v___x_6494_; lean_object* v___x_6495_; lean_object* v___x_6496_; lean_object* v___x_6497_; 
v___x_6494_ = lean_obj_once(&l_Lean_mkIntDvd___closed__3, &l_Lean_mkIntDvd___closed__3_once, _init_l_Lean_mkIntDvd___closed__3);
v___x_6495_ = l_Lean_Int_mkType;
v___x_6496_ = lean_obj_once(&l_Lean_mkIntDvd___closed__6, &l_Lean_mkIntDvd___closed__6_once, _init_l_Lean_mkIntDvd___closed__6);
v___x_6497_ = l_Lean_mkApp4(v___x_6494_, v___x_6495_, v___x_6496_, v_a_6492_, v_b_6493_);
return v___x_6497_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__2(void){
_start:
{
lean_object* v___x_6501_; lean_object* v___x_6502_; lean_object* v___x_6503_; 
v___x_6501_ = lean_box(0);
v___x_6502_ = ((lean_object*)(l_Lean_mkIntLit___closed__1));
v___x_6503_ = l_Lean_Expr_const___override(v___x_6502_, v___x_6501_);
return v___x_6503_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__3(void){
_start:
{
lean_object* v___x_6504_; lean_object* v___x_6505_; 
v___x_6504_ = lean_unsigned_to_nat(0u);
v___x_6505_ = lean_nat_to_int(v___x_6504_);
return v___x_6505_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* v_n_6506_){
_start:
{
lean_object* v___x_6507_; lean_object* v_r_6508_; lean_object* v___x_6509_; lean_object* v___x_6510_; lean_object* v___x_6511_; lean_object* v___x_6512_; lean_object* v_r_6513_; lean_object* v___x_6514_; uint8_t v___x_6515_; 
v___x_6507_ = lean_nat_abs(v_n_6506_);
v_r_6508_ = l_Lean_mkRawNatLit(v___x_6507_);
v___x_6509_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_6510_ = l_Lean_Int_mkType;
v___x_6511_ = lean_obj_once(&l_Lean_mkIntLit___closed__2, &l_Lean_mkIntLit___closed__2_once, _init_l_Lean_mkIntLit___closed__2);
lean_inc_ref(v_r_6508_);
v___x_6512_ = l_Lean_Expr_app___override(v___x_6511_, v_r_6508_);
v_r_6513_ = l_Lean_mkApp3(v___x_6509_, v___x_6510_, v_r_6508_, v___x_6512_);
v___x_6514_ = lean_obj_once(&l_Lean_mkIntLit___closed__3, &l_Lean_mkIntLit___closed__3_once, _init_l_Lean_mkIntLit___closed__3);
v___x_6515_ = lean_int_dec_lt(v_n_6506_, v___x_6514_);
if (v___x_6515_ == 0)
{
return v_r_6513_;
}
else
{
lean_object* v___x_6516_; 
v___x_6516_ = l_Lean_mkIntNeg(v_r_6513_);
return v___x_6516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* v_n_6517_){
_start:
{
lean_object* v_res_6518_; 
v_res_6518_ = l_Lean_mkIntLit(v_n_6517_);
lean_dec(v_n_6517_);
return v_res_6518_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6523_; lean_object* v___x_6524_; 
v___x_6523_ = lean_box(0);
v___x_6524_ = l_Lean_Level_succ___override(v___x_6523_);
return v___x_6524_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6525_; lean_object* v___x_6526_; lean_object* v___x_6527_; 
v___x_6525_ = lean_box(0);
v___x_6526_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__2, &l_Lean_reflBoolTrue___closed__2_once, _init_l_Lean_reflBoolTrue___closed__2);
v___x_6527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6527_, 0, v___x_6526_);
lean_ctor_set(v___x_6527_, 1, v___x_6525_);
return v___x_6527_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; 
v___x_6528_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__3, &l_Lean_reflBoolTrue___closed__3_once, _init_l_Lean_reflBoolTrue___closed__3);
v___x_6529_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__1));
v___x_6530_ = l_Lean_Expr_const___override(v___x_6529_, v___x_6528_);
return v___x_6530_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__6(void){
_start:
{
lean_object* v___x_6533_; lean_object* v___x_6534_; lean_object* v___x_6535_; 
v___x_6533_ = lean_box(0);
v___x_6534_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__5));
v___x_6535_ = l_Lean_Expr_const___override(v___x_6534_, v___x_6533_);
return v___x_6535_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__7(void){
_start:
{
lean_object* v___x_6536_; lean_object* v___x_6537_; lean_object* v___x_6538_; 
v___x_6536_ = lean_box(0);
v___x_6537_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_6538_ = l_Lean_Expr_const___override(v___x_6537_, v___x_6536_);
return v___x_6538_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__8(void){
_start:
{
lean_object* v___x_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; lean_object* v___x_6542_; 
v___x_6539_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6540_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6541_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6542_ = l_Lean_mkAppB(v___x_6541_, v___x_6540_, v___x_6539_);
return v___x_6542_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue(void){
_start:
{
lean_object* v___x_6543_; 
v___x_6543_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__8, &l_Lean_reflBoolTrue___closed__8_once, _init_l_Lean_reflBoolTrue___closed__8);
return v___x_6543_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; 
v___x_6544_ = lean_box(0);
v___x_6545_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_6546_ = l_Lean_Expr_const___override(v___x_6545_, v___x_6544_);
return v___x_6546_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; 
v___x_6547_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6548_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6549_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6550_ = l_Lean_mkAppB(v___x_6549_, v___x_6548_, v___x_6547_);
return v___x_6550_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse(void){
_start:
{
lean_object* v___x_6551_; 
v___x_6551_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
return v___x_6551_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6555_; lean_object* v___x_6556_; lean_object* v___x_6557_; 
v___x_6555_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6556_ = ((lean_object*)(l_Lean_eagerReflBoolTrue___closed__1));
v___x_6557_ = l_Lean_Expr_const___override(v___x_6556_, v___x_6555_);
return v___x_6557_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; 
v___x_6558_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6559_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6560_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6561_ = l_Lean_mkApp3(v___x_6560_, v___x_6559_, v___x_6558_, v___x_6558_);
return v___x_6561_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v___x_6565_; 
v___x_6562_ = l_Lean_reflBoolTrue;
v___x_6563_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__3, &l_Lean_eagerReflBoolTrue___closed__3_once, _init_l_Lean_eagerReflBoolTrue___closed__3);
v___x_6564_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6565_ = l_Lean_mkAppB(v___x_6564_, v___x_6563_, v___x_6562_);
return v___x_6565_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue(void){
_start:
{
lean_object* v___x_6566_; 
v___x_6566_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__4, &l_Lean_eagerReflBoolTrue___closed__4_once, _init_l_Lean_eagerReflBoolTrue___closed__4);
return v___x_6566_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6567_; lean_object* v___x_6568_; lean_object* v___x_6569_; lean_object* v___x_6570_; 
v___x_6567_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6568_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6569_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6570_ = l_Lean_mkApp3(v___x_6569_, v___x_6568_, v___x_6567_, v___x_6567_);
return v___x_6570_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6571_; lean_object* v___x_6572_; lean_object* v___x_6573_; lean_object* v___x_6574_; 
v___x_6571_ = l_Lean_reflBoolFalse;
v___x_6572_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__0, &l_Lean_eagerReflBoolFalse___closed__0_once, _init_l_Lean_eagerReflBoolFalse___closed__0);
v___x_6573_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6574_ = l_Lean_mkAppB(v___x_6573_, v___x_6572_, v___x_6571_);
return v___x_6574_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse(void){
_start:
{
lean_object* v___x_6575_; 
v___x_6575_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__1, &l_Lean_eagerReflBoolFalse___closed__1_once, _init_l_Lean_eagerReflBoolFalse___closed__1);
return v___x_6575_;
}
}
static lean_object* _init_l_Lean_Expr_replaceFn___closed__2(void){
_start:
{
lean_object* v___x_6578_; lean_object* v___x_6579_; lean_object* v___x_6580_; lean_object* v___x_6581_; lean_object* v___x_6582_; lean_object* v___x_6583_; 
v___x_6578_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__1));
v___x_6579_ = lean_unsigned_to_nat(9u);
v___x_6580_ = lean_unsigned_to_nat(2458u);
v___x_6581_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__0));
v___x_6582_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_6583_ = l_mkPanicMessageWithDecl(v___x_6582_, v___x_6581_, v___x_6580_, v___x_6579_, v___x_6578_);
return v___x_6583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object* v_e_6584_, lean_object* v_declName_6585_){
_start:
{
switch(lean_obj_tag(v_e_6584_))
{
case 5:
{
lean_object* v_fn_6586_; lean_object* v_arg_6587_; lean_object* v___x_6588_; lean_object* v___x_6589_; 
v_fn_6586_ = lean_ctor_get(v_e_6584_, 0);
lean_inc_ref(v_fn_6586_);
v_arg_6587_ = lean_ctor_get(v_e_6584_, 1);
lean_inc_ref(v_arg_6587_);
lean_dec_ref_known(v_e_6584_, 2);
v___x_6588_ = l_Lean_Expr_replaceFn(v_fn_6586_, v_declName_6585_);
v___x_6589_ = l_Lean_Expr_app___override(v___x_6588_, v_arg_6587_);
return v___x_6589_;
}
case 4:
{
lean_object* v_us_6590_; lean_object* v___x_6591_; 
v_us_6590_ = lean_ctor_get(v_e_6584_, 1);
lean_inc(v_us_6590_);
lean_dec_ref_known(v_e_6584_, 2);
v___x_6591_ = l_Lean_Expr_const___override(v_declName_6585_, v_us_6590_);
return v___x_6591_;
}
default: 
{
lean_object* v___x_6592_; lean_object* v___x_6593_; 
lean_dec(v_declName_6585_);
lean_dec_ref(v_e_6584_);
v___x_6592_ = lean_obj_once(&l_Lean_Expr_replaceFn___closed__2, &l_Lean_Expr_replaceFn___closed__2_once, _init_l_Lean_Expr_replaceFn___closed__2);
v___x_6593_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_6592_);
return v___x_6593_;
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
