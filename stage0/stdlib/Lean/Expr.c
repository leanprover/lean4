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
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_box(1);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg();
return v_res_1042_;
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
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg(){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_box(1);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg___boxed(lean_object* v___dummy_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_instEmptyCollectionFVarIdMap___redArg();
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* v_00_u03b1_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_box(1);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg(){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_box(1);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg___boxed(lean_object* v___dummy_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_instInhabitedFVarIdMap___redArg();
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* v_00_u03b1_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_box(1);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId_default(void){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_box(0);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId(void){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_box(0);
return v___x_1058_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMVarId_beq(lean_object* v_x_1059_, lean_object* v_x_1060_){
_start:
{
uint8_t v___x_1061_; 
v___x_1061_ = lean_name_eq(v_x_1059_, v_x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object* v_x_1062_, lean_object* v_x_1063_){
_start:
{
uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l_Lean_instBEqMVarId_beq(v_x_1062_, v_x_1063_);
lean_dec(v_x_1063_);
lean_dec(v_x_1062_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableMVarId_hash(lean_object* v_x_1068_){
_start:
{
uint64_t v___x_1069_; 
v___x_1069_ = 0ULL;
if (lean_obj_tag(v_x_1068_) == 0)
{
uint64_t v___x_1070_; 
v___x_1070_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
return v___x_1070_;
}
else
{
uint64_t v_hash_1071_; uint64_t v___x_1072_; 
v_hash_1071_ = lean_ctor_get_uint64(v_x_1068_, sizeof(void*)*2);
v___x_1072_ = lean_uint64_mix_hash(v___x_1069_, v_hash_1071_);
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object* v_x_1073_){
_start:
{
uint64_t v_res_1074_; lean_object* v_r_1075_; 
v_res_1074_ = l_Lean_instHashableMVarId_hash(v_x_1073_);
lean_dec(v_x_1073_);
v_r_1075_ = lean_box_uint64(v_res_1074_);
return v_r_1075_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_box(1);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet(void){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_box(1);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_box(1);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet(void){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_box(1);
return v___x_1082_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object* v_k_1083_, lean_object* v_t_1084_){
_start:
{
if (lean_obj_tag(v_t_1084_) == 0)
{
lean_object* v_k_1085_; lean_object* v_l_1086_; lean_object* v_r_1087_; uint8_t v___x_1088_; 
v_k_1085_ = lean_ctor_get(v_t_1084_, 1);
v_l_1086_ = lean_ctor_get(v_t_1084_, 3);
v_r_1087_ = lean_ctor_get(v_t_1084_, 4);
v___x_1088_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1083_, v_k_1085_);
switch(v___x_1088_)
{
case 0:
{
v_t_1084_ = v_l_1086_;
goto _start;
}
case 1:
{
uint8_t v___x_1090_; 
v___x_1090_ = 1;
return v___x_1090_;
}
default: 
{
v_t_1084_ = v_r_1087_;
goto _start;
}
}
}
else
{
uint8_t v___x_1092_; 
v___x_1092_ = 0;
return v___x_1092_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object* v_k_1093_, lean_object* v_t_1094_){
_start:
{
uint8_t v_res_1095_; lean_object* v_r_1096_; 
v_res_1095_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1093_, v_t_1094_);
lean_dec(v_t_1094_);
lean_dec(v_k_1093_);
v_r_1096_ = lean_box(v_res_1095_);
return v_r_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object* v_k_1097_, lean_object* v_v_1098_, lean_object* v_t_1099_){
_start:
{
if (lean_obj_tag(v_t_1099_) == 0)
{
lean_object* v_size_1100_; lean_object* v_k_1101_; lean_object* v_v_1102_; lean_object* v_l_1103_; lean_object* v_r_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1384_; 
v_size_1100_ = lean_ctor_get(v_t_1099_, 0);
v_k_1101_ = lean_ctor_get(v_t_1099_, 1);
v_v_1102_ = lean_ctor_get(v_t_1099_, 2);
v_l_1103_ = lean_ctor_get(v_t_1099_, 3);
v_r_1104_ = lean_ctor_get(v_t_1099_, 4);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_t_1099_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1106_ = v_t_1099_;
v_isShared_1107_ = v_isSharedCheck_1384_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_r_1104_);
lean_inc(v_l_1103_);
lean_inc(v_v_1102_);
lean_inc(v_k_1101_);
lean_inc(v_size_1100_);
lean_dec(v_t_1099_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1384_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
uint8_t v___x_1108_; 
v___x_1108_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1097_, v_k_1101_);
switch(v___x_1108_)
{
case 0:
{
lean_object* v_impl_1109_; lean_object* v___x_1110_; 
lean_dec(v_size_1100_);
v_impl_1109_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1097_, v_v_1098_, v_l_1103_);
v___x_1110_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1104_) == 0)
{
lean_object* v_size_1111_; lean_object* v_size_1112_; lean_object* v_k_1113_; lean_object* v_v_1114_; lean_object* v_l_1115_; lean_object* v_r_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_size_1111_ = lean_ctor_get(v_r_1104_, 0);
v_size_1112_ = lean_ctor_get(v_impl_1109_, 0);
lean_inc(v_size_1112_);
v_k_1113_ = lean_ctor_get(v_impl_1109_, 1);
lean_inc(v_k_1113_);
v_v_1114_ = lean_ctor_get(v_impl_1109_, 2);
lean_inc(v_v_1114_);
v_l_1115_ = lean_ctor_get(v_impl_1109_, 3);
lean_inc(v_l_1115_);
v_r_1116_ = lean_ctor_get(v_impl_1109_, 4);
lean_inc(v_r_1116_);
v___x_1117_ = lean_unsigned_to_nat(3u);
v___x_1118_ = lean_nat_mul(v___x_1117_, v_size_1111_);
v___x_1119_ = lean_nat_dec_lt(v___x_1118_, v_size_1112_);
lean_dec(v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
lean_dec(v_r_1116_);
lean_dec(v_l_1115_);
lean_dec(v_v_1114_);
lean_dec(v_k_1113_);
v___x_1120_ = lean_nat_add(v___x_1110_, v_size_1112_);
lean_dec(v_size_1112_);
v___x_1121_ = lean_nat_add(v___x_1120_, v_size_1111_);
lean_dec(v___x_1120_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 3, v_impl_1109_);
lean_ctor_set(v___x_1106_, 0, v___x_1121_);
v___x_1123_ = v___x_1106_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_impl_1109_);
lean_ctor_set(v_reuseFailAlloc_1124_, 4, v_r_1104_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
else
{
lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1190_; 
v_isSharedCheck_1190_ = !lean_is_exclusive(v_impl_1109_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; lean_object* v_unused_1192_; lean_object* v_unused_1193_; lean_object* v_unused_1194_; lean_object* v_unused_1195_; 
v_unused_1191_ = lean_ctor_get(v_impl_1109_, 4);
lean_dec(v_unused_1191_);
v_unused_1192_ = lean_ctor_get(v_impl_1109_, 3);
lean_dec(v_unused_1192_);
v_unused_1193_ = lean_ctor_get(v_impl_1109_, 2);
lean_dec(v_unused_1193_);
v_unused_1194_ = lean_ctor_get(v_impl_1109_, 1);
lean_dec(v_unused_1194_);
v_unused_1195_ = lean_ctor_get(v_impl_1109_, 0);
lean_dec(v_unused_1195_);
v___x_1126_ = v_impl_1109_;
v_isShared_1127_ = v_isSharedCheck_1190_;
goto v_resetjp_1125_;
}
else
{
lean_dec(v_impl_1109_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1190_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_size_1128_; lean_object* v_size_1129_; lean_object* v_k_1130_; lean_object* v_v_1131_; lean_object* v_l_1132_; lean_object* v_r_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v_size_1128_ = lean_ctor_get(v_l_1115_, 0);
v_size_1129_ = lean_ctor_get(v_r_1116_, 0);
v_k_1130_ = lean_ctor_get(v_r_1116_, 1);
v_v_1131_ = lean_ctor_get(v_r_1116_, 2);
v_l_1132_ = lean_ctor_get(v_r_1116_, 3);
v_r_1133_ = lean_ctor_get(v_r_1116_, 4);
v___x_1134_ = lean_unsigned_to_nat(2u);
v___x_1135_ = lean_nat_mul(v___x_1134_, v_size_1128_);
v___x_1136_ = lean_nat_dec_lt(v_size_1129_, v___x_1135_);
lean_dec(v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1165_; 
lean_inc(v_r_1133_);
lean_inc(v_l_1132_);
lean_inc(v_v_1131_);
lean_inc(v_k_1130_);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_r_1116_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; lean_object* v_unused_1167_; lean_object* v_unused_1168_; lean_object* v_unused_1169_; lean_object* v_unused_1170_; 
v_unused_1166_ = lean_ctor_get(v_r_1116_, 4);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v_r_1116_, 3);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_r_1116_, 2);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_r_1116_, 1);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_r_1116_, 0);
lean_dec(v_unused_1170_);
v___x_1138_ = v_r_1116_;
v_isShared_1139_ = v_isSharedCheck_1165_;
goto v_resetjp_1137_;
}
else
{
lean_dec(v_r_1116_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1165_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___x_1153_; lean_object* v___y_1155_; 
v___x_1140_ = lean_nat_add(v___x_1110_, v_size_1112_);
lean_dec(v_size_1112_);
v___x_1141_ = lean_nat_add(v___x_1140_, v_size_1111_);
lean_dec(v___x_1140_);
v___x_1153_ = lean_nat_add(v___x_1110_, v_size_1128_);
if (lean_obj_tag(v_l_1132_) == 0)
{
lean_object* v_size_1163_; 
v_size_1163_ = lean_ctor_get(v_l_1132_, 0);
lean_inc(v_size_1163_);
v___y_1155_ = v_size_1163_;
goto v___jp_1154_;
}
else
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_unsigned_to_nat(0u);
v___y_1155_ = v___x_1164_;
goto v___jp_1154_;
}
v___jp_1142_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = lean_nat_add(v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec(v___y_1144_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 4, v_r_1104_);
lean_ctor_set(v___x_1138_, 3, v_r_1133_);
lean_ctor_set(v___x_1138_, 2, v_v_1102_);
lean_ctor_set(v___x_1138_, 1, v_k_1101_);
lean_ctor_set(v___x_1138_, 0, v___x_1146_);
v___x_1148_ = v___x_1138_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1152_, 3, v_r_1133_);
lean_ctor_set(v_reuseFailAlloc_1152_, 4, v_r_1104_);
v___x_1148_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1150_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v___x_1148_);
lean_ctor_set(v___x_1126_, 3, v___y_1143_);
lean_ctor_set(v___x_1126_, 2, v_v_1131_);
lean_ctor_set(v___x_1126_, 1, v_k_1130_);
lean_ctor_set(v___x_1126_, 0, v___x_1141_);
v___x_1150_ = v___x_1126_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_k_1130_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_v_1131_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v___y_1143_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
v___jp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_nat_add(v___x_1153_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec(v___x_1153_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 4, v_l_1132_);
lean_ctor_set(v___x_1106_, 3, v_l_1115_);
lean_ctor_set(v___x_1106_, 2, v_v_1114_);
lean_ctor_set(v___x_1106_, 1, v_k_1113_);
lean_ctor_set(v___x_1106_, 0, v___x_1156_);
v___x_1158_ = v___x_1106_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_k_1113_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_v_1114_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v_l_1115_);
lean_ctor_set(v_reuseFailAlloc_1162_, 4, v_l_1132_);
v___x_1158_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_nat_add(v___x_1110_, v_size_1111_);
if (lean_obj_tag(v_r_1133_) == 0)
{
lean_object* v_size_1160_; 
v_size_1160_ = lean_ctor_get(v_r_1133_, 0);
lean_inc(v_size_1160_);
v___y_1143_ = v___x_1158_;
v___y_1144_ = v___x_1159_;
v___y_1145_ = v_size_1160_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_unsigned_to_nat(0u);
v___y_1143_ = v___x_1158_;
v___y_1144_ = v___x_1159_;
v___y_1145_ = v___x_1161_;
goto v___jp_1142_;
}
}
}
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
lean_del_object(v___x_1106_);
v___x_1171_ = lean_nat_add(v___x_1110_, v_size_1112_);
lean_dec(v_size_1112_);
v___x_1172_ = lean_nat_add(v___x_1171_, v_size_1111_);
lean_dec(v___x_1171_);
v___x_1173_ = lean_nat_add(v___x_1110_, v_size_1111_);
v___x_1174_ = lean_nat_add(v___x_1173_, v_size_1129_);
lean_dec(v___x_1173_);
lean_inc_ref(v_r_1104_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v_r_1104_);
lean_ctor_set(v___x_1126_, 3, v_r_1116_);
lean_ctor_set(v___x_1126_, 2, v_v_1102_);
lean_ctor_set(v___x_1126_, 1, v_k_1101_);
lean_ctor_set(v___x_1126_, 0, v___x_1174_);
v___x_1176_ = v___x_1126_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v_r_1116_);
lean_ctor_set(v_reuseFailAlloc_1189_, 4, v_r_1104_);
v___x_1176_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
v_isSharedCheck_1183_ = !lean_is_exclusive(v_r_1104_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; lean_object* v_unused_1185_; lean_object* v_unused_1186_; lean_object* v_unused_1187_; lean_object* v_unused_1188_; 
v_unused_1184_ = lean_ctor_get(v_r_1104_, 4);
lean_dec(v_unused_1184_);
v_unused_1185_ = lean_ctor_get(v_r_1104_, 3);
lean_dec(v_unused_1185_);
v_unused_1186_ = lean_ctor_get(v_r_1104_, 2);
lean_dec(v_unused_1186_);
v_unused_1187_ = lean_ctor_get(v_r_1104_, 1);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_r_1104_, 0);
lean_dec(v_unused_1188_);
v___x_1178_ = v_r_1104_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_dec(v_r_1104_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 4, v___x_1176_);
lean_ctor_set(v___x_1178_, 3, v_l_1115_);
lean_ctor_set(v___x_1178_, 2, v_v_1114_);
lean_ctor_set(v___x_1178_, 1, v_k_1113_);
lean_ctor_set(v___x_1178_, 0, v___x_1172_);
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_k_1113_);
lean_ctor_set(v_reuseFailAlloc_1182_, 2, v_v_1114_);
lean_ctor_set(v_reuseFailAlloc_1182_, 3, v_l_1115_);
lean_ctor_set(v_reuseFailAlloc_1182_, 4, v___x_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1196_; 
v_l_1196_ = lean_ctor_get(v_impl_1109_, 3);
lean_inc(v_l_1196_);
if (lean_obj_tag(v_l_1196_) == 0)
{
lean_object* v_r_1197_; lean_object* v_k_1198_; lean_object* v_v_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1210_; 
v_r_1197_ = lean_ctor_get(v_impl_1109_, 4);
v_k_1198_ = lean_ctor_get(v_impl_1109_, 1);
v_v_1199_ = lean_ctor_get(v_impl_1109_, 2);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_impl_1109_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; lean_object* v_unused_1212_; 
v_unused_1211_ = lean_ctor_get(v_impl_1109_, 3);
lean_dec(v_unused_1211_);
v_unused_1212_ = lean_ctor_get(v_impl_1109_, 0);
lean_dec(v_unused_1212_);
v___x_1201_ = v_impl_1109_;
v_isShared_1202_ = v_isSharedCheck_1210_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_r_1197_);
lean_inc(v_v_1199_);
lean_inc(v_k_1198_);
lean_dec(v_impl_1109_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1210_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1197_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 3, v_r_1197_);
lean_ctor_set(v___x_1201_, 2, v_v_1102_);
lean_ctor_set(v___x_1201_, 1, v_k_1101_);
lean_ctor_set(v___x_1201_, 0, v___x_1110_);
v___x_1205_ = v___x_1201_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v_r_1197_);
lean_ctor_set(v_reuseFailAlloc_1209_, 4, v_r_1197_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1207_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 4, v___x_1205_);
lean_ctor_set(v___x_1106_, 3, v_l_1196_);
lean_ctor_set(v___x_1106_, 2, v_v_1199_);
lean_ctor_set(v___x_1106_, 1, v_k_1198_);
lean_ctor_set(v___x_1106_, 0, v___x_1203_);
v___x_1207_ = v___x_1106_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_k_1198_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_v_1199_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_l_1196_);
lean_ctor_set(v_reuseFailAlloc_1208_, 4, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_r_1213_; 
v_r_1213_ = lean_ctor_get(v_impl_1109_, 4);
lean_inc(v_r_1213_);
if (lean_obj_tag(v_r_1213_) == 0)
{
lean_object* v_k_1214_; lean_object* v_v_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1238_; 
v_k_1214_ = lean_ctor_get(v_impl_1109_, 1);
v_v_1215_ = lean_ctor_get(v_impl_1109_, 2);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_impl_1109_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; lean_object* v_unused_1240_; lean_object* v_unused_1241_; 
v_unused_1239_ = lean_ctor_get(v_impl_1109_, 4);
lean_dec(v_unused_1239_);
v_unused_1240_ = lean_ctor_get(v_impl_1109_, 3);
lean_dec(v_unused_1240_);
v_unused_1241_ = lean_ctor_get(v_impl_1109_, 0);
lean_dec(v_unused_1241_);
v___x_1217_ = v_impl_1109_;
v_isShared_1218_ = v_isSharedCheck_1238_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_v_1215_);
lean_inc(v_k_1214_);
lean_dec(v_impl_1109_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1238_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v_k_1219_; lean_object* v_v_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1234_; 
v_k_1219_ = lean_ctor_get(v_r_1213_, 1);
v_v_1220_ = lean_ctor_get(v_r_1213_, 2);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_r_1213_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; lean_object* v_unused_1236_; lean_object* v_unused_1237_; 
v_unused_1235_ = lean_ctor_get(v_r_1213_, 4);
lean_dec(v_unused_1235_);
v_unused_1236_ = lean_ctor_get(v_r_1213_, 3);
lean_dec(v_unused_1236_);
v_unused_1237_ = lean_ctor_get(v_r_1213_, 0);
lean_dec(v_unused_1237_);
v___x_1222_ = v_r_1213_;
v_isShared_1223_ = v_isSharedCheck_1234_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_v_1220_);
lean_inc(v_k_1219_);
lean_dec(v_r_1213_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1234_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1224_ = lean_unsigned_to_nat(3u);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 4, v_l_1196_);
lean_ctor_set(v___x_1222_, 3, v_l_1196_);
lean_ctor_set(v___x_1222_, 2, v_v_1215_);
lean_ctor_set(v___x_1222_, 1, v_k_1214_);
lean_ctor_set(v___x_1222_, 0, v___x_1110_);
v___x_1226_ = v___x_1222_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_k_1214_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_v_1215_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v_l_1196_);
lean_ctor_set(v_reuseFailAlloc_1233_, 4, v_l_1196_);
v___x_1226_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1228_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 4, v_l_1196_);
lean_ctor_set(v___x_1217_, 2, v_v_1102_);
lean_ctor_set(v___x_1217_, 1, v_k_1101_);
lean_ctor_set(v___x_1217_, 0, v___x_1110_);
v___x_1228_ = v___x_1217_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1232_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1232_, 3, v_l_1196_);
lean_ctor_set(v_reuseFailAlloc_1232_, 4, v_l_1196_);
v___x_1228_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1230_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 4, v___x_1228_);
lean_ctor_set(v___x_1106_, 3, v___x_1226_);
lean_ctor_set(v___x_1106_, 2, v_v_1220_);
lean_ctor_set(v___x_1106_, 1, v_k_1219_);
lean_ctor_set(v___x_1106_, 0, v___x_1224_);
v___x_1230_ = v___x_1106_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_k_1219_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_v_1220_);
lean_ctor_set(v_reuseFailAlloc_1231_, 3, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1231_, 4, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1242_ = lean_unsigned_to_nat(2u);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 4, v_r_1213_);
lean_ctor_set(v___x_1106_, 3, v_impl_1109_);
lean_ctor_set(v___x_1106_, 0, v___x_1242_);
v___x_1244_ = v___x_1106_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_impl_1109_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v_r_1213_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1247_; 
lean_dec(v_v_1102_);
lean_dec(v_k_1101_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 2, v_v_1098_);
lean_ctor_set(v___x_1106_, 1, v_k_1097_);
v___x_1247_ = v___x_1106_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_size_1100_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1248_, 3, v_l_1103_);
lean_ctor_set(v_reuseFailAlloc_1248_, 4, v_r_1104_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
default: 
{
lean_object* v_impl_1249_; lean_object* v___x_1250_; 
lean_dec(v_size_1100_);
v_impl_1249_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1097_, v_v_1098_, v_r_1104_);
v___x_1250_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1103_) == 0)
{
lean_object* v_size_1251_; lean_object* v_size_1252_; lean_object* v_k_1253_; lean_object* v_v_1254_; lean_object* v_l_1255_; lean_object* v_r_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_size_1251_ = lean_ctor_get(v_l_1103_, 0);
v_size_1252_ = lean_ctor_get(v_impl_1249_, 0);
lean_inc(v_size_1252_);
v_k_1253_ = lean_ctor_get(v_impl_1249_, 1);
lean_inc(v_k_1253_);
v_v_1254_ = lean_ctor_get(v_impl_1249_, 2);
lean_inc(v_v_1254_);
v_l_1255_ = lean_ctor_get(v_impl_1249_, 3);
lean_inc(v_l_1255_);
v_r_1256_ = lean_ctor_get(v_impl_1249_, 4);
lean_inc(v_r_1256_);
v___x_1257_ = lean_unsigned_to_nat(3u);
v___x_1258_ = lean_nat_mul(v___x_1257_, v_size_1251_);
v___x_1259_ = lean_nat_dec_lt(v___x_1258_, v_size_1252_);
lean_dec(v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; 
lean_dec(v_r_1256_);
lean_dec(v_l_1255_);
lean_dec(v_v_1254_);
lean_dec(v_k_1253_);
v___x_1260_ = lean_nat_add(v___x_1250_, v_size_1251_);
v___x_1261_ = lean_nat_add(v___x_1260_, v_size_1252_);
lean_dec(v_size_1252_);
lean_dec(v___x_1260_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 4, v_impl_1249_);
lean_ctor_set(v___x_1106_, 0, v___x_1261_);
v___x_1263_ = v___x_1106_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v_l_1103_);
lean_ctor_set(v_reuseFailAlloc_1264_, 4, v_impl_1249_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
else
{
lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1328_; 
v_isSharedCheck_1328_ = !lean_is_exclusive(v_impl_1249_);
if (v_isSharedCheck_1328_ == 0)
{
lean_object* v_unused_1329_; lean_object* v_unused_1330_; lean_object* v_unused_1331_; lean_object* v_unused_1332_; lean_object* v_unused_1333_; 
v_unused_1329_ = lean_ctor_get(v_impl_1249_, 4);
lean_dec(v_unused_1329_);
v_unused_1330_ = lean_ctor_get(v_impl_1249_, 3);
lean_dec(v_unused_1330_);
v_unused_1331_ = lean_ctor_get(v_impl_1249_, 2);
lean_dec(v_unused_1331_);
v_unused_1332_ = lean_ctor_get(v_impl_1249_, 1);
lean_dec(v_unused_1332_);
v_unused_1333_ = lean_ctor_get(v_impl_1249_, 0);
lean_dec(v_unused_1333_);
v___x_1266_ = v_impl_1249_;
v_isShared_1267_ = v_isSharedCheck_1328_;
goto v_resetjp_1265_;
}
else
{
lean_dec(v_impl_1249_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1328_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_size_1268_; lean_object* v_k_1269_; lean_object* v_v_1270_; lean_object* v_l_1271_; lean_object* v_r_1272_; lean_object* v_size_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v_size_1268_ = lean_ctor_get(v_l_1255_, 0);
v_k_1269_ = lean_ctor_get(v_l_1255_, 1);
v_v_1270_ = lean_ctor_get(v_l_1255_, 2);
v_l_1271_ = lean_ctor_get(v_l_1255_, 3);
v_r_1272_ = lean_ctor_get(v_l_1255_, 4);
v_size_1273_ = lean_ctor_get(v_r_1256_, 0);
v___x_1274_ = lean_unsigned_to_nat(2u);
v___x_1275_ = lean_nat_mul(v___x_1274_, v_size_1273_);
v___x_1276_ = lean_nat_dec_lt(v_size_1268_, v___x_1275_);
lean_dec(v___x_1275_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1304_; 
lean_inc(v_r_1272_);
lean_inc(v_l_1271_);
lean_inc(v_v_1270_);
lean_inc(v_k_1269_);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_l_1255_);
if (v_isSharedCheck_1304_ == 0)
{
lean_object* v_unused_1305_; lean_object* v_unused_1306_; lean_object* v_unused_1307_; lean_object* v_unused_1308_; lean_object* v_unused_1309_; 
v_unused_1305_ = lean_ctor_get(v_l_1255_, 4);
lean_dec(v_unused_1305_);
v_unused_1306_ = lean_ctor_get(v_l_1255_, 3);
lean_dec(v_unused_1306_);
v_unused_1307_ = lean_ctor_get(v_l_1255_, 2);
lean_dec(v_unused_1307_);
v_unused_1308_ = lean_ctor_get(v_l_1255_, 1);
lean_dec(v_unused_1308_);
v_unused_1309_ = lean_ctor_get(v_l_1255_, 0);
lean_dec(v_unused_1309_);
v___x_1278_ = v_l_1255_;
v_isShared_1279_ = v_isSharedCheck_1304_;
goto v_resetjp_1277_;
}
else
{
lean_dec(v_l_1255_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1304_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1294_; 
v___x_1280_ = lean_nat_add(v___x_1250_, v_size_1251_);
v___x_1281_ = lean_nat_add(v___x_1280_, v_size_1252_);
lean_dec(v_size_1252_);
if (lean_obj_tag(v_l_1271_) == 0)
{
lean_object* v_size_1302_; 
v_size_1302_ = lean_ctor_get(v_l_1271_, 0);
lean_inc(v_size_1302_);
v___y_1294_ = v_size_1302_;
goto v___jp_1293_;
}
else
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_unsigned_to_nat(0u);
v___y_1294_ = v___x_1303_;
goto v___jp_1293_;
}
v___jp_1282_:
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1286_ = lean_nat_add(v___y_1283_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec(v___y_1283_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 4, v_r_1256_);
lean_ctor_set(v___x_1278_, 3, v_r_1272_);
lean_ctor_set(v___x_1278_, 2, v_v_1254_);
lean_ctor_set(v___x_1278_, 1, v_k_1253_);
lean_ctor_set(v___x_1278_, 0, v___x_1286_);
v___x_1288_ = v___x_1278_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_k_1253_);
lean_ctor_set(v_reuseFailAlloc_1292_, 2, v_v_1254_);
lean_ctor_set(v_reuseFailAlloc_1292_, 3, v_r_1272_);
lean_ctor_set(v_reuseFailAlloc_1292_, 4, v_r_1256_);
v___x_1288_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1290_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 4, v___x_1288_);
lean_ctor_set(v___x_1266_, 3, v___y_1284_);
lean_ctor_set(v___x_1266_, 2, v_v_1270_);
lean_ctor_set(v___x_1266_, 1, v_k_1269_);
lean_ctor_set(v___x_1266_, 0, v___x_1281_);
v___x_1290_ = v___x_1266_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_k_1269_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_v_1270_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v___y_1284_);
lean_ctor_set(v_reuseFailAlloc_1291_, 4, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
v___jp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1295_ = lean_nat_add(v___x_1280_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec(v___x_1280_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 4, v_l_1271_);
lean_ctor_set(v___x_1106_, 0, v___x_1295_);
v___x_1297_ = v___x_1106_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1301_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1301_, 3, v_l_1103_);
lean_ctor_set(v_reuseFailAlloc_1301_, 4, v_l_1271_);
v___x_1297_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_nat_add(v___x_1250_, v_size_1273_);
if (lean_obj_tag(v_r_1272_) == 0)
{
lean_object* v_size_1299_; 
v_size_1299_ = lean_ctor_get(v_r_1272_, 0);
lean_inc(v_size_1299_);
v___y_1283_ = v___x_1298_;
v___y_1284_ = v___x_1297_;
v___y_1285_ = v_size_1299_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_unsigned_to_nat(0u);
v___y_1283_ = v___x_1298_;
v___y_1284_ = v___x_1297_;
v___y_1285_ = v___x_1300_;
goto v___jp_1282_;
}
}
}
}
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
lean_del_object(v___x_1106_);
v___x_1310_ = lean_nat_add(v___x_1250_, v_size_1251_);
v___x_1311_ = lean_nat_add(v___x_1310_, v_size_1252_);
lean_dec(v_size_1252_);
v___x_1312_ = lean_nat_add(v___x_1310_, v_size_1268_);
lean_dec(v___x_1310_);
lean_inc_ref(v_l_1103_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 4, v_l_1255_);
lean_ctor_set(v___x_1266_, 3, v_l_1103_);
lean_ctor_set(v___x_1266_, 2, v_v_1102_);
lean_ctor_set(v___x_1266_, 1, v_k_1101_);
lean_ctor_set(v___x_1266_, 0, v___x_1312_);
v___x_1314_ = v___x_1266_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1327_, 3, v_l_1103_);
lean_ctor_set(v_reuseFailAlloc_1327_, 4, v_l_1255_);
v___x_1314_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
v_isSharedCheck_1321_ = !lean_is_exclusive(v_l_1103_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; lean_object* v_unused_1323_; lean_object* v_unused_1324_; lean_object* v_unused_1325_; lean_object* v_unused_1326_; 
v_unused_1322_ = lean_ctor_get(v_l_1103_, 4);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v_l_1103_, 3);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v_l_1103_, 2);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v_l_1103_, 1);
lean_dec(v_unused_1325_);
v_unused_1326_ = lean_ctor_get(v_l_1103_, 0);
lean_dec(v_unused_1326_);
v___x_1316_ = v_l_1103_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_dec(v_l_1103_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 4, v_r_1256_);
lean_ctor_set(v___x_1316_, 3, v___x_1314_);
lean_ctor_set(v___x_1316_, 2, v_v_1254_);
lean_ctor_set(v___x_1316_, 1, v_k_1253_);
lean_ctor_set(v___x_1316_, 0, v___x_1311_);
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_k_1253_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_v_1254_);
lean_ctor_set(v_reuseFailAlloc_1320_, 3, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1320_, 4, v_r_1256_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1334_; 
v_l_1334_ = lean_ctor_get(v_impl_1249_, 3);
lean_inc(v_l_1334_);
if (lean_obj_tag(v_l_1334_) == 0)
{
lean_object* v_r_1335_; lean_object* v_k_1336_; lean_object* v_v_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1360_; 
v_r_1335_ = lean_ctor_get(v_impl_1249_, 4);
v_k_1336_ = lean_ctor_get(v_impl_1249_, 1);
v_v_1337_ = lean_ctor_get(v_impl_1249_, 2);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_impl_1249_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; lean_object* v_unused_1362_; 
v_unused_1361_ = lean_ctor_get(v_impl_1249_, 3);
lean_dec(v_unused_1361_);
v_unused_1362_ = lean_ctor_get(v_impl_1249_, 0);
lean_dec(v_unused_1362_);
v___x_1339_ = v_impl_1249_;
v_isShared_1340_ = v_isSharedCheck_1360_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_r_1335_);
lean_inc(v_v_1337_);
lean_inc(v_k_1336_);
lean_dec(v_impl_1249_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1360_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_k_1341_; lean_object* v_v_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1356_; 
v_k_1341_ = lean_ctor_get(v_l_1334_, 1);
v_v_1342_ = lean_ctor_get(v_l_1334_, 2);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_l_1334_);
if (v_isSharedCheck_1356_ == 0)
{
lean_object* v_unused_1357_; lean_object* v_unused_1358_; lean_object* v_unused_1359_; 
v_unused_1357_ = lean_ctor_get(v_l_1334_, 4);
lean_dec(v_unused_1357_);
v_unused_1358_ = lean_ctor_get(v_l_1334_, 3);
lean_dec(v_unused_1358_);
v_unused_1359_ = lean_ctor_get(v_l_1334_, 0);
lean_dec(v_unused_1359_);
v___x_1344_ = v_l_1334_;
v_isShared_1345_ = v_isSharedCheck_1356_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_v_1342_);
lean_inc(v_k_1341_);
lean_dec(v_l_1334_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1356_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1335_, 2);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 4, v_r_1335_);
lean_ctor_set(v___x_1344_, 3, v_r_1335_);
lean_ctor_set(v___x_1344_, 2, v_v_1102_);
lean_ctor_set(v___x_1344_, 1, v_k_1101_);
lean_ctor_set(v___x_1344_, 0, v___x_1250_);
v___x_1348_ = v___x_1344_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v_r_1335_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v_r_1335_);
v___x_1348_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1350_; 
lean_inc(v_r_1335_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 3, v_r_1335_);
lean_ctor_set(v___x_1339_, 0, v___x_1250_);
v___x_1350_ = v___x_1339_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_k_1336_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v_v_1337_);
lean_ctor_set(v_reuseFailAlloc_1354_, 3, v_r_1335_);
lean_ctor_set(v_reuseFailAlloc_1354_, 4, v_r_1335_);
v___x_1350_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1352_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 4, v___x_1350_);
lean_ctor_set(v___x_1106_, 3, v___x_1348_);
lean_ctor_set(v___x_1106_, 2, v_v_1342_);
lean_ctor_set(v___x_1106_, 1, v_k_1341_);
lean_ctor_set(v___x_1106_, 0, v___x_1346_);
v___x_1352_ = v___x_1106_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1353_, 3, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1353_, 4, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
}
else
{
lean_object* v_r_1363_; 
v_r_1363_ = lean_ctor_get(v_impl_1249_, 4);
lean_inc(v_r_1363_);
if (lean_obj_tag(v_r_1363_) == 0)
{
lean_object* v_k_1364_; lean_object* v_v_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1376_; 
v_k_1364_ = lean_ctor_get(v_impl_1249_, 1);
v_v_1365_ = lean_ctor_get(v_impl_1249_, 2);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_impl_1249_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; lean_object* v_unused_1378_; lean_object* v_unused_1379_; 
v_unused_1377_ = lean_ctor_get(v_impl_1249_, 4);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_impl_1249_, 3);
lean_dec(v_unused_1378_);
v_unused_1379_ = lean_ctor_get(v_impl_1249_, 0);
lean_dec(v_unused_1379_);
v___x_1367_ = v_impl_1249_;
v_isShared_1368_ = v_isSharedCheck_1376_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_v_1365_);
lean_inc(v_k_1364_);
lean_dec(v_impl_1249_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1376_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = lean_unsigned_to_nat(3u);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 4, v_l_1334_);
lean_ctor_set(v___x_1367_, 2, v_v_1102_);
lean_ctor_set(v___x_1367_, 1, v_k_1101_);
lean_ctor_set(v___x_1367_, 0, v___x_1250_);
v___x_1371_ = v___x_1367_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1375_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1375_, 3, v_l_1334_);
lean_ctor_set(v_reuseFailAlloc_1375_, 4, v_l_1334_);
v___x_1371_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1373_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 4, v_r_1363_);
lean_ctor_set(v___x_1106_, 3, v___x_1371_);
lean_ctor_set(v___x_1106_, 2, v_v_1365_);
lean_ctor_set(v___x_1106_, 1, v_k_1364_);
lean_ctor_set(v___x_1106_, 0, v___x_1369_);
v___x_1373_ = v___x_1106_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_k_1364_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_v_1365_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v_r_1363_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1380_ = lean_unsigned_to_nat(2u);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 4, v_impl_1249_);
lean_ctor_set(v___x_1106_, 3, v_r_1363_);
lean_ctor_set(v___x_1106_, 0, v___x_1380_);
v___x_1382_ = v___x_1106_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1383_, 3, v_r_1363_);
lean_ctor_set(v_reuseFailAlloc_1383_, 4, v_impl_1249_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
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
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_unsigned_to_nat(1u);
v___x_1386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v_k_1097_);
lean_ctor_set(v___x_1386_, 2, v_v_1098_);
lean_ctor_set(v___x_1386_, 3, v_t_1099_);
lean_ctor_set(v___x_1386_, 4, v_t_1099_);
return v___x_1386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object* v_s_1387_, lean_object* v_mvarId_1388_){
_start:
{
uint8_t v___x_1389_; 
v___x_1389_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_mvarId_1388_, v_s_1387_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_box(0);
v___x_1391_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1388_, v___x_1390_, v_s_1387_);
return v___x_1391_;
}
else
{
lean_dec(v_mvarId_1388_);
return v_s_1387_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object* v_00_u03b2_1392_, lean_object* v_k_1393_, lean_object* v_t_1394_){
_start:
{
uint8_t v___x_1395_; 
v___x_1395_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1393_, v_t_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object* v_00_u03b2_1396_, lean_object* v_k_1397_, lean_object* v_t_1398_){
_start:
{
uint8_t v_res_1399_; lean_object* v_r_1400_; 
v_res_1399_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(v_00_u03b2_1396_, v_k_1397_, v_t_1398_);
lean_dec(v_t_1398_);
lean_dec(v_k_1397_);
v_r_1400_ = lean_box(v_res_1399_);
return v_r_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object* v_00_u03b2_1401_, lean_object* v_k_1402_, lean_object* v_v_1403_, lean_object* v_t_1404_, lean_object* v_hl_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1402_, v_v_1403_, v_t_1404_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object* v_l_1407_){
_start:
{
lean_object* v___f_1408_; lean_object* v___x_1409_; 
v___f_1408_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1409_ = l_Std_TreeSet_ofList___redArg(v_l_1407_, v___f_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList___boxed(lean_object* v_l_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_MVarIdSet_ofList(v_l_1410_);
lean_dec(v_l_1410_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object* v_l_1412_){
_start:
{
lean_object* v___f_1413_; lean_object* v___x_1414_; 
v___f_1413_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1414_ = l_Std_TreeSet_ofArray___redArg(v_l_1412_, v___f_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object* v_l_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_MVarIdSet_ofArray(v_l_1415_);
lean_dec_ref(v_l_1415_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1417_, lean_object* v_m_1418_, lean_object* v_init_1419_, lean_object* v_f_1420_){
_start:
{
lean_object* v_toApplicative_1421_; lean_object* v_toBind_1422_; lean_object* v_toPure_1423_; lean_object* v___f_1424_; lean_object* v___x_1425_; lean_object* v___f_1426_; lean_object* v___x_1427_; 
v_toApplicative_1421_ = lean_ctor_get(v_inst_1417_, 0);
v_toBind_1422_ = lean_ctor_get(v_inst_1417_, 1);
lean_inc(v_toBind_1422_);
v_toPure_1423_ = lean_ctor_get(v_toApplicative_1421_, 1);
lean_inc(v_toPure_1423_);
v___f_1424_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1424_, 0, v_f_1420_);
v___x_1425_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1417_, v___f_1424_, v_init_1419_, v_m_1418_);
v___f_1426_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1426_, 0, v_toPure_1423_);
v___x_1427_ = lean_apply_4(v_toBind_1422_, lean_box(0), lean_box(0), v___x_1425_, v___f_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1(lean_object* v_m_1428_, lean_object* v_inst_1429_, lean_object* v_00_u03b2_1430_, lean_object* v_m_1431_, lean_object* v_init_1432_, lean_object* v_f_1433_){
_start:
{
lean_object* v_toApplicative_1434_; lean_object* v_toBind_1435_; lean_object* v_toPure_1436_; lean_object* v___f_1437_; lean_object* v___x_1438_; lean_object* v___f_1439_; lean_object* v___x_1440_; 
v_toApplicative_1434_ = lean_ctor_get(v_inst_1429_, 0);
v_toBind_1435_ = lean_ctor_get(v_inst_1429_, 1);
lean_inc(v_toBind_1435_);
v_toPure_1436_ = lean_ctor_get(v_toApplicative_1434_, 1);
lean_inc(v_toPure_1436_);
v___f_1437_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1437_, 0, v_f_1433_);
v___x_1438_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1429_, v___f_1437_, v_init_1432_, v_m_1431_);
v___f_1439_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1439_, 0, v_toPure_1436_);
v___x_1440_ = lean_apply_4(v_toBind_1435_, lean_box(0), lean_box(0), v___x_1438_, v___f_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object* v_inst_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1442_, 0, lean_box(0));
lean_closure_set(v___x_1442_, 1, v_inst_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object* v_m_1443_, lean_object* v_inst_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1445_, 0, lean_box(0));
lean_closure_set(v___x_1445_, 1, v_inst_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object* v_s_1446_, lean_object* v_mvarId_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1447_, v_a_1448_, v_s_1446_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object* v_00_u03b1_1450_, lean_object* v_s_1451_, lean_object* v_mvarId_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1452_, v_a_1453_, v_s_1451_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_box(1);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg();
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object* v_00_u03b1_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_box(1);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg(){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_box(1);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg___boxed(lean_object* v___dummy_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_instEmptyCollectionMVarIdMap___redArg();
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* v_00_u03b1_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_box(1);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_1467_, lean_object* v_a_1468_, lean_object* v_b_1469_, lean_object* v_c_1470_){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v_a_1468_);
lean_ctor_set(v___x_1471_, 1, v_b_1469_);
v___x_1472_ = lean_apply_2(v_f_1467_, v___x_1471_, v_c_1470_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1473_, lean_object* v_m_1474_, lean_object* v_init_1475_, lean_object* v_f_1476_){
_start:
{
lean_object* v_toApplicative_1477_; lean_object* v_toBind_1478_; lean_object* v_toPure_1479_; lean_object* v___f_1480_; lean_object* v___x_1481_; lean_object* v___f_1482_; lean_object* v___x_1483_; 
v_toApplicative_1477_ = lean_ctor_get(v_inst_1473_, 0);
v_toBind_1478_ = lean_ctor_get(v_inst_1473_, 1);
lean_inc(v_toBind_1478_);
v_toPure_1479_ = lean_ctor_get(v_toApplicative_1477_, 1);
lean_inc(v_toPure_1479_);
v___f_1480_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1480_, 0, v_f_1476_);
v___x_1481_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1473_, v___f_1480_, v_init_1475_, v_m_1474_);
v___f_1482_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1482_, 0, v_toPure_1479_);
v___x_1483_ = lean_apply_4(v_toBind_1478_, lean_box(0), lean_box(0), v___x_1481_, v___f_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object* v_m_1484_, lean_object* v_00_u03b1_1485_, lean_object* v_inst_1486_, lean_object* v_00_u03b2_1487_, lean_object* v_m_1488_, lean_object* v_init_1489_, lean_object* v_f_1490_){
_start:
{
lean_object* v_toApplicative_1491_; lean_object* v_toBind_1492_; lean_object* v_toPure_1493_; lean_object* v___f_1494_; lean_object* v___x_1495_; lean_object* v___f_1496_; lean_object* v___x_1497_; 
v_toApplicative_1491_ = lean_ctor_get(v_inst_1486_, 0);
v_toBind_1492_ = lean_ctor_get(v_inst_1486_, 1);
lean_inc(v_toBind_1492_);
v_toPure_1493_ = lean_ctor_get(v_toApplicative_1491_, 1);
lean_inc(v_toPure_1493_);
v___f_1494_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1494_, 0, v_f_1490_);
v___x_1495_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1486_, v___f_1494_, v_init_1489_, v_m_1488_);
v___f_1496_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1496_, 0, v_toPure_1493_);
v___x_1497_ = lean_apply_4(v_toBind_1492_, lean_box(0), lean_box(0), v___x_1495_, v___f_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object* v_inst_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1499_, 0, lean_box(0));
lean_closure_set(v___x_1499_, 1, lean_box(0));
lean_closure_set(v___x_1499_, 2, v_inst_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object* v_m_1500_, lean_object* v_00_u03b1_1501_, lean_object* v_inst_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1503_, 0, lean_box(0));
lean_closure_set(v___x_1503_, 1, lean_box(0));
lean_closure_set(v___x_1503_, 2, v_inst_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg(){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_box(1);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg___boxed(lean_object* v___dummy_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_instInhabitedMVarIdMap___redArg();
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* v_00_u03b1_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_box(1);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx(lean_object* v_x_1510_){
_start:
{
switch(lean_obj_tag(v_x_1510_))
{
case 0:
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_unsigned_to_nat(0u);
return v___x_1511_;
}
case 1:
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_unsigned_to_nat(1u);
return v___x_1512_;
}
case 2:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_unsigned_to_nat(2u);
return v___x_1513_;
}
case 3:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_unsigned_to_nat(3u);
return v___x_1514_;
}
case 4:
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_unsigned_to_nat(4u);
return v___x_1515_;
}
case 5:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_unsigned_to_nat(5u);
return v___x_1516_;
}
case 6:
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_unsigned_to_nat(6u);
return v___x_1517_;
}
case 7:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_unsigned_to_nat(7u);
return v___x_1518_;
}
case 8:
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_unsigned_to_nat(8u);
return v___x_1519_;
}
case 9:
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_unsigned_to_nat(9u);
return v___x_1520_;
}
case 10:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_unsigned_to_nat(10u);
return v___x_1521_;
}
default: 
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_unsigned_to_nat(11u);
return v___x_1522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___boxed(lean_object* v_x_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_Expr_ctorIdx(v_x_1523_);
lean_dec_ref(v_x_1523_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object* v_t_1525_, lean_object* v_k_1526_){
_start:
{
switch(lean_obj_tag(v_t_1525_))
{
case 4:
{
lean_object* v_declName_1527_; lean_object* v_us_1528_; lean_object* v___x_1529_; 
v_declName_1527_ = lean_ctor_get(v_t_1525_, 0);
lean_inc(v_declName_1527_);
v_us_1528_ = lean_ctor_get(v_t_1525_, 1);
lean_inc(v_us_1528_);
lean_dec_ref_known(v_t_1525_, 2);
v___x_1529_ = lean_apply_2(v_k_1526_, v_declName_1527_, v_us_1528_);
return v___x_1529_;
}
case 5:
{
lean_object* v_fn_1530_; lean_object* v_arg_1531_; lean_object* v___x_1532_; 
v_fn_1530_ = lean_ctor_get(v_t_1525_, 0);
lean_inc_ref(v_fn_1530_);
v_arg_1531_ = lean_ctor_get(v_t_1525_, 1);
lean_inc_ref(v_arg_1531_);
lean_dec_ref_known(v_t_1525_, 2);
v___x_1532_ = lean_apply_2(v_k_1526_, v_fn_1530_, v_arg_1531_);
return v___x_1532_;
}
case 6:
{
lean_object* v_binderName_1533_; lean_object* v_binderType_1534_; lean_object* v_body_1535_; uint8_t v_binderInfo_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_binderName_1533_ = lean_ctor_get(v_t_1525_, 0);
lean_inc(v_binderName_1533_);
v_binderType_1534_ = lean_ctor_get(v_t_1525_, 1);
lean_inc_ref(v_binderType_1534_);
v_body_1535_ = lean_ctor_get(v_t_1525_, 2);
lean_inc_ref(v_body_1535_);
v_binderInfo_1536_ = lean_ctor_get_uint8(v_t_1525_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1525_, 3);
v___x_1537_ = lean_box(v_binderInfo_1536_);
v___x_1538_ = lean_apply_4(v_k_1526_, v_binderName_1533_, v_binderType_1534_, v_body_1535_, v___x_1537_);
return v___x_1538_;
}
case 7:
{
lean_object* v_binderName_1539_; lean_object* v_binderType_1540_; lean_object* v_body_1541_; uint8_t v_binderInfo_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_binderName_1539_ = lean_ctor_get(v_t_1525_, 0);
lean_inc(v_binderName_1539_);
v_binderType_1540_ = lean_ctor_get(v_t_1525_, 1);
lean_inc_ref(v_binderType_1540_);
v_body_1541_ = lean_ctor_get(v_t_1525_, 2);
lean_inc_ref(v_body_1541_);
v_binderInfo_1542_ = lean_ctor_get_uint8(v_t_1525_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1525_, 3);
v___x_1543_ = lean_box(v_binderInfo_1542_);
v___x_1544_ = lean_apply_4(v_k_1526_, v_binderName_1539_, v_binderType_1540_, v_body_1541_, v___x_1543_);
return v___x_1544_;
}
case 8:
{
lean_object* v_declName_1545_; lean_object* v_type_1546_; lean_object* v_value_1547_; lean_object* v_body_1548_; uint8_t v_nondep_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v_declName_1545_ = lean_ctor_get(v_t_1525_, 0);
lean_inc(v_declName_1545_);
v_type_1546_ = lean_ctor_get(v_t_1525_, 1);
lean_inc_ref(v_type_1546_);
v_value_1547_ = lean_ctor_get(v_t_1525_, 2);
lean_inc_ref(v_value_1547_);
v_body_1548_ = lean_ctor_get(v_t_1525_, 3);
lean_inc_ref(v_body_1548_);
v_nondep_1549_ = lean_ctor_get_uint8(v_t_1525_, sizeof(void*)*4);
lean_dec_ref_known(v_t_1525_, 4);
v___x_1550_ = lean_box(v_nondep_1549_);
v___x_1551_ = lean_apply_5(v_k_1526_, v_declName_1545_, v_type_1546_, v_value_1547_, v_body_1548_, v___x_1550_);
return v___x_1551_;
}
case 9:
{
lean_object* v_a_1552_; lean_object* v___x_1553_; 
v_a_1552_ = lean_ctor_get(v_t_1525_, 0);
lean_inc_ref(v_a_1552_);
lean_dec_ref_known(v_t_1525_, 1);
v___x_1553_ = lean_apply_1(v_k_1526_, v_a_1552_);
return v___x_1553_;
}
case 10:
{
lean_object* v_data_1554_; lean_object* v_expr_1555_; lean_object* v___x_1556_; 
v_data_1554_ = lean_ctor_get(v_t_1525_, 0);
lean_inc(v_data_1554_);
v_expr_1555_ = lean_ctor_get(v_t_1525_, 1);
lean_inc_ref(v_expr_1555_);
lean_dec_ref_known(v_t_1525_, 2);
v___x_1556_ = lean_apply_2(v_k_1526_, v_data_1554_, v_expr_1555_);
return v___x_1556_;
}
case 11:
{
lean_object* v_typeName_1557_; lean_object* v_idx_1558_; lean_object* v_struct_1559_; lean_object* v___x_1560_; 
v_typeName_1557_ = lean_ctor_get(v_t_1525_, 0);
lean_inc(v_typeName_1557_);
v_idx_1558_ = lean_ctor_get(v_t_1525_, 1);
lean_inc(v_idx_1558_);
v_struct_1559_ = lean_ctor_get(v_t_1525_, 2);
lean_inc_ref(v_struct_1559_);
lean_dec_ref_known(v_t_1525_, 3);
v___x_1560_ = lean_apply_3(v_k_1526_, v_typeName_1557_, v_idx_1558_, v_struct_1559_);
return v___x_1560_;
}
default: 
{
lean_object* v_deBruijnIndex_1561_; lean_object* v___x_1562_; 
v_deBruijnIndex_1561_ = lean_ctor_get(v_t_1525_, 0);
lean_inc(v_deBruijnIndex_1561_);
lean_dec_ref(v_t_1525_);
v___x_1562_ = lean_apply_1(v_k_1526_, v_deBruijnIndex_1561_);
return v___x_1562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object* v_motive_1563_, lean_object* v_ctorIdx_1564_, lean_object* v_t_1565_, lean_object* v_h_1566_, lean_object* v_k_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Expr_ctorElim___redArg(v_t_1565_, v_k_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object* v_motive_1569_, lean_object* v_ctorIdx_1570_, lean_object* v_t_1571_, lean_object* v_h_1572_, lean_object* v_k_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Expr_ctorElim(v_motive_1569_, v_ctorIdx_1570_, v_t_1571_, v_h_1572_, v_k_1573_);
lean_dec(v_ctorIdx_1570_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object* v_t_1575_, lean_object* v_bvar_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_Expr_ctorElim___redArg(v_t_1575_, v_bvar_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object* v_motive_1578_, lean_object* v_t_1579_, lean_object* v_h_1580_, lean_object* v_bvar_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_Expr_ctorElim___redArg(v_t_1579_, v_bvar_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object* v_t_1583_, lean_object* v_fvar_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Expr_ctorElim___redArg(v_t_1583_, v_fvar_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object* v_motive_1586_, lean_object* v_t_1587_, lean_object* v_h_1588_, lean_object* v_fvar_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Expr_ctorElim___redArg(v_t_1587_, v_fvar_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object* v_t_1591_, lean_object* v_mvar_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_Expr_ctorElim___redArg(v_t_1591_, v_mvar_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object* v_motive_1594_, lean_object* v_t_1595_, lean_object* v_h_1596_, lean_object* v_mvar_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_Expr_ctorElim___redArg(v_t_1595_, v_mvar_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object* v_t_1599_, lean_object* v_sort_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Expr_ctorElim___redArg(v_t_1599_, v_sort_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object* v_motive_1602_, lean_object* v_t_1603_, lean_object* v_h_1604_, lean_object* v_sort_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Expr_ctorElim___redArg(v_t_1603_, v_sort_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object* v_t_1607_, lean_object* v_const_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Expr_ctorElim___redArg(v_t_1607_, v_const_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object* v_motive_1610_, lean_object* v_t_1611_, lean_object* v_h_1612_, lean_object* v_const_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Expr_ctorElim___redArg(v_t_1611_, v_const_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object* v_t_1615_, lean_object* v_app_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Expr_ctorElim___redArg(v_t_1615_, v_app_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object* v_motive_1618_, lean_object* v_t_1619_, lean_object* v_h_1620_, lean_object* v_app_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Expr_ctorElim___redArg(v_t_1619_, v_app_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object* v_t_1623_, lean_object* v_lam_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_Expr_ctorElim___redArg(v_t_1623_, v_lam_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object* v_motive_1626_, lean_object* v_t_1627_, lean_object* v_h_1628_, lean_object* v_lam_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Expr_ctorElim___redArg(v_t_1627_, v_lam_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object* v_t_1631_, lean_object* v_forallE_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Expr_ctorElim___redArg(v_t_1631_, v_forallE_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object* v_motive_1634_, lean_object* v_t_1635_, lean_object* v_h_1636_, lean_object* v_forallE_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Expr_ctorElim___redArg(v_t_1635_, v_forallE_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object* v_t_1639_, lean_object* v_letE_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Expr_ctorElim___redArg(v_t_1639_, v_letE_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object* v_motive_1642_, lean_object* v_t_1643_, lean_object* v_h_1644_, lean_object* v_letE_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Expr_ctorElim___redArg(v_t_1643_, v_letE_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object* v_t_1647_, lean_object* v_lit_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_Expr_ctorElim___redArg(v_t_1647_, v_lit_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object* v_motive_1650_, lean_object* v_t_1651_, lean_object* v_h_1652_, lean_object* v_lit_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Expr_ctorElim___redArg(v_t_1651_, v_lit_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object* v_t_1655_, lean_object* v_mdata_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Expr_ctorElim___redArg(v_t_1655_, v_mdata_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object* v_motive_1658_, lean_object* v_t_1659_, lean_object* v_h_1660_, lean_object* v_mdata_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Expr_ctorElim___redArg(v_t_1659_, v_mdata_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object* v_t_1663_, lean_object* v_proj_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Expr_ctorElim___redArg(v_t_1663_, v_proj_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object* v_motive_1666_, lean_object* v_t_1667_, lean_object* v_h_1668_, lean_object* v_proj_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_Expr_ctorElim___redArg(v_t_1667_, v_proj_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* v_a_00___x40___internal___hyg_1672_){
_start:
{
uint64_t v_res_1673_; lean_object* v_r_1674_; 
v_res_1673_ = lean_expr_data(v_a_00___x40___internal___hyg_1672_);
lean_dec_ref(v_a_00___x40___internal___hyg_1672_);
v_r_1674_ = lean_box_uint64(v_res_1673_);
return v_r_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object* v_t_1675_, lean_object* v_bvar_1676_, lean_object* v_fvar_1677_, lean_object* v_mvar_1678_, lean_object* v_sort_1679_, lean_object* v_const_1680_, lean_object* v_app_1681_, lean_object* v_lam_1682_, lean_object* v_forallE_1683_, lean_object* v_letE_1684_, lean_object* v_lit_1685_, lean_object* v_mdata_1686_, lean_object* v_proj_1687_){
_start:
{
switch(lean_obj_tag(v_t_1675_))
{
case 0:
{
lean_object* v_deBruijnIndex_1688_; lean_object* v___x_1689_; 
lean_dec(v_proj_1687_);
lean_dec(v_mdata_1686_);
lean_dec(v_lit_1685_);
lean_dec(v_letE_1684_);
lean_dec(v_forallE_1683_);
lean_dec(v_lam_1682_);
lean_dec(v_app_1681_);
lean_dec(v_const_1680_);
lean_dec(v_sort_1679_);
lean_dec(v_mvar_1678_);
lean_dec(v_fvar_1677_);
v_deBruijnIndex_1688_ = lean_ctor_get(v_t_1675_, 0);
lean_inc(v_deBruijnIndex_1688_);
lean_dec_ref_known(v_t_1675_, 1);
v___x_1689_ = lean_apply_1(v_bvar_1676_, v_deBruijnIndex_1688_);
return v___x_1689_;
}
case 1:
{
lean_object* v_fvarId_1690_; lean_object* v___x_1691_; 
lean_dec(v_proj_1687_);
lean_dec(v_mdata_1686_);
lean_dec(v_lit_1685_);
lean_dec(v_letE_1684_);
lean_dec(v_forallE_1683_);
lean_dec(v_lam_1682_);
lean_dec(v_app_1681_);
lean_dec(v_const_1680_);
lean_dec(v_sort_1679_);
lean_dec(v_mvar_1678_);
lean_dec(v_bvar_1676_);
v_fvarId_1690_ = lean_ctor_get(v_t_1675_, 0);
lean_inc(v_fvarId_1690_);
lean_dec_ref_known(v_t_1675_, 1);
v___x_1691_ = lean_apply_1(v_fvar_1677_, v_fvarId_1690_);
return v___x_1691_;
}
case 2:
{
lean_object* v_mvarId_1692_; lean_object* v___x_1693_; 
lean_dec(v_proj_1687_);
lean_dec(v_mdata_1686_);
lean_dec(v_lit_1685_);
lean_dec(v_letE_1684_);
lean_dec(v_forallE_1683_);
lean_dec(v_lam_1682_);
lean_dec(v_app_1681_);
lean_dec(v_const_1680_);
lean_dec(v_sort_1679_);
lean_dec(v_fvar_1677_);
lean_dec(v_bvar_1676_);
v_mvarId_1692_ = lean_ctor_get(v_t_1675_, 0);
lean_inc(v_mvarId_1692_);
lean_dec_ref_known(v_t_1675_, 1);
v___x_1693_ = lean_apply_1(v_mvar_1678_, v_mvarId_1692_);
return v___x_1693_;
}
case 3:
{
lean_object* v_u_1694_; lean_object* v___x_1695_; 
lean_dec(v_proj_1687_);
lean_dec(v_mdata_1686_);
lean_dec(v_lit_1685_);
lean_dec(v_letE_1684_);
lean_dec(v_forallE_1683_);
lean_dec(v_lam_1682_);
lean_dec(v_app_1681_);
lean_dec(v_const_1680_);
lean_dec(v_mvar_1678_);
lean_dec(v_fvar_1677_);
lean_dec(v_bvar_1676_);
v_u_1694_ = lean_ctor_get(v_t_1675_, 0);
lean_inc(v_u_1694_);
lean_dec_ref_known(v_t_1675_, 1);
v___x_1695_ = lean_apply_1(v_sort_1679_, v_u_1694_);
return v___x_1695_;
}
case 4:
{
lean_object* v_declName_1696_; lean_object* v_us_1697_; lean_object* v___x_1698_; 
lean_dec(v_proj_1687_);
lean_dec(v_mdata_1686_);
lean_dec(v_lit_1685_);
lean_dec(v_letE_1684_);
lean_dec(v_forallE_1683_);
lean_dec(v_lam_1682_);
lean_dec(v_app_1681_);
lean_dec(v_sort_1679_);
lean_dec(v_mvar_1678_);
lean_dec(v_fvar_1677_);
lean_dec(v_bvar_1676_);
v_declName_1696_ = lean_ctor_get(v_t_1675_, 0);
lean_inc(v_declName_1696_);
v_us_1697_ = lean_ctor_get(v_t_1675_, 1);
lean_inc(v_us_1697_);
lean_dec_ref_known(v_t_1675_, 2);
v___x_1698_ = lean_apply_2(v_const_1680_, v_declName_1696_, v_us_1697_);
return v___x_1698_;
}
case 5:
{
lean_object* v_fn_1699_; lean_object* v_arg_1700_; lean_object* v___x_1701_; 
lean_dec(v_proj_1687_);
lean_dec(v_mdata_1686_);
lean_dec(v_lit_1685_);
lean_dec(v_letE_1684_);
lean_dec(v_forallE_1683_);
lean_dec(v_lam_1682_);
lean_dec(v_const_1680_);
lean_dec(v_sort_1679_);
lean_dec(v_mvar_1678_);
lean_dec(v_fvar_1677_);
lean_dec(v_bvar_1676_);
v_fn_1699_ = lean_ctor_get(v_t_1675_, 0);
lean_inc_ref(v_fn_1699_);
v_arg_1700_ = lean_ctor_get(v_t_1675_, 1);
lean_inc_ref(v_arg_1700_);
lean_dec_ref_known(v_t_1675_, 2);
v___x_1701_ = lean_apply_2(v_app_1681_, v_fn_1699_, v_arg_1700_);
return v___x_1701_;
}
case 6:
{
lean_object* v_binderName_1702_; lean_object* v_binderType_1703_; lean_object* v_body_1704_; uint8_t v_binderInfo_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec(v_proj_1687_);
lean_dec(v_mdata_1686_);
lean_dec(v_lit_1685_);
lean_dec(v_letE_1684_);
lean_dec(v_forallE_1683_);
lean_dec(v_app_1681_);
lean_dec(v_const_1680_);
lean_dec(v_sort_1679_);
lean_dec(v_mvar_1678_);
lean_dec(v_fvar_1677_);
lean_dec(v_bvar_1676_);
v_binderName_1702_ = lean_ctor_get(v_t_1675_, 0);
lean_inc(v_binderName_1702_);
v_binderType_1703_ = lean_ctor_get(v_t_1675_, 1);
lean_inc_ref(v_binderType_1703_);
v_body_1704_ = lean_ctor_get(v_t_1675_, 2);
lean_inc_ref(v_body_1704_);
v_binderInfo_1705_ = lean_ctor_get_uint8(v_t_1675_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1675_, 3);
v___x_1706_ = lean_box(v_binderInfo_1705_);
v___x_1707_ = lean_apply_4(v_lam_1682_, v_binderName_1702_, v_binderType_1703_, v_body_1704_, v___x_1706_);
return v___x_1707_;
}
case 7:
{
lean_object* v_binderName_1708_; lean_object* v_binderType_1709_; lean_object* v_body_1710_; uint8_t v_binderInfo_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_dec(v_proj_1687_);
lean_dec(v_mdata_1686_);
lean_dec(v_lit_1685_);
lean_dec(v_letE_1684_);
lean_dec(v_lam_1682_);
lean_dec(v_app_1681_);
lean_dec(v_const_1680_);
lean_dec(v_sort_1679_);
lean_dec(v_mvar_1678_);
lean_dec(v_fvar_1677_);
lean_dec(v_bvar_1676_);
v_binderName_1708_ = lean_ctor_get(v_t_1675_, 0);
lean_inc(v_binderName_1708_);
v_binderType_1709_ = lean_ctor_get(v_t_1675_, 1);
lean_inc_ref(v_binderType_1709_);
v_body_1710_ = lean_ctor_get(v_t_1675_, 2);
lean_inc_ref(v_body_1710_);
v_binderInfo_1711_ = lean_ctor_get_uint8(v_t_1675_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1675_, 3);
v___x_1712_ = lean_box(v_binderInfo_1711_);
v___x_1713_ = lean_apply_4(v_forallE_1683_, v_binderName_1708_, v_binderType_1709_, v_body_1710_, v___x_1712_);
return v___x_1713_;
}
case 8:
{
lean_object* v_declName_1714_; lean_object* v_type_1715_; lean_object* v_value_1716_; lean_object* v_body_1717_; uint8_t v_nondep_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_dec(v_proj_1687_);
lean_dec(v_mdata_1686_);
lean_dec(v_lit_1685_);
lean_dec(v_forallE_1683_);
lean_dec(v_lam_1682_);
lean_dec(v_app_1681_);
lean_dec(v_const_1680_);
lean_dec(v_sort_1679_);
lean_dec(v_mvar_1678_);
lean_dec(v_fvar_1677_);
lean_dec(v_bvar_1676_);
v_declName_1714_ = lean_ctor_get(v_t_1675_, 0);
lean_inc(v_declName_1714_);
v_type_1715_ = lean_ctor_get(v_t_1675_, 1);
lean_inc_ref(v_type_1715_);
v_value_1716_ = lean_ctor_get(v_t_1675_, 2);
lean_inc_ref(v_value_1716_);
v_body_1717_ = lean_ctor_get(v_t_1675_, 3);
lean_inc_ref(v_body_1717_);
v_nondep_1718_ = lean_ctor_get_uint8(v_t_1675_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1675_, 4);
v___x_1719_ = lean_box(v_nondep_1718_);
v___x_1720_ = lean_apply_5(v_letE_1684_, v_declName_1714_, v_type_1715_, v_value_1716_, v_body_1717_, v___x_1719_);
return v___x_1720_;
}
case 9:
{
lean_object* v_a_1721_; lean_object* v___x_1722_; 
lean_dec(v_proj_1687_);
lean_dec(v_mdata_1686_);
lean_dec(v_letE_1684_);
lean_dec(v_forallE_1683_);
lean_dec(v_lam_1682_);
lean_dec(v_app_1681_);
lean_dec(v_const_1680_);
lean_dec(v_sort_1679_);
lean_dec(v_mvar_1678_);
lean_dec(v_fvar_1677_);
lean_dec(v_bvar_1676_);
v_a_1721_ = lean_ctor_get(v_t_1675_, 0);
lean_inc_ref(v_a_1721_);
lean_dec_ref_known(v_t_1675_, 1);
v___x_1722_ = lean_apply_1(v_lit_1685_, v_a_1721_);
return v___x_1722_;
}
case 10:
{
lean_object* v_data_1723_; lean_object* v_expr_1724_; lean_object* v___x_1725_; 
lean_dec(v_proj_1687_);
lean_dec(v_lit_1685_);
lean_dec(v_letE_1684_);
lean_dec(v_forallE_1683_);
lean_dec(v_lam_1682_);
lean_dec(v_app_1681_);
lean_dec(v_const_1680_);
lean_dec(v_sort_1679_);
lean_dec(v_mvar_1678_);
lean_dec(v_fvar_1677_);
lean_dec(v_bvar_1676_);
v_data_1723_ = lean_ctor_get(v_t_1675_, 0);
lean_inc(v_data_1723_);
v_expr_1724_ = lean_ctor_get(v_t_1675_, 1);
lean_inc_ref(v_expr_1724_);
lean_dec_ref_known(v_t_1675_, 2);
v___x_1725_ = lean_apply_2(v_mdata_1686_, v_data_1723_, v_expr_1724_);
return v___x_1725_;
}
default: 
{
lean_object* v_typeName_1726_; lean_object* v_idx_1727_; lean_object* v_struct_1728_; lean_object* v___x_1729_; 
lean_dec(v_mdata_1686_);
lean_dec(v_lit_1685_);
lean_dec(v_letE_1684_);
lean_dec(v_forallE_1683_);
lean_dec(v_lam_1682_);
lean_dec(v_app_1681_);
lean_dec(v_const_1680_);
lean_dec(v_sort_1679_);
lean_dec(v_mvar_1678_);
lean_dec(v_fvar_1677_);
lean_dec(v_bvar_1676_);
v_typeName_1726_ = lean_ctor_get(v_t_1675_, 0);
lean_inc(v_typeName_1726_);
v_idx_1727_ = lean_ctor_get(v_t_1675_, 1);
lean_inc(v_idx_1727_);
v_struct_1728_ = lean_ctor_get(v_t_1675_, 2);
lean_inc_ref(v_struct_1728_);
lean_dec_ref_known(v_t_1675_, 3);
v___x_1729_ = lean_apply_3(v_proj_1687_, v_typeName_1726_, v_idx_1727_, v_struct_1728_);
return v___x_1729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* v_motive_1730_, lean_object* v_t_1731_, lean_object* v_bvar_1732_, lean_object* v_fvar_1733_, lean_object* v_mvar_1734_, lean_object* v_sort_1735_, lean_object* v_const_1736_, lean_object* v_app_1737_, lean_object* v_lam_1738_, lean_object* v_forallE_1739_, lean_object* v_letE_1740_, lean_object* v_lit_1741_, lean_object* v_mdata_1742_, lean_object* v_proj_1743_){
_start:
{
switch(lean_obj_tag(v_t_1731_))
{
case 0:
{
lean_object* v_deBruijnIndex_1744_; lean_object* v___x_1745_; 
lean_dec(v_proj_1743_);
lean_dec(v_mdata_1742_);
lean_dec(v_lit_1741_);
lean_dec(v_letE_1740_);
lean_dec(v_forallE_1739_);
lean_dec(v_lam_1738_);
lean_dec(v_app_1737_);
lean_dec(v_const_1736_);
lean_dec(v_sort_1735_);
lean_dec(v_mvar_1734_);
lean_dec(v_fvar_1733_);
v_deBruijnIndex_1744_ = lean_ctor_get(v_t_1731_, 0);
lean_inc(v_deBruijnIndex_1744_);
lean_dec_ref_known(v_t_1731_, 1);
v___x_1745_ = lean_apply_1(v_bvar_1732_, v_deBruijnIndex_1744_);
return v___x_1745_;
}
case 1:
{
lean_object* v_fvarId_1746_; lean_object* v___x_1747_; 
lean_dec(v_proj_1743_);
lean_dec(v_mdata_1742_);
lean_dec(v_lit_1741_);
lean_dec(v_letE_1740_);
lean_dec(v_forallE_1739_);
lean_dec(v_lam_1738_);
lean_dec(v_app_1737_);
lean_dec(v_const_1736_);
lean_dec(v_sort_1735_);
lean_dec(v_mvar_1734_);
lean_dec(v_bvar_1732_);
v_fvarId_1746_ = lean_ctor_get(v_t_1731_, 0);
lean_inc(v_fvarId_1746_);
lean_dec_ref_known(v_t_1731_, 1);
v___x_1747_ = lean_apply_1(v_fvar_1733_, v_fvarId_1746_);
return v___x_1747_;
}
case 2:
{
lean_object* v_mvarId_1748_; lean_object* v___x_1749_; 
lean_dec(v_proj_1743_);
lean_dec(v_mdata_1742_);
lean_dec(v_lit_1741_);
lean_dec(v_letE_1740_);
lean_dec(v_forallE_1739_);
lean_dec(v_lam_1738_);
lean_dec(v_app_1737_);
lean_dec(v_const_1736_);
lean_dec(v_sort_1735_);
lean_dec(v_fvar_1733_);
lean_dec(v_bvar_1732_);
v_mvarId_1748_ = lean_ctor_get(v_t_1731_, 0);
lean_inc(v_mvarId_1748_);
lean_dec_ref_known(v_t_1731_, 1);
v___x_1749_ = lean_apply_1(v_mvar_1734_, v_mvarId_1748_);
return v___x_1749_;
}
case 3:
{
lean_object* v_u_1750_; lean_object* v___x_1751_; 
lean_dec(v_proj_1743_);
lean_dec(v_mdata_1742_);
lean_dec(v_lit_1741_);
lean_dec(v_letE_1740_);
lean_dec(v_forallE_1739_);
lean_dec(v_lam_1738_);
lean_dec(v_app_1737_);
lean_dec(v_const_1736_);
lean_dec(v_mvar_1734_);
lean_dec(v_fvar_1733_);
lean_dec(v_bvar_1732_);
v_u_1750_ = lean_ctor_get(v_t_1731_, 0);
lean_inc(v_u_1750_);
lean_dec_ref_known(v_t_1731_, 1);
v___x_1751_ = lean_apply_1(v_sort_1735_, v_u_1750_);
return v___x_1751_;
}
case 4:
{
lean_object* v_declName_1752_; lean_object* v_us_1753_; lean_object* v___x_1754_; 
lean_dec(v_proj_1743_);
lean_dec(v_mdata_1742_);
lean_dec(v_lit_1741_);
lean_dec(v_letE_1740_);
lean_dec(v_forallE_1739_);
lean_dec(v_lam_1738_);
lean_dec(v_app_1737_);
lean_dec(v_sort_1735_);
lean_dec(v_mvar_1734_);
lean_dec(v_fvar_1733_);
lean_dec(v_bvar_1732_);
v_declName_1752_ = lean_ctor_get(v_t_1731_, 0);
lean_inc(v_declName_1752_);
v_us_1753_ = lean_ctor_get(v_t_1731_, 1);
lean_inc(v_us_1753_);
lean_dec_ref_known(v_t_1731_, 2);
v___x_1754_ = lean_apply_2(v_const_1736_, v_declName_1752_, v_us_1753_);
return v___x_1754_;
}
case 5:
{
lean_object* v_fn_1755_; lean_object* v_arg_1756_; lean_object* v___x_1757_; 
lean_dec(v_proj_1743_);
lean_dec(v_mdata_1742_);
lean_dec(v_lit_1741_);
lean_dec(v_letE_1740_);
lean_dec(v_forallE_1739_);
lean_dec(v_lam_1738_);
lean_dec(v_const_1736_);
lean_dec(v_sort_1735_);
lean_dec(v_mvar_1734_);
lean_dec(v_fvar_1733_);
lean_dec(v_bvar_1732_);
v_fn_1755_ = lean_ctor_get(v_t_1731_, 0);
lean_inc_ref(v_fn_1755_);
v_arg_1756_ = lean_ctor_get(v_t_1731_, 1);
lean_inc_ref(v_arg_1756_);
lean_dec_ref_known(v_t_1731_, 2);
v___x_1757_ = lean_apply_2(v_app_1737_, v_fn_1755_, v_arg_1756_);
return v___x_1757_;
}
case 6:
{
lean_object* v_binderName_1758_; lean_object* v_binderType_1759_; lean_object* v_body_1760_; uint8_t v_binderInfo_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec(v_proj_1743_);
lean_dec(v_mdata_1742_);
lean_dec(v_lit_1741_);
lean_dec(v_letE_1740_);
lean_dec(v_forallE_1739_);
lean_dec(v_app_1737_);
lean_dec(v_const_1736_);
lean_dec(v_sort_1735_);
lean_dec(v_mvar_1734_);
lean_dec(v_fvar_1733_);
lean_dec(v_bvar_1732_);
v_binderName_1758_ = lean_ctor_get(v_t_1731_, 0);
lean_inc(v_binderName_1758_);
v_binderType_1759_ = lean_ctor_get(v_t_1731_, 1);
lean_inc_ref(v_binderType_1759_);
v_body_1760_ = lean_ctor_get(v_t_1731_, 2);
lean_inc_ref(v_body_1760_);
v_binderInfo_1761_ = lean_ctor_get_uint8(v_t_1731_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1731_, 3);
v___x_1762_ = lean_box(v_binderInfo_1761_);
v___x_1763_ = lean_apply_4(v_lam_1738_, v_binderName_1758_, v_binderType_1759_, v_body_1760_, v___x_1762_);
return v___x_1763_;
}
case 7:
{
lean_object* v_binderName_1764_; lean_object* v_binderType_1765_; lean_object* v_body_1766_; uint8_t v_binderInfo_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec(v_proj_1743_);
lean_dec(v_mdata_1742_);
lean_dec(v_lit_1741_);
lean_dec(v_letE_1740_);
lean_dec(v_lam_1738_);
lean_dec(v_app_1737_);
lean_dec(v_const_1736_);
lean_dec(v_sort_1735_);
lean_dec(v_mvar_1734_);
lean_dec(v_fvar_1733_);
lean_dec(v_bvar_1732_);
v_binderName_1764_ = lean_ctor_get(v_t_1731_, 0);
lean_inc(v_binderName_1764_);
v_binderType_1765_ = lean_ctor_get(v_t_1731_, 1);
lean_inc_ref(v_binderType_1765_);
v_body_1766_ = lean_ctor_get(v_t_1731_, 2);
lean_inc_ref(v_body_1766_);
v_binderInfo_1767_ = lean_ctor_get_uint8(v_t_1731_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1731_, 3);
v___x_1768_ = lean_box(v_binderInfo_1767_);
v___x_1769_ = lean_apply_4(v_forallE_1739_, v_binderName_1764_, v_binderType_1765_, v_body_1766_, v___x_1768_);
return v___x_1769_;
}
case 8:
{
lean_object* v_declName_1770_; lean_object* v_type_1771_; lean_object* v_value_1772_; lean_object* v_body_1773_; uint8_t v_nondep_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_dec(v_proj_1743_);
lean_dec(v_mdata_1742_);
lean_dec(v_lit_1741_);
lean_dec(v_forallE_1739_);
lean_dec(v_lam_1738_);
lean_dec(v_app_1737_);
lean_dec(v_const_1736_);
lean_dec(v_sort_1735_);
lean_dec(v_mvar_1734_);
lean_dec(v_fvar_1733_);
lean_dec(v_bvar_1732_);
v_declName_1770_ = lean_ctor_get(v_t_1731_, 0);
lean_inc(v_declName_1770_);
v_type_1771_ = lean_ctor_get(v_t_1731_, 1);
lean_inc_ref(v_type_1771_);
v_value_1772_ = lean_ctor_get(v_t_1731_, 2);
lean_inc_ref(v_value_1772_);
v_body_1773_ = lean_ctor_get(v_t_1731_, 3);
lean_inc_ref(v_body_1773_);
v_nondep_1774_ = lean_ctor_get_uint8(v_t_1731_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1731_, 4);
v___x_1775_ = lean_box(v_nondep_1774_);
v___x_1776_ = lean_apply_5(v_letE_1740_, v_declName_1770_, v_type_1771_, v_value_1772_, v_body_1773_, v___x_1775_);
return v___x_1776_;
}
case 9:
{
lean_object* v_a_1777_; lean_object* v___x_1778_; 
lean_dec(v_proj_1743_);
lean_dec(v_mdata_1742_);
lean_dec(v_letE_1740_);
lean_dec(v_forallE_1739_);
lean_dec(v_lam_1738_);
lean_dec(v_app_1737_);
lean_dec(v_const_1736_);
lean_dec(v_sort_1735_);
lean_dec(v_mvar_1734_);
lean_dec(v_fvar_1733_);
lean_dec(v_bvar_1732_);
v_a_1777_ = lean_ctor_get(v_t_1731_, 0);
lean_inc_ref(v_a_1777_);
lean_dec_ref_known(v_t_1731_, 1);
v___x_1778_ = lean_apply_1(v_lit_1741_, v_a_1777_);
return v___x_1778_;
}
case 10:
{
lean_object* v_data_1779_; lean_object* v_expr_1780_; lean_object* v___x_1781_; 
lean_dec(v_proj_1743_);
lean_dec(v_lit_1741_);
lean_dec(v_letE_1740_);
lean_dec(v_forallE_1739_);
lean_dec(v_lam_1738_);
lean_dec(v_app_1737_);
lean_dec(v_const_1736_);
lean_dec(v_sort_1735_);
lean_dec(v_mvar_1734_);
lean_dec(v_fvar_1733_);
lean_dec(v_bvar_1732_);
v_data_1779_ = lean_ctor_get(v_t_1731_, 0);
lean_inc(v_data_1779_);
v_expr_1780_ = lean_ctor_get(v_t_1731_, 1);
lean_inc_ref(v_expr_1780_);
lean_dec_ref_known(v_t_1731_, 2);
v___x_1781_ = lean_apply_2(v_mdata_1742_, v_data_1779_, v_expr_1780_);
return v___x_1781_;
}
default: 
{
lean_object* v_typeName_1782_; lean_object* v_idx_1783_; lean_object* v_struct_1784_; lean_object* v___x_1785_; 
lean_dec(v_mdata_1742_);
lean_dec(v_lit_1741_);
lean_dec(v_letE_1740_);
lean_dec(v_forallE_1739_);
lean_dec(v_lam_1738_);
lean_dec(v_app_1737_);
lean_dec(v_const_1736_);
lean_dec(v_sort_1735_);
lean_dec(v_mvar_1734_);
lean_dec(v_fvar_1733_);
lean_dec(v_bvar_1732_);
v_typeName_1782_ = lean_ctor_get(v_t_1731_, 0);
lean_inc(v_typeName_1782_);
v_idx_1783_ = lean_ctor_get(v_t_1731_, 1);
lean_inc(v_idx_1783_);
v_struct_1784_ = lean_ctor_get(v_t_1731_, 2);
lean_inc_ref(v_struct_1784_);
lean_dec_ref_known(v_t_1731_, 3);
v___x_1785_ = lean_apply_3(v_proj_1743_, v_typeName_1782_, v_idx_1783_, v_struct_1784_);
return v___x_1785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* v_deBruijnIndex_1786_){
_start:
{
uint64_t v___x_1787_; uint64_t v___x_1788_; uint64_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint32_t v___x_1792_; uint8_t v___x_1793_; uint64_t v___x_1794_; lean_object* v___x_1795_; 
v___x_1787_ = 7ULL;
v___x_1788_ = lean_uint64_of_nat(v_deBruijnIndex_1786_);
v___x_1789_ = lean_uint64_mix_hash(v___x_1787_, v___x_1788_);
v___x_1790_ = lean_unsigned_to_nat(1u);
v___x_1791_ = lean_nat_add(v_deBruijnIndex_1786_, v___x_1790_);
v___x_1792_ = 0;
v___x_1793_ = 0;
v___x_1794_ = lean_expr_mk_data(v___x_1789_, v___x_1791_, v___x_1792_, v___x_1793_, v___x_1793_, v___x_1793_, v___x_1793_);
v___x_1795_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1795_, 0, v_deBruijnIndex_1786_);
lean_ctor_set_uint64(v___x_1795_, sizeof(void*)*1, v___x_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* v_fvarId_1796_){
_start:
{
uint64_t v___x_1797_; uint64_t v___x_1798_; uint64_t v___x_1799_; lean_object* v___x_1800_; uint32_t v___x_1801_; uint8_t v___x_1802_; uint8_t v___x_1803_; uint64_t v___x_1804_; lean_object* v___x_1805_; 
v___x_1797_ = 13ULL;
v___x_1798_ = l_Lean_instHashableFVarId_hash(v_fvarId_1796_);
v___x_1799_ = lean_uint64_mix_hash(v___x_1797_, v___x_1798_);
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = 0;
v___x_1802_ = 1;
v___x_1803_ = 0;
v___x_1804_ = lean_expr_mk_data(v___x_1799_, v___x_1800_, v___x_1801_, v___x_1802_, v___x_1803_, v___x_1803_, v___x_1803_);
v___x_1805_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_1805_, 0, v_fvarId_1796_);
lean_ctor_set_uint64(v___x_1805_, sizeof(void*)*1, v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* v_mvarId_1806_){
_start:
{
uint64_t v___x_1807_; uint64_t v___x_1808_; uint64_t v___x_1809_; lean_object* v___x_1810_; uint32_t v___x_1811_; uint8_t v___x_1812_; uint8_t v___x_1813_; uint64_t v___x_1814_; lean_object* v___x_1815_; 
v___x_1807_ = 17ULL;
v___x_1808_ = l_Lean_instHashableMVarId_hash(v_mvarId_1806_);
v___x_1809_ = lean_uint64_mix_hash(v___x_1807_, v___x_1808_);
v___x_1810_ = lean_unsigned_to_nat(0u);
v___x_1811_ = 0;
v___x_1812_ = 0;
v___x_1813_ = 1;
v___x_1814_ = lean_expr_mk_data(v___x_1809_, v___x_1810_, v___x_1811_, v___x_1812_, v___x_1813_, v___x_1812_, v___x_1812_);
v___x_1815_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_1815_, 0, v_mvarId_1806_);
lean_ctor_set_uint64(v___x_1815_, sizeof(void*)*1, v___x_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* v_u_1816_){
_start:
{
uint64_t v___x_1817_; uint64_t v___x_1818_; uint64_t v___x_1819_; lean_object* v___x_1820_; uint32_t v___x_1821_; uint8_t v___x_1822_; uint8_t v___x_1823_; uint8_t v___x_1824_; uint64_t v___x_1825_; lean_object* v___x_1826_; 
v___x_1817_ = 11ULL;
v___x_1818_ = l_Lean_Level_hash(v_u_1816_);
v___x_1819_ = lean_uint64_mix_hash(v___x_1817_, v___x_1818_);
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = 0;
v___x_1822_ = 0;
v___x_1823_ = l_Lean_Level_hasMVar(v_u_1816_);
v___x_1824_ = l_Lean_Level_hasParam(v_u_1816_);
v___x_1825_ = lean_expr_mk_data(v___x_1819_, v___x_1820_, v___x_1821_, v___x_1822_, v___x_1822_, v___x_1823_, v___x_1824_);
v___x_1826_ = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(v___x_1826_, 0, v_u_1816_);
lean_ctor_set_uint64(v___x_1826_, sizeof(void*)*1, v___x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* v_fn_1827_, lean_object* v_arg_1828_){
_start:
{
uint64_t v___x_1829_; uint64_t v___x_1830_; uint64_t v___x_1831_; lean_object* v___x_1832_; 
v___x_1829_ = lean_expr_data(v_fn_1827_);
v___x_1830_ = lean_expr_data(v_arg_1828_);
v___x_1831_ = lean_expr_mk_app_data(v___x_1829_, v___x_1830_);
v___x_1832_ = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(v___x_1832_, 0, v_fn_1827_);
lean_ctor_set(v___x_1832_, 1, v_arg_1828_);
lean_ctor_set_uint64(v___x_1832_, sizeof(void*)*2, v___x_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object* v_binderName_1833_, lean_object* v_binderType_1834_, lean_object* v_body_1835_, uint8_t v_binderInfo_1836_){
_start:
{
uint64_t v___y_1838_; uint8_t v___y_1839_; uint8_t v___y_1840_; uint8_t v___y_1841_; lean_object* v___y_1842_; uint32_t v___y_1843_; uint8_t v___y_1844_; uint64_t v___x_1847_; uint8_t v___x_1848_; uint32_t v___x_1849_; uint64_t v___x_1850_; uint64_t v___y_1852_; uint8_t v___y_1853_; uint8_t v___y_1854_; lean_object* v___y_1855_; uint32_t v___y_1856_; uint8_t v___y_1857_; uint64_t v___y_1861_; uint8_t v___y_1862_; lean_object* v___y_1863_; uint32_t v___y_1864_; uint8_t v___y_1865_; uint64_t v___y_1869_; lean_object* v___y_1870_; uint32_t v___y_1871_; uint8_t v___y_1872_; uint64_t v___y_1876_; uint32_t v___y_1877_; lean_object* v___y_1878_; uint32_t v___y_1882_; uint8_t v___x_1897_; uint32_t v___x_1898_; uint8_t v___x_1899_; 
v___x_1847_ = lean_expr_data(v_binderType_1834_);
v___x_1848_ = l_Lean_Expr_Data_approxDepth(v___x_1847_);
v___x_1849_ = lean_uint8_to_uint32(v___x_1848_);
v___x_1850_ = lean_expr_data(v_body_1835_);
v___x_1897_ = l_Lean_Expr_Data_approxDepth(v___x_1850_);
v___x_1898_ = lean_uint8_to_uint32(v___x_1897_);
v___x_1899_ = lean_uint32_dec_le(v___x_1849_, v___x_1898_);
if (v___x_1899_ == 0)
{
v___y_1882_ = v___x_1849_;
goto v___jp_1881_;
}
else
{
v___y_1882_ = v___x_1898_;
goto v___jp_1881_;
}
v___jp_1837_:
{
uint64_t v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = lean_expr_mk_data(v___y_1838_, v___y_1842_, v___y_1843_, v___y_1841_, v___y_1840_, v___y_1839_, v___y_1844_);
v___x_1846_ = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(v___x_1846_, 0, v_binderName_1833_);
lean_ctor_set(v___x_1846_, 1, v_binderType_1834_);
lean_ctor_set(v___x_1846_, 2, v_body_1835_);
lean_ctor_set_uint64(v___x_1846_, sizeof(void*)*3, v___x_1845_);
lean_ctor_set_uint8(v___x_1846_, sizeof(void*)*3 + 8, v_binderInfo_1836_);
return v___x_1846_;
}
v___jp_1851_:
{
uint8_t v___x_1858_; 
v___x_1858_ = l_Lean_Expr_Data_hasLevelParam(v___x_1847_);
if (v___x_1858_ == 0)
{
uint8_t v___x_1859_; 
v___x_1859_ = l_Lean_Expr_Data_hasLevelParam(v___x_1850_);
v___y_1838_ = v___y_1852_;
v___y_1839_ = v___y_1857_;
v___y_1840_ = v___y_1854_;
v___y_1841_ = v___y_1853_;
v___y_1842_ = v___y_1855_;
v___y_1843_ = v___y_1856_;
v___y_1844_ = v___x_1859_;
goto v___jp_1837_;
}
else
{
v___y_1838_ = v___y_1852_;
v___y_1839_ = v___y_1857_;
v___y_1840_ = v___y_1854_;
v___y_1841_ = v___y_1853_;
v___y_1842_ = v___y_1855_;
v___y_1843_ = v___y_1856_;
v___y_1844_ = v___x_1858_;
goto v___jp_1837_;
}
}
v___jp_1860_:
{
uint8_t v___x_1866_; 
v___x_1866_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1847_);
if (v___x_1866_ == 0)
{
uint8_t v___x_1867_; 
v___x_1867_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1850_);
v___y_1852_ = v___y_1861_;
v___y_1853_ = v___y_1862_;
v___y_1854_ = v___y_1865_;
v___y_1855_ = v___y_1863_;
v___y_1856_ = v___y_1864_;
v___y_1857_ = v___x_1867_;
goto v___jp_1851_;
}
else
{
v___y_1852_ = v___y_1861_;
v___y_1853_ = v___y_1862_;
v___y_1854_ = v___y_1865_;
v___y_1855_ = v___y_1863_;
v___y_1856_ = v___y_1864_;
v___y_1857_ = v___x_1866_;
goto v___jp_1851_;
}
}
v___jp_1868_:
{
uint8_t v___x_1873_; 
v___x_1873_ = l_Lean_Expr_Data_hasExprMVar(v___x_1847_);
if (v___x_1873_ == 0)
{
uint8_t v___x_1874_; 
v___x_1874_ = l_Lean_Expr_Data_hasExprMVar(v___x_1850_);
v___y_1861_ = v___y_1869_;
v___y_1862_ = v___y_1872_;
v___y_1863_ = v___y_1870_;
v___y_1864_ = v___y_1871_;
v___y_1865_ = v___x_1874_;
goto v___jp_1860_;
}
else
{
v___y_1861_ = v___y_1869_;
v___y_1862_ = v___y_1872_;
v___y_1863_ = v___y_1870_;
v___y_1864_ = v___y_1871_;
v___y_1865_ = v___x_1873_;
goto v___jp_1860_;
}
}
v___jp_1875_:
{
uint8_t v___x_1879_; 
v___x_1879_ = l_Lean_Expr_Data_hasFVar(v___x_1847_);
if (v___x_1879_ == 0)
{
uint8_t v___x_1880_; 
v___x_1880_ = l_Lean_Expr_Data_hasFVar(v___x_1850_);
v___y_1869_ = v___y_1876_;
v___y_1870_ = v___y_1878_;
v___y_1871_ = v___y_1877_;
v___y_1872_ = v___x_1880_;
goto v___jp_1868_;
}
else
{
v___y_1869_ = v___y_1876_;
v___y_1870_ = v___y_1878_;
v___y_1871_ = v___y_1877_;
v___y_1872_ = v___x_1879_;
goto v___jp_1868_;
}
}
v___jp_1881_:
{
lean_object* v___x_1883_; uint32_t v___x_1884_; uint32_t v___x_1885_; uint64_t v___x_1886_; uint64_t v___x_1887_; uint64_t v___x_1888_; uint64_t v___x_1889_; uint64_t v___x_1890_; uint32_t v___x_1891_; lean_object* v___x_1892_; uint32_t v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1883_ = lean_unsigned_to_nat(1u);
v___x_1884_ = 1;
v___x_1885_ = lean_uint32_add(v___y_1882_, v___x_1884_);
v___x_1886_ = lean_uint32_to_uint64(v___x_1885_);
v___x_1887_ = l_Lean_Expr_Data_hash(v___x_1847_);
v___x_1888_ = l_Lean_Expr_Data_hash(v___x_1850_);
v___x_1889_ = lean_uint64_mix_hash(v___x_1887_, v___x_1888_);
v___x_1890_ = lean_uint64_mix_hash(v___x_1886_, v___x_1889_);
v___x_1891_ = l_Lean_Expr_Data_looseBVarRange(v___x_1847_);
v___x_1892_ = lean_uint32_to_nat(v___x_1891_);
v___x_1893_ = l_Lean_Expr_Data_looseBVarRange(v___x_1850_);
v___x_1894_ = lean_uint32_to_nat(v___x_1893_);
v___x_1895_ = lean_nat_sub(v___x_1894_, v___x_1883_);
lean_dec(v___x_1894_);
v___x_1896_ = lean_nat_dec_le(v___x_1892_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_dec(v___x_1895_);
v___y_1876_ = v___x_1890_;
v___y_1877_ = v___x_1885_;
v___y_1878_ = v___x_1892_;
goto v___jp_1875_;
}
else
{
lean_dec(v___x_1892_);
v___y_1876_ = v___x_1890_;
v___y_1877_ = v___x_1885_;
v___y_1878_ = v___x_1895_;
goto v___jp_1875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* v_binderName_1900_, lean_object* v_binderType_1901_, lean_object* v_body_1902_, lean_object* v_binderInfo_1903_){
_start:
{
uint8_t v_binderInfo_boxed_1904_; lean_object* v_res_1905_; 
v_binderInfo_boxed_1904_ = lean_unbox(v_binderInfo_1903_);
v_res_1905_ = l_Lean_Expr_lam___override(v_binderName_1900_, v_binderType_1901_, v_body_1902_, v_binderInfo_boxed_1904_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object* v_binderName_1906_, lean_object* v_binderType_1907_, lean_object* v_body_1908_, uint8_t v_binderInfo_1909_){
_start:
{
uint64_t v___y_1911_; uint8_t v___y_1912_; lean_object* v___y_1913_; uint32_t v___y_1914_; uint8_t v___y_1915_; uint8_t v___y_1916_; uint8_t v___y_1917_; uint64_t v___x_1920_; uint8_t v___x_1921_; uint32_t v___x_1922_; uint64_t v___x_1923_; uint64_t v___y_1925_; uint8_t v___y_1926_; lean_object* v___y_1927_; uint32_t v___y_1928_; uint8_t v___y_1929_; uint8_t v___y_1930_; uint64_t v___y_1934_; uint8_t v___y_1935_; lean_object* v___y_1936_; uint32_t v___y_1937_; uint8_t v___y_1938_; uint64_t v___y_1942_; lean_object* v___y_1943_; uint32_t v___y_1944_; uint8_t v___y_1945_; uint64_t v___y_1949_; uint32_t v___y_1950_; lean_object* v___y_1951_; uint32_t v___y_1955_; uint8_t v___x_1970_; uint32_t v___x_1971_; uint8_t v___x_1972_; 
v___x_1920_ = lean_expr_data(v_binderType_1907_);
v___x_1921_ = l_Lean_Expr_Data_approxDepth(v___x_1920_);
v___x_1922_ = lean_uint8_to_uint32(v___x_1921_);
v___x_1923_ = lean_expr_data(v_body_1908_);
v___x_1970_ = l_Lean_Expr_Data_approxDepth(v___x_1923_);
v___x_1971_ = lean_uint8_to_uint32(v___x_1970_);
v___x_1972_ = lean_uint32_dec_le(v___x_1922_, v___x_1971_);
if (v___x_1972_ == 0)
{
v___y_1955_ = v___x_1922_;
goto v___jp_1954_;
}
else
{
v___y_1955_ = v___x_1971_;
goto v___jp_1954_;
}
v___jp_1910_:
{
uint64_t v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_expr_mk_data(v___y_1911_, v___y_1913_, v___y_1914_, v___y_1912_, v___y_1916_, v___y_1915_, v___y_1917_);
v___x_1919_ = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(v___x_1919_, 0, v_binderName_1906_);
lean_ctor_set(v___x_1919_, 1, v_binderType_1907_);
lean_ctor_set(v___x_1919_, 2, v_body_1908_);
lean_ctor_set_uint64(v___x_1919_, sizeof(void*)*3, v___x_1918_);
lean_ctor_set_uint8(v___x_1919_, sizeof(void*)*3 + 8, v_binderInfo_1909_);
return v___x_1919_;
}
v___jp_1924_:
{
uint8_t v___x_1931_; 
v___x_1931_ = l_Lean_Expr_Data_hasLevelParam(v___x_1920_);
if (v___x_1931_ == 0)
{
uint8_t v___x_1932_; 
v___x_1932_ = l_Lean_Expr_Data_hasLevelParam(v___x_1923_);
v___y_1911_ = v___y_1925_;
v___y_1912_ = v___y_1926_;
v___y_1913_ = v___y_1927_;
v___y_1914_ = v___y_1928_;
v___y_1915_ = v___y_1930_;
v___y_1916_ = v___y_1929_;
v___y_1917_ = v___x_1932_;
goto v___jp_1910_;
}
else
{
v___y_1911_ = v___y_1925_;
v___y_1912_ = v___y_1926_;
v___y_1913_ = v___y_1927_;
v___y_1914_ = v___y_1928_;
v___y_1915_ = v___y_1930_;
v___y_1916_ = v___y_1929_;
v___y_1917_ = v___x_1931_;
goto v___jp_1910_;
}
}
v___jp_1933_:
{
uint8_t v___x_1939_; 
v___x_1939_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1920_);
if (v___x_1939_ == 0)
{
uint8_t v___x_1940_; 
v___x_1940_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1923_);
v___y_1925_ = v___y_1934_;
v___y_1926_ = v___y_1935_;
v___y_1927_ = v___y_1936_;
v___y_1928_ = v___y_1937_;
v___y_1929_ = v___y_1938_;
v___y_1930_ = v___x_1940_;
goto v___jp_1924_;
}
else
{
v___y_1925_ = v___y_1934_;
v___y_1926_ = v___y_1935_;
v___y_1927_ = v___y_1936_;
v___y_1928_ = v___y_1937_;
v___y_1929_ = v___y_1938_;
v___y_1930_ = v___x_1939_;
goto v___jp_1924_;
}
}
v___jp_1941_:
{
uint8_t v___x_1946_; 
v___x_1946_ = l_Lean_Expr_Data_hasExprMVar(v___x_1920_);
if (v___x_1946_ == 0)
{
uint8_t v___x_1947_; 
v___x_1947_ = l_Lean_Expr_Data_hasExprMVar(v___x_1923_);
v___y_1934_ = v___y_1942_;
v___y_1935_ = v___y_1945_;
v___y_1936_ = v___y_1943_;
v___y_1937_ = v___y_1944_;
v___y_1938_ = v___x_1947_;
goto v___jp_1933_;
}
else
{
v___y_1934_ = v___y_1942_;
v___y_1935_ = v___y_1945_;
v___y_1936_ = v___y_1943_;
v___y_1937_ = v___y_1944_;
v___y_1938_ = v___x_1946_;
goto v___jp_1933_;
}
}
v___jp_1948_:
{
uint8_t v___x_1952_; 
v___x_1952_ = l_Lean_Expr_Data_hasFVar(v___x_1920_);
if (v___x_1952_ == 0)
{
uint8_t v___x_1953_; 
v___x_1953_ = l_Lean_Expr_Data_hasFVar(v___x_1923_);
v___y_1942_ = v___y_1949_;
v___y_1943_ = v___y_1951_;
v___y_1944_ = v___y_1950_;
v___y_1945_ = v___x_1953_;
goto v___jp_1941_;
}
else
{
v___y_1942_ = v___y_1949_;
v___y_1943_ = v___y_1951_;
v___y_1944_ = v___y_1950_;
v___y_1945_ = v___x_1952_;
goto v___jp_1941_;
}
}
v___jp_1954_:
{
lean_object* v___x_1956_; uint32_t v___x_1957_; uint32_t v___x_1958_; uint64_t v___x_1959_; uint64_t v___x_1960_; uint64_t v___x_1961_; uint64_t v___x_1962_; uint64_t v___x_1963_; uint32_t v___x_1964_; lean_object* v___x_1965_; uint32_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1956_ = lean_unsigned_to_nat(1u);
v___x_1957_ = 1;
v___x_1958_ = lean_uint32_add(v___y_1955_, v___x_1957_);
v___x_1959_ = lean_uint32_to_uint64(v___x_1958_);
v___x_1960_ = l_Lean_Expr_Data_hash(v___x_1920_);
v___x_1961_ = l_Lean_Expr_Data_hash(v___x_1923_);
v___x_1962_ = lean_uint64_mix_hash(v___x_1960_, v___x_1961_);
v___x_1963_ = lean_uint64_mix_hash(v___x_1959_, v___x_1962_);
v___x_1964_ = l_Lean_Expr_Data_looseBVarRange(v___x_1920_);
v___x_1965_ = lean_uint32_to_nat(v___x_1964_);
v___x_1966_ = l_Lean_Expr_Data_looseBVarRange(v___x_1923_);
v___x_1967_ = lean_uint32_to_nat(v___x_1966_);
v___x_1968_ = lean_nat_sub(v___x_1967_, v___x_1956_);
lean_dec(v___x_1967_);
v___x_1969_ = lean_nat_dec_le(v___x_1965_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_dec(v___x_1968_);
v___y_1949_ = v___x_1963_;
v___y_1950_ = v___x_1958_;
v___y_1951_ = v___x_1965_;
goto v___jp_1948_;
}
else
{
lean_dec(v___x_1965_);
v___y_1949_ = v___x_1963_;
v___y_1950_ = v___x_1958_;
v___y_1951_ = v___x_1968_;
goto v___jp_1948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* v_binderName_1973_, lean_object* v_binderType_1974_, lean_object* v_body_1975_, lean_object* v_binderInfo_1976_){
_start:
{
uint8_t v_binderInfo_boxed_1977_; lean_object* v_res_1978_; 
v_binderInfo_boxed_1977_ = lean_unbox(v_binderInfo_1976_);
v_res_1978_ = l_Lean_Expr_forallE___override(v_binderName_1973_, v_binderType_1974_, v_body_1975_, v_binderInfo_boxed_1977_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object* v_declName_1979_, lean_object* v_type_1980_, lean_object* v_value_1981_, lean_object* v_body_1982_, uint8_t v_nondep_1983_){
_start:
{
uint8_t v___y_1985_; lean_object* v___y_1986_; uint32_t v___y_1987_; uint64_t v___y_1988_; uint8_t v___y_1989_; uint8_t v___y_1990_; uint8_t v___y_1991_; uint8_t v___y_1995_; lean_object* v___y_1996_; uint64_t v___y_1997_; uint32_t v___y_1998_; uint64_t v___y_1999_; uint8_t v___y_2000_; uint8_t v___y_2001_; uint8_t v___y_2002_; uint64_t v___x_2004_; uint8_t v___x_2005_; uint32_t v___x_2006_; uint64_t v___x_2007_; uint8_t v___y_2009_; lean_object* v___y_2010_; uint64_t v___y_2011_; uint32_t v___y_2012_; uint64_t v___y_2013_; uint8_t v___y_2014_; uint8_t v___y_2015_; uint8_t v___y_2019_; lean_object* v___y_2020_; uint64_t v___y_2021_; uint32_t v___y_2022_; uint64_t v___y_2023_; uint8_t v___y_2024_; uint8_t v___y_2025_; uint8_t v___y_2028_; lean_object* v___y_2029_; uint64_t v___y_2030_; uint32_t v___y_2031_; uint64_t v___y_2032_; uint8_t v___y_2033_; uint8_t v___y_2037_; lean_object* v___y_2038_; uint64_t v___y_2039_; uint32_t v___y_2040_; uint64_t v___y_2041_; uint8_t v___y_2042_; lean_object* v___y_2045_; uint64_t v___y_2046_; uint32_t v___y_2047_; uint64_t v___y_2048_; uint8_t v___y_2049_; lean_object* v___y_2053_; uint64_t v___y_2054_; uint32_t v___y_2055_; uint64_t v___y_2056_; uint8_t v___y_2057_; uint64_t v___y_2060_; uint32_t v___y_2061_; uint64_t v___y_2062_; lean_object* v___y_2063_; uint64_t v___y_2067_; uint32_t v___y_2068_; uint64_t v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; uint64_t v___y_2077_; uint32_t v___y_2078_; uint32_t v___y_2095_; uint8_t v___x_2100_; uint32_t v___x_2101_; uint8_t v___x_2102_; 
v___x_2004_ = lean_expr_data(v_type_1980_);
v___x_2005_ = l_Lean_Expr_Data_approxDepth(v___x_2004_);
v___x_2006_ = lean_uint8_to_uint32(v___x_2005_);
v___x_2007_ = lean_expr_data(v_value_1981_);
v___x_2100_ = l_Lean_Expr_Data_approxDepth(v___x_2007_);
v___x_2101_ = lean_uint8_to_uint32(v___x_2100_);
v___x_2102_ = lean_uint32_dec_le(v___x_2006_, v___x_2101_);
if (v___x_2102_ == 0)
{
v___y_2095_ = v___x_2006_;
goto v___jp_2094_;
}
else
{
v___y_2095_ = v___x_2101_;
goto v___jp_2094_;
}
v___jp_1984_:
{
uint64_t v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_expr_mk_data(v___y_1988_, v___y_1986_, v___y_1987_, v___y_1985_, v___y_1990_, v___y_1989_, v___y_1991_);
v___x_1993_ = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(v___x_1993_, 0, v_declName_1979_);
lean_ctor_set(v___x_1993_, 1, v_type_1980_);
lean_ctor_set(v___x_1993_, 2, v_value_1981_);
lean_ctor_set(v___x_1993_, 3, v_body_1982_);
lean_ctor_set_uint64(v___x_1993_, sizeof(void*)*4, v___x_1992_);
lean_ctor_set_uint8(v___x_1993_, sizeof(void*)*4 + 8, v_nondep_1983_);
return v___x_1993_;
}
v___jp_1994_:
{
if (v___y_2002_ == 0)
{
uint8_t v___x_2003_; 
v___x_2003_ = l_Lean_Expr_Data_hasLevelParam(v___y_1997_);
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1998_;
v___y_1988_ = v___y_1999_;
v___y_1989_ = v___y_2000_;
v___y_1990_ = v___y_2001_;
v___y_1991_ = v___x_2003_;
goto v___jp_1984_;
}
else
{
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1998_;
v___y_1988_ = v___y_1999_;
v___y_1989_ = v___y_2000_;
v___y_1990_ = v___y_2001_;
v___y_1991_ = v___y_2002_;
goto v___jp_1984_;
}
}
v___jp_2008_:
{
uint8_t v___x_2016_; 
v___x_2016_ = l_Lean_Expr_Data_hasLevelParam(v___x_2004_);
if (v___x_2016_ == 0)
{
uint8_t v___x_2017_; 
v___x_2017_ = l_Lean_Expr_Data_hasLevelParam(v___x_2007_);
v___y_1995_ = v___y_2009_;
v___y_1996_ = v___y_2010_;
v___y_1997_ = v___y_2011_;
v___y_1998_ = v___y_2012_;
v___y_1999_ = v___y_2013_;
v___y_2000_ = v___y_2015_;
v___y_2001_ = v___y_2014_;
v___y_2002_ = v___x_2017_;
goto v___jp_1994_;
}
else
{
v___y_1995_ = v___y_2009_;
v___y_1996_ = v___y_2010_;
v___y_1997_ = v___y_2011_;
v___y_1998_ = v___y_2012_;
v___y_1999_ = v___y_2013_;
v___y_2000_ = v___y_2015_;
v___y_2001_ = v___y_2014_;
v___y_2002_ = v___x_2016_;
goto v___jp_1994_;
}
}
v___jp_2018_:
{
if (v___y_2025_ == 0)
{
uint8_t v___x_2026_; 
v___x_2026_ = l_Lean_Expr_Data_hasLevelMVar(v___y_2021_);
v___y_2009_ = v___y_2019_;
v___y_2010_ = v___y_2020_;
v___y_2011_ = v___y_2021_;
v___y_2012_ = v___y_2022_;
v___y_2013_ = v___y_2023_;
v___y_2014_ = v___y_2024_;
v___y_2015_ = v___x_2026_;
goto v___jp_2008_;
}
else
{
v___y_2009_ = v___y_2019_;
v___y_2010_ = v___y_2020_;
v___y_2011_ = v___y_2021_;
v___y_2012_ = v___y_2022_;
v___y_2013_ = v___y_2023_;
v___y_2014_ = v___y_2024_;
v___y_2015_ = v___y_2025_;
goto v___jp_2008_;
}
}
v___jp_2027_:
{
uint8_t v___x_2034_; 
v___x_2034_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2004_);
if (v___x_2034_ == 0)
{
uint8_t v___x_2035_; 
v___x_2035_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2007_);
v___y_2019_ = v___y_2028_;
v___y_2020_ = v___y_2029_;
v___y_2021_ = v___y_2030_;
v___y_2022_ = v___y_2031_;
v___y_2023_ = v___y_2032_;
v___y_2024_ = v___y_2033_;
v___y_2025_ = v___x_2035_;
goto v___jp_2018_;
}
else
{
v___y_2019_ = v___y_2028_;
v___y_2020_ = v___y_2029_;
v___y_2021_ = v___y_2030_;
v___y_2022_ = v___y_2031_;
v___y_2023_ = v___y_2032_;
v___y_2024_ = v___y_2033_;
v___y_2025_ = v___x_2034_;
goto v___jp_2018_;
}
}
v___jp_2036_:
{
if (v___y_2042_ == 0)
{
uint8_t v___x_2043_; 
v___x_2043_ = l_Lean_Expr_Data_hasExprMVar(v___y_2039_);
v___y_2028_ = v___y_2037_;
v___y_2029_ = v___y_2038_;
v___y_2030_ = v___y_2039_;
v___y_2031_ = v___y_2040_;
v___y_2032_ = v___y_2041_;
v___y_2033_ = v___x_2043_;
goto v___jp_2027_;
}
else
{
v___y_2028_ = v___y_2037_;
v___y_2029_ = v___y_2038_;
v___y_2030_ = v___y_2039_;
v___y_2031_ = v___y_2040_;
v___y_2032_ = v___y_2041_;
v___y_2033_ = v___y_2042_;
goto v___jp_2027_;
}
}
v___jp_2044_:
{
uint8_t v___x_2050_; 
v___x_2050_ = l_Lean_Expr_Data_hasExprMVar(v___x_2004_);
if (v___x_2050_ == 0)
{
uint8_t v___x_2051_; 
v___x_2051_ = l_Lean_Expr_Data_hasExprMVar(v___x_2007_);
v___y_2037_ = v___y_2049_;
v___y_2038_ = v___y_2045_;
v___y_2039_ = v___y_2046_;
v___y_2040_ = v___y_2047_;
v___y_2041_ = v___y_2048_;
v___y_2042_ = v___x_2051_;
goto v___jp_2036_;
}
else
{
v___y_2037_ = v___y_2049_;
v___y_2038_ = v___y_2045_;
v___y_2039_ = v___y_2046_;
v___y_2040_ = v___y_2047_;
v___y_2041_ = v___y_2048_;
v___y_2042_ = v___x_2050_;
goto v___jp_2036_;
}
}
v___jp_2052_:
{
if (v___y_2057_ == 0)
{
uint8_t v___x_2058_; 
v___x_2058_ = l_Lean_Expr_Data_hasFVar(v___y_2054_);
v___y_2045_ = v___y_2053_;
v___y_2046_ = v___y_2054_;
v___y_2047_ = v___y_2055_;
v___y_2048_ = v___y_2056_;
v___y_2049_ = v___x_2058_;
goto v___jp_2044_;
}
else
{
v___y_2045_ = v___y_2053_;
v___y_2046_ = v___y_2054_;
v___y_2047_ = v___y_2055_;
v___y_2048_ = v___y_2056_;
v___y_2049_ = v___y_2057_;
goto v___jp_2044_;
}
}
v___jp_2059_:
{
uint8_t v___x_2064_; 
v___x_2064_ = l_Lean_Expr_Data_hasFVar(v___x_2004_);
if (v___x_2064_ == 0)
{
uint8_t v___x_2065_; 
v___x_2065_ = l_Lean_Expr_Data_hasFVar(v___x_2007_);
v___y_2053_ = v___y_2063_;
v___y_2054_ = v___y_2060_;
v___y_2055_ = v___y_2061_;
v___y_2056_ = v___y_2062_;
v___y_2057_ = v___x_2065_;
goto v___jp_2052_;
}
else
{
v___y_2053_ = v___y_2063_;
v___y_2054_ = v___y_2060_;
v___y_2055_ = v___y_2061_;
v___y_2056_ = v___y_2062_;
v___y_2057_ = v___x_2064_;
goto v___jp_2052_;
}
}
v___jp_2066_:
{
uint32_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2072_ = l_Lean_Expr_Data_looseBVarRange(v___y_2067_);
v___x_2073_ = lean_uint32_to_nat(v___x_2072_);
v___x_2074_ = lean_nat_sub(v___x_2073_, v___y_2070_);
lean_dec(v___x_2073_);
v___x_2075_ = lean_nat_dec_le(v___y_2071_, v___x_2074_);
if (v___x_2075_ == 0)
{
lean_dec(v___x_2074_);
v___y_2060_ = v___y_2067_;
v___y_2061_ = v___y_2068_;
v___y_2062_ = v___y_2069_;
v___y_2063_ = v___y_2071_;
goto v___jp_2059_;
}
else
{
lean_dec(v___y_2071_);
v___y_2060_ = v___y_2067_;
v___y_2061_ = v___y_2068_;
v___y_2062_ = v___y_2069_;
v___y_2063_ = v___x_2074_;
goto v___jp_2059_;
}
}
v___jp_2076_:
{
lean_object* v___x_2079_; uint32_t v___x_2080_; uint32_t v___x_2081_; uint64_t v___x_2082_; uint64_t v___x_2083_; uint64_t v___x_2084_; uint64_t v___x_2085_; uint64_t v___x_2086_; uint64_t v___x_2087_; uint64_t v___x_2088_; uint32_t v___x_2089_; lean_object* v___x_2090_; uint32_t v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2079_ = lean_unsigned_to_nat(1u);
v___x_2080_ = 1;
v___x_2081_ = lean_uint32_add(v___y_2078_, v___x_2080_);
v___x_2082_ = lean_uint32_to_uint64(v___x_2081_);
v___x_2083_ = l_Lean_Expr_Data_hash(v___x_2004_);
v___x_2084_ = l_Lean_Expr_Data_hash(v___x_2007_);
v___x_2085_ = l_Lean_Expr_Data_hash(v___y_2077_);
v___x_2086_ = lean_uint64_mix_hash(v___x_2084_, v___x_2085_);
v___x_2087_ = lean_uint64_mix_hash(v___x_2083_, v___x_2086_);
v___x_2088_ = lean_uint64_mix_hash(v___x_2082_, v___x_2087_);
v___x_2089_ = l_Lean_Expr_Data_looseBVarRange(v___x_2004_);
v___x_2090_ = lean_uint32_to_nat(v___x_2089_);
v___x_2091_ = l_Lean_Expr_Data_looseBVarRange(v___x_2007_);
v___x_2092_ = lean_uint32_to_nat(v___x_2091_);
v___x_2093_ = lean_nat_dec_le(v___x_2090_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_dec(v___x_2092_);
v___y_2067_ = v___y_2077_;
v___y_2068_ = v___x_2081_;
v___y_2069_ = v___x_2088_;
v___y_2070_ = v___x_2079_;
v___y_2071_ = v___x_2090_;
goto v___jp_2066_;
}
else
{
lean_dec(v___x_2090_);
v___y_2067_ = v___y_2077_;
v___y_2068_ = v___x_2081_;
v___y_2069_ = v___x_2088_;
v___y_2070_ = v___x_2079_;
v___y_2071_ = v___x_2092_;
goto v___jp_2066_;
}
}
v___jp_2094_:
{
uint64_t v___x_2096_; uint8_t v___x_2097_; uint32_t v___x_2098_; uint8_t v___x_2099_; 
v___x_2096_ = lean_expr_data(v_body_1982_);
v___x_2097_ = l_Lean_Expr_Data_approxDepth(v___x_2096_);
v___x_2098_ = lean_uint8_to_uint32(v___x_2097_);
v___x_2099_ = lean_uint32_dec_le(v___y_2095_, v___x_2098_);
if (v___x_2099_ == 0)
{
v___y_2077_ = v___x_2096_;
v___y_2078_ = v___y_2095_;
goto v___jp_2076_;
}
else
{
v___y_2077_ = v___x_2096_;
v___y_2078_ = v___x_2098_;
goto v___jp_2076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* v_declName_2103_, lean_object* v_type_2104_, lean_object* v_value_2105_, lean_object* v_body_2106_, lean_object* v_nondep_2107_){
_start:
{
uint8_t v_nondep_boxed_2108_; lean_object* v_res_2109_; 
v_nondep_boxed_2108_ = lean_unbox(v_nondep_2107_);
v_res_2109_ = l_Lean_Expr_letE___override(v_declName_2103_, v_type_2104_, v_value_2105_, v_body_2106_, v_nondep_boxed_2108_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* v_a_2110_){
_start:
{
uint64_t v___x_2111_; uint64_t v___x_2112_; uint64_t v___x_2113_; lean_object* v___x_2114_; uint32_t v___x_2115_; uint8_t v___x_2116_; uint64_t v___x_2117_; lean_object* v___x_2118_; 
v___x_2111_ = 3ULL;
v___x_2112_ = l_Lean_Literal_hash(v_a_2110_);
v___x_2113_ = lean_uint64_mix_hash(v___x_2111_, v___x_2112_);
v___x_2114_ = lean_unsigned_to_nat(0u);
v___x_2115_ = 0;
v___x_2116_ = 0;
v___x_2117_ = lean_expr_mk_data(v___x_2113_, v___x_2114_, v___x_2115_, v___x_2116_, v___x_2116_, v___x_2116_, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(v___x_2118_, 0, v_a_2110_);
lean_ctor_set_uint64(v___x_2118_, sizeof(void*)*1, v___x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* v_data_2119_, lean_object* v_expr_2120_){
_start:
{
uint64_t v___x_2121_; uint8_t v___x_2122_; uint32_t v___x_2123_; uint32_t v___x_2124_; uint32_t v___x_2125_; uint64_t v___x_2126_; uint64_t v___x_2127_; uint64_t v___x_2128_; uint32_t v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; uint8_t v___x_2132_; uint8_t v___x_2133_; uint8_t v___x_2134_; uint64_t v___x_2135_; lean_object* v___x_2136_; 
v___x_2121_ = lean_expr_data(v_expr_2120_);
v___x_2122_ = l_Lean_Expr_Data_approxDepth(v___x_2121_);
v___x_2123_ = lean_uint8_to_uint32(v___x_2122_);
v___x_2124_ = 1;
v___x_2125_ = lean_uint32_add(v___x_2123_, v___x_2124_);
v___x_2126_ = lean_uint32_to_uint64(v___x_2125_);
v___x_2127_ = l_Lean_Expr_Data_hash(v___x_2121_);
v___x_2128_ = lean_uint64_mix_hash(v___x_2126_, v___x_2127_);
v___x_2129_ = l_Lean_Expr_Data_looseBVarRange(v___x_2121_);
v___x_2130_ = lean_uint32_to_nat(v___x_2129_);
v___x_2131_ = l_Lean_Expr_Data_hasFVar(v___x_2121_);
v___x_2132_ = l_Lean_Expr_Data_hasExprMVar(v___x_2121_);
v___x_2133_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2121_);
v___x_2134_ = l_Lean_Expr_Data_hasLevelParam(v___x_2121_);
v___x_2135_ = lean_expr_mk_data(v___x_2128_, v___x_2130_, v___x_2125_, v___x_2131_, v___x_2132_, v___x_2133_, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(v___x_2136_, 0, v_data_2119_);
lean_ctor_set(v___x_2136_, 1, v_expr_2120_);
lean_ctor_set_uint64(v___x_2136_, sizeof(void*)*2, v___x_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* v_typeName_2137_, lean_object* v_idx_2138_, lean_object* v_struct_2139_){
_start:
{
uint64_t v___x_2140_; uint8_t v___x_2141_; uint32_t v___x_2142_; uint32_t v___x_2143_; uint32_t v___x_2144_; uint64_t v___x_2145_; uint64_t v___y_2147_; 
v___x_2140_ = lean_expr_data(v_struct_2139_);
v___x_2141_ = l_Lean_Expr_Data_approxDepth(v___x_2140_);
v___x_2142_ = lean_uint8_to_uint32(v___x_2141_);
v___x_2143_ = 1;
v___x_2144_ = lean_uint32_add(v___x_2142_, v___x_2143_);
v___x_2145_ = lean_uint32_to_uint64(v___x_2144_);
if (lean_obj_tag(v_typeName_2137_) == 0)
{
uint64_t v___x_2161_; 
v___x_2161_ = 1723ULL;
v___y_2147_ = v___x_2161_;
goto v___jp_2146_;
}
else
{
uint64_t v_hash_2162_; 
v_hash_2162_ = lean_ctor_get_uint64(v_typeName_2137_, sizeof(void*)*2);
v___y_2147_ = v_hash_2162_;
goto v___jp_2146_;
}
v___jp_2146_:
{
uint64_t v___x_2148_; uint64_t v___x_2149_; uint64_t v___x_2150_; uint64_t v___x_2151_; uint64_t v___x_2152_; uint32_t v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; uint8_t v___x_2156_; uint8_t v___x_2157_; uint8_t v___x_2158_; uint64_t v___x_2159_; lean_object* v___x_2160_; 
v___x_2148_ = lean_uint64_of_nat(v_idx_2138_);
v___x_2149_ = l_Lean_Expr_Data_hash(v___x_2140_);
v___x_2150_ = lean_uint64_mix_hash(v___x_2148_, v___x_2149_);
v___x_2151_ = lean_uint64_mix_hash(v___y_2147_, v___x_2150_);
v___x_2152_ = lean_uint64_mix_hash(v___x_2145_, v___x_2151_);
v___x_2153_ = l_Lean_Expr_Data_looseBVarRange(v___x_2140_);
v___x_2154_ = lean_uint32_to_nat(v___x_2153_);
v___x_2155_ = l_Lean_Expr_Data_hasFVar(v___x_2140_);
v___x_2156_ = l_Lean_Expr_Data_hasExprMVar(v___x_2140_);
v___x_2157_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2140_);
v___x_2158_ = l_Lean_Expr_Data_hasLevelParam(v___x_2140_);
v___x_2159_ = lean_expr_mk_data(v___x_2152_, v___x_2154_, v___x_2144_, v___x_2155_, v___x_2156_, v___x_2157_, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(v___x_2160_, 0, v_typeName_2137_);
lean_ctor_set(v___x_2160_, 1, v_idx_2138_);
lean_ctor_set(v___x_2160_, 2, v_struct_2139_);
lean_ctor_set_uint64(v___x_2160_, sizeof(void*)*3, v___x_2159_);
return v___x_2160_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__5(lean_object* v_x_2163_){
_start:
{
if (lean_obj_tag(v_x_2163_) == 0)
{
uint8_t v___x_2164_; 
v___x_2164_ = 0;
return v___x_2164_;
}
else
{
lean_object* v_head_2165_; lean_object* v_tail_2166_; uint8_t v___x_2167_; 
v_head_2165_ = lean_ctor_get(v_x_2163_, 0);
v_tail_2166_ = lean_ctor_get(v_x_2163_, 1);
v___x_2167_ = l_Lean_Level_hasMVar(v_head_2165_);
if (v___x_2167_ == 0)
{
v_x_2163_ = v_tail_2166_;
goto _start;
}
else
{
return v___x_2167_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__5___boxed(lean_object* v_x_2169_){
_start:
{
uint8_t v_res_2170_; lean_object* v_r_2171_; 
v_res_2170_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_x_2169_);
lean_dec(v_x_2169_);
v_r_2171_ = lean_box(v_res_2170_);
return v_r_2171_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__6(lean_object* v_x_2172_){
_start:
{
if (lean_obj_tag(v_x_2172_) == 0)
{
uint8_t v___x_2173_; 
v___x_2173_ = 0;
return v___x_2173_;
}
else
{
lean_object* v_head_2174_; lean_object* v_tail_2175_; uint8_t v___x_2176_; 
v_head_2174_ = lean_ctor_get(v_x_2172_, 0);
v_tail_2175_ = lean_ctor_get(v_x_2172_, 1);
v___x_2176_ = l_Lean_Level_hasParam(v_head_2174_);
if (v___x_2176_ == 0)
{
v_x_2172_ = v_tail_2175_;
goto _start;
}
else
{
return v___x_2176_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__6___boxed(lean_object* v_x_2178_){
_start:
{
uint8_t v_res_2179_; lean_object* v_r_2180_; 
v_res_2179_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_x_2178_);
lean_dec(v_x_2178_);
v_r_2180_ = lean_box(v_res_2179_);
return v_r_2180_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t v_x_2181_, lean_object* v_x_2182_){
_start:
{
if (lean_obj_tag(v_x_2182_) == 0)
{
return v_x_2181_;
}
else
{
lean_object* v_head_2183_; lean_object* v_tail_2184_; uint64_t v___x_2185_; uint64_t v___x_2186_; 
v_head_2183_ = lean_ctor_get(v_x_2182_, 0);
v_tail_2184_ = lean_ctor_get(v_x_2182_, 1);
v___x_2185_ = l_Lean_Level_hash(v_head_2183_);
v___x_2186_ = lean_uint64_mix_hash(v_x_2181_, v___x_2185_);
v_x_2181_ = v___x_2186_;
v_x_2182_ = v_tail_2184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object* v_x_2188_, lean_object* v_x_2189_){
_start:
{
uint64_t v_x_1715__boxed_2190_; uint64_t v_res_2191_; lean_object* v_r_2192_; 
v_x_1715__boxed_2190_ = lean_unbox_uint64(v_x_2188_);
lean_dec_ref(v_x_2188_);
v_res_2191_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_1715__boxed_2190_, v_x_2189_);
lean_dec(v_x_2189_);
v_r_2192_ = lean_box_uint64(v_res_2191_);
return v_r_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* v_declName_2193_, lean_object* v_us_2194_){
_start:
{
uint64_t v___x_2195_; uint64_t v___y_2197_; 
v___x_2195_ = 5ULL;
if (lean_obj_tag(v_declName_2193_) == 0)
{
uint64_t v___x_2209_; 
v___x_2209_ = 1723ULL;
v___y_2197_ = v___x_2209_;
goto v___jp_2196_;
}
else
{
uint64_t v_hash_2210_; 
v_hash_2210_ = lean_ctor_get_uint64(v_declName_2193_, sizeof(void*)*2);
v___y_2197_ = v_hash_2210_;
goto v___jp_2196_;
}
v___jp_2196_:
{
uint64_t v___x_2198_; uint64_t v___x_2199_; uint64_t v___x_2200_; uint64_t v___x_2201_; lean_object* v___x_2202_; uint32_t v___x_2203_; uint8_t v___x_2204_; uint8_t v___x_2205_; uint8_t v___x_2206_; uint64_t v___x_2207_; lean_object* v___x_2208_; 
v___x_2198_ = 7ULL;
v___x_2199_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v___x_2198_, v_us_2194_);
v___x_2200_ = lean_uint64_mix_hash(v___y_2197_, v___x_2199_);
v___x_2201_ = lean_uint64_mix_hash(v___x_2195_, v___x_2200_);
v___x_2202_ = lean_unsigned_to_nat(0u);
v___x_2203_ = 0;
v___x_2204_ = 0;
v___x_2205_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_us_2194_);
v___x_2206_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_us_2194_);
v___x_2207_ = lean_expr_mk_data(v___x_2201_, v___x_2202_, v___x_2203_, v___x_2204_, v___x_2204_, v___x_2205_, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(v___x_2208_, 0, v_declName_2193_);
lean_ctor_set(v___x_2208_, 1, v_us_2194_);
lean_ctor_set_uint64(v___x_2208_, sizeof(void*)*2, v___x_2207_);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object* v___y_2211_){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = lean_unsigned_to_nat(0u);
v___x_2213_ = l_Lean_instReprLevel_repr(v___y_2211_, v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2214_, lean_object* v_x_2215_, lean_object* v_x_2216_){
_start:
{
if (lean_obj_tag(v_x_2216_) == 0)
{
lean_dec(v_x_2214_);
return v_x_2215_;
}
else
{
lean_object* v_head_2217_; lean_object* v_tail_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2229_; 
v_head_2217_ = lean_ctor_get(v_x_2216_, 0);
v_tail_2218_ = lean_ctor_get(v_x_2216_, 1);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_x_2216_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2220_ = v_x_2216_;
v_isShared_2221_ = v_isSharedCheck_2229_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_tail_2218_);
lean_inc(v_head_2217_);
lean_dec(v_x_2216_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2229_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
lean_inc(v_x_2214_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set_tag(v___x_2220_, 5);
lean_ctor_set(v___x_2220_, 1, v_x_2214_);
lean_ctor_set(v___x_2220_, 0, v_x_2215_);
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_x_2215_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_x_2214_);
v___x_2223_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = lean_unsigned_to_nat(0u);
v___x_2225_ = l_Lean_instReprLevel_repr(v_head_2217_, v___x_2224_);
v___x_2226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2223_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
v_x_2215_ = v___x_2226_;
v_x_2216_ = v_tail_2218_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object* v_x_2230_, lean_object* v_x_2231_, lean_object* v_x_2232_){
_start:
{
if (lean_obj_tag(v_x_2232_) == 0)
{
lean_dec(v_x_2230_);
return v_x_2231_;
}
else
{
lean_object* v_head_2233_; lean_object* v_tail_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2245_; 
v_head_2233_ = lean_ctor_get(v_x_2232_, 0);
v_tail_2234_ = lean_ctor_get(v_x_2232_, 1);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_x_2232_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2236_ = v_x_2232_;
v_isShared_2237_ = v_isSharedCheck_2245_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_tail_2234_);
lean_inc(v_head_2233_);
lean_dec(v_x_2232_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2245_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
lean_inc(v_x_2230_);
if (v_isShared_2237_ == 0)
{
lean_ctor_set_tag(v___x_2236_, 5);
lean_ctor_set(v___x_2236_, 1, v_x_2230_);
lean_ctor_set(v___x_2236_, 0, v_x_2231_);
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_x_2231_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_x_2230_);
v___x_2239_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2240_ = lean_unsigned_to_nat(0u);
v___x_2241_ = l_Lean_instReprLevel_repr(v_head_2233_, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2239_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(v_x_2230_, v___x_2242_, v_tail_2234_);
return v___x_2243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object* v_x_2246_, lean_object* v_x_2247_){
_start:
{
if (lean_obj_tag(v_x_2246_) == 0)
{
lean_object* v___x_2248_; 
lean_dec(v_x_2247_);
v___x_2248_ = lean_box(0);
return v___x_2248_;
}
else
{
lean_object* v_tail_2249_; 
v_tail_2249_ = lean_ctor_get(v_x_2246_, 1);
if (lean_obj_tag(v_tail_2249_) == 0)
{
lean_object* v_head_2250_; lean_object* v___x_2251_; 
lean_dec(v_x_2247_);
v_head_2250_ = lean_ctor_get(v_x_2246_, 0);
lean_inc(v_head_2250_);
lean_dec_ref_known(v_x_2246_, 2);
v___x_2251_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2250_);
return v___x_2251_;
}
else
{
lean_object* v_head_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
lean_inc(v_tail_2249_);
v_head_2252_ = lean_ctor_get(v_x_2246_, 0);
lean_inc(v_head_2252_);
lean_dec_ref_known(v_x_2246_, 2);
v___x_2253_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2252_);
v___x_2254_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(v_x_2247_, v___x_2253_, v_tail_2249_);
return v___x_2254_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2));
v___x_2267_ = lean_string_length(v___x_2266_);
return v___x_2267_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7);
v___x_2269_ = lean_nat_to_int(v___x_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object* v_a_2274_){
_start:
{
if (lean_obj_tag(v_a_2274_) == 0)
{
lean_object* v___x_2275_; 
v___x_2275_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1));
return v___x_2275_;
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; 
v___x_2276_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5));
v___x_2277_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(v_a_2274_, v___x_2276_);
v___x_2278_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8);
v___x_2279_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9));
v___x_2280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v___x_2277_);
v___x_2281_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10));
v___x_2282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2278_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = 0;
v___x_2285_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2285_, 0, v___x_2283_);
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*1, v___x_2284_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object* v_x_2358_, lean_object* v_prec_2359_){
_start:
{
switch(lean_obj_tag(v_x_2358_))
{
case 0:
{
lean_object* v_deBruijnIndex_2360_; lean_object* v___y_2362_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v_deBruijnIndex_2360_ = lean_ctor_get(v_x_2358_, 0);
lean_inc(v_deBruijnIndex_2360_);
lean_dec_ref_known(v_x_2358_, 1);
v___x_2371_ = lean_unsigned_to_nat(1024u);
v___x_2372_ = lean_nat_dec_le(v___x_2371_, v_prec_2359_);
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
v___x_2363_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__2));
v___x_2364_ = l_Nat_reprFast(v_deBruijnIndex_2360_);
v___x_2365_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
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
v___x_2370_ = l_Repr_addAppParen(v___x_2369_, v_prec_2359_);
return v___x_2370_;
}
}
case 1:
{
lean_object* v_fvarId_2375_; lean_object* v___y_2377_; lean_object* v___x_2386_; uint8_t v___x_2387_; 
v_fvarId_2375_ = lean_ctor_get(v_x_2358_, 0);
lean_inc(v_fvarId_2375_);
lean_dec_ref_known(v_x_2358_, 1);
v___x_2386_ = lean_unsigned_to_nat(1024u);
v___x_2387_ = lean_nat_dec_le(v___x_2386_, v_prec_2359_);
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
v___x_2378_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__5));
v___x_2379_ = lean_unsigned_to_nat(1024u);
v___x_2380_ = l_Lean_Name_reprPrec(v_fvarId_2375_, v___x_2379_);
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
v___x_2385_ = l_Repr_addAppParen(v___x_2384_, v_prec_2359_);
return v___x_2385_;
}
}
case 2:
{
lean_object* v_mvarId_2390_; lean_object* v___y_2392_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
v_mvarId_2390_ = lean_ctor_get(v_x_2358_, 0);
lean_inc(v_mvarId_2390_);
lean_dec_ref_known(v_x_2358_, 1);
v___x_2401_ = lean_unsigned_to_nat(1024u);
v___x_2402_ = lean_nat_dec_le(v___x_2401_, v_prec_2359_);
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
v___x_2393_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__8));
v___x_2394_ = lean_unsigned_to_nat(1024u);
v___x_2395_ = l_Lean_Name_reprPrec(v_mvarId_2390_, v___x_2394_);
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
v___x_2400_ = l_Repr_addAppParen(v___x_2399_, v_prec_2359_);
return v___x_2400_;
}
}
case 3:
{
lean_object* v_u_2405_; lean_object* v___y_2407_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v_u_2405_ = lean_ctor_get(v_x_2358_, 0);
lean_inc(v_u_2405_);
lean_dec_ref_known(v_x_2358_, 1);
v___x_2416_ = lean_unsigned_to_nat(1024u);
v___x_2417_ = lean_nat_dec_le(v___x_2416_, v_prec_2359_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2407_ = v___x_2418_;
goto v___jp_2406_;
}
else
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2407_ = v___x_2419_;
goto v___jp_2406_;
}
v___jp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2408_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__11));
v___x_2409_ = lean_unsigned_to_nat(1024u);
v___x_2410_ = l_Lean_instReprLevel_repr(v_u_2405_, v___x_2409_);
v___x_2411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2408_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
lean_inc(v___y_2407_);
v___x_2412_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___y_2407_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = 0;
v___x_2414_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set_uint8(v___x_2414_, sizeof(void*)*1, v___x_2413_);
v___x_2415_ = l_Repr_addAppParen(v___x_2414_, v_prec_2359_);
return v___x_2415_;
}
}
case 4:
{
lean_object* v_declName_2420_; lean_object* v_us_2421_; lean_object* v___y_2423_; lean_object* v___x_2436_; uint8_t v___x_2437_; 
v_declName_2420_ = lean_ctor_get(v_x_2358_, 0);
lean_inc(v_declName_2420_);
v_us_2421_ = lean_ctor_get(v_x_2358_, 1);
lean_inc(v_us_2421_);
lean_dec_ref_known(v_x_2358_, 2);
v___x_2436_ = lean_unsigned_to_nat(1024u);
v___x_2437_ = lean_nat_dec_le(v___x_2436_, v_prec_2359_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; 
v___x_2438_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2423_ = v___x_2438_;
goto v___jp_2422_;
}
else
{
lean_object* v___x_2439_; 
v___x_2439_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2423_ = v___x_2439_;
goto v___jp_2422_;
}
v___jp_2422_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2424_ = lean_box(1);
v___x_2425_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__14));
v___x_2426_ = lean_unsigned_to_nat(1024u);
v___x_2427_ = l_Lean_Name_reprPrec(v_declName_2420_, v___x_2426_);
v___x_2428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2425_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v___x_2424_);
v___x_2430_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_us_2421_);
v___x_2431_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
lean_inc(v___y_2423_);
v___x_2432_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___y_2423_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = 0;
v___x_2434_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2434_, 0, v___x_2432_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*1, v___x_2433_);
v___x_2435_ = l_Repr_addAppParen(v___x_2434_, v_prec_2359_);
return v___x_2435_;
}
}
case 5:
{
lean_object* v_fn_2440_; lean_object* v_arg_2441_; lean_object* v___x_2442_; lean_object* v___y_2444_; uint8_t v___x_2456_; 
v_fn_2440_ = lean_ctor_get(v_x_2358_, 0);
lean_inc_ref(v_fn_2440_);
v_arg_2441_ = lean_ctor_get(v_x_2358_, 1);
lean_inc_ref(v_arg_2441_);
lean_dec_ref_known(v_x_2358_, 2);
v___x_2442_ = lean_unsigned_to_nat(1024u);
v___x_2456_ = lean_nat_dec_le(v___x_2442_, v_prec_2359_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2444_ = v___x_2457_;
goto v___jp_2443_;
}
else
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2444_ = v___x_2458_;
goto v___jp_2443_;
}
v___jp_2443_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2445_ = lean_box(1);
v___x_2446_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__17));
v___x_2447_ = l_Lean_instReprExpr_repr(v_fn_2440_, v___x_2442_);
v___x_2448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
lean_ctor_set(v___x_2449_, 1, v___x_2445_);
v___x_2450_ = l_Lean_instReprExpr_repr(v_arg_2441_, v___x_2442_);
v___x_2451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
lean_inc(v___y_2444_);
v___x_2452_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___y_2444_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = 0;
v___x_2454_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set_uint8(v___x_2454_, sizeof(void*)*1, v___x_2453_);
v___x_2455_ = l_Repr_addAppParen(v___x_2454_, v_prec_2359_);
return v___x_2455_;
}
}
case 6:
{
lean_object* v_binderName_2459_; lean_object* v_binderType_2460_; lean_object* v_body_2461_; uint8_t v_binderInfo_2462_; lean_object* v___x_2463_; lean_object* v___y_2465_; uint8_t v___x_2483_; 
v_binderName_2459_ = lean_ctor_get(v_x_2358_, 0);
lean_inc(v_binderName_2459_);
v_binderType_2460_ = lean_ctor_get(v_x_2358_, 1);
lean_inc_ref(v_binderType_2460_);
v_body_2461_ = lean_ctor_get(v_x_2358_, 2);
lean_inc_ref(v_body_2461_);
v_binderInfo_2462_ = lean_ctor_get_uint8(v_x_2358_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2358_, 3);
v___x_2463_ = lean_unsigned_to_nat(1024u);
v___x_2483_ = lean_nat_dec_le(v___x_2463_, v_prec_2359_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2465_ = v___x_2484_;
goto v___jp_2464_;
}
else
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2465_ = v___x_2485_;
goto v___jp_2464_;
}
v___jp_2464_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2466_ = lean_box(1);
v___x_2467_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__20));
v___x_2468_ = l_Lean_Name_reprPrec(v_binderName_2459_, v___x_2463_);
v___x_2469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
lean_ctor_set(v___x_2470_, 1, v___x_2466_);
v___x_2471_ = l_Lean_instReprExpr_repr(v_binderType_2460_, v___x_2463_);
v___x_2472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set(v___x_2473_, 1, v___x_2466_);
v___x_2474_ = l_Lean_instReprExpr_repr(v_body_2461_, v___x_2463_);
v___x_2475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
lean_ctor_set(v___x_2476_, 1, v___x_2466_);
v___x_2477_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2462_, v___x_2463_);
v___x_2478_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
lean_inc(v___y_2465_);
v___x_2479_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___y_2465_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = 0;
v___x_2481_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*1, v___x_2480_);
v___x_2482_ = l_Repr_addAppParen(v___x_2481_, v_prec_2359_);
return v___x_2482_;
}
}
case 7:
{
lean_object* v_binderName_2486_; lean_object* v_binderType_2487_; lean_object* v_body_2488_; uint8_t v_binderInfo_2489_; lean_object* v___x_2490_; lean_object* v___y_2492_; uint8_t v___x_2510_; 
v_binderName_2486_ = lean_ctor_get(v_x_2358_, 0);
lean_inc(v_binderName_2486_);
v_binderType_2487_ = lean_ctor_get(v_x_2358_, 1);
lean_inc_ref(v_binderType_2487_);
v_body_2488_ = lean_ctor_get(v_x_2358_, 2);
lean_inc_ref(v_body_2488_);
v_binderInfo_2489_ = lean_ctor_get_uint8(v_x_2358_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2358_, 3);
v___x_2490_ = lean_unsigned_to_nat(1024u);
v___x_2510_ = lean_nat_dec_le(v___x_2490_, v_prec_2359_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2492_ = v___x_2511_;
goto v___jp_2491_;
}
else
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2492_ = v___x_2512_;
goto v___jp_2491_;
}
v___jp_2491_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2493_ = lean_box(1);
v___x_2494_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__23));
v___x_2495_ = l_Lean_Name_reprPrec(v_binderName_2486_, v___x_2490_);
v___x_2496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2494_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___x_2493_);
v___x_2498_ = l_Lean_instReprExpr_repr(v_binderType_2487_, v___x_2490_);
v___x_2499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2497_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
lean_ctor_set(v___x_2500_, 1, v___x_2493_);
v___x_2501_ = l_Lean_instReprExpr_repr(v_body_2488_, v___x_2490_);
v___x_2502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2500_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
lean_ctor_set(v___x_2503_, 1, v___x_2493_);
v___x_2504_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2489_, v___x_2490_);
v___x_2505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
lean_inc(v___y_2492_);
v___x_2506_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___y_2492_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = 0;
v___x_2508_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2508_, 0, v___x_2506_);
lean_ctor_set_uint8(v___x_2508_, sizeof(void*)*1, v___x_2507_);
v___x_2509_ = l_Repr_addAppParen(v___x_2508_, v_prec_2359_);
return v___x_2509_;
}
}
case 8:
{
lean_object* v_declName_2513_; lean_object* v_type_2514_; lean_object* v_value_2515_; lean_object* v_body_2516_; uint8_t v_nondep_2517_; lean_object* v___x_2518_; lean_object* v___y_2520_; uint8_t v___x_2541_; 
v_declName_2513_ = lean_ctor_get(v_x_2358_, 0);
lean_inc(v_declName_2513_);
v_type_2514_ = lean_ctor_get(v_x_2358_, 1);
lean_inc_ref(v_type_2514_);
v_value_2515_ = lean_ctor_get(v_x_2358_, 2);
lean_inc_ref(v_value_2515_);
v_body_2516_ = lean_ctor_get(v_x_2358_, 3);
lean_inc_ref(v_body_2516_);
v_nondep_2517_ = lean_ctor_get_uint8(v_x_2358_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_x_2358_, 4);
v___x_2518_ = lean_unsigned_to_nat(1024u);
v___x_2541_ = lean_nat_dec_le(v___x_2518_, v_prec_2359_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2520_ = v___x_2542_;
goto v___jp_2519_;
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2520_ = v___x_2543_;
goto v___jp_2519_;
}
v___jp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2521_ = lean_box(1);
v___x_2522_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__26));
v___x_2523_ = l_Lean_Name_reprPrec(v_declName_2513_, v___x_2518_);
v___x_2524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2522_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
lean_ctor_set(v___x_2525_, 1, v___x_2521_);
v___x_2526_ = l_Lean_instReprExpr_repr(v_type_2514_, v___x_2518_);
v___x_2527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
lean_ctor_set(v___x_2528_, 1, v___x_2521_);
v___x_2529_ = l_Lean_instReprExpr_repr(v_value_2515_, v___x_2518_);
v___x_2530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2528_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___x_2531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
lean_ctor_set(v___x_2531_, 1, v___x_2521_);
v___x_2532_ = l_Lean_instReprExpr_repr(v_body_2516_, v___x_2518_);
v___x_2533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2531_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
lean_ctor_set(v___x_2534_, 1, v___x_2521_);
v___x_2535_ = l_Bool_repr___redArg(v_nondep_2517_);
v___x_2536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
lean_inc(v___y_2520_);
v___x_2537_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___y_2520_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = 0;
v___x_2539_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set_uint8(v___x_2539_, sizeof(void*)*1, v___x_2538_);
v___x_2540_ = l_Repr_addAppParen(v___x_2539_, v_prec_2359_);
return v___x_2540_;
}
}
case 9:
{
lean_object* v_a_2544_; lean_object* v___y_2546_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v_a_2544_ = lean_ctor_get(v_x_2358_, 0);
lean_inc_ref(v_a_2544_);
lean_dec_ref_known(v_x_2358_, 1);
v___x_2555_ = lean_unsigned_to_nat(1024u);
v___x_2556_ = lean_nat_dec_le(v___x_2555_, v_prec_2359_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2557_; 
v___x_2557_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2546_ = v___x_2557_;
goto v___jp_2545_;
}
else
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2546_ = v___x_2558_;
goto v___jp_2545_;
}
v___jp_2545_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2547_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__29));
v___x_2548_ = lean_unsigned_to_nat(1024u);
v___x_2549_ = l_Lean_instReprLiteral_repr(v_a_2544_, v___x_2548_);
v___x_2550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2547_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
lean_inc(v___y_2546_);
v___x_2551_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___y_2546_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = 0;
v___x_2553_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2553_, 0, v___x_2551_);
lean_ctor_set_uint8(v___x_2553_, sizeof(void*)*1, v___x_2552_);
v___x_2554_ = l_Repr_addAppParen(v___x_2553_, v_prec_2359_);
return v___x_2554_;
}
}
case 10:
{
lean_object* v_data_2559_; lean_object* v_expr_2560_; lean_object* v___x_2561_; lean_object* v___y_2563_; uint8_t v___x_2575_; 
v_data_2559_ = lean_ctor_get(v_x_2358_, 0);
lean_inc(v_data_2559_);
v_expr_2560_ = lean_ctor_get(v_x_2358_, 1);
lean_inc_ref(v_expr_2560_);
lean_dec_ref_known(v_x_2358_, 2);
v___x_2561_ = lean_unsigned_to_nat(1024u);
v___x_2575_ = lean_nat_dec_le(v___x_2561_, v_prec_2359_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; 
v___x_2576_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2563_ = v___x_2576_;
goto v___jp_2562_;
}
else
{
lean_object* v___x_2577_; 
v___x_2577_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2563_ = v___x_2577_;
goto v___jp_2562_;
}
v___jp_2562_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2564_ = lean_box(1);
v___x_2565_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__32));
v___x_2566_ = l_Lean_instReprKVMap_repr___redArg(v_data_2559_);
v___x_2567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v___x_2564_);
v___x_2569_ = l_Lean_instReprExpr_repr(v_expr_2560_, v___x_2561_);
v___x_2570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2568_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
lean_inc(v___y_2563_);
v___x_2571_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___y_2563_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = 0;
v___x_2573_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2573_, 0, v___x_2571_);
lean_ctor_set_uint8(v___x_2573_, sizeof(void*)*1, v___x_2572_);
v___x_2574_ = l_Repr_addAppParen(v___x_2573_, v_prec_2359_);
return v___x_2574_;
}
}
default: 
{
lean_object* v_typeName_2578_; lean_object* v_idx_2579_; lean_object* v_struct_2580_; lean_object* v___x_2581_; lean_object* v___y_2583_; uint8_t v___x_2599_; 
v_typeName_2578_ = lean_ctor_get(v_x_2358_, 0);
lean_inc(v_typeName_2578_);
v_idx_2579_ = lean_ctor_get(v_x_2358_, 1);
lean_inc(v_idx_2579_);
v_struct_2580_ = lean_ctor_get(v_x_2358_, 2);
lean_inc_ref(v_struct_2580_);
lean_dec_ref_known(v_x_2358_, 3);
v___x_2581_ = lean_unsigned_to_nat(1024u);
v___x_2599_ = lean_nat_dec_le(v___x_2581_, v_prec_2359_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2583_ = v___x_2600_;
goto v___jp_2582_;
}
else
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2583_ = v___x_2601_;
goto v___jp_2582_;
}
v___jp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; uint8_t v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2584_ = lean_box(1);
v___x_2585_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__35));
v___x_2586_ = l_Lean_Name_reprPrec(v_typeName_2578_, v___x_2581_);
v___x_2587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2585_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v___x_2584_);
v___x_2589_ = l_Nat_reprFast(v_idx_2579_);
v___x_2590_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
v___x_2591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2588_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
lean_ctor_set(v___x_2592_, 1, v___x_2584_);
v___x_2593_ = l_Lean_instReprExpr_repr(v_struct_2580_, v___x_2581_);
v___x_2594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2592_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
lean_inc(v___y_2583_);
v___x_2595_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___y_2583_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = 0;
v___x_2597_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2597_, 0, v___x_2595_);
lean_ctor_set_uint8(v___x_2597_, sizeof(void*)*1, v___x_2596_);
v___x_2598_ = l_Repr_addAppParen(v___x_2597_, v_prec_2359_);
return v___x_2598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object* v_x_2602_, lean_object* v_prec_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_instReprExpr_repr(v_x_2602_, v_prec_2603_);
lean_dec(v_prec_2603_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object* v_a_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = lean_nat_to_int(v_a_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object* v_a_2607_, lean_object* v_n_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_a_2607_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object* v_a_2610_, lean_object* v_n_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0(v_a_2610_, v_n_2611_);
lean_dec(v_n_2611_);
return v_res_2612_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__2(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_box(0);
v___x_2619_ = ((lean_object*)(l_Lean_instInhabitedExpr___closed__1));
v___x_2620_ = l_Lean_Expr_const___override(v___x_2619_, v___x_2618_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr(void){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* v_x_2634_){
_start:
{
switch(lean_obj_tag(v_x_2634_))
{
case 0:
{
lean_object* v___x_2635_; 
v___x_2635_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__0));
return v___x_2635_;
}
case 1:
{
lean_object* v___x_2636_; 
v___x_2636_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__1));
return v___x_2636_;
}
case 2:
{
lean_object* v___x_2637_; 
v___x_2637_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__2));
return v___x_2637_;
}
case 3:
{
lean_object* v___x_2638_; 
v___x_2638_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__3));
return v___x_2638_;
}
case 4:
{
lean_object* v___x_2639_; 
v___x_2639_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__4));
return v___x_2639_;
}
case 5:
{
lean_object* v___x_2640_; 
v___x_2640_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__5));
return v___x_2640_;
}
case 6:
{
lean_object* v___x_2641_; 
v___x_2641_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__6));
return v___x_2641_;
}
case 7:
{
lean_object* v___x_2642_; 
v___x_2642_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__7));
return v___x_2642_;
}
case 8:
{
lean_object* v___x_2643_; 
v___x_2643_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__8));
return v___x_2643_;
}
case 9:
{
lean_object* v___x_2644_; 
v___x_2644_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__9));
return v___x_2644_;
}
case 10:
{
lean_object* v___x_2645_; 
v___x_2645_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__10));
return v___x_2645_;
}
default: 
{
lean_object* v___x_2646_; 
v___x_2646_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__11));
return v___x_2646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* v_x_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lean_Expr_ctorName(v_x_2647_);
lean_dec_ref(v_x_2647_);
return v_res_2648_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object* v_e_2649_){
_start:
{
uint64_t v___x_2650_; uint64_t v___x_2651_; 
v___x_2650_ = lean_expr_data(v_e_2649_);
v___x_2651_ = l_Lean_Expr_Data_hash(v___x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* v_e_2652_){
_start:
{
uint64_t v_res_2653_; lean_object* v_r_2654_; 
v_res_2653_ = l_Lean_Expr_hash(v_e_2652_);
lean_dec_ref(v_e_2652_);
v_r_2654_ = lean_box_uint64(v_res_2653_);
return v_r_2654_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object* v_e_2657_){
_start:
{
uint64_t v___x_2658_; uint8_t v___x_2659_; 
v___x_2658_ = lean_expr_data(v_e_2657_);
v___x_2659_ = l_Lean_Expr_Data_hasFVar(v___x_2658_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* v_e_2660_){
_start:
{
uint8_t v_res_2661_; lean_object* v_r_2662_; 
v_res_2661_ = l_Lean_Expr_hasFVar(v_e_2660_);
lean_dec_ref(v_e_2660_);
v_r_2662_ = lean_box(v_res_2661_);
return v_r_2662_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object* v_e_2663_){
_start:
{
uint64_t v___x_2664_; uint8_t v___x_2665_; 
v___x_2664_ = lean_expr_data(v_e_2663_);
v___x_2665_ = l_Lean_Expr_Data_hasExprMVar(v___x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* v_e_2666_){
_start:
{
uint8_t v_res_2667_; lean_object* v_r_2668_; 
v_res_2667_ = l_Lean_Expr_hasExprMVar(v_e_2666_);
lean_dec_ref(v_e_2666_);
v_r_2668_ = lean_box(v_res_2667_);
return v_r_2668_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object* v_e_2669_){
_start:
{
uint64_t v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = lean_expr_data(v_e_2669_);
v___x_2671_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* v_e_2672_){
_start:
{
uint8_t v_res_2673_; lean_object* v_r_2674_; 
v_res_2673_ = l_Lean_Expr_hasLevelMVar(v_e_2672_);
lean_dec_ref(v_e_2672_);
v_r_2674_ = lean_box(v_res_2673_);
return v_r_2674_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object* v_e_2675_){
_start:
{
uint64_t v_d_2676_; uint8_t v___x_2677_; 
v_d_2676_ = lean_expr_data(v_e_2675_);
v___x_2677_ = l_Lean_Expr_Data_hasExprMVar(v_d_2676_);
if (v___x_2677_ == 0)
{
uint8_t v___x_2678_; 
v___x_2678_ = l_Lean_Expr_Data_hasLevelMVar(v_d_2676_);
return v___x_2678_;
}
else
{
return v___x_2677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* v_e_2679_){
_start:
{
uint8_t v_res_2680_; lean_object* v_r_2681_; 
v_res_2680_ = l_Lean_Expr_hasMVar(v_e_2679_);
lean_dec_ref(v_e_2679_);
v_r_2681_ = lean_box(v_res_2680_);
return v_r_2681_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object* v_e_2682_){
_start:
{
uint64_t v___x_2683_; uint8_t v___x_2684_; 
v___x_2683_ = lean_expr_data(v_e_2682_);
v___x_2684_ = l_Lean_Expr_Data_hasLevelParam(v___x_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* v_e_2685_){
_start:
{
uint8_t v_res_2686_; lean_object* v_r_2687_; 
v_res_2686_ = l_Lean_Expr_hasLevelParam(v_e_2685_);
lean_dec_ref(v_e_2685_);
v_r_2687_ = lean_box(v_res_2686_);
return v_r_2687_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object* v_e_2688_){
_start:
{
uint64_t v___x_2689_; uint8_t v___x_2690_; uint32_t v___x_2691_; 
v___x_2689_ = lean_expr_data(v_e_2688_);
v___x_2690_ = l_Lean_Expr_Data_approxDepth(v___x_2689_);
v___x_2691_ = lean_uint8_to_uint32(v___x_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* v_e_2692_){
_start:
{
uint32_t v_res_2693_; lean_object* v_r_2694_; 
v_res_2693_ = l_Lean_Expr_approxDepth(v_e_2692_);
lean_dec_ref(v_e_2692_);
v_r_2694_ = lean_box_uint32(v_res_2693_);
return v_r_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* v_e_2695_){
_start:
{
uint64_t v___x_2696_; uint32_t v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = lean_expr_data(v_e_2695_);
v___x_2697_ = l_Lean_Expr_Data_looseBVarRange(v___x_2696_);
v___x_2698_ = lean_uint32_to_nat(v___x_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* v_e_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Lean_Expr_looseBVarRange(v_e_2699_);
lean_dec_ref(v_e_2699_);
return v_res_2700_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object* v_e_2701_){
_start:
{
switch(lean_obj_tag(v_e_2701_))
{
case 7:
{
uint8_t v_binderInfo_2702_; 
v_binderInfo_2702_ = lean_ctor_get_uint8(v_e_2701_, sizeof(void*)*3 + 8);
return v_binderInfo_2702_;
}
case 6:
{
uint8_t v_binderInfo_2703_; 
v_binderInfo_2703_ = lean_ctor_get_uint8(v_e_2701_, sizeof(void*)*3 + 8);
return v_binderInfo_2703_;
}
default: 
{
uint8_t v___x_2704_; 
v___x_2704_ = 0;
return v___x_2704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* v_e_2705_){
_start:
{
uint8_t v_res_2706_; lean_object* v_r_2707_; 
v_res_2706_ = l_Lean_Expr_binderInfo(v_e_2705_);
lean_dec_ref(v_e_2705_);
v_r_2707_ = lean_box(v_res_2706_);
return v_r_2707_;
}
}
LEAN_EXPORT uint64_t lean_expr_hash(lean_object* v_a_2708_){
_start:
{
uint64_t v___x_2709_; 
v___x_2709_ = l_Lean_Expr_hash(v_a_2708_);
lean_dec_ref(v_a_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* v_a_2710_){
_start:
{
uint64_t v_res_2711_; lean_object* v_r_2712_; 
v_res_2711_ = lean_expr_hash(v_a_2710_);
v_r_2712_ = lean_box_uint64(v_res_2711_);
return v_r_2712_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object* v_e_2713_){
_start:
{
uint8_t v___x_2714_; 
v___x_2714_ = l_Lean_Expr_hasFVar(v_e_2713_);
lean_dec_ref(v_e_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* v_e_2715_){
_start:
{
uint8_t v_res_2716_; lean_object* v_r_2717_; 
v_res_2716_ = lean_expr_has_fvar(v_e_2715_);
v_r_2717_ = lean_box(v_res_2716_);
return v_r_2717_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object* v_e_2718_){
_start:
{
uint8_t v___x_2719_; 
v___x_2719_ = l_Lean_Expr_hasExprMVar(v_e_2718_);
lean_dec_ref(v_e_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* v_e_2720_){
_start:
{
uint8_t v_res_2721_; lean_object* v_r_2722_; 
v_res_2721_ = lean_expr_has_expr_mvar(v_e_2720_);
v_r_2722_ = lean_box(v_res_2721_);
return v_r_2722_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object* v_e_2723_){
_start:
{
uint8_t v___x_2724_; 
v___x_2724_ = l_Lean_Expr_hasLevelMVar(v_e_2723_);
lean_dec_ref(v_e_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* v_e_2725_){
_start:
{
uint8_t v_res_2726_; lean_object* v_r_2727_; 
v_res_2726_ = lean_expr_has_level_mvar(v_e_2725_);
v_r_2727_ = lean_box(v_res_2726_);
return v_r_2727_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* v_e_2728_){
_start:
{
uint8_t v___x_2729_; 
v___x_2729_ = l_Lean_Expr_hasLevelParam(v_e_2728_);
lean_dec_ref(v_e_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* v_e_2730_){
_start:
{
uint8_t v_res_2731_; lean_object* v_r_2732_; 
v_res_2731_ = lean_expr_has_level_param(v_e_2730_);
v_r_2732_ = lean_box(v_res_2731_);
return v_r_2732_;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* v_e_2733_){
_start:
{
uint64_t v___x_2734_; uint32_t v___x_2735_; 
v___x_2734_ = lean_expr_data(v_e_2733_);
lean_dec_ref(v_e_2733_);
v___x_2735_ = l_Lean_Expr_Data_looseBVarRange(v___x_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* v_e_2736_){
_start:
{
uint32_t v_res_2737_; lean_object* v_r_2738_; 
v_res_2737_ = lean_expr_loose_bvar_range(v_e_2736_);
v_r_2738_ = lean_box_uint32(v_res_2737_);
return v_r_2738_;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* v_e_2739_){
_start:
{
uint8_t v___x_2740_; 
v___x_2740_ = l_Lean_Expr_binderInfo(v_e_2739_);
lean_dec_ref(v_e_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* v_e_2741_){
_start:
{
uint8_t v_res_2742_; lean_object* v_r_2743_; 
v_res_2742_ = lean_expr_binder_info(v_e_2741_);
v_r_2743_ = lean_box(v_res_2742_);
return v_r_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* v_declName_2744_, lean_object* v_us_2745_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_Expr_const___override(v_declName_2744_, v_us_2745_);
return v___x_2746_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2750_ = lean_box(0);
v___x_2751_ = ((lean_object*)(l_Lean_Literal_type___closed__1));
v___x_2752_ = l_Lean_Expr_const___override(v___x_2751_, v___x_2750_);
return v___x_2752_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = lean_box(0);
v___x_2757_ = ((lean_object*)(l_Lean_Literal_type___closed__4));
v___x_2758_ = l_Lean_Expr_const___override(v___x_2757_, v___x_2756_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* v_x_2759_){
_start:
{
if (lean_obj_tag(v_x_2759_) == 0)
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_2760_;
}
else
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_obj_once(&l_Lean_Literal_type___closed__5, &l_Lean_Literal_type___closed__5_once, _init_l_Lean_Literal_type___closed__5);
return v___x_2761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* v_x_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_Literal_type(v_x_2762_);
lean_dec_ref(v_x_2762_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* v_a_2764_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_Literal_type(v_a_2764_);
lean_dec_ref(v_a_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* v_idx_2766_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Lean_Expr_bvar___override(v_idx_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* v_u_2768_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_Expr_sort___override(v_u_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* v_fvarId_2770_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_Expr_fvar___override(v_fvarId_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* v_mvarId_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_Expr_mvar___override(v_mvarId_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* v_m_2774_, lean_object* v_e_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_Expr_mdata___override(v_m_2774_, v_e_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* v_structName_2777_, lean_object* v_idx_2778_, lean_object* v_struct_2779_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_Expr_proj___override(v_structName_2777_, v_idx_2778_, v_struct_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* v_f_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l_Lean_Expr_app___override(v_f_2781_, v_a_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* v_x_2784_, uint8_t v_bi_2785_, lean_object* v_t_2786_, lean_object* v_b_2787_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Lean_Expr_lam___override(v_x_2784_, v_t_2786_, v_b_2787_, v_bi_2785_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* v_x_2789_, lean_object* v_bi_2790_, lean_object* v_t_2791_, lean_object* v_b_2792_){
_start:
{
uint8_t v_bi_boxed_2793_; lean_object* v_res_2794_; 
v_bi_boxed_2793_ = lean_unbox(v_bi_2790_);
v_res_2794_ = l_Lean_mkLambda(v_x_2789_, v_bi_boxed_2793_, v_t_2791_, v_b_2792_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* v_x_2795_, uint8_t v_bi_2796_, lean_object* v_t_2797_, lean_object* v_b_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_Expr_forallE___override(v_x_2795_, v_t_2797_, v_b_2798_, v_bi_2796_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* v_x_2800_, lean_object* v_bi_2801_, lean_object* v_t_2802_, lean_object* v_b_2803_){
_start:
{
uint8_t v_bi_boxed_2804_; lean_object* v_res_2805_; 
v_bi_boxed_2804_ = lean_unbox(v_bi_2801_);
v_res_2805_ = l_Lean_mkForall(v_x_2800_, v_bi_boxed_2804_, v_t_2802_, v_b_2803_);
return v_res_2805_;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__4(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2812_ = lean_box(0);
v___x_2813_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__3));
v___x_2814_ = l_Lean_Expr_const___override(v___x_2813_, v___x_2812_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* v_type_2815_){
_start:
{
lean_object* v___x_2816_; uint8_t v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2816_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2817_ = 0;
v___x_2818_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2819_ = l_Lean_Expr_forallE___override(v___x_2816_, v___x_2818_, v_type_2815_, v___x_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* v_type_2820_){
_start:
{
lean_object* v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2821_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2822_ = 0;
v___x_2823_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2824_ = l_Lean_Expr_lam___override(v___x_2821_, v___x_2823_, v_type_2820_, v___x_2822_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* v_x_2825_, lean_object* v_t_2826_, lean_object* v_v_2827_, lean_object* v_b_2828_, uint8_t v_nondep_2829_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Lean_Expr_letE___override(v_x_2825_, v_t_2826_, v_v_2827_, v_b_2828_, v_nondep_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* v_x_2831_, lean_object* v_t_2832_, lean_object* v_v_2833_, lean_object* v_b_2834_, lean_object* v_nondep_2835_){
_start:
{
uint8_t v_nondep_boxed_2836_; lean_object* v_res_2837_; 
v_nondep_boxed_2836_ = lean_unbox(v_nondep_2835_);
v_res_2837_ = l_Lean_mkLet(v_x_2831_, v_t_2832_, v_v_2833_, v_b_2834_, v_nondep_boxed_2836_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object* v_x_2838_, lean_object* v_t_2839_, lean_object* v_v_2840_, lean_object* v_b_2841_){
_start:
{
uint8_t v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = 1;
v___x_2843_ = l_Lean_Expr_letE___override(v_x_2838_, v_t_2839_, v_v_2840_, v_b_2841_, v___x_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* v_f_2844_, lean_object* v_a_2845_, lean_object* v_b_2846_){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = l_Lean_Expr_app___override(v_f_2844_, v_a_2845_);
v___x_2848_ = l_Lean_Expr_app___override(v___x_2847_, v_b_2846_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* v_f_2849_, lean_object* v_a_2850_, lean_object* v_b_2851_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l_Lean_mkAppB(v_f_2849_, v_a_2850_, v_b_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* v_f_2853_, lean_object* v_a_2854_, lean_object* v_b_2855_, lean_object* v_c_2856_){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = l_Lean_mkAppB(v_f_2853_, v_a_2854_, v_b_2855_);
v___x_2858_ = l_Lean_Expr_app___override(v___x_2857_, v_c_2856_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* v_f_2859_, lean_object* v_a_2860_, lean_object* v_b_2861_, lean_object* v_c_2862_, lean_object* v_d_2863_){
_start:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = l_Lean_mkAppB(v_f_2859_, v_a_2860_, v_b_2861_);
v___x_2865_ = l_Lean_mkAppB(v___x_2864_, v_c_2862_, v_d_2863_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* v_f_2866_, lean_object* v_a_2867_, lean_object* v_b_2868_, lean_object* v_c_2869_, lean_object* v_d_2870_, lean_object* v_e_2871_){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = l_Lean_mkApp4(v_f_2866_, v_a_2867_, v_b_2868_, v_c_2869_, v_d_2870_);
v___x_2873_ = l_Lean_Expr_app___override(v___x_2872_, v_e_2871_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* v_f_2874_, lean_object* v_a_2875_, lean_object* v_b_2876_, lean_object* v_c_2877_, lean_object* v_d_2878_, lean_object* v_e_u2081_2879_, lean_object* v_e_u2082_2880_){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = l_Lean_mkApp4(v_f_2874_, v_a_2875_, v_b_2876_, v_c_2877_, v_d_2878_);
v___x_2882_ = l_Lean_mkAppB(v___x_2881_, v_e_u2081_2879_, v_e_u2082_2880_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* v_f_2883_, lean_object* v_a_2884_, lean_object* v_b_2885_, lean_object* v_c_2886_, lean_object* v_d_2887_, lean_object* v_e_u2081_2888_, lean_object* v_e_u2082_2889_, lean_object* v_e_u2083_2890_){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = l_Lean_mkApp4(v_f_2883_, v_a_2884_, v_b_2885_, v_c_2886_, v_d_2887_);
v___x_2892_ = l_Lean_mkApp3(v___x_2891_, v_e_u2081_2888_, v_e_u2082_2889_, v_e_u2083_2890_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* v_f_2893_, lean_object* v_a_2894_, lean_object* v_b_2895_, lean_object* v_c_2896_, lean_object* v_d_2897_, lean_object* v_e_u2081_2898_, lean_object* v_e_u2082_2899_, lean_object* v_e_u2083_2900_, lean_object* v_e_u2084_2901_){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = l_Lean_mkApp4(v_f_2893_, v_a_2894_, v_b_2895_, v_c_2896_, v_d_2897_);
v___x_2903_ = l_Lean_mkApp4(v___x_2902_, v_e_u2081_2898_, v_e_u2082_2899_, v_e_u2083_2900_, v_e_u2084_2901_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* v_f_2904_, lean_object* v_a_2905_, lean_object* v_b_2906_, lean_object* v_c_2907_, lean_object* v_d_2908_, lean_object* v_e_u2081_2909_, lean_object* v_e_u2082_2910_, lean_object* v_e_u2083_2911_, lean_object* v_e_u2084_2912_, lean_object* v_e_u2085_2913_){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = l_Lean_mkApp4(v_f_2904_, v_a_2905_, v_b_2906_, v_c_2907_, v_d_2908_);
v___x_2915_ = l_Lean_mkApp5(v___x_2914_, v_e_u2081_2909_, v_e_u2082_2910_, v_e_u2083_2911_, v_e_u2084_2912_, v_e_u2085_2913_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* v_f_2916_, lean_object* v_a_2917_, lean_object* v_b_2918_, lean_object* v_c_2919_, lean_object* v_d_2920_, lean_object* v_e_u2081_2921_, lean_object* v_e_u2082_2922_, lean_object* v_e_u2083_2923_, lean_object* v_e_u2084_2924_, lean_object* v_e_u2085_2925_, lean_object* v_e_u2086_2926_){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = l_Lean_mkApp4(v_f_2916_, v_a_2917_, v_b_2918_, v_c_2919_, v_d_2920_);
v___x_2928_ = l_Lean_mkApp6(v___x_2927_, v_e_u2081_2921_, v_e_u2082_2922_, v_e_u2083_2923_, v_e_u2084_2924_, v_e_u2085_2925_, v_e_u2086_2926_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* v_l_2929_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_Expr_lit___override(v_l_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* v_n_2931_){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2932_, 0, v_n_2931_);
v___x_2933_ = l_Lean_Expr_lit___override(v___x_2932_);
return v___x_2933_;
}
}
static lean_object* _init_l_Lean_mkInstOfNatNat___closed__2(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2937_ = lean_box(0);
v___x_2938_ = ((lean_object*)(l_Lean_mkInstOfNatNat___closed__1));
v___x_2939_ = l_Lean_Expr_const___override(v___x_2938_, v___x_2937_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object* v_n_2940_){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = lean_obj_once(&l_Lean_mkInstOfNatNat___closed__2, &l_Lean_mkInstOfNatNat___closed__2_once, _init_l_Lean_mkInstOfNatNat___closed__2);
v___x_2942_ = l_Lean_Expr_app___override(v___x_2941_, v_n_2940_);
return v___x_2942_;
}
}
static lean_object* _init_l_Lean_mkNatLitCore___closed__4(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_2952_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_2953_ = l_Lean_Expr_const___override(v___x_2952_, v___x_2951_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object* v_n_2954_){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2955_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_2956_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
lean_inc_ref(v_n_2954_);
v___x_2957_ = l_Lean_mkInstOfNatNat(v_n_2954_);
v___x_2958_ = l_Lean_mkApp3(v___x_2955_, v___x_2956_, v_n_2954_, v___x_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* v_n_2959_){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = l_Lean_mkRawNatLit(v_n_2959_);
v___x_2961_ = l_Lean_mkNatLitCore(v___x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* v_s_2962_){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2963_, 0, v_s_2962_);
v___x_2964_ = l_Lean_Expr_lit___override(v___x_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* v_idx_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_Expr_bvar___override(v_idx_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* v_fvarId_2967_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_Expr_fvar___override(v_fvarId_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object* v_mvarId_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_Expr_mvar___override(v_mvarId_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_Expr_sort___override(v_u_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_2973_, lean_object* v_lvls_2974_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_Expr_const___override(v_c_2973_, v_lvls_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Lean_Expr_app___override(v_f_2976_, v_a_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* v_n_2979_, lean_object* v_d_2980_, lean_object* v_b_2981_, uint8_t v_bi_2982_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Lean_Expr_lam___override(v_n_2979_, v_d_2980_, v_b_2981_, v_bi_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_2984_, lean_object* v_d_2985_, lean_object* v_b_2986_, lean_object* v_bi_2987_){
_start:
{
uint8_t v_bi_boxed_2988_; lean_object* v_res_2989_; 
v_bi_boxed_2988_ = lean_unbox(v_bi_2987_);
v_res_2989_ = lean_expr_mk_lambda(v_n_2984_, v_d_2985_, v_b_2986_, v_bi_boxed_2988_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* v_n_2990_, lean_object* v_d_2991_, lean_object* v_b_2992_, uint8_t v_bi_2993_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Lean_Expr_forallE___override(v_n_2990_, v_d_2991_, v_b_2992_, v_bi_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_2995_, lean_object* v_d_2996_, lean_object* v_b_2997_, lean_object* v_bi_2998_){
_start:
{
uint8_t v_bi_boxed_2999_; lean_object* v_res_3000_; 
v_bi_boxed_2999_ = lean_unbox(v_bi_2998_);
v_res_3000_ = lean_expr_mk_forall(v_n_2995_, v_d_2996_, v_b_2997_, v_bi_boxed_2999_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* v_n_3001_, lean_object* v_t_3002_, lean_object* v_v_3003_, lean_object* v_b_3004_, uint8_t v_nondep_3005_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_Expr_letE___override(v_n_3001_, v_t_3002_, v_v_3003_, v_b_3004_, v_nondep_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_3007_, lean_object* v_t_3008_, lean_object* v_v_3009_, lean_object* v_b_3010_, lean_object* v_nondep_3011_){
_start:
{
uint8_t v_nondep_boxed_3012_; lean_object* v_res_3013_; 
v_nondep_boxed_3012_ = lean_unbox(v_nondep_3011_);
v_res_3013_ = lean_expr_mk_let(v_n_3007_, v_t_3008_, v_v_3009_, v_b_3010_, v_nondep_boxed_3012_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Lean_Expr_lit___override(v_l_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_3016_, lean_object* v_e_3017_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l_Lean_Expr_mdata___override(v_m_3016_, v_e_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_3019_, lean_object* v_idx_3020_, lean_object* v_struct_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Lean_Expr_proj___override(v_structName_3019_, v_idx_3020_, v_struct_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_3023_, size_t v_i_3024_, size_t v_stop_3025_, lean_object* v_b_3026_){
_start:
{
uint8_t v___x_3027_; 
v___x_3027_ = lean_usize_dec_eq(v_i_3024_, v_stop_3025_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3028_; lean_object* v___x_3029_; size_t v___x_3030_; size_t v___x_3031_; 
v___x_3028_ = lean_array_uget_borrowed(v_as_3023_, v_i_3024_);
lean_inc(v___x_3028_);
v___x_3029_ = l_Lean_Expr_app___override(v_b_3026_, v___x_3028_);
v___x_3030_ = ((size_t)1ULL);
v___x_3031_ = lean_usize_add(v_i_3024_, v___x_3030_);
v_i_3024_ = v___x_3031_;
v_b_3026_ = v___x_3029_;
goto _start;
}
else
{
return v_b_3026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_3033_, lean_object* v_i_3034_, lean_object* v_stop_3035_, lean_object* v_b_3036_){
_start:
{
size_t v_i_boxed_3037_; size_t v_stop_boxed_3038_; lean_object* v_res_3039_; 
v_i_boxed_3037_ = lean_unbox_usize(v_i_3034_);
lean_dec(v_i_3034_);
v_stop_boxed_3038_ = lean_unbox_usize(v_stop_3035_);
lean_dec(v_stop_3035_);
v_res_3039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_3033_, v_i_boxed_3037_, v_stop_boxed_3038_, v_b_3036_);
lean_dec_ref(v_as_3033_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_3040_, lean_object* v_args_3041_){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
v___x_3042_ = lean_unsigned_to_nat(0u);
v___x_3043_ = lean_array_get_size(v_args_3041_);
v___x_3044_ = lean_nat_dec_lt(v___x_3042_, v___x_3043_);
if (v___x_3044_ == 0)
{
return v_f_3040_;
}
else
{
uint8_t v___x_3045_; 
v___x_3045_ = lean_nat_dec_le(v___x_3043_, v___x_3043_);
if (v___x_3045_ == 0)
{
if (v___x_3044_ == 0)
{
return v_f_3040_;
}
else
{
size_t v___x_3046_; size_t v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = ((size_t)0ULL);
v___x_3047_ = lean_usize_of_nat(v___x_3043_);
v___x_3048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3041_, v___x_3046_, v___x_3047_, v_f_3040_);
return v___x_3048_;
}
}
else
{
size_t v___x_3049_; size_t v___x_3050_; lean_object* v___x_3051_; 
v___x_3049_ = ((size_t)0ULL);
v___x_3050_ = lean_usize_of_nat(v___x_3043_);
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3041_, v___x_3049_, v___x_3050_, v_f_3040_);
return v___x_3051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_3052_, lean_object* v_args_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_mkAppN(v_f_3052_, v_args_3053_);
lean_dec_ref(v_args_3053_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_3055_, lean_object* v_args_3056_, lean_object* v_i_3057_, lean_object* v_e_3058_){
_start:
{
uint8_t v___x_3059_; 
v___x_3059_ = lean_nat_dec_lt(v_i_3057_, v_n_3055_);
if (v___x_3059_ == 0)
{
lean_dec(v_i_3057_);
return v_e_3058_;
}
else
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3060_ = l_Lean_instInhabitedExpr;
v___x_3061_ = lean_unsigned_to_nat(1u);
v___x_3062_ = lean_nat_add(v_i_3057_, v___x_3061_);
v___x_3063_ = lean_array_get_borrowed(v___x_3060_, v_args_3056_, v_i_3057_);
lean_dec(v_i_3057_);
lean_inc(v___x_3063_);
v___x_3064_ = l_Lean_Expr_app___override(v_e_3058_, v___x_3063_);
v_i_3057_ = v___x_3062_;
v_e_3058_ = v___x_3064_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_3066_, lean_object* v_args_3067_, lean_object* v_i_3068_, lean_object* v_e_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_3066_, v_args_3067_, v_i_3068_, v_e_3069_);
lean_dec_ref(v_args_3067_);
lean_dec(v_n_3066_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_3071_, lean_object* v_i_3072_, lean_object* v_j_3073_, lean_object* v_args_3074_){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_3073_, v_args_3074_, v_i_3072_, v_f_3071_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_3076_, lean_object* v_i_3077_, lean_object* v_j_3078_, lean_object* v_args_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Lean_mkAppRange(v_f_3076_, v_i_3077_, v_j_3078_, v_args_3079_);
lean_dec_ref(v_args_3079_);
lean_dec(v_j_3078_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_3081_, size_t v_i_3082_, size_t v_stop_3083_, lean_object* v_b_3084_){
_start:
{
uint8_t v___x_3085_; 
v___x_3085_ = lean_usize_dec_eq(v_i_3082_, v_stop_3083_);
if (v___x_3085_ == 0)
{
size_t v___x_3086_; size_t v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3086_ = ((size_t)1ULL);
v___x_3087_ = lean_usize_sub(v_i_3082_, v___x_3086_);
v___x_3088_ = lean_array_uget_borrowed(v_as_3081_, v___x_3087_);
lean_inc(v___x_3088_);
v___x_3089_ = l_Lean_Expr_app___override(v_b_3084_, v___x_3088_);
v_i_3082_ = v___x_3087_;
v_b_3084_ = v___x_3089_;
goto _start;
}
else
{
return v_b_3084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_3091_, lean_object* v_i_3092_, lean_object* v_stop_3093_, lean_object* v_b_3094_){
_start:
{
size_t v_i_boxed_3095_; size_t v_stop_boxed_3096_; lean_object* v_res_3097_; 
v_i_boxed_3095_ = lean_unbox_usize(v_i_3092_);
lean_dec(v_i_3092_);
v_stop_boxed_3096_ = lean_unbox_usize(v_stop_3093_);
lean_dec(v_stop_3093_);
v_res_3097_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3091_, v_i_boxed_3095_, v_stop_boxed_3096_, v_b_3094_);
lean_dec_ref(v_as_3091_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_3098_, lean_object* v_revArgs_3099_){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3100_ = lean_array_get_size(v_revArgs_3099_);
v___x_3101_ = lean_unsigned_to_nat(0u);
v___x_3102_ = lean_nat_dec_lt(v___x_3101_, v___x_3100_);
if (v___x_3102_ == 0)
{
return v_fn_3098_;
}
else
{
size_t v___x_3103_; size_t v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = lean_usize_of_nat(v___x_3100_);
v___x_3104_ = ((size_t)0ULL);
v___x_3105_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_3099_, v___x_3103_, v___x_3104_, v_fn_3098_);
return v___x_3105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_3106_, lean_object* v_revArgs_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_mkAppRev(v_fn_3106_, v_revArgs_3107_);
lean_dec_ref(v_revArgs_3107_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = lean_expr_dbg_to_string(v_e_3110_);
lean_dec_ref(v_e_3110_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_3114_, lean_object* v_b_3115_){
_start:
{
uint8_t v_res_3116_; lean_object* v_r_3117_; 
v_res_3116_ = lean_expr_quick_lt(v_a_3114_, v_b_3115_);
lean_dec_ref(v_b_3115_);
lean_dec_ref(v_a_3114_);
v_r_3117_ = lean_box(v_res_3116_);
return v_r_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_3120_, lean_object* v_b_3121_){
_start:
{
uint8_t v_res_3122_; lean_object* v_r_3123_; 
v_res_3122_ = lean_expr_lt(v_a_3120_, v_b_3121_);
lean_dec_ref(v_b_3121_);
lean_dec_ref(v_a_3120_);
v_r_3123_ = lean_box(v_res_3122_);
return v_r_3123_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* v_a_3124_, lean_object* v_b_3125_){
_start:
{
uint8_t v___x_3126_; 
v___x_3126_ = lean_expr_quick_lt(v_a_3124_, v_b_3125_);
if (v___x_3126_ == 0)
{
uint8_t v___x_3127_; 
v___x_3127_ = lean_expr_quick_lt(v_b_3125_, v_a_3124_);
if (v___x_3127_ == 0)
{
uint8_t v___x_3128_; 
v___x_3128_ = 1;
return v___x_3128_;
}
else
{
uint8_t v___x_3129_; 
v___x_3129_ = 2;
return v___x_3129_;
}
}
else
{
uint8_t v___x_3130_; 
v___x_3130_ = 0;
return v___x_3130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_3131_, lean_object* v_b_3132_){
_start:
{
uint8_t v_res_3133_; lean_object* v_r_3134_; 
v_res_3133_ = l_Lean_Expr_quickComp(v_a_3131_, v_b_3132_);
lean_dec_ref(v_b_3132_);
lean_dec_ref(v_a_3131_);
v_r_3134_ = lean_box(v_res_3133_);
return v_r_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_3137_, lean_object* v_b_3138_){
_start:
{
uint8_t v_res_3139_; lean_object* v_r_3140_; 
v_res_3139_ = lean_expr_eqv(v_a_3137_, v_b_3138_);
lean_dec_ref(v_b_3138_);
lean_dec_ref(v_a_3137_);
v_r_3140_ = lean_box(v_res_3139_);
return v_r_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3145_, lean_object* v_b_3146_){
_start:
{
uint8_t v_res_3147_; lean_object* v_r_3148_; 
v_res_3147_ = lean_expr_equal(v_a_3145_, v_b_3146_);
lean_dec_ref(v_b_3146_);
lean_dec_ref(v_a_3145_);
v_r_3148_ = lean_box(v_res_3147_);
return v_r_3148_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* v_x_3149_){
_start:
{
if (lean_obj_tag(v_x_3149_) == 3)
{
uint8_t v___x_3150_; 
v___x_3150_ = 1;
return v___x_3150_;
}
else
{
uint8_t v___x_3151_; 
v___x_3151_ = 0;
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3152_){
_start:
{
uint8_t v_res_3153_; lean_object* v_r_3154_; 
v_res_3153_ = l_Lean_Expr_isSort(v_x_3152_);
lean_dec_ref(v_x_3152_);
v_r_3154_ = lean_box(v_res_3153_);
return v_r_3154_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* v_x_3155_){
_start:
{
if (lean_obj_tag(v_x_3155_) == 3)
{
lean_object* v_u_3156_; 
v_u_3156_ = lean_ctor_get(v_x_3155_, 0);
if (lean_obj_tag(v_u_3156_) == 1)
{
uint8_t v___x_3157_; 
v___x_3157_ = 1;
return v___x_3157_;
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
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3160_){
_start:
{
uint8_t v_res_3161_; lean_object* v_r_3162_; 
v_res_3161_ = l_Lean_Expr_isType(v_x_3160_);
lean_dec_ref(v_x_3160_);
v_r_3162_ = lean_box(v_res_3161_);
return v_r_3162_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* v_x_3163_){
_start:
{
if (lean_obj_tag(v_x_3163_) == 3)
{
lean_object* v_u_3164_; 
v_u_3164_ = lean_ctor_get(v_x_3163_, 0);
if (lean_obj_tag(v_u_3164_) == 1)
{
lean_object* v_a_3165_; 
v_a_3165_ = lean_ctor_get(v_u_3164_, 0);
if (lean_obj_tag(v_a_3165_) == 0)
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
else
{
uint8_t v___x_3168_; 
v___x_3168_ = 0;
return v___x_3168_;
}
}
else
{
uint8_t v___x_3169_; 
v___x_3169_ = 0;
return v___x_3169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3170_){
_start:
{
uint8_t v_res_3171_; lean_object* v_r_3172_; 
v_res_3171_ = l_Lean_Expr_isType0(v_x_3170_);
lean_dec_ref(v_x_3170_);
v_r_3172_ = lean_box(v_res_3171_);
return v_r_3172_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* v_x_3173_){
_start:
{
if (lean_obj_tag(v_x_3173_) == 3)
{
lean_object* v_u_3174_; 
v_u_3174_ = lean_ctor_get(v_x_3173_, 0);
if (lean_obj_tag(v_u_3174_) == 0)
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
else
{
uint8_t v___x_3177_; 
v___x_3177_ = 0;
return v___x_3177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3178_){
_start:
{
uint8_t v_res_3179_; lean_object* v_r_3180_; 
v_res_3179_ = l_Lean_Expr_isProp(v_x_3178_);
lean_dec_ref(v_x_3178_);
v_r_3180_ = lean_box(v_res_3179_);
return v_r_3180_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3181_){
_start:
{
if (lean_obj_tag(v_x_3181_) == 0)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3184_){
_start:
{
uint8_t v_res_3185_; lean_object* v_r_3186_; 
v_res_3185_ = l_Lean_Expr_isBVar(v_x_3184_);
lean_dec_ref(v_x_3184_);
v_r_3186_ = lean_box(v_res_3185_);
return v_r_3186_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3187_){
_start:
{
if (lean_obj_tag(v_x_3187_) == 2)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3190_){
_start:
{
uint8_t v_res_3191_; lean_object* v_r_3192_; 
v_res_3191_ = l_Lean_Expr_isMVar(v_x_3190_);
lean_dec_ref(v_x_3190_);
v_r_3192_ = lean_box(v_res_3191_);
return v_r_3192_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3193_){
_start:
{
if (lean_obj_tag(v_x_3193_) == 1)
{
uint8_t v___x_3194_; 
v___x_3194_ = 1;
return v___x_3194_;
}
else
{
uint8_t v___x_3195_; 
v___x_3195_ = 0;
return v___x_3195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3196_){
_start:
{
uint8_t v_res_3197_; lean_object* v_r_3198_; 
v_res_3197_ = l_Lean_Expr_isFVar(v_x_3196_);
lean_dec_ref(v_x_3196_);
v_r_3198_ = lean_box(v_res_3197_);
return v_r_3198_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* v_x_3199_){
_start:
{
if (lean_obj_tag(v_x_3199_) == 5)
{
uint8_t v___x_3200_; 
v___x_3200_ = 1;
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
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3202_){
_start:
{
uint8_t v_res_3203_; lean_object* v_r_3204_; 
v_res_3203_ = l_Lean_Expr_isApp(v_x_3202_);
lean_dec_ref(v_x_3202_);
v_r_3204_ = lean_box(v_res_3203_);
return v_r_3204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* v_x_3205_){
_start:
{
if (lean_obj_tag(v_x_3205_) == 11)
{
uint8_t v___x_3206_; 
v___x_3206_ = 1;
return v___x_3206_;
}
else
{
uint8_t v___x_3207_; 
v___x_3207_ = 0;
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3208_){
_start:
{
uint8_t v_res_3209_; lean_object* v_r_3210_; 
v_res_3209_ = l_Lean_Expr_isProj(v_x_3208_);
lean_dec_ref(v_x_3208_);
v_r_3210_ = lean_box(v_res_3209_);
return v_r_3210_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* v_x_3211_){
_start:
{
if (lean_obj_tag(v_x_3211_) == 4)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3214_){
_start:
{
uint8_t v_res_3215_; lean_object* v_r_3216_; 
v_res_3215_ = l_Lean_Expr_isConst(v_x_3214_);
lean_dec_ref(v_x_3214_);
v_r_3216_ = lean_box(v_res_3215_);
return v_r_3216_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3217_, lean_object* v_x_3218_){
_start:
{
if (lean_obj_tag(v_x_3217_) == 4)
{
lean_object* v_declName_3219_; uint8_t v___x_3220_; 
v_declName_3219_ = lean_ctor_get(v_x_3217_, 0);
v___x_3220_ = lean_name_eq(v_declName_3219_, v_x_3218_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3222_, lean_object* v_x_3223_){
_start:
{
uint8_t v_res_3224_; lean_object* v_r_3225_; 
v_res_3224_ = l_Lean_Expr_isConstOf(v_x_3222_, v_x_3223_);
lean_dec(v_x_3223_);
lean_dec_ref(v_x_3222_);
v_r_3225_ = lean_box(v_res_3224_);
return v_r_3225_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3226_, lean_object* v_x_3227_){
_start:
{
if (lean_obj_tag(v_x_3226_) == 1)
{
lean_object* v_fvarId_3228_; uint8_t v___x_3229_; 
v_fvarId_3228_ = lean_ctor_get(v_x_3226_, 0);
v___x_3229_ = lean_name_eq(v_fvarId_3228_, v_x_3227_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3231_, lean_object* v_x_3232_){
_start:
{
uint8_t v_res_3233_; lean_object* v_r_3234_; 
v_res_3233_ = l_Lean_Expr_isFVarOf(v_x_3231_, v_x_3232_);
lean_dec(v_x_3232_);
lean_dec_ref(v_x_3231_);
v_r_3234_ = lean_box(v_res_3233_);
return v_r_3234_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* v_x_3235_){
_start:
{
if (lean_obj_tag(v_x_3235_) == 7)
{
uint8_t v___x_3236_; 
v___x_3236_ = 1;
return v___x_3236_;
}
else
{
uint8_t v___x_3237_; 
v___x_3237_ = 0;
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3238_){
_start:
{
uint8_t v_res_3239_; lean_object* v_r_3240_; 
v_res_3239_ = l_Lean_Expr_isForall(v_x_3238_);
lean_dec_ref(v_x_3238_);
v_r_3240_ = lean_box(v_res_3239_);
return v_r_3240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3241_){
_start:
{
if (lean_obj_tag(v_x_3241_) == 6)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3244_){
_start:
{
uint8_t v_res_3245_; lean_object* v_r_3246_; 
v_res_3245_ = l_Lean_Expr_isLambda(v_x_3244_);
lean_dec_ref(v_x_3244_);
v_r_3246_ = lean_box(v_res_3245_);
return v_r_3246_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3247_){
_start:
{
switch(lean_obj_tag(v_x_3247_))
{
case 6:
{
uint8_t v___x_3248_; 
v___x_3248_ = 1;
return v___x_3248_;
}
case 7:
{
uint8_t v___x_3249_; 
v___x_3249_ = 1;
return v___x_3249_;
}
default: 
{
uint8_t v___x_3250_; 
v___x_3250_ = 0;
return v___x_3250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3251_){
_start:
{
uint8_t v_res_3252_; lean_object* v_r_3253_; 
v_res_3252_ = l_Lean_Expr_isBinding(v_x_3251_);
lean_dec_ref(v_x_3251_);
v_r_3253_ = lean_box(v_res_3252_);
return v_r_3253_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* v_x_3254_){
_start:
{
if (lean_obj_tag(v_x_3254_) == 8)
{
uint8_t v___x_3255_; 
v___x_3255_ = 1;
return v___x_3255_;
}
else
{
uint8_t v___x_3256_; 
v___x_3256_ = 0;
return v___x_3256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3257_){
_start:
{
uint8_t v_res_3258_; lean_object* v_r_3259_; 
v_res_3258_ = l_Lean_Expr_isLet(v_x_3257_);
lean_dec_ref(v_x_3257_);
v_r_3259_ = lean_box(v_res_3258_);
return v_r_3259_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object* v_x_3260_){
_start:
{
if (lean_obj_tag(v_x_3260_) == 8)
{
uint8_t v_nondep_3261_; 
v_nondep_3261_ = lean_ctor_get_uint8(v_x_3260_, sizeof(void*)*4 + 8);
return v_nondep_3261_;
}
else
{
uint8_t v___x_3262_; 
v___x_3262_ = 0;
return v___x_3262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3263_){
_start:
{
uint8_t v_res_3264_; lean_object* v_r_3265_; 
v_res_3264_ = l_Lean_Expr_isHave(v_x_3263_);
lean_dec_ref(v_x_3263_);
v_r_3265_ = lean_box(v_res_3264_);
return v_r_3265_;
}
}
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object* v_a_3266_){
_start:
{
uint8_t v___x_3267_; 
v___x_3267_ = l_Lean_Expr_isHave(v_a_3266_);
lean_dec_ref(v_a_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3268_){
_start:
{
uint8_t v_res_3269_; lean_object* v_r_3270_; 
v_res_3269_ = lean_expr_is_have(v_a_3268_);
v_r_3270_ = lean_box(v_res_3269_);
return v_r_3270_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* v_x_3271_){
_start:
{
if (lean_obj_tag(v_x_3271_) == 10)
{
uint8_t v___x_3272_; 
v___x_3272_ = 1;
return v___x_3272_;
}
else
{
uint8_t v___x_3273_; 
v___x_3273_ = 0;
return v___x_3273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3274_){
_start:
{
uint8_t v_res_3275_; lean_object* v_r_3276_; 
v_res_3275_ = l_Lean_Expr_isMData(v_x_3274_);
lean_dec_ref(v_x_3274_);
v_r_3276_ = lean_box(v_res_3275_);
return v_r_3276_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* v_x_3277_){
_start:
{
if (lean_obj_tag(v_x_3277_) == 9)
{
uint8_t v___x_3278_; 
v___x_3278_ = 1;
return v___x_3278_;
}
else
{
uint8_t v___x_3279_; 
v___x_3279_ = 0;
return v___x_3279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3280_){
_start:
{
uint8_t v_res_3281_; lean_object* v_r_3282_; 
v_res_3281_ = l_Lean_Expr_isLit(v_x_3280_);
lean_dec_ref(v_x_3280_);
v_r_3282_ = lean_box(v_res_3281_);
return v_r_3282_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3283_){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3284_ = l_Lean_instInhabitedExpr;
v___x_3285_ = lean_panic_fn_borrowed(v___x_3284_, v_msg_3283_);
return v___x_3285_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3289_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3290_ = lean_unsigned_to_nat(15u);
v___x_3291_ = lean_unsigned_to_nat(932u);
v___x_3292_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3293_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3294_ = l_mkPanicMessageWithDecl(v___x_3293_, v___x_3292_, v___x_3291_, v___x_3290_, v___x_3289_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3295_){
_start:
{
if (lean_obj_tag(v_x_3295_) == 5)
{
lean_object* v_fn_3296_; 
v_fn_3296_ = lean_ctor_get(v_x_3295_, 0);
lean_inc_ref(v_fn_3296_);
return v_fn_3296_;
}
else
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3298_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3297_);
return v___x_3298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_Expr_appFn_x21(v_x_3299_);
lean_dec_ref(v_x_3299_);
return v_res_3300_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3302_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3303_ = lean_unsigned_to_nat(15u);
v___x_3304_ = lean_unsigned_to_nat(936u);
v___x_3305_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3306_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3307_ = l_mkPanicMessageWithDecl(v___x_3306_, v___x_3305_, v___x_3304_, v___x_3303_, v___x_3302_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3308_){
_start:
{
if (lean_obj_tag(v_x_3308_) == 5)
{
lean_object* v_arg_3309_; 
v_arg_3309_ = lean_ctor_get(v_x_3308_, 1);
lean_inc_ref(v_arg_3309_);
return v_arg_3309_;
}
else
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3311_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3310_);
return v___x_3311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_Expr_appArg_x21(v_x_3312_);
lean_dec_ref(v_x_3312_);
return v_res_3313_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3315_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3316_ = lean_unsigned_to_nat(17u);
v___x_3317_ = lean_unsigned_to_nat(941u);
v___x_3318_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3319_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3320_ = l_mkPanicMessageWithDecl(v___x_3319_, v___x_3318_, v___x_3317_, v___x_3316_, v___x_3315_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3321_){
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
lean_object* v_fn_3324_; 
v_fn_3324_ = lean_ctor_get(v_x_3321_, 0);
lean_inc_ref(v_fn_3324_);
return v_fn_3324_;
}
default: 
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3326_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3325_);
return v___x_3326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Lean_Expr_appFn_x21_x27(v_x_3327_);
lean_dec_ref(v_x_3327_);
return v_res_3328_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3330_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3331_ = lean_unsigned_to_nat(17u);
v___x_3332_ = lean_unsigned_to_nat(946u);
v___x_3333_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3334_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3335_ = l_mkPanicMessageWithDecl(v___x_3334_, v___x_3333_, v___x_3332_, v___x_3331_, v___x_3330_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3336_){
_start:
{
switch(lean_obj_tag(v_x_3336_))
{
case 10:
{
lean_object* v_expr_3337_; 
v_expr_3337_ = lean_ctor_get(v_x_3336_, 1);
v_x_3336_ = v_expr_3337_;
goto _start;
}
case 5:
{
lean_object* v_arg_3339_; 
v_arg_3339_ = lean_ctor_get(v_x_3336_, 1);
lean_inc_ref(v_arg_3339_);
return v_arg_3339_;
}
default: 
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3341_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3340_);
return v___x_3341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_Expr_appArg_x21_x27(v_x_3342_);
lean_dec_ref(v_x_3342_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3344_){
_start:
{
lean_object* v_arg_3345_; 
v_arg_3345_ = lean_ctor_get(v_e_3344_, 1);
lean_inc_ref(v_arg_3345_);
return v_arg_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_Expr_appArg___redArg(v_e_3346_);
lean_dec_ref(v_e_3346_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3348_, lean_object* v_h_3349_){
_start:
{
lean_object* v_arg_3350_; 
v_arg_3350_ = lean_ctor_get(v_e_3348_, 1);
lean_inc_ref(v_arg_3350_);
return v_arg_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3351_, lean_object* v_h_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lean_Expr_appArg(v_e_3351_, v_h_3352_);
lean_dec_ref(v_e_3351_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3354_){
_start:
{
lean_object* v_fn_3355_; 
v_fn_3355_ = lean_ctor_get(v_e_3354_, 0);
lean_inc_ref(v_fn_3355_);
return v_fn_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l_Lean_Expr_appFn___redArg(v_e_3356_);
lean_dec_ref(v_e_3356_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3358_, lean_object* v_h_3359_){
_start:
{
lean_object* v_fn_3360_; 
v_fn_3360_ = lean_ctor_get(v_e_3358_, 0);
lean_inc_ref(v_fn_3360_);
return v_fn_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3361_, lean_object* v_h_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l_Lean_Expr_appFn(v_e_3361_, v_h_3362_);
lean_dec_ref(v_e_3361_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3364_){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = lean_box(0);
v___x_3366_ = lean_panic_fn_borrowed(v___x_3365_, v_msg_3364_);
return v___x_3366_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3369_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3370_ = lean_unsigned_to_nat(14u);
v___x_3371_ = lean_unsigned_to_nat(958u);
v___x_3372_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3373_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3374_ = l_mkPanicMessageWithDecl(v___x_3373_, v___x_3372_, v___x_3371_, v___x_3370_, v___x_3369_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3375_){
_start:
{
if (lean_obj_tag(v_x_3375_) == 3)
{
lean_object* v_u_3376_; 
v_u_3376_ = lean_ctor_get(v_x_3375_, 0);
lean_inc(v_u_3376_);
return v_u_3376_;
}
else
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3378_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3377_);
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Lean_Expr_sortLevel_x21(v_x_3379_);
lean_dec_ref(v_x_3379_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3381_){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3383_ = lean_panic_fn_borrowed(v___x_3382_, v_msg_3381_);
return v___x_3383_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3386_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3387_ = lean_unsigned_to_nat(13u);
v___x_3388_ = lean_unsigned_to_nat(962u);
v___x_3389_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3390_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3391_ = l_mkPanicMessageWithDecl(v___x_3390_, v___x_3389_, v___x_3388_, v___x_3387_, v___x_3386_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3392_){
_start:
{
if (lean_obj_tag(v_x_3392_) == 9)
{
lean_object* v_a_3393_; 
v_a_3393_ = lean_ctor_get(v_x_3392_, 0);
lean_inc_ref(v_a_3393_);
return v_a_3393_;
}
else
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3395_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3394_);
return v___x_3395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l_Lean_Expr_litValue_x21(v_x_3396_);
lean_dec_ref(v_x_3396_);
return v_res_3397_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3398_){
_start:
{
if (lean_obj_tag(v_x_3398_) == 9)
{
lean_object* v_a_3399_; 
v_a_3399_ = lean_ctor_get(v_x_3398_, 0);
if (lean_obj_tag(v_a_3399_) == 0)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3403_){
_start:
{
uint8_t v_res_3404_; lean_object* v_r_3405_; 
v_res_3404_ = l_Lean_Expr_isRawNatLit(v_x_3403_);
lean_dec_ref(v_x_3403_);
v_r_3405_ = lean_box(v_res_3404_);
return v_r_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3406_){
_start:
{
if (lean_obj_tag(v_x_3406_) == 9)
{
lean_object* v_a_3407_; 
v_a_3407_ = lean_ctor_get(v_x_3406_, 0);
lean_inc_ref(v_a_3407_);
lean_dec_ref_known(v_x_3406_, 1);
if (lean_obj_tag(v_a_3407_) == 0)
{
lean_object* v_val_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
v_val_3408_ = lean_ctor_get(v_a_3407_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_a_3407_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v_a_3407_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_val_3408_);
lean_dec(v_a_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
lean_ctor_set_tag(v___x_3410_, 1);
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_val_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
else
{
lean_object* v___x_3416_; 
lean_dec_ref(v_a_3407_);
v___x_3416_ = lean_box(0);
return v___x_3416_;
}
}
else
{
lean_object* v___x_3417_; 
lean_dec_ref(v_x_3406_);
v___x_3417_ = lean_box(0);
return v___x_3417_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3418_){
_start:
{
if (lean_obj_tag(v_x_3418_) == 9)
{
lean_object* v_a_3419_; 
v_a_3419_ = lean_ctor_get(v_x_3418_, 0);
if (lean_obj_tag(v_a_3419_) == 1)
{
uint8_t v___x_3420_; 
v___x_3420_ = 1;
return v___x_3420_;
}
else
{
uint8_t v___x_3421_; 
v___x_3421_ = 0;
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3423_){
_start:
{
uint8_t v_res_3424_; lean_object* v_r_3425_; 
v_res_3424_ = l_Lean_Expr_isStringLit(v_x_3423_);
lean_dec_ref(v_x_3423_);
v_r_3425_ = lean_box(v_res_3424_);
return v_r_3425_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3430_){
_start:
{
if (lean_obj_tag(v_x_3430_) == 5)
{
lean_object* v_fn_3431_; 
v_fn_3431_ = lean_ctor_get(v_x_3430_, 0);
if (lean_obj_tag(v_fn_3431_) == 4)
{
lean_object* v_arg_3432_; lean_object* v_declName_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
v_arg_3432_ = lean_ctor_get(v_x_3430_, 1);
v_declName_3433_ = lean_ctor_get(v_fn_3431_, 0);
v___x_3434_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3435_ = lean_name_eq(v_declName_3433_, v___x_3434_);
if (v___x_3435_ == 0)
{
return v___x_3435_;
}
else
{
uint8_t v___x_3436_; 
v___x_3436_ = l_Lean_Expr_isRawNatLit(v_arg_3432_);
return v___x_3436_;
}
}
else
{
uint8_t v___x_3437_; 
v___x_3437_ = 0;
return v___x_3437_;
}
}
else
{
uint8_t v___x_3438_; 
v___x_3438_ = 0;
return v___x_3438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3439_){
_start:
{
uint8_t v_res_3440_; lean_object* v_r_3441_; 
v_res_3440_ = l_Lean_Expr_isCharLit(v_x_3439_);
lean_dec_ref(v_x_3439_);
v_r_3441_ = lean_box(v_res_3440_);
return v_r_3441_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3442_){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3443_ = lean_box(0);
v___x_3444_ = lean_panic_fn_borrowed(v___x_3443_, v_msg_3442_);
return v___x_3444_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3447_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3448_ = lean_unsigned_to_nat(17u);
v___x_3449_ = lean_unsigned_to_nat(986u);
v___x_3450_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3451_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3452_ = l_mkPanicMessageWithDecl(v___x_3451_, v___x_3450_, v___x_3449_, v___x_3448_, v___x_3447_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3453_){
_start:
{
if (lean_obj_tag(v_x_3453_) == 4)
{
lean_object* v_declName_3454_; 
v_declName_3454_ = lean_ctor_get(v_x_3453_, 0);
lean_inc(v_declName_3454_);
return v_declName_3454_;
}
else
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3456_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3455_);
return v___x_3456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_Expr_constName_x21(v_x_3457_);
lean_dec_ref(v_x_3457_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3459_){
_start:
{
if (lean_obj_tag(v_x_3459_) == 4)
{
lean_object* v_declName_3460_; lean_object* v___x_3461_; 
v_declName_3460_ = lean_ctor_get(v_x_3459_, 0);
lean_inc(v_declName_3460_);
v___x_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3461_, 0, v_declName_3460_);
return v___x_3461_;
}
else
{
lean_object* v___x_3462_; 
v___x_3462_ = lean_box(0);
return v___x_3462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_Expr_constName_x3f(v_x_3463_);
lean_dec_ref(v_x_3463_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3465_){
_start:
{
lean_object* v___x_3466_; 
v___x_3466_ = l_Lean_Expr_constName_x3f(v_e_3465_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_box(0);
return v___x_3467_;
}
else
{
lean_object* v_val_3468_; 
v_val_3468_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_val_3468_);
lean_dec_ref_known(v___x_3466_, 1);
return v_val_3468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_Expr_constName(v_e_3469_);
lean_dec_ref(v_e_3469_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3471_){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = lean_box(0);
v___x_3473_ = lean_panic_fn_borrowed(v___x_3472_, v_msg_3471_);
return v___x_3473_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3475_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3476_ = lean_unsigned_to_nat(18u);
v___x_3477_ = lean_unsigned_to_nat(1006u);
v___x_3478_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3479_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3480_ = l_mkPanicMessageWithDecl(v___x_3479_, v___x_3478_, v___x_3477_, v___x_3476_, v___x_3475_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3481_){
_start:
{
if (lean_obj_tag(v_x_3481_) == 4)
{
lean_object* v_us_3482_; 
v_us_3482_ = lean_ctor_get(v_x_3481_, 1);
lean_inc(v_us_3482_);
return v_us_3482_;
}
else
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3484_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3483_);
return v___x_3484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Lean_Expr_constLevels_x21(v_x_3485_);
lean_dec_ref(v_x_3485_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3487_){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3488_ = lean_unsigned_to_nat(0u);
v___x_3489_ = lean_panic_fn_borrowed(v___x_3488_, v_msg_3487_);
return v___x_3489_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3492_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3493_ = lean_unsigned_to_nat(16u);
v___x_3494_ = lean_unsigned_to_nat(1010u);
v___x_3495_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3496_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3497_ = l_mkPanicMessageWithDecl(v___x_3496_, v___x_3495_, v___x_3494_, v___x_3493_, v___x_3492_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3498_){
_start:
{
if (lean_obj_tag(v_x_3498_) == 0)
{
lean_object* v_deBruijnIndex_3499_; 
v_deBruijnIndex_3499_ = lean_ctor_get(v_x_3498_, 0);
lean_inc(v_deBruijnIndex_3499_);
return v_deBruijnIndex_3499_;
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3501_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3500_);
return v___x_3501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Expr_bvarIdx_x21(v_x_3502_);
lean_dec_ref(v_x_3502_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3504_){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = lean_box(0);
v___x_3506_ = lean_panic_fn_borrowed(v___x_3505_, v_msg_3504_);
return v___x_3506_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3509_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3510_ = lean_unsigned_to_nat(14u);
v___x_3511_ = lean_unsigned_to_nat(1014u);
v___x_3512_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3513_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3514_ = l_mkPanicMessageWithDecl(v___x_3513_, v___x_3512_, v___x_3511_, v___x_3510_, v___x_3509_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3515_){
_start:
{
if (lean_obj_tag(v_x_3515_) == 1)
{
lean_object* v_fvarId_3516_; 
v_fvarId_3516_ = lean_ctor_get(v_x_3515_, 0);
lean_inc(v_fvarId_3516_);
return v_fvarId_3516_;
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3518_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3517_);
return v___x_3518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_Expr_fvarId_x21(v_x_3519_);
lean_dec_ref(v_x_3519_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3521_){
_start:
{
if (lean_obj_tag(v_x_3521_) == 1)
{
lean_object* v_fvarId_3522_; lean_object* v___x_3523_; 
v_fvarId_3522_ = lean_ctor_get(v_x_3521_, 0);
lean_inc(v_fvarId_3522_);
v___x_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3523_, 0, v_fvarId_3522_);
return v___x_3523_;
}
else
{
lean_object* v___x_3524_; 
v___x_3524_ = lean_box(0);
return v___x_3524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Lean_Expr_fvarId_x3f(v_x_3525_);
lean_dec_ref(v_x_3525_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3527_){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3528_ = lean_box(0);
v___x_3529_ = lean_panic_fn_borrowed(v___x_3528_, v_msg_3527_);
return v___x_3529_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3532_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3533_ = lean_unsigned_to_nat(14u);
v___x_3534_ = lean_unsigned_to_nat(1022u);
v___x_3535_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3536_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3537_ = l_mkPanicMessageWithDecl(v___x_3536_, v___x_3535_, v___x_3534_, v___x_3533_, v___x_3532_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3538_){
_start:
{
if (lean_obj_tag(v_x_3538_) == 2)
{
lean_object* v_mvarId_3539_; 
v_mvarId_3539_ = lean_ctor_get(v_x_3538_, 0);
lean_inc(v_mvarId_3539_);
return v_mvarId_3539_;
}
else
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3541_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3540_);
return v___x_3541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Lean_Expr_mvarId_x21(v_x_3542_);
lean_dec_ref(v_x_3542_);
return v_res_3543_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3546_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3547_ = lean_unsigned_to_nat(23u);
v___x_3548_ = lean_unsigned_to_nat(1027u);
v___x_3549_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3550_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3551_ = l_mkPanicMessageWithDecl(v___x_3550_, v___x_3549_, v___x_3548_, v___x_3547_, v___x_3546_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3552_){
_start:
{
switch(lean_obj_tag(v_x_3552_))
{
case 7:
{
lean_object* v_binderName_3553_; 
v_binderName_3553_ = lean_ctor_get(v_x_3552_, 0);
lean_inc(v_binderName_3553_);
return v_binderName_3553_;
}
case 6:
{
lean_object* v_binderName_3554_; 
v_binderName_3554_ = lean_ctor_get(v_x_3552_, 0);
lean_inc(v_binderName_3554_);
return v_binderName_3554_;
}
default: 
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3556_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3555_);
return v___x_3556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_Lean_Expr_bindingName_x21(v_x_3557_);
lean_dec_ref(v_x_3557_);
return v_res_3558_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3560_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3561_ = lean_unsigned_to_nat(23u);
v___x_3562_ = lean_unsigned_to_nat(1032u);
v___x_3563_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3564_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3565_ = l_mkPanicMessageWithDecl(v___x_3564_, v___x_3563_, v___x_3562_, v___x_3561_, v___x_3560_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3566_){
_start:
{
switch(lean_obj_tag(v_x_3566_))
{
case 7:
{
lean_object* v_binderType_3567_; 
v_binderType_3567_ = lean_ctor_get(v_x_3566_, 1);
lean_inc_ref(v_binderType_3567_);
return v_binderType_3567_;
}
case 6:
{
lean_object* v_binderType_3568_; 
v_binderType_3568_ = lean_ctor_get(v_x_3566_, 1);
lean_inc_ref(v_binderType_3568_);
return v_binderType_3568_;
}
default: 
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3570_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3569_);
return v___x_3570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Lean_Expr_bindingDomain_x21(v_x_3571_);
lean_dec_ref(v_x_3571_);
return v_res_3572_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3574_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3575_ = lean_unsigned_to_nat(23u);
v___x_3576_ = lean_unsigned_to_nat(1037u);
v___x_3577_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3578_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3579_ = l_mkPanicMessageWithDecl(v___x_3578_, v___x_3577_, v___x_3576_, v___x_3575_, v___x_3574_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3580_){
_start:
{
switch(lean_obj_tag(v_x_3580_))
{
case 7:
{
lean_object* v_body_3581_; 
v_body_3581_ = lean_ctor_get(v_x_3580_, 2);
lean_inc_ref(v_body_3581_);
return v_body_3581_;
}
case 6:
{
lean_object* v_body_3582_; 
v_body_3582_ = lean_ctor_get(v_x_3580_, 2);
lean_inc_ref(v_body_3582_);
return v_body_3582_;
}
default: 
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3584_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3583_);
return v___x_3584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Lean_Expr_bindingBody_x21(v_x_3585_);
lean_dec_ref(v_x_3585_);
return v_res_3586_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3587_){
_start:
{
uint8_t v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; uint8_t v___x_3591_; 
v___x_3588_ = 0;
v___x_3589_ = lean_box(v___x_3588_);
v___x_3590_ = lean_panic_fn_borrowed(v___x_3589_, v_msg_3587_);
lean_dec(v___x_3589_);
v___x_3591_ = lean_unbox(v___x_3590_);
lean_dec(v___x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3592_){
_start:
{
uint8_t v_res_3593_; lean_object* v_r_3594_; 
v_res_3593_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3592_);
v_r_3594_ = lean_box(v_res_3593_);
return v_r_3594_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3596_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3597_ = lean_unsigned_to_nat(24u);
v___x_3598_ = lean_unsigned_to_nat(1042u);
v___x_3599_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3600_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3601_ = l_mkPanicMessageWithDecl(v___x_3600_, v___x_3599_, v___x_3598_, v___x_3597_, v___x_3596_);
return v___x_3601_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3602_){
_start:
{
switch(lean_obj_tag(v_x_3602_))
{
case 7:
{
uint8_t v_binderInfo_3603_; 
v_binderInfo_3603_ = lean_ctor_get_uint8(v_x_3602_, sizeof(void*)*3 + 8);
return v_binderInfo_3603_;
}
case 6:
{
uint8_t v_binderInfo_3604_; 
v_binderInfo_3604_ = lean_ctor_get_uint8(v_x_3602_, sizeof(void*)*3 + 8);
return v_binderInfo_3604_;
}
default: 
{
lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3606_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3605_);
return v___x_3606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3607_){
_start:
{
uint8_t v_res_3608_; lean_object* v_r_3609_; 
v_res_3608_ = l_Lean_Expr_bindingInfo_x21(v_x_3607_);
lean_dec_ref(v_x_3607_);
v_r_3609_ = lean_box(v_res_3608_);
return v_r_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3610_){
_start:
{
lean_object* v_binderName_3611_; 
v_binderName_3611_ = lean_ctor_get(v_x_3610_, 0);
lean_inc(v_binderName_3611_);
return v_binderName_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_Expr_forallName___redArg(v_x_3612_);
lean_dec_ref(v_x_3612_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3614_, lean_object* v_x_3615_){
_start:
{
lean_object* v_binderName_3616_; 
v_binderName_3616_ = lean_ctor_get(v_x_3614_, 0);
lean_inc(v_binderName_3616_);
return v_binderName_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3617_, lean_object* v_x_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_Expr_forallName(v_x_3617_, v_x_3618_);
lean_dec_ref(v_x_3617_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3620_){
_start:
{
lean_object* v_binderType_3621_; 
v_binderType_3621_ = lean_ctor_get(v_x_3620_, 1);
lean_inc_ref(v_binderType_3621_);
return v_binderType_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Lean_Expr_forallDomain___redArg(v_x_3622_);
lean_dec_ref(v_x_3622_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3624_, lean_object* v_x_3625_){
_start:
{
lean_object* v_binderType_3626_; 
v_binderType_3626_ = lean_ctor_get(v_x_3624_, 1);
lean_inc_ref(v_binderType_3626_);
return v_binderType_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3627_, lean_object* v_x_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Lean_Expr_forallDomain(v_x_3627_, v_x_3628_);
lean_dec_ref(v_x_3627_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3630_){
_start:
{
lean_object* v_body_3631_; 
v_body_3631_ = lean_ctor_get(v_x_3630_, 2);
lean_inc_ref(v_body_3631_);
return v_body_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Lean_Expr_forallBody___redArg(v_x_3632_);
lean_dec_ref(v_x_3632_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3634_, lean_object* v_x_3635_){
_start:
{
lean_object* v_body_3636_; 
v_body_3636_ = lean_ctor_get(v_x_3634_, 2);
lean_inc_ref(v_body_3636_);
return v_body_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3637_, lean_object* v_x_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Lean_Expr_forallBody(v_x_3637_, v_x_3638_);
lean_dec_ref(v_x_3637_);
return v_res_3639_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3640_){
_start:
{
uint8_t v_binderInfo_3641_; 
v_binderInfo_3641_ = lean_ctor_get_uint8(v_x_3640_, sizeof(void*)*3 + 8);
return v_binderInfo_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3642_){
_start:
{
uint8_t v_res_3643_; lean_object* v_r_3644_; 
v_res_3643_ = l_Lean_Expr_forallInfo___redArg(v_x_3642_);
lean_dec_ref(v_x_3642_);
v_r_3644_ = lean_box(v_res_3643_);
return v_r_3644_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3645_, lean_object* v_x_3646_){
_start:
{
uint8_t v_binderInfo_3647_; 
v_binderInfo_3647_ = lean_ctor_get_uint8(v_x_3645_, sizeof(void*)*3 + 8);
return v_binderInfo_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3648_, lean_object* v_x_3649_){
_start:
{
uint8_t v_res_3650_; lean_object* v_r_3651_; 
v_res_3650_ = l_Lean_Expr_forallInfo(v_x_3648_, v_x_3649_);
lean_dec_ref(v_x_3648_);
v_r_3651_ = lean_box(v_res_3650_);
return v_r_3651_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3654_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3655_ = lean_unsigned_to_nat(17u);
v___x_3656_ = lean_unsigned_to_nat(1058u);
v___x_3657_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3658_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3659_ = l_mkPanicMessageWithDecl(v___x_3658_, v___x_3657_, v___x_3656_, v___x_3655_, v___x_3654_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3660_){
_start:
{
if (lean_obj_tag(v_x_3660_) == 8)
{
lean_object* v_declName_3661_; 
v_declName_3661_ = lean_ctor_get(v_x_3660_, 0);
lean_inc(v_declName_3661_);
return v_declName_3661_;
}
else
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3663_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3662_);
return v___x_3663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lean_Expr_letName_x21(v_x_3664_);
lean_dec_ref(v_x_3664_);
return v_res_3665_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3667_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3668_ = lean_unsigned_to_nat(19u);
v___x_3669_ = lean_unsigned_to_nat(1062u);
v___x_3670_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3671_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3672_ = l_mkPanicMessageWithDecl(v___x_3671_, v___x_3670_, v___x_3669_, v___x_3668_, v___x_3667_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3673_){
_start:
{
if (lean_obj_tag(v_x_3673_) == 8)
{
lean_object* v_type_3674_; 
v_type_3674_ = lean_ctor_get(v_x_3673_, 1);
lean_inc_ref(v_type_3674_);
return v_type_3674_;
}
else
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3675_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3676_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3675_);
return v___x_3676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_Expr_letType_x21(v_x_3677_);
lean_dec_ref(v_x_3677_);
return v_res_3678_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3680_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3681_ = lean_unsigned_to_nat(21u);
v___x_3682_ = lean_unsigned_to_nat(1066u);
v___x_3683_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3684_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3685_ = l_mkPanicMessageWithDecl(v___x_3684_, v___x_3683_, v___x_3682_, v___x_3681_, v___x_3680_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3686_){
_start:
{
if (lean_obj_tag(v_x_3686_) == 8)
{
lean_object* v_value_3687_; 
v_value_3687_ = lean_ctor_get(v_x_3686_, 2);
lean_inc_ref(v_value_3687_);
return v_value_3687_;
}
else
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3689_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3688_);
return v___x_3689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_Expr_letValue_x21(v_x_3690_);
lean_dec_ref(v_x_3690_);
return v_res_3691_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3693_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3694_ = lean_unsigned_to_nat(23u);
v___x_3695_ = lean_unsigned_to_nat(1070u);
v___x_3696_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3697_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3698_ = l_mkPanicMessageWithDecl(v___x_3697_, v___x_3696_, v___x_3695_, v___x_3694_, v___x_3693_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3699_){
_start:
{
if (lean_obj_tag(v_x_3699_) == 8)
{
lean_object* v_body_3700_; 
v_body_3700_ = lean_ctor_get(v_x_3699_, 3);
lean_inc_ref(v_body_3700_);
return v_body_3700_;
}
else
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3702_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3701_);
return v___x_3702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l_Lean_Expr_letBody_x21(v_x_3703_);
lean_dec_ref(v_x_3703_);
return v_res_3704_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3705_){
_start:
{
uint8_t v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; uint8_t v___x_3709_; 
v___x_3706_ = 0;
v___x_3707_ = lean_box(v___x_3706_);
v___x_3708_ = lean_panic_fn_borrowed(v___x_3707_, v_msg_3705_);
lean_dec(v___x_3707_);
v___x_3709_ = lean_unbox(v___x_3708_);
lean_dec(v___x_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3710_){
_start:
{
uint8_t v_res_3711_; lean_object* v_r_3712_; 
v_res_3711_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3710_);
v_r_3712_ = lean_box(v_res_3711_);
return v_r_3712_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3714_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3715_ = lean_unsigned_to_nat(27u);
v___x_3716_ = lean_unsigned_to_nat(1074u);
v___x_3717_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3718_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3719_ = l_mkPanicMessageWithDecl(v___x_3718_, v___x_3717_, v___x_3716_, v___x_3715_, v___x_3714_);
return v___x_3719_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3720_){
_start:
{
if (lean_obj_tag(v_x_3720_) == 8)
{
uint8_t v_nondep_3721_; 
v_nondep_3721_ = lean_ctor_get_uint8(v_x_3720_, sizeof(void*)*4 + 8);
return v_nondep_3721_;
}
else
{
lean_object* v___x_3722_; uint8_t v___x_3723_; 
v___x_3722_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3723_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3722_);
return v___x_3723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3724_){
_start:
{
uint8_t v_res_3725_; lean_object* v_r_3726_; 
v_res_3725_ = l_Lean_Expr_letNondep_x21(v_x_3724_);
lean_dec_ref(v_x_3724_);
v_r_3726_ = lean_box(v_res_3725_);
return v_r_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3727_){
_start:
{
if (lean_obj_tag(v_x_3727_) == 10)
{
lean_object* v_expr_3728_; 
v_expr_3728_ = lean_ctor_get(v_x_3727_, 1);
v_x_3727_ = v_expr_3728_;
goto _start;
}
else
{
lean_inc_ref(v_x_3727_);
return v_x_3727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Lean_Expr_consumeMData(v_x_3730_);
lean_dec_ref(v_x_3730_);
return v_res_3731_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3734_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3735_ = lean_unsigned_to_nat(17u);
v___x_3736_ = lean_unsigned_to_nat(1082u);
v___x_3737_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3738_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3739_ = l_mkPanicMessageWithDecl(v___x_3738_, v___x_3737_, v___x_3736_, v___x_3735_, v___x_3734_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3740_){
_start:
{
if (lean_obj_tag(v_x_3740_) == 10)
{
lean_object* v_expr_3741_; 
v_expr_3741_ = lean_ctor_get(v_x_3740_, 1);
lean_inc_ref(v_expr_3741_);
return v_expr_3741_;
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3742_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3743_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3742_);
return v___x_3743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_Expr_mdataExpr_x21(v_x_3744_);
lean_dec_ref(v_x_3744_);
return v_res_3745_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3748_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3749_ = lean_unsigned_to_nat(18u);
v___x_3750_ = lean_unsigned_to_nat(1086u);
v___x_3751_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3752_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3753_ = l_mkPanicMessageWithDecl(v___x_3752_, v___x_3751_, v___x_3750_, v___x_3749_, v___x_3748_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3754_){
_start:
{
if (lean_obj_tag(v_x_3754_) == 11)
{
lean_object* v_struct_3755_; 
v_struct_3755_ = lean_ctor_get(v_x_3754_, 2);
lean_inc_ref(v_struct_3755_);
return v_struct_3755_;
}
else
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3756_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3757_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3756_);
return v___x_3757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l_Lean_Expr_projExpr_x21(v_x_3758_);
lean_dec_ref(v_x_3758_);
return v_res_3759_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3761_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3762_ = lean_unsigned_to_nat(18u);
v___x_3763_ = lean_unsigned_to_nat(1090u);
v___x_3764_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3765_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3766_ = l_mkPanicMessageWithDecl(v___x_3765_, v___x_3764_, v___x_3763_, v___x_3762_, v___x_3761_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3767_){
_start:
{
if (lean_obj_tag(v_x_3767_) == 11)
{
lean_object* v_idx_3768_; 
v_idx_3768_ = lean_ctor_get(v_x_3767_, 1);
lean_inc(v_idx_3768_);
return v_idx_3768_;
}
else
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3769_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3770_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3769_);
return v___x_3770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_Expr_projIdx_x21(v_x_3771_);
lean_dec_ref(v_x_3771_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3773_){
_start:
{
if (lean_obj_tag(v_x_3773_) == 7)
{
lean_object* v_body_3774_; 
v_body_3774_ = lean_ctor_get(v_x_3773_, 2);
v_x_3773_ = v_body_3774_;
goto _start;
}
else
{
lean_inc_ref(v_x_3773_);
return v_x_3773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_Lean_Expr_getForallBody(v_x_3776_);
lean_dec_ref(v_x_3776_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3778_, lean_object* v_x_3779_){
_start:
{
lean_object* v_zero_3780_; uint8_t v_isZero_3781_; 
v_zero_3780_ = lean_unsigned_to_nat(0u);
v_isZero_3781_ = lean_nat_dec_eq(v_x_3778_, v_zero_3780_);
if (v_isZero_3781_ == 1)
{
lean_dec(v_x_3778_);
lean_inc_ref(v_x_3779_);
return v_x_3779_;
}
else
{
if (lean_obj_tag(v_x_3779_) == 7)
{
lean_object* v_body_3782_; lean_object* v_one_3783_; lean_object* v_n_3784_; 
v_body_3782_ = lean_ctor_get(v_x_3779_, 2);
v_one_3783_ = lean_unsigned_to_nat(1u);
v_n_3784_ = lean_nat_sub(v_x_3778_, v_one_3783_);
lean_dec(v_x_3778_);
v_x_3778_ = v_n_3784_;
v_x_3779_ = v_body_3782_;
goto _start;
}
else
{
lean_dec(v_x_3778_);
lean_inc_ref(v_x_3779_);
return v_x_3779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3786_, lean_object* v_x_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3786_, v_x_3787_);
lean_dec_ref(v_x_3787_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3789_){
_start:
{
if (lean_obj_tag(v_x_3789_) == 7)
{
lean_object* v_binderName_3790_; lean_object* v_body_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v_binderName_3790_ = lean_ctor_get(v_x_3789_, 0);
v_body_3791_ = lean_ctor_get(v_x_3789_, 2);
v___x_3792_ = l_Lean_Expr_getForallBinderNames(v_body_3791_);
lean_inc(v_binderName_3790_);
v___x_3793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3793_, 0, v_binderName_3790_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
return v___x_3793_;
}
else
{
lean_object* v___x_3794_; 
v___x_3794_ = lean_box(0);
return v___x_3794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Lean_Expr_getForallBinderNames(v_x_3795_);
lean_dec_ref(v_x_3795_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3797_){
_start:
{
switch(lean_obj_tag(v_x_3797_))
{
case 10:
{
lean_object* v_expr_3798_; 
v_expr_3798_ = lean_ctor_get(v_x_3797_, 1);
v_x_3797_ = v_expr_3798_;
goto _start;
}
case 7:
{
lean_object* v_body_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v_body_3800_ = lean_ctor_get(v_x_3797_, 2);
v___x_3801_ = l_Lean_Expr_getNumHeadForalls(v_body_3800_);
v___x_3802_ = lean_unsigned_to_nat(1u);
v___x_3803_ = lean_nat_add(v___x_3801_, v___x_3802_);
lean_dec(v___x_3801_);
return v___x_3803_;
}
default: 
{
lean_object* v___x_3804_; 
v___x_3804_ = lean_unsigned_to_nat(0u);
return v___x_3804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Lean_Expr_getNumHeadForalls(v_x_3805_);
lean_dec_ref(v_x_3805_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3807_){
_start:
{
if (lean_obj_tag(v_x_3807_) == 5)
{
lean_object* v_fn_3808_; 
v_fn_3808_ = lean_ctor_get(v_x_3807_, 0);
v_x_3807_ = v_fn_3808_;
goto _start;
}
else
{
lean_inc_ref(v_x_3807_);
return v_x_3807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lean_Expr_getAppFn(v_x_3810_);
lean_dec_ref(v_x_3810_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3812_){
_start:
{
switch(lean_obj_tag(v_x_3812_))
{
case 5:
{
lean_object* v_fn_3813_; 
v_fn_3813_ = lean_ctor_get(v_x_3812_, 0);
v_x_3812_ = v_fn_3813_;
goto _start;
}
case 10:
{
lean_object* v_expr_3815_; 
v_expr_3815_ = lean_ctor_get(v_x_3812_, 1);
v_x_3812_ = v_expr_3815_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3812_);
return v_x_3812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_Expr_getAppFn_x27(v_x_3817_);
lean_dec_ref(v_x_3817_);
return v_res_3818_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3819_, lean_object* v_n_3820_){
_start:
{
lean_object* v___x_3821_; 
v___x_3821_ = l_Lean_Expr_getAppFn(v_e_3819_);
if (lean_obj_tag(v___x_3821_) == 4)
{
lean_object* v_declName_3822_; uint8_t v___x_3823_; 
v_declName_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_declName_3822_);
lean_dec_ref_known(v___x_3821_, 2);
v___x_3823_ = lean_name_eq(v_declName_3822_, v_n_3820_);
lean_dec(v_declName_3822_);
return v___x_3823_;
}
else
{
uint8_t v___x_3824_; 
lean_dec_ref(v___x_3821_);
v___x_3824_ = 0;
return v___x_3824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3825_, lean_object* v_n_3826_){
_start:
{
uint8_t v_res_3827_; lean_object* v_r_3828_; 
v_res_3827_ = l_Lean_Expr_isAppOf(v_e_3825_, v_n_3826_);
lean_dec(v_n_3826_);
lean_dec_ref(v_e_3825_);
v_r_3828_ = lean_box(v_res_3827_);
return v_r_3828_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3829_, lean_object* v_x_3830_, lean_object* v_x_3831_){
_start:
{
switch(lean_obj_tag(v_x_3829_))
{
case 4:
{
lean_object* v_declName_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; 
v_declName_3832_ = lean_ctor_get(v_x_3829_, 0);
v___x_3833_ = lean_unsigned_to_nat(0u);
v___x_3834_ = lean_nat_dec_eq(v_x_3831_, v___x_3833_);
lean_dec(v_x_3831_);
if (v___x_3834_ == 0)
{
return v___x_3834_;
}
else
{
uint8_t v___x_3835_; 
v___x_3835_ = lean_name_eq(v_declName_3832_, v_x_3830_);
return v___x_3835_;
}
}
case 5:
{
lean_object* v_fn_3836_; lean_object* v_zero_3837_; uint8_t v_isZero_3838_; 
v_fn_3836_ = lean_ctor_get(v_x_3829_, 0);
v_zero_3837_ = lean_unsigned_to_nat(0u);
v_isZero_3838_ = lean_nat_dec_eq(v_x_3831_, v_zero_3837_);
if (v_isZero_3838_ == 0)
{
lean_object* v_one_3839_; lean_object* v_n_3840_; 
v_one_3839_ = lean_unsigned_to_nat(1u);
v_n_3840_ = lean_nat_sub(v_x_3831_, v_one_3839_);
lean_dec(v_x_3831_);
v_x_3829_ = v_fn_3836_;
v_x_3831_ = v_n_3840_;
goto _start;
}
else
{
uint8_t v___x_3842_; 
lean_dec(v_x_3831_);
v___x_3842_ = 0;
return v___x_3842_;
}
}
default: 
{
uint8_t v___x_3843_; 
lean_dec(v_x_3831_);
v___x_3843_ = 0;
return v___x_3843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3844_, lean_object* v_x_3845_, lean_object* v_x_3846_){
_start:
{
uint8_t v_res_3847_; lean_object* v_r_3848_; 
v_res_3847_ = l_Lean_Expr_isAppOfArity(v_x_3844_, v_x_3845_, v_x_3846_);
lean_dec(v_x_3845_);
lean_dec_ref(v_x_3844_);
v_r_3848_ = lean_box(v_res_3847_);
return v_r_3848_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3849_, lean_object* v_x_3850_, lean_object* v_x_3851_){
_start:
{
switch(lean_obj_tag(v_x_3849_))
{
case 10:
{
lean_object* v_expr_3852_; 
v_expr_3852_ = lean_ctor_get(v_x_3849_, 1);
v_x_3849_ = v_expr_3852_;
goto _start;
}
case 4:
{
lean_object* v_declName_3854_; lean_object* v___x_3855_; uint8_t v___x_3856_; 
v_declName_3854_ = lean_ctor_get(v_x_3849_, 0);
v___x_3855_ = lean_unsigned_to_nat(0u);
v___x_3856_ = lean_nat_dec_eq(v_x_3851_, v___x_3855_);
lean_dec(v_x_3851_);
if (v___x_3856_ == 0)
{
return v___x_3856_;
}
else
{
uint8_t v___x_3857_; 
v___x_3857_ = lean_name_eq(v_declName_3854_, v_x_3850_);
return v___x_3857_;
}
}
case 5:
{
lean_object* v_fn_3858_; lean_object* v_zero_3859_; uint8_t v_isZero_3860_; 
v_fn_3858_ = lean_ctor_get(v_x_3849_, 0);
v_zero_3859_ = lean_unsigned_to_nat(0u);
v_isZero_3860_ = lean_nat_dec_eq(v_x_3851_, v_zero_3859_);
if (v_isZero_3860_ == 0)
{
lean_object* v_one_3861_; lean_object* v_n_3862_; 
v_one_3861_ = lean_unsigned_to_nat(1u);
v_n_3862_ = lean_nat_sub(v_x_3851_, v_one_3861_);
lean_dec(v_x_3851_);
v_x_3849_ = v_fn_3858_;
v_x_3851_ = v_n_3862_;
goto _start;
}
else
{
uint8_t v___x_3864_; 
lean_dec(v_x_3851_);
v___x_3864_ = 0;
return v___x_3864_;
}
}
default: 
{
uint8_t v___x_3865_; 
lean_dec(v_x_3851_);
v___x_3865_ = 0;
return v___x_3865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3866_, lean_object* v_x_3867_, lean_object* v_x_3868_){
_start:
{
uint8_t v_res_3869_; lean_object* v_r_3870_; 
v_res_3869_ = l_Lean_Expr_isAppOfArity_x27(v_x_3866_, v_x_3867_, v_x_3868_);
lean_dec(v_x_3867_);
lean_dec_ref(v_x_3866_);
v_r_3870_ = lean_box(v_res_3869_);
return v_r_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3871_, lean_object* v_x_3872_){
_start:
{
if (lean_obj_tag(v_x_3871_) == 5)
{
lean_object* v_fn_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v_fn_3873_ = lean_ctor_get(v_x_3871_, 0);
v___x_3874_ = lean_unsigned_to_nat(1u);
v___x_3875_ = lean_nat_add(v_x_3872_, v___x_3874_);
lean_dec(v_x_3872_);
v_x_3871_ = v_fn_3873_;
v_x_3872_ = v___x_3875_;
goto _start;
}
else
{
return v_x_3872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3877_, lean_object* v_x_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3877_, v_x_3878_);
lean_dec_ref(v_x_3877_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3880_){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = lean_unsigned_to_nat(0u);
v___x_3882_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3880_, v___x_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_Expr_getAppNumArgs(v_e_3883_);
lean_dec_ref(v_e_3883_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3885_, lean_object* v_a_3886_){
_start:
{
switch(lean_obj_tag(v_a_3885_))
{
case 10:
{
lean_object* v_expr_3887_; 
v_expr_3887_ = lean_ctor_get(v_a_3885_, 1);
v_a_3885_ = v_expr_3887_;
goto _start;
}
case 5:
{
lean_object* v_fn_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v_fn_3889_ = lean_ctor_get(v_a_3885_, 0);
v___x_3890_ = lean_unsigned_to_nat(1u);
v___x_3891_ = lean_nat_add(v_a_3886_, v___x_3890_);
lean_dec(v_a_3886_);
v_a_3885_ = v_fn_3889_;
v_a_3886_ = v___x_3891_;
goto _start;
}
default: 
{
return v_a_3886_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3893_, v_a_3894_);
lean_dec_ref(v_a_3893_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3896_){
_start:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = lean_unsigned_to_nat(0u);
v___x_3898_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3896_, v___x_3897_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3899_);
lean_dec_ref(v_e_3899_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3901_, lean_object* v_x_3902_){
_start:
{
lean_object* v_zero_3903_; uint8_t v_isZero_3904_; 
v_zero_3903_ = lean_unsigned_to_nat(0u);
v_isZero_3904_ = lean_nat_dec_eq(v_x_3901_, v_zero_3903_);
if (v_isZero_3904_ == 0)
{
if (lean_obj_tag(v_x_3902_) == 5)
{
lean_object* v_fn_3905_; lean_object* v_one_3906_; lean_object* v_n_3907_; 
v_fn_3905_ = lean_ctor_get(v_x_3902_, 0);
v_one_3906_ = lean_unsigned_to_nat(1u);
v_n_3907_ = lean_nat_sub(v_x_3901_, v_one_3906_);
lean_dec(v_x_3901_);
v_x_3901_ = v_n_3907_;
v_x_3902_ = v_fn_3905_;
goto _start;
}
else
{
lean_dec(v_x_3901_);
lean_inc_ref(v_x_3902_);
return v_x_3902_;
}
}
else
{
lean_dec(v_x_3901_);
lean_inc_ref(v_x_3902_);
return v_x_3902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_3909_, lean_object* v_x_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_Expr_getBoundedAppFn(v_x_3909_, v_x_3910_);
lean_dec_ref(v_x_3910_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_3912_, lean_object* v_x_3913_, lean_object* v_x_3914_){
_start:
{
if (lean_obj_tag(v_x_3912_) == 5)
{
lean_object* v_fn_3915_; lean_object* v_arg_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v_fn_3915_ = lean_ctor_get(v_x_3912_, 0);
lean_inc_ref(v_fn_3915_);
v_arg_3916_ = lean_ctor_get(v_x_3912_, 1);
lean_inc_ref(v_arg_3916_);
lean_dec_ref_known(v_x_3912_, 2);
v___x_3917_ = lean_array_set(v_x_3913_, v_x_3914_, v_arg_3916_);
v___x_3918_ = lean_unsigned_to_nat(1u);
v___x_3919_ = lean_nat_sub(v_x_3914_, v___x_3918_);
lean_dec(v_x_3914_);
v_x_3912_ = v_fn_3915_;
v_x_3913_ = v___x_3917_;
v_x_3914_ = v___x_3919_;
goto _start;
}
else
{
lean_dec(v_x_3914_);
lean_dec_ref(v_x_3912_);
return v_x_3913_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_3921_; lean_object* v_dummy_3922_; 
v___x_3921_ = lean_box(0);
v_dummy_3922_ = l_Lean_Expr_sort___override(v___x_3921_);
return v_dummy_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_3923_){
_start:
{
lean_object* v_dummy_3924_; lean_object* v_nargs_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v_dummy_3924_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3925_ = l_Lean_Expr_getAppNumArgs(v_e_3923_);
lean_inc(v_nargs_3925_);
v___x_3926_ = lean_mk_array(v_nargs_3925_, v_dummy_3924_);
v___x_3927_ = lean_unsigned_to_nat(1u);
v___x_3928_ = lean_nat_sub(v_nargs_3925_, v___x_3927_);
lean_dec(v_nargs_3925_);
v___x_3929_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3923_, v___x_3926_, v___x_3928_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_3930_, lean_object* v_x_3931_, lean_object* v_x_3932_){
_start:
{
if (lean_obj_tag(v_x_3930_) == 5)
{
lean_object* v_fn_3933_; lean_object* v_arg_3934_; lean_object* v_zero_3935_; uint8_t v_isZero_3936_; 
v_fn_3933_ = lean_ctor_get(v_x_3930_, 0);
lean_inc_ref(v_fn_3933_);
v_arg_3934_ = lean_ctor_get(v_x_3930_, 1);
lean_inc_ref(v_arg_3934_);
lean_dec_ref_known(v_x_3930_, 2);
v_zero_3935_ = lean_unsigned_to_nat(0u);
v_isZero_3936_ = lean_nat_dec_eq(v_x_3932_, v_zero_3935_);
if (v_isZero_3936_ == 0)
{
lean_object* v_one_3937_; lean_object* v_n_3938_; lean_object* v___x_3939_; 
v_one_3937_ = lean_unsigned_to_nat(1u);
v_n_3938_ = lean_nat_sub(v_x_3932_, v_one_3937_);
lean_dec(v_x_3932_);
v___x_3939_ = lean_array_set(v_x_3931_, v_n_3938_, v_arg_3934_);
v_x_3930_ = v_fn_3933_;
v_x_3931_ = v___x_3939_;
v_x_3932_ = v_n_3938_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3934_);
lean_dec_ref(v_fn_3933_);
lean_dec(v_x_3932_);
return v_x_3931_;
}
}
else
{
lean_dec(v_x_3932_);
lean_dec_ref(v_x_3930_);
return v_x_3931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_3941_, lean_object* v_e_3942_){
_start:
{
lean_object* v_dummy_3943_; lean_object* v___y_3945_; lean_object* v___x_3948_; uint8_t v___x_3949_; 
v_dummy_3943_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_3948_ = l_Lean_Expr_getAppNumArgs(v_e_3942_);
v___x_3949_ = lean_nat_dec_le(v_maxArgs_3941_, v___x_3948_);
if (v___x_3949_ == 0)
{
lean_dec(v_maxArgs_3941_);
v___y_3945_ = v___x_3948_;
goto v___jp_3944_;
}
else
{
lean_dec(v___x_3948_);
v___y_3945_ = v_maxArgs_3941_;
goto v___jp_3944_;
}
v___jp_3944_:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; 
lean_inc(v___y_3945_);
v___x_3946_ = lean_mk_array(v___y_3945_, v_dummy_3943_);
v___x_3947_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_3942_, v___x_3946_, v___y_3945_);
return v___x_3947_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_3950_, lean_object* v_x_3951_){
_start:
{
if (lean_obj_tag(v_x_3950_) == 5)
{
lean_object* v_fn_3952_; lean_object* v_arg_3953_; lean_object* v___x_3954_; 
v_fn_3952_ = lean_ctor_get(v_x_3950_, 0);
lean_inc_ref(v_fn_3952_);
v_arg_3953_ = lean_ctor_get(v_x_3950_, 1);
lean_inc_ref(v_arg_3953_);
lean_dec_ref_known(v_x_3950_, 2);
v___x_3954_ = lean_array_push(v_x_3951_, v_arg_3953_);
v_x_3950_ = v_fn_3952_;
v_x_3951_ = v___x_3954_;
goto _start;
}
else
{
lean_dec_ref(v_x_3950_);
return v_x_3951_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_3956_){
_start:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3957_ = l_Lean_Expr_getAppNumArgs(v_e_3956_);
v___x_3958_ = lean_mk_empty_array_with_capacity(v___x_3957_);
lean_dec(v___x_3957_);
v___x_3959_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3956_, v___x_3958_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_3960_, lean_object* v_x_3961_, lean_object* v_x_3962_, lean_object* v_x_3963_){
_start:
{
if (lean_obj_tag(v_x_3961_) == 5)
{
lean_object* v_fn_3964_; lean_object* v_arg_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v_fn_3964_ = lean_ctor_get(v_x_3961_, 0);
lean_inc_ref(v_fn_3964_);
v_arg_3965_ = lean_ctor_get(v_x_3961_, 1);
lean_inc_ref(v_arg_3965_);
lean_dec_ref_known(v_x_3961_, 2);
v___x_3966_ = lean_array_set(v_x_3962_, v_x_3963_, v_arg_3965_);
v___x_3967_ = lean_unsigned_to_nat(1u);
v___x_3968_ = lean_nat_sub(v_x_3963_, v___x_3967_);
lean_dec(v_x_3963_);
v_x_3961_ = v_fn_3964_;
v_x_3962_ = v___x_3966_;
v_x_3963_ = v___x_3968_;
goto _start;
}
else
{
lean_object* v___x_3970_; 
lean_dec(v_x_3963_);
v___x_3970_ = lean_apply_2(v_k_3960_, v_x_3961_, v_x_3962_);
return v___x_3970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_3971_, lean_object* v_k_3972_, lean_object* v_x_3973_, lean_object* v_x_3974_, lean_object* v_x_3975_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_Expr_withAppAux___redArg(v_k_3972_, v_x_3973_, v_x_3974_, v_x_3975_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_3977_, lean_object* v_k_3978_){
_start:
{
lean_object* v_dummy_3979_; lean_object* v_nargs_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v_dummy_3979_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3980_ = l_Lean_Expr_getAppNumArgs(v_e_3977_);
lean_inc(v_nargs_3980_);
v___x_3981_ = lean_mk_array(v_nargs_3980_, v_dummy_3979_);
v___x_3982_ = lean_unsigned_to_nat(1u);
v___x_3983_ = lean_nat_sub(v_nargs_3980_, v___x_3982_);
lean_dec(v_nargs_3980_);
v___x_3984_ = l_Lean_Expr_withAppAux___redArg(v_k_3978_, v_e_3977_, v___x_3981_, v___x_3983_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_3985_, lean_object* v_e_3986_, lean_object* v_k_3987_){
_start:
{
lean_object* v_dummy_3988_; lean_object* v_nargs_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v_dummy_3988_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3989_ = l_Lean_Expr_getAppNumArgs(v_e_3986_);
lean_inc(v_nargs_3989_);
v___x_3990_ = lean_mk_array(v_nargs_3989_, v_dummy_3988_);
v___x_3991_ = lean_unsigned_to_nat(1u);
v___x_3992_ = lean_nat_sub(v_nargs_3989_, v___x_3991_);
lean_dec(v_nargs_3989_);
v___x_3993_ = l_Lean_Expr_withAppAux___redArg(v_k_3987_, v_e_3986_, v___x_3990_, v___x_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_3994_, lean_object* v_x_3995_, lean_object* v_x_3996_){
_start:
{
if (lean_obj_tag(v_x_3994_) == 5)
{
lean_object* v_fn_3997_; lean_object* v_arg_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v_fn_3997_ = lean_ctor_get(v_x_3994_, 0);
lean_inc_ref(v_fn_3997_);
v_arg_3998_ = lean_ctor_get(v_x_3994_, 1);
lean_inc_ref(v_arg_3998_);
lean_dec_ref_known(v_x_3994_, 2);
v___x_3999_ = lean_array_set(v_x_3995_, v_x_3996_, v_arg_3998_);
v___x_4000_ = lean_unsigned_to_nat(1u);
v___x_4001_ = lean_nat_sub(v_x_3996_, v___x_4000_);
lean_dec(v_x_3996_);
v_x_3994_ = v_fn_3997_;
v_x_3995_ = v___x_3999_;
v_x_3996_ = v___x_4001_;
goto _start;
}
else
{
lean_object* v___x_4003_; lean_object* v___x_4004_; 
lean_dec(v_x_3996_);
v___x_4003_ = l_Lean_Expr_constName(v_x_3994_);
lean_dec_ref(v_x_3994_);
v___x_4004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
lean_ctor_set(v___x_4004_, 1, v_x_3995_);
return v___x_4004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_4005_){
_start:
{
lean_object* v_dummy_4006_; lean_object* v_nargs_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v_dummy_4006_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4007_ = l_Lean_Expr_getAppNumArgs(v_e_4005_);
lean_inc(v_nargs_4007_);
v___x_4008_ = lean_mk_array(v_nargs_4007_, v_dummy_4006_);
v___x_4009_ = lean_unsigned_to_nat(1u);
v___x_4010_ = lean_nat_sub(v_nargs_4007_, v___x_4009_);
lean_dec(v_nargs_4007_);
v___x_4011_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_4005_, v___x_4008_, v___x_4010_);
return v___x_4011_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Array_instInhabited___redArg();
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_4013_){
_start:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_4015_ = lean_panic_fn_borrowed(v___x_4014_, v_msg_4013_);
return v___x_4015_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4018_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_4019_ = lean_unsigned_to_nat(27u);
v___x_4020_ = lean_unsigned_to_nat(1247u);
v___x_4021_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_4022_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4023_ = l_mkPanicMessageWithDecl(v___x_4022_, v___x_4021_, v___x_4020_, v___x_4019_, v___x_4018_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_){
_start:
{
lean_object* v_zero_4027_; uint8_t v_isZero_4028_; 
v_zero_4027_ = lean_unsigned_to_nat(0u);
v_isZero_4028_ = lean_nat_dec_eq(v_a_4024_, v_zero_4027_);
if (v_isZero_4028_ == 1)
{
lean_dec_ref(v_a_4025_);
lean_dec(v_a_4024_);
return v_a_4026_;
}
else
{
if (lean_obj_tag(v_a_4025_) == 5)
{
lean_object* v_fn_4029_; lean_object* v_arg_4030_; lean_object* v_one_4031_; lean_object* v_n_4032_; lean_object* v___x_4033_; 
v_fn_4029_ = lean_ctor_get(v_a_4025_, 0);
lean_inc_ref(v_fn_4029_);
v_arg_4030_ = lean_ctor_get(v_a_4025_, 1);
lean_inc_ref(v_arg_4030_);
lean_dec_ref_known(v_a_4025_, 2);
v_one_4031_ = lean_unsigned_to_nat(1u);
v_n_4032_ = lean_nat_sub(v_a_4024_, v_one_4031_);
lean_dec(v_a_4024_);
v___x_4033_ = lean_array_set(v_a_4026_, v_n_4032_, v_arg_4030_);
v_a_4024_ = v_n_4032_;
v_a_4025_ = v_fn_4029_;
v_a_4026_ = v___x_4033_;
goto _start;
}
else
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
lean_dec_ref(v_a_4026_);
lean_dec_ref(v_a_4025_);
lean_dec(v_a_4024_);
v___x_4035_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_4036_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_4035_);
return v___x_4036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_4037_, lean_object* v_n_4038_){
_start:
{
lean_object* v_dummy_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v_dummy_4039_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_4038_);
v___x_4040_ = lean_mk_array(v_n_4038_, v_dummy_4039_);
v___x_4041_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_4038_, v_e_4037_, v___x_4040_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_4042_, lean_object* v_n_4043_){
_start:
{
lean_object* v_zero_4044_; uint8_t v_isZero_4045_; 
v_zero_4044_ = lean_unsigned_to_nat(0u);
v_isZero_4045_ = lean_nat_dec_eq(v_n_4043_, v_zero_4044_);
if (v_isZero_4045_ == 1)
{
lean_dec(v_n_4043_);
lean_inc_ref(v_e_4042_);
return v_e_4042_;
}
else
{
if (lean_obj_tag(v_e_4042_) == 5)
{
lean_object* v_fn_4046_; lean_object* v_one_4047_; lean_object* v_n_4048_; 
v_fn_4046_ = lean_ctor_get(v_e_4042_, 0);
v_one_4047_ = lean_unsigned_to_nat(1u);
v_n_4048_ = lean_nat_sub(v_n_4043_, v_one_4047_);
lean_dec(v_n_4043_);
v_e_4042_ = v_fn_4046_;
v_n_4043_ = v_n_4048_;
goto _start;
}
else
{
lean_dec(v_n_4043_);
lean_inc_ref(v_e_4042_);
return v_e_4042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_4050_, lean_object* v_n_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_Lean_Expr_stripArgsN(v_e_4050_, v_n_4051_);
lean_dec_ref(v_e_4050_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_4053_, lean_object* v_n_4054_){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4055_ = l_Lean_Expr_getAppNumArgs(v_e_4053_);
v___x_4056_ = lean_nat_sub(v___x_4055_, v_n_4054_);
lean_dec(v___x_4055_);
v___x_4057_ = l_Lean_Expr_stripArgsN(v_e_4053_, v___x_4056_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_4058_, lean_object* v_n_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l_Lean_Expr_getAppPrefix(v_e_4058_, v_n_4059_);
lean_dec(v_n_4059_);
lean_dec_ref(v_e_4058_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_4061_, lean_object* v_inst_4062_, lean_object* v_f_4063_, lean_object* v_x_4064_){
_start:
{
size_t v_sz_4065_; size_t v___x_4066_; lean_object* v___x_4067_; 
v_sz_4065_ = lean_array_size(v_args_4061_);
v___x_4066_ = ((size_t)0ULL);
v___x_4067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4062_, v_f_4063_, v_sz_4065_, v___x_4066_, v_args_4061_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_4069_, lean_object* v_inst_4070_, lean_object* v_f_4071_, lean_object* v_toSeq_4072_, lean_object* v_fn_4073_, lean_object* v_args_4074_){
_start:
{
lean_object* v_map_4075_; lean_object* v___f_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v_map_4075_ = lean_ctor_get(v_toFunctor_4069_, 0);
lean_inc(v_map_4075_);
lean_dec_ref(v_toFunctor_4069_);
lean_inc(v_f_4071_);
v___f_4076_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4076_, 0, v_args_4074_);
lean_closure_set(v___f_4076_, 1, v_inst_4070_);
lean_closure_set(v___f_4076_, 2, v_f_4071_);
v___x_4077_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_4078_ = lean_apply_1(v_f_4071_, v_fn_4073_);
v___x_4079_ = lean_apply_4(v_map_4075_, lean_box(0), lean_box(0), v___x_4077_, v___x_4078_);
v___x_4080_ = lean_apply_4(v_toSeq_4072_, lean_box(0), lean_box(0), v___x_4079_, v___f_4076_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_4081_, lean_object* v_f_4082_, lean_object* v_e_4083_){
_start:
{
lean_object* v_toApplicative_4084_; lean_object* v_toFunctor_4085_; lean_object* v_toSeq_4086_; lean_object* v___f_4087_; lean_object* v_dummy_4088_; lean_object* v_nargs_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v_toApplicative_4084_ = lean_ctor_get(v_inst_4081_, 0);
v_toFunctor_4085_ = lean_ctor_get(v_toApplicative_4084_, 0);
lean_inc_ref(v_toFunctor_4085_);
v_toSeq_4086_ = lean_ctor_get(v_toApplicative_4084_, 2);
lean_inc(v_toSeq_4086_);
v___f_4087_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_4087_, 0, v_toFunctor_4085_);
lean_closure_set(v___f_4087_, 1, v_inst_4081_);
lean_closure_set(v___f_4087_, 2, v_f_4082_);
lean_closure_set(v___f_4087_, 3, v_toSeq_4086_);
v_dummy_4088_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4089_ = l_Lean_Expr_getAppNumArgs(v_e_4083_);
lean_inc(v_nargs_4089_);
v___x_4090_ = lean_mk_array(v_nargs_4089_, v_dummy_4088_);
v___x_4091_ = lean_unsigned_to_nat(1u);
v___x_4092_ = lean_nat_sub(v_nargs_4089_, v___x_4091_);
lean_dec(v_nargs_4089_);
v___x_4093_ = l_Lean_Expr_withAppAux___redArg(v___f_4087_, v_e_4083_, v___x_4090_, v___x_4092_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_4094_, lean_object* v_inst_4095_, lean_object* v_f_4096_, lean_object* v_e_4097_){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Lean_Expr_traverseApp___redArg(v_inst_4095_, v_f_4096_, v_e_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_4099_, lean_object* v_x_4100_, lean_object* v_x_4101_){
_start:
{
if (lean_obj_tag(v_x_4100_) == 5)
{
lean_object* v_fn_4102_; lean_object* v_arg_4103_; lean_object* v___x_4104_; 
v_fn_4102_ = lean_ctor_get(v_x_4100_, 0);
lean_inc_ref(v_fn_4102_);
v_arg_4103_ = lean_ctor_get(v_x_4100_, 1);
lean_inc_ref(v_arg_4103_);
lean_dec_ref_known(v_x_4100_, 2);
v___x_4104_ = lean_array_push(v_x_4101_, v_arg_4103_);
v_x_4100_ = v_fn_4102_;
v_x_4101_ = v___x_4104_;
goto _start;
}
else
{
lean_object* v___x_4106_; 
v___x_4106_ = lean_apply_2(v_k_4099_, v_x_4100_, v_x_4101_);
return v___x_4106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_4107_, lean_object* v_k_4108_, lean_object* v_x_4109_, lean_object* v_x_4110_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4108_, v_x_4109_, v_x_4110_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_4112_, lean_object* v_k_4113_){
_start:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4114_ = l_Lean_Expr_getAppNumArgs(v_e_4112_);
v___x_4115_ = lean_mk_empty_array_with_capacity(v___x_4114_);
lean_dec(v___x_4114_);
v___x_4116_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4113_, v_e_4112_, v___x_4115_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_4117_, lean_object* v_e_4118_, lean_object* v_k_4119_){
_start:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4120_ = l_Lean_Expr_getAppNumArgs(v_e_4118_);
v___x_4121_ = lean_mk_empty_array_with_capacity(v___x_4120_);
lean_dec(v___x_4120_);
v___x_4122_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4119_, v_e_4118_, v___x_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_4123_, lean_object* v_x_4124_, lean_object* v_x_4125_){
_start:
{
if (lean_obj_tag(v_x_4123_) == 5)
{
lean_object* v_fn_4126_; lean_object* v_arg_4127_; lean_object* v_zero_4128_; uint8_t v_isZero_4129_; 
v_fn_4126_ = lean_ctor_get(v_x_4123_, 0);
v_arg_4127_ = lean_ctor_get(v_x_4123_, 1);
v_zero_4128_ = lean_unsigned_to_nat(0u);
v_isZero_4129_ = lean_nat_dec_eq(v_x_4124_, v_zero_4128_);
if (v_isZero_4129_ == 1)
{
lean_dec(v_x_4124_);
lean_inc_ref(v_arg_4127_);
return v_arg_4127_;
}
else
{
lean_object* v_one_4130_; lean_object* v_n_4131_; 
v_one_4130_ = lean_unsigned_to_nat(1u);
v_n_4131_ = lean_nat_sub(v_x_4124_, v_one_4130_);
lean_dec(v_x_4124_);
v_x_4123_ = v_fn_4126_;
v_x_4124_ = v_n_4131_;
goto _start;
}
}
else
{
lean_dec(v_x_4124_);
lean_inc_ref(v_x_4125_);
return v_x_4125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_4133_, lean_object* v_x_4134_, lean_object* v_x_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_Lean_Expr_getRevArgD(v_x_4133_, v_x_4134_, v_x_4135_);
lean_dec_ref(v_x_4135_);
lean_dec_ref(v_x_4133_);
return v_res_4136_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4139_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4140_ = lean_unsigned_to_nat(20u);
v___x_4141_ = lean_unsigned_to_nat(1288u);
v___x_4142_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4143_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4144_ = l_mkPanicMessageWithDecl(v___x_4143_, v___x_4142_, v___x_4141_, v___x_4140_, v___x_4139_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4145_, lean_object* v_x_4146_){
_start:
{
if (lean_obj_tag(v_x_4145_) == 5)
{
lean_object* v_fn_4147_; lean_object* v_arg_4148_; lean_object* v_zero_4149_; uint8_t v_isZero_4150_; 
v_fn_4147_ = lean_ctor_get(v_x_4145_, 0);
v_arg_4148_ = lean_ctor_get(v_x_4145_, 1);
v_zero_4149_ = lean_unsigned_to_nat(0u);
v_isZero_4150_ = lean_nat_dec_eq(v_x_4146_, v_zero_4149_);
if (v_isZero_4150_ == 1)
{
lean_dec(v_x_4146_);
lean_inc_ref(v_arg_4148_);
return v_arg_4148_;
}
else
{
lean_object* v_one_4151_; lean_object* v_n_4152_; 
v_one_4151_ = lean_unsigned_to_nat(1u);
v_n_4152_ = lean_nat_sub(v_x_4146_, v_one_4151_);
lean_dec(v_x_4146_);
v_x_4145_ = v_fn_4147_;
v_x_4146_ = v_n_4152_;
goto _start;
}
}
else
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
lean_dec(v_x_4146_);
v___x_4154_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4155_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4154_);
return v___x_4155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4156_, lean_object* v_x_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Lean_Expr_getRevArg_x21(v_x_4156_, v_x_4157_);
lean_dec_ref(v_x_4156_);
return v_res_4158_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v___x_4160_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4161_ = lean_unsigned_to_nat(20u);
v___x_4162_ = lean_unsigned_to_nat(1295u);
v___x_4163_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4164_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4165_ = l_mkPanicMessageWithDecl(v___x_4164_, v___x_4163_, v___x_4162_, v___x_4161_, v___x_4160_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4166_, lean_object* v_x_4167_){
_start:
{
switch(lean_obj_tag(v_x_4166_))
{
case 10:
{
lean_object* v_expr_4168_; 
v_expr_4168_ = lean_ctor_get(v_x_4166_, 1);
v_x_4166_ = v_expr_4168_;
goto _start;
}
case 5:
{
lean_object* v_fn_4170_; lean_object* v_arg_4171_; lean_object* v_zero_4172_; uint8_t v_isZero_4173_; 
v_fn_4170_ = lean_ctor_get(v_x_4166_, 0);
v_arg_4171_ = lean_ctor_get(v_x_4166_, 1);
v_zero_4172_ = lean_unsigned_to_nat(0u);
v_isZero_4173_ = lean_nat_dec_eq(v_x_4167_, v_zero_4172_);
if (v_isZero_4173_ == 1)
{
lean_dec(v_x_4167_);
lean_inc_ref(v_arg_4171_);
return v_arg_4171_;
}
else
{
lean_object* v_one_4174_; lean_object* v_n_4175_; 
v_one_4174_ = lean_unsigned_to_nat(1u);
v_n_4175_ = lean_nat_sub(v_x_4167_, v_one_4174_);
lean_dec(v_x_4167_);
v_x_4166_ = v_fn_4170_;
v_x_4167_ = v_n_4175_;
goto _start;
}
}
default: 
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_dec(v_x_4167_);
v___x_4177_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4178_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4177_);
return v___x_4178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4179_, lean_object* v_x_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4179_, v_x_4180_);
lean_dec_ref(v_x_4179_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4182_, lean_object* v_i_4183_, lean_object* v_n_4184_){
_start:
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4185_ = lean_nat_sub(v_n_4184_, v_i_4183_);
v___x_4186_ = lean_unsigned_to_nat(1u);
v___x_4187_ = lean_nat_sub(v___x_4185_, v___x_4186_);
lean_dec(v___x_4185_);
v___x_4188_ = l_Lean_Expr_getRevArg_x21(v_e_4182_, v___x_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4189_, lean_object* v_i_4190_, lean_object* v_n_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l_Lean_Expr_getArg_x21(v_e_4189_, v_i_4190_, v_n_4191_);
lean_dec(v_n_4191_);
lean_dec(v_i_4190_);
lean_dec_ref(v_e_4189_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4193_, lean_object* v_i_4194_, lean_object* v_n_4195_){
_start:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4196_ = lean_nat_sub(v_n_4195_, v_i_4194_);
v___x_4197_ = lean_unsigned_to_nat(1u);
v___x_4198_ = lean_nat_sub(v___x_4196_, v___x_4197_);
lean_dec(v___x_4196_);
v___x_4199_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4193_, v___x_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4200_, lean_object* v_i_4201_, lean_object* v_n_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l_Lean_Expr_getArg_x21_x27(v_e_4200_, v_i_4201_, v_n_4202_);
lean_dec(v_n_4202_);
lean_dec(v_i_4201_);
lean_dec_ref(v_e_4200_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4204_, lean_object* v_i_4205_, lean_object* v_v_u2080_4206_, lean_object* v_n_4207_){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4208_ = lean_nat_sub(v_n_4207_, v_i_4205_);
v___x_4209_ = lean_unsigned_to_nat(1u);
v___x_4210_ = lean_nat_sub(v___x_4208_, v___x_4209_);
lean_dec(v___x_4208_);
v___x_4211_ = l_Lean_Expr_getRevArgD(v_e_4204_, v___x_4210_, v_v_u2080_4206_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4212_, lean_object* v_i_4213_, lean_object* v_v_u2080_4214_, lean_object* v_n_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l_Lean_Expr_getArgD(v_e_4212_, v_i_4213_, v_v_u2080_4214_, v_n_4215_);
lean_dec(v_n_4215_);
lean_dec_ref(v_v_u2080_4214_);
lean_dec(v_i_4213_);
lean_dec_ref(v_e_4212_);
return v_res_4216_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4217_){
_start:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
v___x_4218_ = lean_unsigned_to_nat(0u);
v___x_4219_ = l_Lean_Expr_looseBVarRange(v_e_4217_);
v___x_4220_ = lean_nat_dec_lt(v___x_4218_, v___x_4219_);
lean_dec(v___x_4219_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4221_){
_start:
{
uint8_t v_res_4222_; lean_object* v_r_4223_; 
v_res_4222_ = l_Lean_Expr_hasLooseBVars(v_e_4221_);
lean_dec_ref(v_e_4221_);
v_r_4223_ = lean_box(v_res_4222_);
return v_r_4223_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4224_){
_start:
{
if (lean_obj_tag(v_e_4224_) == 7)
{
lean_object* v_body_4225_; uint8_t v___x_4226_; 
v_body_4225_ = lean_ctor_get(v_e_4224_, 2);
v___x_4226_ = l_Lean_Expr_hasLooseBVars(v_body_4225_);
if (v___x_4226_ == 0)
{
uint8_t v___x_4227_; 
v___x_4227_ = 1;
return v___x_4227_;
}
else
{
uint8_t v___x_4228_; 
v___x_4228_ = 0;
return v___x_4228_;
}
}
else
{
uint8_t v___x_4229_; 
v___x_4229_ = 0;
return v___x_4229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4230_){
_start:
{
uint8_t v_res_4231_; lean_object* v_r_4232_; 
v_res_4231_ = l_Lean_Expr_isArrow(v_e_4230_);
lean_dec_ref(v_e_4230_);
v_r_4232_ = lean_box(v_res_4231_);
return v_r_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4235_, lean_object* v_bvarIdx_4236_){
_start:
{
uint8_t v_res_4237_; lean_object* v_r_4238_; 
v_res_4237_ = lean_expr_has_loose_bvar(v_e_4235_, v_bvarIdx_4236_);
lean_dec(v_bvarIdx_4236_);
lean_dec_ref(v_e_4235_);
v_r_4238_ = lean_box(v_res_4237_);
return v_r_4238_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4239_, lean_object* v_bvarIdx_4240_, uint8_t v_considerRange_4241_){
_start:
{
if (lean_obj_tag(v_e_4239_) == 7)
{
lean_object* v_binderType_4242_; lean_object* v_body_4243_; uint8_t v_binderInfo_4244_; uint8_t v___y_4246_; uint8_t v___x_4250_; 
v_binderType_4242_ = lean_ctor_get(v_e_4239_, 1);
v_body_4243_ = lean_ctor_get(v_e_4239_, 2);
v_binderInfo_4244_ = lean_ctor_get_uint8(v_e_4239_, sizeof(void*)*3 + 8);
v___x_4250_ = lean_expr_has_loose_bvar(v_binderType_4242_, v_bvarIdx_4240_);
if (v___x_4250_ == 0)
{
v___y_4246_ = v___x_4250_;
goto v___jp_4245_;
}
else
{
uint8_t v___x_4251_; 
v___x_4251_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4244_);
if (v___x_4251_ == 0)
{
lean_object* v___x_4252_; uint8_t v___x_4253_; 
v___x_4252_ = lean_unsigned_to_nat(0u);
v___x_4253_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4243_, v___x_4252_, v_considerRange_4241_);
v___y_4246_ = v___x_4253_;
goto v___jp_4245_;
}
else
{
v___y_4246_ = v___x_4251_;
goto v___jp_4245_;
}
}
v___jp_4245_:
{
if (v___y_4246_ == 0)
{
lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4247_ = lean_unsigned_to_nat(1u);
v___x_4248_ = lean_nat_add(v_bvarIdx_4240_, v___x_4247_);
lean_dec(v_bvarIdx_4240_);
v_e_4239_ = v_body_4243_;
v_bvarIdx_4240_ = v___x_4248_;
goto _start;
}
else
{
lean_dec(v_bvarIdx_4240_);
return v___y_4246_;
}
}
}
else
{
if (v_considerRange_4241_ == 0)
{
lean_dec(v_bvarIdx_4240_);
return v_considerRange_4241_;
}
else
{
uint8_t v___x_4254_; 
v___x_4254_ = lean_expr_has_loose_bvar(v_e_4239_, v_bvarIdx_4240_);
lean_dec(v_bvarIdx_4240_);
return v___x_4254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4255_, lean_object* v_bvarIdx_4256_, lean_object* v_considerRange_4257_){
_start:
{
uint8_t v_considerRange_boxed_4258_; uint8_t v_res_4259_; lean_object* v_r_4260_; 
v_considerRange_boxed_4258_ = lean_unbox(v_considerRange_4257_);
v_res_4259_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4255_, v_bvarIdx_4256_, v_considerRange_boxed_4258_);
lean_dec_ref(v_e_4255_);
v_r_4260_ = lean_box(v_res_4259_);
return v_r_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4264_, lean_object* v_s_4265_, lean_object* v_d_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = lean_expr_lower_loose_bvars(v_e_4264_, v_s_4265_, v_d_4266_);
lean_dec(v_d_4266_);
lean_dec(v_s_4265_);
lean_dec_ref(v_e_4264_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4271_, lean_object* v_s_4272_, lean_object* v_d_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = lean_expr_lift_loose_bvars(v_e_4271_, v_s_4272_, v_d_4273_);
lean_dec(v_d_4273_);
lean_dec(v_s_4272_);
lean_dec_ref(v_e_4271_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4275_, lean_object* v_numParams_4276_, uint8_t v_considerRange_4277_){
_start:
{
if (lean_obj_tag(v_e_4275_) == 7)
{
lean_object* v_binderName_4278_; lean_object* v_binderType_4279_; lean_object* v_body_4280_; uint8_t v_binderInfo_4281_; lean_object* v_zero_4282_; uint8_t v_isZero_4283_; 
v_binderName_4278_ = lean_ctor_get(v_e_4275_, 0);
v_binderType_4279_ = lean_ctor_get(v_e_4275_, 1);
v_body_4280_ = lean_ctor_get(v_e_4275_, 2);
v_binderInfo_4281_ = lean_ctor_get_uint8(v_e_4275_, sizeof(void*)*3 + 8);
v_zero_4282_ = lean_unsigned_to_nat(0u);
v_isZero_4283_ = lean_nat_dec_eq(v_numParams_4276_, v_zero_4282_);
if (v_isZero_4283_ == 0)
{
lean_object* v_one_4284_; lean_object* v_n_4285_; lean_object* v_b_4286_; uint8_t v___y_4288_; uint8_t v___x_4292_; 
lean_inc_ref(v_body_4280_);
lean_inc_ref(v_binderType_4279_);
lean_inc(v_binderName_4278_);
lean_dec_ref_known(v_e_4275_, 3);
v_one_4284_ = lean_unsigned_to_nat(1u);
v_n_4285_ = lean_nat_sub(v_numParams_4276_, v_one_4284_);
v_b_4286_ = l_Lean_Expr_inferImplicit(v_body_4280_, v_n_4285_, v_considerRange_4277_);
lean_dec(v_n_4285_);
v___x_4292_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4281_);
if (v___x_4292_ == 0)
{
v___y_4288_ = v___x_4292_;
goto v___jp_4287_;
}
else
{
uint8_t v___x_4293_; 
v___x_4293_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4286_, v_zero_4282_, v_considerRange_4277_);
v___y_4288_ = v___x_4293_;
goto v___jp_4287_;
}
v___jp_4287_:
{
if (v___y_4288_ == 0)
{
lean_object* v___x_4289_; 
v___x_4289_ = l_Lean_Expr_forallE___override(v_binderName_4278_, v_binderType_4279_, v_b_4286_, v_binderInfo_4281_);
return v___x_4289_;
}
else
{
uint8_t v___x_4290_; lean_object* v___x_4291_; 
v___x_4290_ = 1;
v___x_4291_ = l_Lean_Expr_forallE___override(v_binderName_4278_, v_binderType_4279_, v_b_4286_, v___x_4290_);
return v___x_4291_;
}
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
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4294_, lean_object* v_numParams_4295_, lean_object* v_considerRange_4296_){
_start:
{
uint8_t v_considerRange_boxed_4297_; lean_object* v_res_4298_; 
v_considerRange_boxed_4297_ = lean_unbox(v_considerRange_4296_);
v_res_4298_ = l_Lean_Expr_inferImplicit(v_e_4294_, v_numParams_4295_, v_considerRange_boxed_4297_);
lean_dec(v_numParams_4295_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4299_, lean_object* v_binderInfos_x3f_4300_){
_start:
{
if (lean_obj_tag(v_e_4299_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4300_) == 1)
{
lean_object* v_binderName_4301_; lean_object* v_binderType_4302_; lean_object* v_body_4303_; uint8_t v_binderInfo_4304_; lean_object* v_head_4305_; lean_object* v_tail_4306_; lean_object* v_b_4307_; 
v_binderName_4301_ = lean_ctor_get(v_e_4299_, 0);
lean_inc(v_binderName_4301_);
v_binderType_4302_ = lean_ctor_get(v_e_4299_, 1);
lean_inc_ref(v_binderType_4302_);
v_body_4303_ = lean_ctor_get(v_e_4299_, 2);
lean_inc_ref(v_body_4303_);
v_binderInfo_4304_ = lean_ctor_get_uint8(v_e_4299_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4299_, 3);
v_head_4305_ = lean_ctor_get(v_binderInfos_x3f_4300_, 0);
v_tail_4306_ = lean_ctor_get(v_binderInfos_x3f_4300_, 1);
v_b_4307_ = l_Lean_Expr_updateForallBinderInfos(v_body_4303_, v_tail_4306_);
if (lean_obj_tag(v_head_4305_) == 0)
{
lean_object* v___x_4308_; 
v___x_4308_ = l_Lean_Expr_forallE___override(v_binderName_4301_, v_binderType_4302_, v_b_4307_, v_binderInfo_4304_);
return v___x_4308_;
}
else
{
lean_object* v_val_4309_; uint8_t v___x_4310_; lean_object* v___x_4311_; 
v_val_4309_ = lean_ctor_get(v_head_4305_, 0);
v___x_4310_ = lean_unbox(v_val_4309_);
v___x_4311_ = l_Lean_Expr_forallE___override(v_binderName_4301_, v_binderType_4302_, v_b_4307_, v___x_4310_);
return v___x_4311_;
}
}
else
{
return v_e_4299_;
}
}
else
{
return v_e_4299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4312_, lean_object* v_binderInfos_x3f_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l_Lean_Expr_updateForallBinderInfos(v_e_4312_, v_binderInfos_x3f_4313_);
lean_dec(v_binderInfos_x3f_4313_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4315_, lean_object* v_binderNames_x3f_4316_){
_start:
{
switch(lean_obj_tag(v_e_4315_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4316_) == 1)
{
lean_object* v_binderName_4317_; lean_object* v_binderType_4318_; lean_object* v_body_4319_; uint8_t v_binderInfo_4320_; lean_object* v_head_4321_; lean_object* v_tail_4322_; lean_object* v_b_4323_; 
v_binderName_4317_ = lean_ctor_get(v_e_4315_, 0);
lean_inc(v_binderName_4317_);
v_binderType_4318_ = lean_ctor_get(v_e_4315_, 1);
lean_inc_ref(v_binderType_4318_);
v_body_4319_ = lean_ctor_get(v_e_4315_, 2);
lean_inc_ref(v_body_4319_);
v_binderInfo_4320_ = lean_ctor_get_uint8(v_e_4315_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4315_, 3);
v_head_4321_ = lean_ctor_get(v_binderNames_x3f_4316_, 0);
lean_inc(v_head_4321_);
v_tail_4322_ = lean_ctor_get(v_binderNames_x3f_4316_, 1);
lean_inc(v_tail_4322_);
lean_dec_ref_known(v_binderNames_x3f_4316_, 2);
v_b_4323_ = l_Lean_Expr_updateBinderNames(v_body_4319_, v_tail_4322_);
if (lean_obj_tag(v_head_4321_) == 0)
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Lean_Expr_forallE___override(v_binderName_4317_, v_binderType_4318_, v_b_4323_, v_binderInfo_4320_);
return v___x_4324_;
}
else
{
lean_object* v_val_4325_; lean_object* v___x_4326_; 
lean_dec(v_binderName_4317_);
v_val_4325_ = lean_ctor_get(v_head_4321_, 0);
lean_inc(v_val_4325_);
lean_dec_ref_known(v_head_4321_, 1);
v___x_4326_ = l_Lean_Expr_forallE___override(v_val_4325_, v_binderType_4318_, v_b_4323_, v_binderInfo_4320_);
return v___x_4326_;
}
}
else
{
lean_dec(v_binderNames_x3f_4316_);
return v_e_4315_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4316_) == 1)
{
lean_object* v_binderName_4327_; lean_object* v_binderType_4328_; lean_object* v_body_4329_; uint8_t v_binderInfo_4330_; lean_object* v_head_4331_; lean_object* v_tail_4332_; lean_object* v_b_4333_; 
v_binderName_4327_ = lean_ctor_get(v_e_4315_, 0);
lean_inc(v_binderName_4327_);
v_binderType_4328_ = lean_ctor_get(v_e_4315_, 1);
lean_inc_ref(v_binderType_4328_);
v_body_4329_ = lean_ctor_get(v_e_4315_, 2);
lean_inc_ref(v_body_4329_);
v_binderInfo_4330_ = lean_ctor_get_uint8(v_e_4315_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4315_, 3);
v_head_4331_ = lean_ctor_get(v_binderNames_x3f_4316_, 0);
lean_inc(v_head_4331_);
v_tail_4332_ = lean_ctor_get(v_binderNames_x3f_4316_, 1);
lean_inc(v_tail_4332_);
lean_dec_ref_known(v_binderNames_x3f_4316_, 2);
v_b_4333_ = l_Lean_Expr_updateBinderNames(v_body_4329_, v_tail_4332_);
if (lean_obj_tag(v_head_4331_) == 0)
{
lean_object* v___x_4334_; 
v___x_4334_ = l_Lean_Expr_lam___override(v_binderName_4327_, v_binderType_4328_, v_b_4333_, v_binderInfo_4330_);
return v___x_4334_;
}
else
{
lean_object* v_val_4335_; lean_object* v___x_4336_; 
lean_dec(v_binderName_4327_);
v_val_4335_ = lean_ctor_get(v_head_4331_, 0);
lean_inc(v_val_4335_);
lean_dec_ref_known(v_head_4331_, 1);
v___x_4336_ = l_Lean_Expr_lam___override(v_val_4335_, v_binderType_4328_, v_b_4333_, v_binderInfo_4330_);
return v___x_4336_;
}
}
else
{
lean_dec(v_binderNames_x3f_4316_);
return v_e_4315_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4316_);
return v_e_4315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4339_, lean_object* v_subst_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = lean_expr_instantiate(v_e_4339_, v_subst_4340_);
lean_dec_ref(v_subst_4340_);
lean_dec_ref(v_e_4339_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4344_, lean_object* v_subst_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = lean_expr_instantiate1(v_e_4344_, v_subst_4345_);
lean_dec_ref(v_subst_4345_);
lean_dec_ref(v_e_4344_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4349_, lean_object* v_subst_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = lean_expr_instantiate_rev(v_e_4349_, v_subst_4350_);
lean_dec_ref(v_subst_4350_);
lean_dec_ref(v_e_4349_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4356_, lean_object* v_beginIdx_4357_, lean_object* v_endIdx_4358_, lean_object* v_subst_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = lean_expr_instantiate_range(v_e_4356_, v_beginIdx_4357_, v_endIdx_4358_, v_subst_4359_);
lean_dec_ref(v_subst_4359_);
lean_dec(v_endIdx_4358_);
lean_dec(v_beginIdx_4357_);
lean_dec_ref(v_e_4356_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4365_, lean_object* v_beginIdx_4366_, lean_object* v_endIdx_4367_, lean_object* v_subst_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = lean_expr_instantiate_rev_range(v_e_4365_, v_beginIdx_4366_, v_endIdx_4367_, v_subst_4368_);
lean_dec_ref(v_subst_4368_);
lean_dec(v_endIdx_4367_);
lean_dec(v_beginIdx_4366_);
lean_dec_ref(v_e_4365_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4372_, lean_object* v_xs_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = lean_expr_abstract(v_e_4372_, v_xs_4373_);
lean_dec_ref(v_xs_4373_);
lean_dec_ref(v_e_4372_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4378_, lean_object* v_n_4379_, lean_object* v_xs_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = lean_expr_abstract_range(v_e_4378_, v_n_4379_, v_xs_4380_);
lean_dec_ref(v_xs_4380_);
lean_dec(v_n_4379_);
lean_dec_ref(v_e_4378_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4382_, lean_object* v_fvar_4383_, lean_object* v_v_4384_){
_start:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4385_ = lean_unsigned_to_nat(1u);
v___x_4386_ = lean_mk_empty_array_with_capacity(v___x_4385_);
v___x_4387_ = lean_array_push(v___x_4386_, v_fvar_4383_);
v___x_4388_ = lean_expr_abstract(v_e_4382_, v___x_4387_);
lean_dec_ref(v___x_4387_);
v___x_4389_ = lean_expr_instantiate1(v___x_4388_, v_v_4384_);
lean_dec_ref(v___x_4388_);
return v___x_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4390_, lean_object* v_fvar_4391_, lean_object* v_v_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_Lean_Expr_replaceFVar(v_e_4390_, v_fvar_4391_, v_v_4392_);
lean_dec_ref(v_v_4392_);
lean_dec_ref(v_e_4390_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4394_, lean_object* v_fvarId_4395_, lean_object* v_v_4396_){
_start:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4397_ = l_Lean_Expr_fvar___override(v_fvarId_4395_);
v___x_4398_ = l_Lean_Expr_replaceFVar(v_e_4394_, v___x_4397_, v_v_4396_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4399_, lean_object* v_fvarId_4400_, lean_object* v_v_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l_Lean_Expr_replaceFVarId(v_e_4399_, v_fvarId_4400_, v_v_4401_);
lean_dec_ref(v_v_4401_);
lean_dec_ref(v_e_4399_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4403_, lean_object* v_fvars_4404_, lean_object* v_vs_4405_){
_start:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4406_ = lean_expr_abstract(v_e_4403_, v_fvars_4404_);
v___x_4407_ = lean_expr_instantiate_rev(v___x_4406_, v_vs_4405_);
lean_dec_ref(v___x_4406_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4408_, lean_object* v_fvars_4409_, lean_object* v_vs_4410_){
_start:
{
lean_object* v_res_4411_; 
v_res_4411_ = l_Lean_Expr_replaceFVars(v_e_4408_, v_fvars_4409_, v_vs_4410_);
lean_dec_ref(v_vs_4410_);
lean_dec_ref(v_fvars_4409_);
lean_dec_ref(v_e_4408_);
return v_res_4411_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4414_){
_start:
{
switch(lean_obj_tag(v_x_4414_))
{
case 4:
{
uint8_t v___x_4415_; 
v___x_4415_ = 1;
return v___x_4415_;
}
case 3:
{
uint8_t v___x_4416_; 
v___x_4416_ = 1;
return v___x_4416_;
}
case 0:
{
uint8_t v___x_4417_; 
v___x_4417_ = 1;
return v___x_4417_;
}
case 9:
{
uint8_t v___x_4418_; 
v___x_4418_ = 1;
return v___x_4418_;
}
case 2:
{
uint8_t v___x_4419_; 
v___x_4419_ = 1;
return v___x_4419_;
}
case 1:
{
uint8_t v___x_4420_; 
v___x_4420_ = 1;
return v___x_4420_;
}
default: 
{
uint8_t v___x_4421_; 
v___x_4421_ = 0;
return v___x_4421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4422_){
_start:
{
uint8_t v_res_4423_; lean_object* v_r_4424_; 
v_res_4423_ = l_Lean_Expr_isAtomic(v_x_4422_);
lean_dec_ref(v_x_4422_);
v_r_4424_ = lean_box(v_res_4423_);
return v_r_4424_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4430_ = lean_box(0);
v___x_4431_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4432_ = l_Lean_Expr_const___override(v___x_4431_, v___x_4430_);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4433_, lean_object* v_proof_4434_){
_start:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4435_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4436_ = l_Lean_mkAppB(v___x_4435_, v_pred_4433_, v_proof_4434_);
return v___x_4436_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4441_ = lean_box(0);
v___x_4442_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4443_ = l_Lean_Expr_const___override(v___x_4442_, v___x_4441_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4444_, lean_object* v_proof_4445_){
_start:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4446_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4447_ = l_Lean_mkAppB(v___x_4446_, v_pred_4444_, v_proof_4445_);
return v___x_4447_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4448_; 
v___x_4448_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4448_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4449_; 
v___x_4449_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4450_){
_start:
{
lean_inc_ref(v_val_4450_);
return v_val_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4451_);
lean_dec_ref(v_val_4451_);
return v_res_4452_;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4455_, lean_object* v_x_4456_){
_start:
{
uint8_t v___x_4457_; 
v___x_4457_ = lean_expr_equal(v_x_4455_, v_x_4456_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4458_, lean_object* v_x_4459_){
_start:
{
uint8_t v_res_4460_; lean_object* v_r_4461_; 
v_res_4460_ = l_Lean_ExprStructEq_beq(v_x_4458_, v_x_4459_);
lean_dec_ref(v_x_4459_);
lean_dec_ref(v_x_4458_);
v_r_4461_ = lean_box(v_res_4460_);
return v_r_4461_;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4462_){
_start:
{
uint64_t v___x_4463_; 
v___x_4463_ = l_Lean_Expr_hash(v_x_4462_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4464_){
_start:
{
uint64_t v_res_4465_; lean_object* v_r_4466_; 
v_res_4465_ = l_Lean_ExprStructEq_hash(v_x_4464_);
lean_dec_ref(v_x_4464_);
v_r_4466_ = lean_box_uint64(v_res_4465_);
return v_r_4466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4473_, lean_object* v_start_4474_, lean_object* v_b_4475_, lean_object* v_i_4476_){
_start:
{
uint8_t v___x_4477_; 
v___x_4477_ = lean_nat_dec_le(v_i_4476_, v_start_4474_);
if (v___x_4477_ == 0)
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v_i_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4478_ = l_Lean_instInhabitedExpr;
v___x_4479_ = lean_unsigned_to_nat(1u);
v_i_4480_ = lean_nat_sub(v_i_4476_, v___x_4479_);
lean_dec(v_i_4476_);
v___x_4481_ = lean_array_get_borrowed(v___x_4478_, v_revArgs_4473_, v_i_4480_);
lean_inc(v___x_4481_);
v___x_4482_ = l_Lean_Expr_app___override(v_b_4475_, v___x_4481_);
v_b_4475_ = v___x_4482_;
v_i_4476_ = v_i_4480_;
goto _start;
}
else
{
lean_dec(v_i_4476_);
return v_b_4475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4484_, lean_object* v_start_4485_, lean_object* v_b_4486_, lean_object* v_i_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4484_, v_start_4485_, v_b_4486_, v_i_4487_);
lean_dec(v_start_4485_);
lean_dec_ref(v_revArgs_4484_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4489_, lean_object* v_beginIdx_4490_, lean_object* v_endIdx_4491_, lean_object* v_revArgs_4492_){
_start:
{
lean_object* v___x_4493_; 
v___x_4493_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4492_, v_beginIdx_4490_, v_f_4489_, v_endIdx_4491_);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4494_, lean_object* v_beginIdx_4495_, lean_object* v_endIdx_4496_, lean_object* v_revArgs_4497_){
_start:
{
lean_object* v_res_4498_; 
v_res_4498_ = l_Lean_Expr_mkAppRevRange(v_f_4494_, v_beginIdx_4495_, v_endIdx_4496_, v_revArgs_4497_);
lean_dec_ref(v_revArgs_4497_);
lean_dec(v_beginIdx_4495_);
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4499_, uint8_t v_useZeta_4500_, uint8_t v_preserveMData_4501_, lean_object* v_sz_4502_, lean_object* v_e_4503_, lean_object* v_i_4504_){
_start:
{
switch(lean_obj_tag(v_e_4503_))
{
case 6:
{
lean_object* v_body_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; uint8_t v___x_4513_; 
v_body_4510_ = lean_ctor_get(v_e_4503_, 2);
lean_inc_ref(v_body_4510_);
lean_dec_ref_known(v_e_4503_, 3);
v___x_4511_ = lean_unsigned_to_nat(1u);
v___x_4512_ = lean_nat_add(v_i_4504_, v___x_4511_);
lean_dec(v_i_4504_);
v___x_4513_ = lean_nat_dec_lt(v___x_4512_, v_sz_4502_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; 
lean_dec(v___x_4512_);
v___x_4514_ = lean_expr_instantiate(v_body_4510_, v_revArgs_4499_);
lean_dec_ref(v_body_4510_);
return v___x_4514_;
}
else
{
v_e_4503_ = v_body_4510_;
v_i_4504_ = v___x_4512_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4500_ == 0)
{
goto v___jp_4505_;
}
else
{
lean_object* v_value_4516_; lean_object* v_body_4517_; uint8_t v___x_4518_; 
v_value_4516_ = lean_ctor_get(v_e_4503_, 2);
v_body_4517_ = lean_ctor_get(v_e_4503_, 3);
v___x_4518_ = lean_nat_dec_lt(v_i_4504_, v_sz_4502_);
if (v___x_4518_ == 0)
{
goto v___jp_4505_;
}
else
{
lean_object* v___x_4519_; 
lean_inc_ref(v_body_4517_);
lean_inc_ref(v_value_4516_);
lean_dec_ref_known(v_e_4503_, 4);
v___x_4519_ = lean_expr_instantiate1(v_body_4517_, v_value_4516_);
lean_dec_ref(v_value_4516_);
lean_dec_ref(v_body_4517_);
v_e_4503_ = v___x_4519_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4501_ == 0)
{
lean_object* v_expr_4521_; 
v_expr_4521_ = lean_ctor_get(v_e_4503_, 1);
lean_inc_ref(v_expr_4521_);
lean_dec_ref_known(v_e_4503_, 2);
v_e_4503_ = v_expr_4521_;
goto _start;
}
else
{
goto v___jp_4505_;
}
}
default: 
{
goto v___jp_4505_;
}
}
v___jp_4505_:
{
lean_object* v_n_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v_n_4506_ = lean_nat_sub(v_sz_4502_, v_i_4504_);
lean_dec(v_i_4504_);
v___x_4507_ = lean_expr_instantiate_range(v_e_4503_, v_n_4506_, v_sz_4502_, v_revArgs_4499_);
lean_dec_ref(v_e_4503_);
v___x_4508_ = lean_unsigned_to_nat(0u);
v___x_4509_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4499_, v___x_4508_, v___x_4507_, v_n_4506_);
return v___x_4509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4523_, lean_object* v_useZeta_4524_, lean_object* v_preserveMData_4525_, lean_object* v_sz_4526_, lean_object* v_e_4527_, lean_object* v_i_4528_){
_start:
{
uint8_t v_useZeta_boxed_4529_; uint8_t v_preserveMData_boxed_4530_; lean_object* v_res_4531_; 
v_useZeta_boxed_4529_ = lean_unbox(v_useZeta_4524_);
v_preserveMData_boxed_4530_ = lean_unbox(v_preserveMData_4525_);
v_res_4531_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4523_, v_useZeta_boxed_4529_, v_preserveMData_boxed_4530_, v_sz_4526_, v_e_4527_, v_i_4528_);
lean_dec(v_sz_4526_);
lean_dec_ref(v_revArgs_4523_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4532_, lean_object* v_revArgs_4533_, uint8_t v_useZeta_4534_, uint8_t v_preserveMData_4535_){
_start:
{
lean_object* v_sz_4536_; lean_object* v___x_4537_; uint8_t v___x_4538_; 
v_sz_4536_ = lean_array_get_size(v_revArgs_4533_);
v___x_4537_ = lean_unsigned_to_nat(0u);
v___x_4538_ = lean_nat_dec_eq(v_sz_4536_, v___x_4537_);
if (v___x_4538_ == 0)
{
lean_object* v___x_4539_; 
v___x_4539_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4533_, v_useZeta_4534_, v_preserveMData_4535_, v_sz_4536_, v_f_4532_, v___x_4537_);
return v___x_4539_;
}
else
{
return v_f_4532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4540_, lean_object* v_revArgs_4541_, lean_object* v_useZeta_4542_, lean_object* v_preserveMData_4543_){
_start:
{
uint8_t v_useZeta_boxed_4544_; uint8_t v_preserveMData_boxed_4545_; lean_object* v_res_4546_; 
v_useZeta_boxed_4544_ = lean_unbox(v_useZeta_4542_);
v_preserveMData_boxed_4545_ = lean_unbox(v_preserveMData_4543_);
v_res_4546_ = l_Lean_Expr_betaRev(v_f_4540_, v_revArgs_4541_, v_useZeta_boxed_4544_, v_preserveMData_boxed_4545_);
lean_dec_ref(v_revArgs_4541_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4547_, lean_object* v_args_4548_){
_start:
{
lean_object* v___x_4549_; uint8_t v___x_4550_; lean_object* v___x_4551_; 
v___x_4549_ = l_Array_reverse___redArg(v_args_4548_);
v___x_4550_ = 0;
v___x_4551_ = l_Lean_Expr_betaRev(v_f_4547_, v___x_4549_, v___x_4550_, v___x_4550_);
lean_dec_ref(v___x_4549_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4552_){
_start:
{
switch(lean_obj_tag(v_x_4552_))
{
case 6:
{
lean_object* v_body_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v_body_4553_ = lean_ctor_get(v_x_4552_, 2);
v___x_4554_ = l_Lean_Expr_getNumHeadLambdas(v_body_4553_);
v___x_4555_ = lean_unsigned_to_nat(1u);
v___x_4556_ = lean_nat_add(v___x_4554_, v___x_4555_);
lean_dec(v___x_4554_);
return v___x_4556_;
}
case 10:
{
lean_object* v_expr_4557_; 
v_expr_4557_ = lean_ctor_get(v_x_4552_, 1);
v_x_4552_ = v_expr_4557_;
goto _start;
}
default: 
{
lean_object* v___x_4559_; 
v___x_4559_ = lean_unsigned_to_nat(0u);
return v___x_4559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4560_){
_start:
{
lean_object* v_res_4561_; 
v_res_4561_ = l_Lean_Expr_getNumHeadLambdas(v_x_4560_);
lean_dec_ref(v_x_4560_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object* v_x_4562_){
_start:
{
switch(lean_obj_tag(v_x_4562_))
{
case 6:
{
lean_object* v_body_4563_; 
v_body_4563_ = lean_ctor_get(v_x_4562_, 2);
v_x_4562_ = v_body_4563_;
goto _start;
}
case 10:
{
lean_object* v_expr_4565_; 
v_expr_4565_ = lean_ctor_get(v_x_4562_, 1);
v_x_4562_ = v_expr_4565_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_4562_);
return v_x_4562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object* v_x_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l_Lean_Expr_getLambdaBody(v_x_4567_);
lean_dec_ref(v_x_4567_);
return v_res_4568_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4569_, lean_object* v_x_4570_){
_start:
{
switch(lean_obj_tag(v_x_4570_))
{
case 6:
{
uint8_t v___x_4571_; 
v___x_4571_ = 1;
return v___x_4571_;
}
case 8:
{
if (v_useZeta_4569_ == 0)
{
return v_useZeta_4569_;
}
else
{
lean_object* v_body_4572_; 
v_body_4572_ = lean_ctor_get(v_x_4570_, 3);
v_x_4570_ = v_body_4572_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4574_; 
v_expr_4574_ = lean_ctor_get(v_x_4570_, 1);
v_x_4570_ = v_expr_4574_;
goto _start;
}
default: 
{
uint8_t v___x_4576_; 
v___x_4576_ = 0;
return v___x_4576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4577_, lean_object* v_x_4578_){
_start:
{
uint8_t v_useZeta_boxed_4579_; uint8_t v_res_4580_; lean_object* v_r_4581_; 
v_useZeta_boxed_4579_ = lean_unbox(v_useZeta_4577_);
v_res_4580_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4579_, v_x_4578_);
lean_dec_ref(v_x_4578_);
v_r_4581_ = lean_box(v_res_4580_);
return v_r_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4582_){
_start:
{
lean_object* v_f_4583_; uint8_t v___x_4584_; uint8_t v___x_4585_; 
v_f_4583_ = l_Lean_Expr_getAppFn(v_e_4582_);
v___x_4584_ = 0;
v___x_4585_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4584_, v_f_4583_);
if (v___x_4585_ == 0)
{
lean_dec_ref(v_f_4583_);
return v_e_4582_;
}
else
{
lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4586_ = l_Lean_Expr_getAppNumArgs(v_e_4582_);
v___x_4587_ = lean_mk_empty_array_with_capacity(v___x_4586_);
lean_dec(v___x_4586_);
v___x_4588_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4582_, v___x_4587_);
v___x_4589_ = l_Lean_Expr_betaRev(v_f_4583_, v___x_4588_, v___x_4584_, v___x_4584_);
lean_dec_ref(v___x_4588_);
return v___x_4589_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4590_, uint8_t v_useZeta_4591_){
_start:
{
uint8_t v___x_4592_; 
v___x_4592_ = l_Lean_Expr_isApp(v_e_4590_);
if (v___x_4592_ == 0)
{
return v___x_4592_;
}
else
{
lean_object* v___x_4593_; uint8_t v___x_4594_; 
v___x_4593_ = l_Lean_Expr_getAppFn(v_e_4590_);
v___x_4594_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4591_, v___x_4593_);
lean_dec_ref(v___x_4593_);
return v___x_4594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4595_, lean_object* v_useZeta_4596_){
_start:
{
uint8_t v_useZeta_boxed_4597_; uint8_t v_res_4598_; lean_object* v_r_4599_; 
v_useZeta_boxed_4597_ = lean_unbox(v_useZeta_4596_);
v_res_4598_ = l_Lean_Expr_isHeadBetaTarget(v_e_4595_, v_useZeta_boxed_4597_);
lean_dec_ref(v_e_4595_);
v_r_4599_ = lean_box(v_res_4598_);
return v_r_4599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4600_, lean_object* v_x_4601_, lean_object* v_x_4602_){
_start:
{
lean_object* v_f_4604_; 
if (lean_obj_tag(v_x_4600_) == 5)
{
lean_object* v_arg_4608_; 
v_arg_4608_ = lean_ctor_get(v_x_4600_, 1);
if (lean_obj_tag(v_arg_4608_) == 0)
{
lean_object* v_fn_4609_; lean_object* v_deBruijnIndex_4610_; lean_object* v_zero_4611_; uint8_t v_isZero_4612_; 
v_fn_4609_ = lean_ctor_get(v_x_4600_, 0);
v_deBruijnIndex_4610_ = lean_ctor_get(v_arg_4608_, 0);
v_zero_4611_ = lean_unsigned_to_nat(0u);
v_isZero_4612_ = lean_nat_dec_eq(v_x_4601_, v_zero_4611_);
if (v_isZero_4612_ == 1)
{
lean_dec(v_x_4602_);
lean_dec(v_x_4601_);
v_f_4604_ = v_x_4600_;
goto v___jp_4603_;
}
else
{
uint8_t v___x_4613_; 
lean_inc(v_deBruijnIndex_4610_);
lean_inc_ref(v_fn_4609_);
lean_dec_ref_known(v_x_4600_, 2);
v___x_4613_ = lean_nat_dec_eq(v_deBruijnIndex_4610_, v_x_4602_);
lean_dec(v_deBruijnIndex_4610_);
if (v___x_4613_ == 0)
{
lean_object* v___x_4614_; 
lean_dec_ref(v_fn_4609_);
lean_dec(v_x_4602_);
lean_dec(v_x_4601_);
v___x_4614_ = lean_box(0);
return v___x_4614_;
}
else
{
lean_object* v_one_4615_; lean_object* v_n_4616_; lean_object* v___x_4617_; 
v_one_4615_ = lean_unsigned_to_nat(1u);
v_n_4616_ = lean_nat_sub(v_x_4601_, v_one_4615_);
lean_dec(v_x_4601_);
v___x_4617_ = lean_nat_add(v_x_4602_, v_one_4615_);
lean_dec(v_x_4602_);
v_x_4600_ = v_fn_4609_;
v_x_4601_ = v_n_4616_;
v_x_4602_ = v___x_4617_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4619_; uint8_t v_isZero_4620_; 
lean_dec(v_x_4602_);
v_zero_4619_ = lean_unsigned_to_nat(0u);
v_isZero_4620_ = lean_nat_dec_eq(v_x_4601_, v_zero_4619_);
lean_dec(v_x_4601_);
if (v_isZero_4620_ == 1)
{
v_f_4604_ = v_x_4600_;
goto v___jp_4603_;
}
else
{
lean_object* v___x_4621_; 
lean_dec_ref_known(v_x_4600_, 2);
v___x_4621_ = lean_box(0);
return v___x_4621_;
}
}
}
else
{
lean_object* v_zero_4622_; uint8_t v_isZero_4623_; 
lean_dec(v_x_4602_);
v_zero_4622_ = lean_unsigned_to_nat(0u);
v_isZero_4623_ = lean_nat_dec_eq(v_x_4601_, v_zero_4622_);
lean_dec(v_x_4601_);
if (v_isZero_4623_ == 1)
{
v_f_4604_ = v_x_4600_;
goto v___jp_4603_;
}
else
{
lean_object* v___x_4624_; 
lean_dec_ref(v_x_4600_);
v___x_4624_ = lean_box(0);
return v___x_4624_;
}
}
v___jp_4603_:
{
uint8_t v___x_4605_; 
v___x_4605_ = l_Lean_Expr_hasLooseBVars(v_f_4604_);
if (v___x_4605_ == 0)
{
lean_object* v___x_4606_; 
v___x_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4606_, 0, v_f_4604_);
return v___x_4606_;
}
else
{
lean_object* v___x_4607_; 
lean_dec_ref(v_f_4604_);
v___x_4607_ = lean_box(0);
return v___x_4607_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4625_, lean_object* v_x_4626_){
_start:
{
if (lean_obj_tag(v_x_4625_) == 6)
{
lean_object* v_body_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
v_body_4627_ = lean_ctor_get(v_x_4625_, 2);
lean_inc_ref(v_body_4627_);
lean_dec_ref_known(v_x_4625_, 3);
v___x_4628_ = lean_unsigned_to_nat(1u);
v___x_4629_ = lean_nat_add(v_x_4626_, v___x_4628_);
lean_dec(v_x_4626_);
v_x_4625_ = v_body_4627_;
v_x_4626_ = v___x_4629_;
goto _start;
}
else
{
lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4631_ = lean_unsigned_to_nat(0u);
v___x_4632_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4625_, v_x_4626_, v___x_4631_);
return v___x_4632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4633_){
_start:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4634_ = lean_unsigned_to_nat(0u);
v___x_4635_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4633_, v___x_4634_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4636_){
_start:
{
if (lean_obj_tag(v_x_4636_) == 6)
{
lean_object* v_body_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; 
v_body_4637_ = lean_ctor_get(v_x_4636_, 2);
lean_inc_ref(v_body_4637_);
lean_dec_ref_known(v_x_4636_, 3);
v___x_4638_ = lean_unsigned_to_nat(1u);
v___x_4639_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4637_, v___x_4638_);
return v___x_4639_;
}
else
{
lean_object* v___x_4640_; 
lean_dec_ref(v_x_4636_);
v___x_4640_ = lean_box(0);
return v___x_4640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4644_){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; uint8_t v___x_4647_; 
v___x_4645_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4646_ = lean_unsigned_to_nat(2u);
v___x_4647_ = l_Lean_Expr_isAppOfArity(v_e_4644_, v___x_4645_, v___x_4646_);
if (v___x_4647_ == 0)
{
lean_object* v___x_4648_; 
v___x_4648_ = lean_box(0);
return v___x_4648_;
}
else
{
lean_object* v___x_4649_; lean_object* v___x_4650_; 
v___x_4649_ = l_Lean_Expr_appArg_x21(v_e_4644_);
v___x_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4649_);
return v___x_4650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4651_){
_start:
{
lean_object* v_res_4652_; 
v_res_4652_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4651_);
lean_dec_ref(v_e_4651_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4656_){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; uint8_t v___x_4659_; 
v___x_4657_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4658_ = lean_unsigned_to_nat(2u);
v___x_4659_ = l_Lean_Expr_isAppOfArity(v_e_4656_, v___x_4657_, v___x_4658_);
if (v___x_4659_ == 0)
{
lean_object* v___x_4660_; 
v___x_4660_ = lean_box(0);
return v___x_4660_;
}
else
{
lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4661_ = l_Lean_Expr_appArg_x21(v_e_4656_);
v___x_4662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4662_, 0, v___x_4661_);
return v___x_4662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4663_);
lean_dec_ref(v_e_4663_);
return v_res_4664_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOutParam(lean_object* v_e_4668_){
_start:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; uint8_t v___x_4671_; 
v___x_4669_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4670_ = lean_unsigned_to_nat(1u);
v___x_4671_ = l_Lean_Expr_isAppOfArity(v_e_4668_, v___x_4669_, v___x_4670_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4672_){
_start:
{
uint8_t v_res_4673_; lean_object* v_r_4674_; 
v_res_4673_ = l_Lean_Expr_isOutParam(v_e_4672_);
lean_dec_ref(v_e_4672_);
v_r_4674_ = lean_box(v_res_4673_);
return v_r_4674_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4678_){
_start:
{
lean_object* v___x_4679_; lean_object* v___x_4680_; uint8_t v___x_4681_; 
v___x_4679_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4680_ = lean_unsigned_to_nat(1u);
v___x_4681_ = l_Lean_Expr_isAppOfArity(v_e_4678_, v___x_4679_, v___x_4680_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4682_){
_start:
{
uint8_t v_res_4683_; lean_object* v_r_4684_; 
v_res_4683_ = l_Lean_Expr_isSemiOutParam(v_e_4682_);
lean_dec_ref(v_e_4682_);
v_r_4684_ = lean_box(v_res_4683_);
return v_r_4684_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4685_){
_start:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; uint8_t v___x_4688_; 
v___x_4686_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4687_ = lean_unsigned_to_nat(2u);
v___x_4688_ = l_Lean_Expr_isAppOfArity(v_e_4685_, v___x_4686_, v___x_4687_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4689_){
_start:
{
uint8_t v_res_4690_; lean_object* v_r_4691_; 
v_res_4690_ = l_Lean_Expr_isOptParam(v_e_4689_);
lean_dec_ref(v_e_4689_);
v_r_4691_ = lean_box(v_res_4690_);
return v_r_4691_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4692_){
_start:
{
lean_object* v___x_4693_; lean_object* v___x_4694_; uint8_t v___x_4695_; 
v___x_4693_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4694_ = lean_unsigned_to_nat(2u);
v___x_4695_ = l_Lean_Expr_isAppOfArity(v_e_4692_, v___x_4693_, v___x_4694_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4696_){
_start:
{
uint8_t v_res_4697_; lean_object* v_r_4698_; 
v_res_4697_ = l_Lean_Expr_isAutoParam(v_e_4696_);
lean_dec_ref(v_e_4696_);
v_r_4698_ = lean_box(v_res_4697_);
return v_r_4698_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4699_){
_start:
{
lean_object* v___x_4700_; 
v___x_4700_ = l_Lean_Expr_getAppFn(v_e_4699_);
if (lean_obj_tag(v___x_4700_) == 4)
{
lean_object* v_declName_4701_; uint8_t v___y_4703_; lean_object* v___x_4708_; uint8_t v___x_4709_; 
v_declName_4701_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_declName_4701_);
lean_dec_ref_known(v___x_4700_, 2);
v___x_4708_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4709_ = lean_name_eq(v_declName_4701_, v___x_4708_);
if (v___x_4709_ == 0)
{
lean_object* v___x_4710_; uint8_t v___x_4711_; 
v___x_4710_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4711_ = lean_name_eq(v_declName_4701_, v___x_4710_);
v___y_4703_ = v___x_4711_;
goto v___jp_4702_;
}
else
{
v___y_4703_ = v___x_4709_;
goto v___jp_4702_;
}
v___jp_4702_:
{
if (v___y_4703_ == 0)
{
lean_object* v___x_4704_; uint8_t v___x_4705_; 
v___x_4704_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4705_ = lean_name_eq(v_declName_4701_, v___x_4704_);
if (v___x_4705_ == 0)
{
lean_object* v___x_4706_; uint8_t v___x_4707_; 
v___x_4706_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4707_ = lean_name_eq(v_declName_4701_, v___x_4706_);
lean_dec(v_declName_4701_);
return v___x_4707_;
}
else
{
lean_dec(v_declName_4701_);
return v___x_4705_;
}
}
else
{
lean_dec(v_declName_4701_);
return v___y_4703_;
}
}
}
else
{
uint8_t v___x_4712_; 
lean_dec_ref(v___x_4700_);
v___x_4712_ = 0;
return v___x_4712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4713_){
_start:
{
uint8_t v_res_4714_; lean_object* v_r_4715_; 
v_res_4714_ = l_Lean_Expr_isTypeAnnotation(v_e_4713_);
lean_dec_ref(v_e_4713_);
v_r_4715_ = lean_box(v_res_4714_);
return v_r_4715_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4716_){
_start:
{
uint8_t v___y_4718_; uint8_t v___y_4722_; uint8_t v___x_4728_; 
v___x_4728_ = l_Lean_Expr_isOptParam(v_e_4716_);
if (v___x_4728_ == 0)
{
uint8_t v___x_4729_; 
v___x_4729_ = l_Lean_Expr_isAutoParam(v_e_4716_);
v___y_4722_ = v___x_4729_;
goto v___jp_4721_;
}
else
{
v___y_4722_ = v___x_4728_;
goto v___jp_4721_;
}
v___jp_4717_:
{
if (v___y_4718_ == 0)
{
return v_e_4716_;
}
else
{
lean_object* v___x_4719_; 
v___x_4719_ = l_Lean_Expr_appArg_x21(v_e_4716_);
lean_dec_ref(v_e_4716_);
v_e_4716_ = v___x_4719_;
goto _start;
}
}
v___jp_4721_:
{
if (v___y_4722_ == 0)
{
uint8_t v___x_4723_; 
v___x_4723_ = l_Lean_Expr_isOutParam(v_e_4716_);
if (v___x_4723_ == 0)
{
uint8_t v___x_4724_; 
v___x_4724_ = l_Lean_Expr_isSemiOutParam(v_e_4716_);
v___y_4718_ = v___x_4724_;
goto v___jp_4717_;
}
else
{
v___y_4718_ = v___x_4723_;
goto v___jp_4717_;
}
}
else
{
lean_object* v___x_4725_; lean_object* v___x_4726_; 
v___x_4725_ = l_Lean_Expr_appFn_x21(v_e_4716_);
lean_dec_ref(v_e_4716_);
v___x_4726_ = l_Lean_Expr_appArg_x21(v___x_4725_);
lean_dec_ref(v___x_4725_);
v_e_4716_ = v___x_4726_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4730_){
_start:
{
lean_object* v___x_4731_; lean_object* v_e_x27_4732_; uint8_t v___x_4733_; 
v___x_4731_ = l_Lean_Expr_consumeMData(v_e_4730_);
v_e_x27_4732_ = lean_expr_consume_type_annotations(v___x_4731_);
v___x_4733_ = lean_expr_eqv(v_e_x27_4732_, v_e_4730_);
if (v___x_4733_ == 0)
{
lean_dec_ref(v_e_4730_);
v_e_4730_ = v_e_x27_4732_;
goto _start;
}
else
{
lean_dec_ref(v_e_x27_4732_);
return v_e_4730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4735_){
_start:
{
lean_object* v_fn_4736_; lean_object* v___x_4737_; 
v_fn_4736_ = lean_ctor_get(v_e_4735_, 0);
lean_inc_ref(v_fn_4736_);
lean_dec_ref(v_e_4735_);
v___x_4737_ = l_Lean_Expr_cleanupAnnotations(v_fn_4736_);
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* v_e_4738_, lean_object* v_h_4739_){
_start:
{
lean_object* v___x_4740_; 
v___x_4740_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4738_);
return v___x_4740_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4744_){
_start:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; uint8_t v___x_4747_; 
v___x_4745_ = l_Lean_Expr_cleanupAnnotations(v_e_4744_);
v___x_4746_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4747_ = l_Lean_Expr_isConstOf(v___x_4745_, v___x_4746_);
lean_dec_ref(v___x_4745_);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4748_){
_start:
{
uint8_t v_res_4749_; lean_object* v_r_4750_; 
v_res_4749_ = l_Lean_Expr_isFalse(v_e_4748_);
v_r_4750_ = lean_box(v_res_4749_);
return v_r_4750_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4754_){
_start:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; uint8_t v___x_4757_; 
v___x_4755_ = l_Lean_Expr_cleanupAnnotations(v_e_4754_);
v___x_4756_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4757_ = l_Lean_Expr_isConstOf(v___x_4755_, v___x_4756_);
lean_dec_ref(v___x_4755_);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4758_){
_start:
{
uint8_t v_res_4759_; lean_object* v_r_4760_; 
v_res_4759_ = l_Lean_Expr_isTrue(v_e_4758_);
v_r_4760_ = lean_box(v_res_4759_);
return v_r_4760_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object* v_e_4765_){
_start:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; uint8_t v___x_4768_; 
v___x_4766_ = l_Lean_Expr_cleanupAnnotations(v_e_4765_);
v___x_4767_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_4768_ = l_Lean_Expr_isConstOf(v___x_4766_, v___x_4767_);
lean_dec_ref(v___x_4766_);
return v___x_4768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object* v_e_4769_){
_start:
{
uint8_t v_res_4770_; lean_object* v_r_4771_; 
v_res_4770_ = l_Lean_Expr_isBoolFalse(v_e_4769_);
v_r_4771_ = lean_box(v_res_4770_);
return v_r_4771_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object* v_e_4775_){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; uint8_t v___x_4778_; 
v___x_4776_ = l_Lean_Expr_cleanupAnnotations(v_e_4775_);
v___x_4777_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_4778_ = l_Lean_Expr_isConstOf(v___x_4776_, v___x_4777_);
lean_dec_ref(v___x_4776_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object* v_e_4779_){
_start:
{
uint8_t v_res_4780_; lean_object* v_r_4781_; 
v_res_4780_ = l_Lean_Expr_isBoolTrue(v_e_4779_);
v_r_4781_ = lean_box(v_res_4780_);
return v_r_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* v_x_4782_){
_start:
{
switch(lean_obj_tag(v_x_4782_))
{
case 10:
{
lean_object* v_expr_4783_; 
v_expr_4783_ = lean_ctor_get(v_x_4782_, 1);
lean_inc_ref(v_expr_4783_);
lean_dec_ref_known(v_x_4782_, 2);
v_x_4782_ = v_expr_4783_;
goto _start;
}
case 7:
{
lean_object* v_body_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; 
v_body_4785_ = lean_ctor_get(v_x_4782_, 2);
lean_inc_ref(v_body_4785_);
lean_dec_ref_known(v_x_4782_, 3);
v___x_4786_ = l_Lean_Expr_getForallArity(v_body_4785_);
v___x_4787_ = lean_unsigned_to_nat(1u);
v___x_4788_ = lean_nat_add(v___x_4786_, v___x_4787_);
lean_dec(v___x_4786_);
return v___x_4788_;
}
default: 
{
uint8_t v___x_4789_; uint8_t v___x_4790_; 
v___x_4789_ = 0;
v___x_4790_ = l_Lean_Expr_isHeadBetaTarget(v_x_4782_, v___x_4789_);
if (v___x_4790_ == 0)
{
lean_object* v_e_x27_4791_; uint8_t v___x_4792_; 
lean_inc_ref(v_x_4782_);
v_e_x27_4791_ = l_Lean_Expr_cleanupAnnotations(v_x_4782_);
v___x_4792_ = lean_expr_eqv(v_x_4782_, v_e_x27_4791_);
lean_dec_ref(v_x_4782_);
if (v___x_4792_ == 0)
{
v_x_4782_ = v_e_x27_4791_;
goto _start;
}
else
{
if (v___x_4790_ == 0)
{
lean_object* v___x_4794_; 
lean_dec_ref(v_e_x27_4791_);
v___x_4794_ = lean_unsigned_to_nat(0u);
return v___x_4794_;
}
else
{
v_x_4782_ = v_e_x27_4791_;
goto _start;
}
}
}
else
{
lean_object* v___x_4796_; 
v___x_4796_ = l_Lean_Expr_headBeta(v_x_4782_);
v_x_4782_ = v___x_4796_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4798_){
_start:
{
lean_object* v___x_4799_; uint8_t v___x_4800_; 
v___x_4799_ = l_Lean_Expr_cleanupAnnotations(v_e_4798_);
v___x_4800_ = l_Lean_Expr_isApp(v___x_4799_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; 
lean_dec_ref(v___x_4799_);
v___x_4801_ = lean_box(0);
return v___x_4801_;
}
else
{
lean_object* v___x_4802_; uint8_t v___x_4803_; 
v___x_4802_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4799_);
v___x_4803_ = l_Lean_Expr_isApp(v___x_4802_);
if (v___x_4803_ == 0)
{
lean_object* v___x_4804_; 
lean_dec_ref(v___x_4802_);
v___x_4804_ = lean_box(0);
return v___x_4804_;
}
else
{
lean_object* v_arg_4805_; lean_object* v___x_4806_; uint8_t v___x_4807_; 
v_arg_4805_ = lean_ctor_get(v___x_4802_, 1);
lean_inc_ref(v_arg_4805_);
v___x_4806_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4802_);
v___x_4807_ = l_Lean_Expr_isApp(v___x_4806_);
if (v___x_4807_ == 0)
{
lean_object* v___x_4808_; 
lean_dec_ref(v___x_4806_);
lean_dec_ref(v_arg_4805_);
v___x_4808_ = lean_box(0);
return v___x_4808_;
}
else
{
lean_object* v___x_4809_; lean_object* v___x_4810_; uint8_t v___x_4811_; 
v___x_4809_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4806_);
v___x_4810_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4811_ = l_Lean_Expr_isConstOf(v___x_4809_, v___x_4810_);
lean_dec_ref(v___x_4809_);
if (v___x_4811_ == 0)
{
lean_object* v___x_4812_; 
lean_dec_ref(v_arg_4805_);
v___x_4812_ = lean_box(0);
return v___x_4812_;
}
else
{
if (lean_obj_tag(v_arg_4805_) == 9)
{
lean_object* v_a_4813_; 
v_a_4813_ = lean_ctor_get(v_arg_4805_, 0);
lean_inc_ref(v_a_4813_);
lean_dec_ref_known(v_arg_4805_, 1);
if (lean_obj_tag(v_a_4813_) == 0)
{
lean_object* v_val_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4821_; 
v_val_4814_ = lean_ctor_get(v_a_4813_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v_a_4813_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4816_ = v_a_4813_;
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_val_4814_);
lean_dec(v_a_4813_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4819_; 
if (v_isShared_4817_ == 0)
{
lean_ctor_set_tag(v___x_4816_, 1);
v___x_4819_ = v___x_4816_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_val_4814_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
else
{
lean_object* v___x_4822_; 
lean_dec_ref(v_a_4813_);
v___x_4822_ = lean_box(0);
return v___x_4822_;
}
}
else
{
lean_object* v___x_4823_; 
lean_dec_ref(v_arg_4805_);
v___x_4823_ = lean_box(0);
return v___x_4823_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4829_){
_start:
{
lean_object* v___x_4842_; uint8_t v___x_4843_; 
lean_inc_ref(v_e_4829_);
v___x_4842_ = l_Lean_Expr_cleanupAnnotations(v_e_4829_);
v___x_4843_ = l_Lean_Expr_isApp(v___x_4842_);
if (v___x_4843_ == 0)
{
lean_dec_ref(v___x_4842_);
goto v___jp_4830_;
}
else
{
lean_object* v_arg_4844_; lean_object* v___x_4845_; uint8_t v___x_4846_; 
v_arg_4844_ = lean_ctor_get(v___x_4842_, 1);
lean_inc_ref(v_arg_4844_);
v___x_4845_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4842_);
v___x_4846_ = l_Lean_Expr_isApp(v___x_4845_);
if (v___x_4846_ == 0)
{
lean_dec_ref(v___x_4845_);
lean_dec_ref(v_arg_4844_);
goto v___jp_4830_;
}
else
{
lean_object* v___x_4847_; uint8_t v___x_4848_; 
v___x_4847_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4845_);
v___x_4848_ = l_Lean_Expr_isApp(v___x_4847_);
if (v___x_4848_ == 0)
{
lean_dec_ref(v___x_4847_);
lean_dec_ref(v_arg_4844_);
goto v___jp_4830_;
}
else
{
lean_object* v___x_4849_; lean_object* v___x_4850_; uint8_t v___x_4851_; 
v___x_4849_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4847_);
v___x_4850_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4851_ = l_Lean_Expr_isConstOf(v___x_4849_, v___x_4850_);
lean_dec_ref(v___x_4849_);
if (v___x_4851_ == 0)
{
lean_dec_ref(v_arg_4844_);
goto v___jp_4830_;
}
else
{
lean_object* v___x_4852_; 
lean_dec_ref(v_e_4829_);
v___x_4852_ = l_Lean_Expr_nat_x3f(v_arg_4844_);
if (lean_obj_tag(v___x_4852_) == 0)
{
lean_object* v___x_4853_; 
v___x_4853_ = lean_box(0);
return v___x_4853_;
}
else
{
lean_object* v_val_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4866_; 
v_val_4854_ = lean_ctor_get(v___x_4852_, 0);
v_isSharedCheck_4866_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_4866_ == 0)
{
v___x_4856_ = v___x_4852_;
v_isShared_4857_ = v_isSharedCheck_4866_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_val_4854_);
lean_dec(v___x_4852_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4866_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4858_; uint8_t v___x_4859_; 
v___x_4858_ = lean_unsigned_to_nat(0u);
v___x_4859_ = lean_nat_dec_eq(v_val_4854_, v___x_4858_);
if (v___x_4859_ == 0)
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4863_; 
v___x_4860_ = lean_nat_to_int(v_val_4854_);
v___x_4861_ = lean_int_neg(v___x_4860_);
lean_dec(v___x_4860_);
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 0, v___x_4861_);
v___x_4863_ = v___x_4856_;
goto v_reusejp_4862_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v___x_4861_);
v___x_4863_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4862_;
}
v_reusejp_4862_:
{
return v___x_4863_;
}
}
else
{
lean_object* v___x_4865_; 
lean_del_object(v___x_4856_);
lean_dec(v_val_4854_);
v___x_4865_ = lean_box(0);
return v___x_4865_;
}
}
}
}
}
}
}
v___jp_4830_:
{
lean_object* v___x_4831_; 
v___x_4831_ = l_Lean_Expr_nat_x3f(v_e_4829_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_object* v___x_4832_; 
v___x_4832_ = lean_box(0);
return v___x_4832_;
}
else
{
lean_object* v_val_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4841_; 
v_val_4833_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4835_ = v___x_4831_;
v_isShared_4836_ = v_isSharedCheck_4841_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_val_4833_);
lean_dec(v___x_4831_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4841_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4837_; lean_object* v___x_4839_; 
v___x_4837_ = lean_nat_to_int(v_val_4833_);
if (v_isShared_4836_ == 0)
{
lean_ctor_set(v___x_4835_, 0, v___x_4837_);
v___x_4839_ = v___x_4835_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v___x_4837_);
v___x_4839_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
return v___x_4839_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4867_, lean_object* v_e_4868_){
_start:
{
uint8_t v___x_4869_; lean_object* v_d_4871_; lean_object* v_b_4872_; 
v___x_4869_ = l_Lean_Expr_hasFVar(v_e_4868_);
if (v___x_4869_ == 0)
{
lean_dec_ref(v_e_4868_);
lean_dec_ref(v_p_4867_);
return v___x_4869_;
}
else
{
switch(lean_obj_tag(v_e_4868_))
{
case 7:
{
lean_object* v_binderType_4875_; lean_object* v_body_4876_; 
v_binderType_4875_ = lean_ctor_get(v_e_4868_, 1);
lean_inc_ref(v_binderType_4875_);
v_body_4876_ = lean_ctor_get(v_e_4868_, 2);
lean_inc_ref(v_body_4876_);
lean_dec_ref_known(v_e_4868_, 3);
v_d_4871_ = v_binderType_4875_;
v_b_4872_ = v_body_4876_;
goto v___jp_4870_;
}
case 6:
{
lean_object* v_binderType_4877_; lean_object* v_body_4878_; 
v_binderType_4877_ = lean_ctor_get(v_e_4868_, 1);
lean_inc_ref(v_binderType_4877_);
v_body_4878_ = lean_ctor_get(v_e_4868_, 2);
lean_inc_ref(v_body_4878_);
lean_dec_ref_known(v_e_4868_, 3);
v_d_4871_ = v_binderType_4877_;
v_b_4872_ = v_body_4878_;
goto v___jp_4870_;
}
case 10:
{
lean_object* v_expr_4879_; 
v_expr_4879_ = lean_ctor_get(v_e_4868_, 1);
lean_inc_ref(v_expr_4879_);
lean_dec_ref_known(v_e_4868_, 2);
v_e_4868_ = v_expr_4879_;
goto _start;
}
case 8:
{
lean_object* v_type_4881_; lean_object* v_value_4882_; lean_object* v_body_4883_; uint8_t v___x_4884_; 
v_type_4881_ = lean_ctor_get(v_e_4868_, 1);
lean_inc_ref(v_type_4881_);
v_value_4882_ = lean_ctor_get(v_e_4868_, 2);
lean_inc_ref(v_value_4882_);
v_body_4883_ = lean_ctor_get(v_e_4868_, 3);
lean_inc_ref(v_body_4883_);
lean_dec_ref_known(v_e_4868_, 4);
lean_inc_ref(v_p_4867_);
v___x_4884_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4867_, v_type_4881_);
if (v___x_4884_ == 0)
{
uint8_t v___x_4885_; 
lean_inc_ref(v_p_4867_);
v___x_4885_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4867_, v_value_4882_);
if (v___x_4885_ == 0)
{
v_e_4868_ = v_body_4883_;
goto _start;
}
else
{
lean_dec_ref(v_body_4883_);
lean_dec_ref(v_p_4867_);
return v___x_4869_;
}
}
else
{
lean_dec_ref(v_body_4883_);
lean_dec_ref(v_value_4882_);
lean_dec_ref(v_p_4867_);
return v___x_4869_;
}
}
case 5:
{
lean_object* v_fn_4887_; lean_object* v_arg_4888_; uint8_t v___x_4889_; 
v_fn_4887_ = lean_ctor_get(v_e_4868_, 0);
lean_inc_ref(v_fn_4887_);
v_arg_4888_ = lean_ctor_get(v_e_4868_, 1);
lean_inc_ref(v_arg_4888_);
lean_dec_ref_known(v_e_4868_, 2);
lean_inc_ref(v_p_4867_);
v___x_4889_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4867_, v_fn_4887_);
if (v___x_4889_ == 0)
{
v_e_4868_ = v_arg_4888_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4888_);
lean_dec_ref(v_p_4867_);
return v___x_4869_;
}
}
case 11:
{
lean_object* v_struct_4891_; 
v_struct_4891_ = lean_ctor_get(v_e_4868_, 2);
lean_inc_ref(v_struct_4891_);
lean_dec_ref_known(v_e_4868_, 3);
v_e_4868_ = v_struct_4891_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4893_; lean_object* v___x_4894_; uint8_t v___x_4895_; 
v_fvarId_4893_ = lean_ctor_get(v_e_4868_, 0);
lean_inc(v_fvarId_4893_);
lean_dec_ref_known(v_e_4868_, 1);
v___x_4894_ = lean_apply_1(v_p_4867_, v_fvarId_4893_);
v___x_4895_ = lean_unbox(v___x_4894_);
return v___x_4895_;
}
default: 
{
uint8_t v___x_4896_; 
lean_dec_ref(v_e_4868_);
lean_dec_ref(v_p_4867_);
v___x_4896_ = 0;
return v___x_4896_;
}
}
}
v___jp_4870_:
{
uint8_t v___x_4873_; 
lean_inc_ref(v_p_4867_);
v___x_4873_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4867_, v_d_4871_);
if (v___x_4873_ == 0)
{
v_e_4868_ = v_b_4872_;
goto _start;
}
else
{
lean_dec_ref(v_b_4872_);
lean_dec_ref(v_p_4867_);
return v___x_4869_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_4897_, lean_object* v_e_4898_){
_start:
{
uint8_t v_res_4899_; lean_object* v_r_4900_; 
v_res_4899_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4897_, v_e_4898_);
v_r_4900_ = lean_box(v_res_4899_);
return v_r_4900_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_4901_, lean_object* v_p_4902_){
_start:
{
uint8_t v___x_4903_; 
v___x_4903_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4902_, v_e_4901_);
return v___x_4903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_4904_, lean_object* v_p_4905_){
_start:
{
uint8_t v_res_4906_; lean_object* v_r_4907_; 
v_res_4906_ = l_Lean_Expr_hasAnyFVar(v_e_4904_, v_p_4905_);
v_r_4907_ = lean_box(v_res_4906_);
return v_r_4907_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_4908_, lean_object* v_e_4909_){
_start:
{
uint8_t v___x_4910_; lean_object* v_d_4912_; lean_object* v_b_4913_; 
v___x_4910_ = l_Lean_Expr_hasFVar(v_e_4909_);
if (v___x_4910_ == 0)
{
return v___x_4910_;
}
else
{
switch(lean_obj_tag(v_e_4909_))
{
case 7:
{
lean_object* v_binderType_4916_; lean_object* v_body_4917_; 
v_binderType_4916_ = lean_ctor_get(v_e_4909_, 1);
v_body_4917_ = lean_ctor_get(v_e_4909_, 2);
v_d_4912_ = v_binderType_4916_;
v_b_4913_ = v_body_4917_;
goto v___jp_4911_;
}
case 6:
{
lean_object* v_binderType_4918_; lean_object* v_body_4919_; 
v_binderType_4918_ = lean_ctor_get(v_e_4909_, 1);
v_body_4919_ = lean_ctor_get(v_e_4909_, 2);
v_d_4912_ = v_binderType_4918_;
v_b_4913_ = v_body_4919_;
goto v___jp_4911_;
}
case 10:
{
lean_object* v_expr_4920_; 
v_expr_4920_ = lean_ctor_get(v_e_4909_, 1);
v_e_4909_ = v_expr_4920_;
goto _start;
}
case 8:
{
lean_object* v_type_4922_; lean_object* v_value_4923_; lean_object* v_body_4924_; uint8_t v___x_4925_; 
v_type_4922_ = lean_ctor_get(v_e_4909_, 1);
v_value_4923_ = lean_ctor_get(v_e_4909_, 2);
v_body_4924_ = lean_ctor_get(v_e_4909_, 3);
v___x_4925_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4908_, v_type_4922_);
if (v___x_4925_ == 0)
{
uint8_t v___x_4926_; 
v___x_4926_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4908_, v_value_4923_);
if (v___x_4926_ == 0)
{
v_e_4909_ = v_body_4924_;
goto _start;
}
else
{
return v___x_4910_;
}
}
else
{
return v___x_4910_;
}
}
case 5:
{
lean_object* v_fn_4928_; lean_object* v_arg_4929_; uint8_t v___x_4930_; 
v_fn_4928_ = lean_ctor_get(v_e_4909_, 0);
v_arg_4929_ = lean_ctor_get(v_e_4909_, 1);
v___x_4930_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4908_, v_fn_4928_);
if (v___x_4930_ == 0)
{
v_e_4909_ = v_arg_4929_;
goto _start;
}
else
{
return v___x_4910_;
}
}
case 11:
{
lean_object* v_struct_4932_; 
v_struct_4932_ = lean_ctor_get(v_e_4909_, 2);
v_e_4909_ = v_struct_4932_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4934_; uint8_t v___x_4935_; 
v_fvarId_4934_ = lean_ctor_get(v_e_4909_, 0);
v___x_4935_ = lean_name_eq(v_fvarId_4934_, v_fvarId_4908_);
return v___x_4935_;
}
default: 
{
uint8_t v___x_4936_; 
v___x_4936_ = 0;
return v___x_4936_;
}
}
}
v___jp_4911_:
{
uint8_t v___x_4914_; 
v___x_4914_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4908_, v_d_4912_);
if (v___x_4914_ == 0)
{
v_e_4909_ = v_b_4913_;
goto _start;
}
else
{
return v___x_4910_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_4937_, lean_object* v_e_4938_){
_start:
{
uint8_t v_res_4939_; lean_object* v_r_4940_; 
v_res_4939_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4937_, v_e_4938_);
lean_dec_ref(v_e_4938_);
lean_dec(v_fvarId_4937_);
v_r_4940_ = lean_box(v_res_4939_);
return v_r_4940_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_4941_, lean_object* v_fvarId_4942_){
_start:
{
uint8_t v___x_4943_; 
v___x_4943_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4942_, v_e_4941_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_4944_, lean_object* v_fvarId_4945_){
_start:
{
uint8_t v_res_4946_; lean_object* v_r_4947_; 
v_res_4946_ = l_Lean_Expr_containsFVar(v_e_4944_, v_fvarId_4945_);
lean_dec(v_fvarId_4945_);
lean_dec_ref(v_e_4944_);
v_r_4947_ = lean_box(v_res_4946_);
return v_r_4947_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4949_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_4950_ = lean_unsigned_to_nat(18u);
v___x_4951_ = lean_unsigned_to_nat(1847u);
v___x_4952_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_4953_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4954_ = l_mkPanicMessageWithDecl(v___x_4953_, v___x_4952_, v___x_4951_, v___x_4950_, v___x_4949_);
return v___x_4954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_4955_, lean_object* v_newFn_4956_, lean_object* v_newArg_4957_){
_start:
{
if (lean_obj_tag(v_e_4955_) == 5)
{
lean_object* v_fn_4958_; lean_object* v_arg_4959_; size_t v___x_4960_; size_t v___x_4961_; uint8_t v___x_4962_; 
v_fn_4958_ = lean_ctor_get(v_e_4955_, 0);
v_arg_4959_ = lean_ctor_get(v_e_4955_, 1);
v___x_4960_ = lean_ptr_addr(v_fn_4958_);
v___x_4961_ = lean_ptr_addr(v_newFn_4956_);
v___x_4962_ = lean_usize_dec_eq(v___x_4960_, v___x_4961_);
if (v___x_4962_ == 0)
{
lean_object* v___x_4963_; 
v___x_4963_ = l_Lean_Expr_app___override(v_newFn_4956_, v_newArg_4957_);
return v___x_4963_;
}
else
{
size_t v___x_4964_; size_t v___x_4965_; uint8_t v___x_4966_; 
v___x_4964_ = lean_ptr_addr(v_arg_4959_);
v___x_4965_ = lean_ptr_addr(v_newArg_4957_);
v___x_4966_ = lean_usize_dec_eq(v___x_4964_, v___x_4965_);
if (v___x_4966_ == 0)
{
lean_object* v___x_4967_; 
v___x_4967_ = l_Lean_Expr_app___override(v_newFn_4956_, v_newArg_4957_);
return v___x_4967_;
}
else
{
lean_dec_ref(v_newArg_4957_);
lean_dec_ref(v_newFn_4956_);
lean_inc_ref(v_e_4955_);
return v_e_4955_;
}
}
}
else
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
lean_dec_ref(v_newArg_4957_);
lean_dec_ref(v_newFn_4956_);
v___x_4968_ = l_Lean_instInhabitedExpr;
v___x_4969_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_4970_ = l_panic___redArg(v___x_4968_, v___x_4969_);
return v___x_4970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_4971_, lean_object* v_newFn_4972_, lean_object* v_newArg_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_4971_, v_newFn_4972_, v_newArg_4973_);
lean_dec_ref(v_e_4971_);
return v_res_4974_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4976_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_4977_ = lean_unsigned_to_nat(20u);
v___x_4978_ = lean_unsigned_to_nat(1858u);
v___x_4979_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_4980_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4981_ = l_mkPanicMessageWithDecl(v___x_4980_, v___x_4979_, v___x_4978_, v___x_4977_, v___x_4976_);
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_4982_, lean_object* v_fvarIdNew_4983_){
_start:
{
if (lean_obj_tag(v_e_4982_) == 1)
{
lean_object* v_fvarId_4984_; uint8_t v___x_4985_; 
v_fvarId_4984_ = lean_ctor_get(v_e_4982_, 0);
v___x_4985_ = lean_name_eq(v_fvarId_4984_, v_fvarIdNew_4983_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; 
v___x_4986_ = l_Lean_Expr_fvar___override(v_fvarIdNew_4983_);
return v___x_4986_;
}
else
{
lean_dec(v_fvarIdNew_4983_);
lean_inc_ref(v_e_4982_);
return v_e_4982_;
}
}
else
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
lean_dec(v_fvarIdNew_4983_);
v___x_4987_ = l_Lean_instInhabitedExpr;
v___x_4988_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_4989_ = l_panic___redArg(v___x_4987_, v___x_4988_);
return v___x_4989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_4990_, lean_object* v_fvarIdNew_4991_){
_start:
{
lean_object* v_res_4992_; 
v_res_4992_ = l_Lean_Expr_updateFVar_x21(v_e_4990_, v_fvarIdNew_4991_);
lean_dec_ref(v_e_4990_);
return v_res_4992_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
v___x_4994_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_4995_ = lean_unsigned_to_nat(18u);
v___x_4996_ = lean_unsigned_to_nat(1863u);
v___x_4997_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_4998_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4999_ = l_mkPanicMessageWithDecl(v___x_4998_, v___x_4997_, v___x_4996_, v___x_4995_, v___x_4994_);
return v___x_4999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_5000_, lean_object* v_newLevels_5001_){
_start:
{
if (lean_obj_tag(v_e_5000_) == 4)
{
lean_object* v_declName_5002_; lean_object* v_us_5003_; uint8_t v___x_5004_; 
v_declName_5002_ = lean_ctor_get(v_e_5000_, 0);
v_us_5003_ = lean_ctor_get(v_e_5000_, 1);
v___x_5004_ = l_ptrEqList___redArg(v_us_5003_, v_newLevels_5001_);
if (v___x_5004_ == 0)
{
lean_object* v___x_5005_; 
lean_inc(v_declName_5002_);
lean_dec_ref_known(v_e_5000_, 2);
v___x_5005_ = l_Lean_Expr_const___override(v_declName_5002_, v_newLevels_5001_);
return v___x_5005_;
}
else
{
lean_dec(v_newLevels_5001_);
return v_e_5000_;
}
}
else
{
lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; 
lean_dec(v_newLevels_5001_);
lean_dec_ref(v_e_5000_);
v___x_5006_ = l_Lean_instInhabitedExpr;
v___x_5007_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_5008_ = l_panic___redArg(v___x_5006_, v___x_5007_);
return v___x_5008_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
v___x_5011_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_5012_ = lean_unsigned_to_nat(14u);
v___x_5013_ = lean_unsigned_to_nat(1874u);
v___x_5014_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_5015_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5016_ = l_mkPanicMessageWithDecl(v___x_5015_, v___x_5014_, v___x_5013_, v___x_5012_, v___x_5011_);
return v___x_5016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_5017_, lean_object* v_u_x27_5018_){
_start:
{
if (lean_obj_tag(v_e_5017_) == 3)
{
lean_object* v_u_5019_; size_t v___x_5020_; size_t v___x_5021_; uint8_t v___x_5022_; 
v_u_5019_ = lean_ctor_get(v_e_5017_, 0);
v___x_5020_ = lean_ptr_addr(v_u_5019_);
v___x_5021_ = lean_ptr_addr(v_u_x27_5018_);
v___x_5022_ = lean_usize_dec_eq(v___x_5020_, v___x_5021_);
if (v___x_5022_ == 0)
{
lean_object* v___x_5023_; 
v___x_5023_ = l_Lean_Expr_sort___override(v_u_x27_5018_);
return v___x_5023_;
}
else
{
lean_dec(v_u_x27_5018_);
lean_inc_ref(v_e_5017_);
return v_e_5017_;
}
}
else
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
lean_dec(v_u_x27_5018_);
v___x_5024_ = l_Lean_instInhabitedExpr;
v___x_5025_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_5026_ = l_panic___redArg(v___x_5024_, v___x_5025_);
return v___x_5026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_5027_, lean_object* v_u_x27_5028_){
_start:
{
lean_object* v_res_5029_; 
v_res_5029_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_5027_, v_u_x27_5028_);
lean_dec_ref(v_e_5027_);
return v_res_5029_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; 
v___x_5032_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_5033_ = lean_unsigned_to_nat(17u);
v___x_5034_ = lean_unsigned_to_nat(1885u);
v___x_5035_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_5036_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5037_ = l_mkPanicMessageWithDecl(v___x_5036_, v___x_5035_, v___x_5034_, v___x_5033_, v___x_5032_);
return v___x_5037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_5038_, lean_object* v_newExpr_5039_){
_start:
{
if (lean_obj_tag(v_e_5038_) == 10)
{
lean_object* v_data_5040_; lean_object* v_expr_5041_; size_t v___x_5042_; size_t v___x_5043_; uint8_t v___x_5044_; 
v_data_5040_ = lean_ctor_get(v_e_5038_, 0);
v_expr_5041_ = lean_ctor_get(v_e_5038_, 1);
v___x_5042_ = lean_ptr_addr(v_expr_5041_);
v___x_5043_ = lean_ptr_addr(v_newExpr_5039_);
v___x_5044_ = lean_usize_dec_eq(v___x_5042_, v___x_5043_);
if (v___x_5044_ == 0)
{
lean_object* v___x_5045_; 
lean_inc(v_data_5040_);
lean_dec_ref_known(v_e_5038_, 2);
v___x_5045_ = l_Lean_Expr_mdata___override(v_data_5040_, v_newExpr_5039_);
return v___x_5045_;
}
else
{
lean_dec_ref(v_newExpr_5039_);
return v_e_5038_;
}
}
else
{
lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
lean_dec_ref(v_newExpr_5039_);
lean_dec_ref(v_e_5038_);
v___x_5046_ = l_Lean_instInhabitedExpr;
v___x_5047_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_5048_ = l_panic___redArg(v___x_5046_, v___x_5047_);
return v___x_5048_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5051_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_5052_ = lean_unsigned_to_nat(18u);
v___x_5053_ = lean_unsigned_to_nat(1896u);
v___x_5054_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_5055_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5056_ = l_mkPanicMessageWithDecl(v___x_5055_, v___x_5054_, v___x_5053_, v___x_5052_, v___x_5051_);
return v___x_5056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_5057_, lean_object* v_newExpr_5058_){
_start:
{
if (lean_obj_tag(v_e_5057_) == 11)
{
lean_object* v_typeName_5059_; lean_object* v_idx_5060_; lean_object* v_struct_5061_; size_t v___x_5062_; size_t v___x_5063_; uint8_t v___x_5064_; 
v_typeName_5059_ = lean_ctor_get(v_e_5057_, 0);
v_idx_5060_ = lean_ctor_get(v_e_5057_, 1);
v_struct_5061_ = lean_ctor_get(v_e_5057_, 2);
v___x_5062_ = lean_ptr_addr(v_struct_5061_);
v___x_5063_ = lean_ptr_addr(v_newExpr_5058_);
v___x_5064_ = lean_usize_dec_eq(v___x_5062_, v___x_5063_);
if (v___x_5064_ == 0)
{
lean_object* v___x_5065_; 
lean_inc(v_idx_5060_);
lean_inc(v_typeName_5059_);
lean_dec_ref_known(v_e_5057_, 3);
v___x_5065_ = l_Lean_Expr_proj___override(v_typeName_5059_, v_idx_5060_, v_newExpr_5058_);
return v___x_5065_;
}
else
{
lean_dec_ref(v_newExpr_5058_);
return v_e_5057_;
}
}
else
{
lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; 
lean_dec_ref(v_newExpr_5058_);
lean_dec_ref(v_e_5057_);
v___x_5066_ = l_Lean_instInhabitedExpr;
v___x_5067_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_5068_ = l_panic___redArg(v___x_5066_, v___x_5067_);
return v___x_5068_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___x_5071_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5072_ = lean_unsigned_to_nat(23u);
v___x_5073_ = lean_unsigned_to_nat(1911u);
v___x_5074_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_5075_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5076_ = l_mkPanicMessageWithDecl(v___x_5075_, v___x_5074_, v___x_5073_, v___x_5072_, v___x_5071_);
return v___x_5076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_5077_, uint8_t v_newBinfo_5078_, lean_object* v_newDomain_5079_, lean_object* v_newBody_5080_){
_start:
{
if (lean_obj_tag(v_e_5077_) == 7)
{
lean_object* v_binderName_5081_; lean_object* v_binderType_5082_; lean_object* v_body_5083_; uint8_t v_binderInfo_5084_; size_t v___x_5085_; size_t v___x_5086_; uint8_t v___x_5087_; 
v_binderName_5081_ = lean_ctor_get(v_e_5077_, 0);
v_binderType_5082_ = lean_ctor_get(v_e_5077_, 1);
v_body_5083_ = lean_ctor_get(v_e_5077_, 2);
v_binderInfo_5084_ = lean_ctor_get_uint8(v_e_5077_, sizeof(void*)*3 + 8);
v___x_5085_ = lean_ptr_addr(v_binderType_5082_);
v___x_5086_ = lean_ptr_addr(v_newDomain_5079_);
v___x_5087_ = lean_usize_dec_eq(v___x_5085_, v___x_5086_);
if (v___x_5087_ == 0)
{
lean_object* v___x_5088_; 
lean_inc(v_binderName_5081_);
lean_dec_ref_known(v_e_5077_, 3);
v___x_5088_ = l_Lean_Expr_forallE___override(v_binderName_5081_, v_newDomain_5079_, v_newBody_5080_, v_newBinfo_5078_);
return v___x_5088_;
}
else
{
size_t v___x_5089_; size_t v___x_5090_; uint8_t v___x_5091_; 
v___x_5089_ = lean_ptr_addr(v_body_5083_);
v___x_5090_ = lean_ptr_addr(v_newBody_5080_);
v___x_5091_ = lean_usize_dec_eq(v___x_5089_, v___x_5090_);
if (v___x_5091_ == 0)
{
lean_object* v___x_5092_; 
lean_inc(v_binderName_5081_);
lean_dec_ref_known(v_e_5077_, 3);
v___x_5092_ = l_Lean_Expr_forallE___override(v_binderName_5081_, v_newDomain_5079_, v_newBody_5080_, v_newBinfo_5078_);
return v___x_5092_;
}
else
{
uint8_t v___x_5093_; 
v___x_5093_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5084_, v_newBinfo_5078_);
if (v___x_5093_ == 0)
{
lean_object* v___x_5094_; 
lean_inc(v_binderName_5081_);
lean_dec_ref_known(v_e_5077_, 3);
v___x_5094_ = l_Lean_Expr_forallE___override(v_binderName_5081_, v_newDomain_5079_, v_newBody_5080_, v_newBinfo_5078_);
return v___x_5094_;
}
else
{
lean_dec_ref(v_newBody_5080_);
lean_dec_ref(v_newDomain_5079_);
return v_e_5077_;
}
}
}
}
else
{
lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; 
lean_dec_ref(v_newBody_5080_);
lean_dec_ref(v_newDomain_5079_);
lean_dec_ref(v_e_5077_);
v___x_5095_ = l_Lean_instInhabitedExpr;
v___x_5096_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_5097_ = l_panic___redArg(v___x_5095_, v___x_5096_);
return v___x_5097_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_5098_, lean_object* v_newBinfo_5099_, lean_object* v_newDomain_5100_, lean_object* v_newBody_5101_){
_start:
{
uint8_t v_newBinfo_boxed_5102_; lean_object* v_res_5103_; 
v_newBinfo_boxed_5102_ = lean_unbox(v_newBinfo_5099_);
v_res_5103_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5098_, v_newBinfo_boxed_5102_, v_newDomain_5100_, v_newBody_5101_);
return v_res_5103_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; 
v___x_5105_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5106_ = lean_unsigned_to_nat(24u);
v___x_5107_ = lean_unsigned_to_nat(1922u);
v___x_5108_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_5109_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5110_ = l_mkPanicMessageWithDecl(v___x_5109_, v___x_5108_, v___x_5107_, v___x_5106_, v___x_5105_);
return v___x_5110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_5111_, lean_object* v_newDomain_5112_, lean_object* v_newBody_5113_){
_start:
{
if (lean_obj_tag(v_e_5111_) == 7)
{
lean_object* v_binderName_5114_; lean_object* v_binderType_5115_; lean_object* v_body_5116_; uint8_t v_binderInfo_5117_; size_t v___x_5118_; size_t v___x_5119_; uint8_t v___x_5120_; 
v_binderName_5114_ = lean_ctor_get(v_e_5111_, 0);
v_binderType_5115_ = lean_ctor_get(v_e_5111_, 1);
v_body_5116_ = lean_ctor_get(v_e_5111_, 2);
v_binderInfo_5117_ = lean_ctor_get_uint8(v_e_5111_, sizeof(void*)*3 + 8);
v___x_5118_ = lean_ptr_addr(v_binderType_5115_);
v___x_5119_ = lean_ptr_addr(v_newDomain_5112_);
v___x_5120_ = lean_usize_dec_eq(v___x_5118_, v___x_5119_);
if (v___x_5120_ == 0)
{
lean_object* v___x_5121_; 
lean_inc(v_binderName_5114_);
lean_dec_ref_known(v_e_5111_, 3);
v___x_5121_ = l_Lean_Expr_forallE___override(v_binderName_5114_, v_newDomain_5112_, v_newBody_5113_, v_binderInfo_5117_);
return v___x_5121_;
}
else
{
size_t v___x_5122_; size_t v___x_5123_; uint8_t v___x_5124_; 
v___x_5122_ = lean_ptr_addr(v_body_5116_);
v___x_5123_ = lean_ptr_addr(v_newBody_5113_);
v___x_5124_ = lean_usize_dec_eq(v___x_5122_, v___x_5123_);
if (v___x_5124_ == 0)
{
lean_object* v___x_5125_; 
lean_inc(v_binderName_5114_);
lean_dec_ref_known(v_e_5111_, 3);
v___x_5125_ = l_Lean_Expr_forallE___override(v_binderName_5114_, v_newDomain_5112_, v_newBody_5113_, v_binderInfo_5117_);
return v___x_5125_;
}
else
{
uint8_t v___x_5126_; 
v___x_5126_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5117_, v_binderInfo_5117_);
if (v___x_5126_ == 0)
{
lean_object* v___x_5127_; 
lean_inc(v_binderName_5114_);
lean_dec_ref_known(v_e_5111_, 3);
v___x_5127_ = l_Lean_Expr_forallE___override(v_binderName_5114_, v_newDomain_5112_, v_newBody_5113_, v_binderInfo_5117_);
return v___x_5127_;
}
else
{
lean_dec_ref(v_newBody_5113_);
lean_dec_ref(v_newDomain_5112_);
return v_e_5111_;
}
}
}
}
else
{
lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; 
lean_dec_ref(v_newBody_5113_);
lean_dec_ref(v_newDomain_5112_);
lean_dec_ref(v_e_5111_);
v___x_5128_ = l_Lean_instInhabitedExpr;
v___x_5129_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_5130_ = l_panic___redArg(v___x_5128_, v___x_5129_);
return v___x_5130_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; 
v___x_5133_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5134_ = lean_unsigned_to_nat(19u);
v___x_5135_ = lean_unsigned_to_nat(1931u);
v___x_5136_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_5137_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5138_ = l_mkPanicMessageWithDecl(v___x_5137_, v___x_5136_, v___x_5135_, v___x_5134_, v___x_5133_);
return v___x_5138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_5139_, uint8_t v_newBinfo_5140_, lean_object* v_newDomain_5141_, lean_object* v_newBody_5142_){
_start:
{
if (lean_obj_tag(v_e_5139_) == 6)
{
lean_object* v_binderName_5143_; lean_object* v_binderType_5144_; lean_object* v_body_5145_; uint8_t v_binderInfo_5146_; size_t v___x_5147_; size_t v___x_5148_; uint8_t v___x_5149_; 
v_binderName_5143_ = lean_ctor_get(v_e_5139_, 0);
v_binderType_5144_ = lean_ctor_get(v_e_5139_, 1);
v_body_5145_ = lean_ctor_get(v_e_5139_, 2);
v_binderInfo_5146_ = lean_ctor_get_uint8(v_e_5139_, sizeof(void*)*3 + 8);
v___x_5147_ = lean_ptr_addr(v_binderType_5144_);
v___x_5148_ = lean_ptr_addr(v_newDomain_5141_);
v___x_5149_ = lean_usize_dec_eq(v___x_5147_, v___x_5148_);
if (v___x_5149_ == 0)
{
lean_object* v___x_5150_; 
lean_inc(v_binderName_5143_);
lean_dec_ref_known(v_e_5139_, 3);
v___x_5150_ = l_Lean_Expr_lam___override(v_binderName_5143_, v_newDomain_5141_, v_newBody_5142_, v_newBinfo_5140_);
return v___x_5150_;
}
else
{
size_t v___x_5151_; size_t v___x_5152_; uint8_t v___x_5153_; 
v___x_5151_ = lean_ptr_addr(v_body_5145_);
v___x_5152_ = lean_ptr_addr(v_newBody_5142_);
v___x_5153_ = lean_usize_dec_eq(v___x_5151_, v___x_5152_);
if (v___x_5153_ == 0)
{
lean_object* v___x_5154_; 
lean_inc(v_binderName_5143_);
lean_dec_ref_known(v_e_5139_, 3);
v___x_5154_ = l_Lean_Expr_lam___override(v_binderName_5143_, v_newDomain_5141_, v_newBody_5142_, v_newBinfo_5140_);
return v___x_5154_;
}
else
{
uint8_t v___x_5155_; 
v___x_5155_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5146_, v_newBinfo_5140_);
if (v___x_5155_ == 0)
{
lean_object* v___x_5156_; 
lean_inc(v_binderName_5143_);
lean_dec_ref_known(v_e_5139_, 3);
v___x_5156_ = l_Lean_Expr_lam___override(v_binderName_5143_, v_newDomain_5141_, v_newBody_5142_, v_newBinfo_5140_);
return v___x_5156_;
}
else
{
lean_dec_ref(v_newBody_5142_);
lean_dec_ref(v_newDomain_5141_);
return v_e_5139_;
}
}
}
}
else
{
lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; 
lean_dec_ref(v_newBody_5142_);
lean_dec_ref(v_newDomain_5141_);
lean_dec_ref(v_e_5139_);
v___x_5157_ = l_Lean_instInhabitedExpr;
v___x_5158_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_5159_ = l_panic___redArg(v___x_5157_, v___x_5158_);
return v___x_5159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_5160_, lean_object* v_newBinfo_5161_, lean_object* v_newDomain_5162_, lean_object* v_newBody_5163_){
_start:
{
uint8_t v_newBinfo_boxed_5164_; lean_object* v_res_5165_; 
v_newBinfo_boxed_5164_ = lean_unbox(v_newBinfo_5161_);
v_res_5165_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5160_, v_newBinfo_boxed_5164_, v_newDomain_5162_, v_newBody_5163_);
return v_res_5165_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
v___x_5167_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5168_ = lean_unsigned_to_nat(20u);
v___x_5169_ = lean_unsigned_to_nat(1942u);
v___x_5170_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5171_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5172_ = l_mkPanicMessageWithDecl(v___x_5171_, v___x_5170_, v___x_5169_, v___x_5168_, v___x_5167_);
return v___x_5172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5173_, lean_object* v_newDomain_5174_, lean_object* v_newBody_5175_){
_start:
{
if (lean_obj_tag(v_e_5173_) == 6)
{
lean_object* v_binderName_5176_; lean_object* v_binderType_5177_; lean_object* v_body_5178_; uint8_t v_binderInfo_5179_; size_t v___x_5180_; size_t v___x_5181_; uint8_t v___x_5182_; 
v_binderName_5176_ = lean_ctor_get(v_e_5173_, 0);
v_binderType_5177_ = lean_ctor_get(v_e_5173_, 1);
v_body_5178_ = lean_ctor_get(v_e_5173_, 2);
v_binderInfo_5179_ = lean_ctor_get_uint8(v_e_5173_, sizeof(void*)*3 + 8);
v___x_5180_ = lean_ptr_addr(v_binderType_5177_);
v___x_5181_ = lean_ptr_addr(v_newDomain_5174_);
v___x_5182_ = lean_usize_dec_eq(v___x_5180_, v___x_5181_);
if (v___x_5182_ == 0)
{
lean_object* v___x_5183_; 
lean_inc(v_binderName_5176_);
lean_dec_ref_known(v_e_5173_, 3);
v___x_5183_ = l_Lean_Expr_lam___override(v_binderName_5176_, v_newDomain_5174_, v_newBody_5175_, v_binderInfo_5179_);
return v___x_5183_;
}
else
{
size_t v___x_5184_; size_t v___x_5185_; uint8_t v___x_5186_; 
v___x_5184_ = lean_ptr_addr(v_body_5178_);
v___x_5185_ = lean_ptr_addr(v_newBody_5175_);
v___x_5186_ = lean_usize_dec_eq(v___x_5184_, v___x_5185_);
if (v___x_5186_ == 0)
{
lean_object* v___x_5187_; 
lean_inc(v_binderName_5176_);
lean_dec_ref_known(v_e_5173_, 3);
v___x_5187_ = l_Lean_Expr_lam___override(v_binderName_5176_, v_newDomain_5174_, v_newBody_5175_, v_binderInfo_5179_);
return v___x_5187_;
}
else
{
uint8_t v___x_5188_; 
v___x_5188_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5179_, v_binderInfo_5179_);
if (v___x_5188_ == 0)
{
lean_object* v___x_5189_; 
lean_inc(v_binderName_5176_);
lean_dec_ref_known(v_e_5173_, 3);
v___x_5189_ = l_Lean_Expr_lam___override(v_binderName_5176_, v_newDomain_5174_, v_newBody_5175_, v_binderInfo_5179_);
return v___x_5189_;
}
else
{
lean_dec_ref(v_newBody_5175_);
lean_dec_ref(v_newDomain_5174_);
return v_e_5173_;
}
}
}
}
else
{
lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; 
lean_dec_ref(v_newBody_5175_);
lean_dec_ref(v_newDomain_5174_);
lean_dec_ref(v_e_5173_);
v___x_5190_ = l_Lean_instInhabitedExpr;
v___x_5191_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5192_ = l_panic___redArg(v___x_5190_, v___x_5191_);
return v___x_5192_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; 
v___x_5194_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5195_ = lean_unsigned_to_nat(22u);
v___x_5196_ = lean_unsigned_to_nat(1951u);
v___x_5197_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5198_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5199_ = l_mkPanicMessageWithDecl(v___x_5198_, v___x_5197_, v___x_5196_, v___x_5195_, v___x_5194_);
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5200_, lean_object* v_newType_5201_, lean_object* v_newVal_5202_, lean_object* v_newBody_5203_, uint8_t v_newNondep_5204_){
_start:
{
if (lean_obj_tag(v_e_5200_) == 8)
{
lean_object* v_declName_5205_; lean_object* v_type_5206_; lean_object* v_value_5207_; lean_object* v_body_5208_; uint8_t v_nondep_5209_; size_t v___x_5210_; size_t v___x_5211_; uint8_t v___x_5212_; 
v_declName_5205_ = lean_ctor_get(v_e_5200_, 0);
v_type_5206_ = lean_ctor_get(v_e_5200_, 1);
v_value_5207_ = lean_ctor_get(v_e_5200_, 2);
v_body_5208_ = lean_ctor_get(v_e_5200_, 3);
v_nondep_5209_ = lean_ctor_get_uint8(v_e_5200_, sizeof(void*)*4 + 8);
v___x_5210_ = lean_ptr_addr(v_type_5206_);
v___x_5211_ = lean_ptr_addr(v_newType_5201_);
v___x_5212_ = lean_usize_dec_eq(v___x_5210_, v___x_5211_);
if (v___x_5212_ == 0)
{
lean_object* v___x_5213_; 
lean_inc(v_declName_5205_);
lean_dec_ref_known(v_e_5200_, 4);
v___x_5213_ = l_Lean_Expr_letE___override(v_declName_5205_, v_newType_5201_, v_newVal_5202_, v_newBody_5203_, v_newNondep_5204_);
return v___x_5213_;
}
else
{
size_t v___x_5214_; size_t v___x_5215_; uint8_t v___x_5216_; 
v___x_5214_ = lean_ptr_addr(v_value_5207_);
v___x_5215_ = lean_ptr_addr(v_newVal_5202_);
v___x_5216_ = lean_usize_dec_eq(v___x_5214_, v___x_5215_);
if (v___x_5216_ == 0)
{
lean_object* v___x_5217_; 
lean_inc(v_declName_5205_);
lean_dec_ref_known(v_e_5200_, 4);
v___x_5217_ = l_Lean_Expr_letE___override(v_declName_5205_, v_newType_5201_, v_newVal_5202_, v_newBody_5203_, v_newNondep_5204_);
return v___x_5217_;
}
else
{
size_t v___x_5218_; size_t v___x_5219_; uint8_t v___x_5220_; 
v___x_5218_ = lean_ptr_addr(v_body_5208_);
v___x_5219_ = lean_ptr_addr(v_newBody_5203_);
v___x_5220_ = lean_usize_dec_eq(v___x_5218_, v___x_5219_);
if (v___x_5220_ == 0)
{
lean_object* v___x_5221_; 
lean_inc(v_declName_5205_);
lean_dec_ref_known(v_e_5200_, 4);
v___x_5221_ = l_Lean_Expr_letE___override(v_declName_5205_, v_newType_5201_, v_newVal_5202_, v_newBody_5203_, v_newNondep_5204_);
return v___x_5221_;
}
else
{
if (v_newNondep_5204_ == 0)
{
if (v_nondep_5209_ == 0)
{
lean_dec_ref(v_newBody_5203_);
lean_dec_ref(v_newVal_5202_);
lean_dec_ref(v_newType_5201_);
return v_e_5200_;
}
else
{
lean_object* v___x_5222_; 
lean_inc(v_declName_5205_);
lean_dec_ref_known(v_e_5200_, 4);
v___x_5222_ = l_Lean_Expr_letE___override(v_declName_5205_, v_newType_5201_, v_newVal_5202_, v_newBody_5203_, v_newNondep_5204_);
return v___x_5222_;
}
}
else
{
if (v_nondep_5209_ == 0)
{
lean_object* v___x_5223_; 
lean_inc(v_declName_5205_);
lean_dec_ref_known(v_e_5200_, 4);
v___x_5223_ = l_Lean_Expr_letE___override(v_declName_5205_, v_newType_5201_, v_newVal_5202_, v_newBody_5203_, v_newNondep_5204_);
return v___x_5223_;
}
else
{
lean_dec_ref(v_newBody_5203_);
lean_dec_ref(v_newVal_5202_);
lean_dec_ref(v_newType_5201_);
return v_e_5200_;
}
}
}
}
}
}
else
{
lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; 
lean_dec_ref(v_newBody_5203_);
lean_dec_ref(v_newVal_5202_);
lean_dec_ref(v_newType_5201_);
lean_dec_ref(v_e_5200_);
v___x_5224_ = l_Lean_instInhabitedExpr;
v___x_5225_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5226_ = l_panic___redArg(v___x_5224_, v___x_5225_);
return v___x_5226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5227_, lean_object* v_newType_5228_, lean_object* v_newVal_5229_, lean_object* v_newBody_5230_, lean_object* v_newNondep_5231_){
_start:
{
uint8_t v_newNondep_boxed_5232_; lean_object* v_res_5233_; 
v_newNondep_boxed_5232_ = lean_unbox(v_newNondep_5231_);
v_res_5233_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5227_, v_newType_5228_, v_newVal_5229_, v_newBody_5230_, v_newNondep_boxed_5232_);
return v_res_5233_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; 
v___x_5235_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5236_ = lean_unsigned_to_nat(27u);
v___x_5237_ = lean_unsigned_to_nat(1964u);
v___x_5238_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5239_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5240_ = l_mkPanicMessageWithDecl(v___x_5239_, v___x_5238_, v___x_5237_, v___x_5236_, v___x_5235_);
return v___x_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5241_, lean_object* v_newType_5242_, lean_object* v_newVal_5243_, lean_object* v_newBody_5244_){
_start:
{
if (lean_obj_tag(v_e_5241_) == 8)
{
lean_object* v_declName_5245_; lean_object* v_type_5246_; lean_object* v_value_5247_; lean_object* v_body_5248_; uint8_t v_nondep_5249_; size_t v___x_5250_; size_t v___x_5251_; uint8_t v___x_5252_; 
v_declName_5245_ = lean_ctor_get(v_e_5241_, 0);
v_type_5246_ = lean_ctor_get(v_e_5241_, 1);
v_value_5247_ = lean_ctor_get(v_e_5241_, 2);
v_body_5248_ = lean_ctor_get(v_e_5241_, 3);
v_nondep_5249_ = lean_ctor_get_uint8(v_e_5241_, sizeof(void*)*4 + 8);
v___x_5250_ = lean_ptr_addr(v_type_5246_);
v___x_5251_ = lean_ptr_addr(v_newType_5242_);
v___x_5252_ = lean_usize_dec_eq(v___x_5250_, v___x_5251_);
if (v___x_5252_ == 0)
{
lean_object* v___x_5253_; 
lean_inc(v_declName_5245_);
lean_dec_ref_known(v_e_5241_, 4);
v___x_5253_ = l_Lean_Expr_letE___override(v_declName_5245_, v_newType_5242_, v_newVal_5243_, v_newBody_5244_, v_nondep_5249_);
return v___x_5253_;
}
else
{
size_t v___x_5254_; size_t v___x_5255_; uint8_t v___x_5256_; 
v___x_5254_ = lean_ptr_addr(v_value_5247_);
v___x_5255_ = lean_ptr_addr(v_newVal_5243_);
v___x_5256_ = lean_usize_dec_eq(v___x_5254_, v___x_5255_);
if (v___x_5256_ == 0)
{
lean_object* v___x_5257_; 
lean_inc(v_declName_5245_);
lean_dec_ref_known(v_e_5241_, 4);
v___x_5257_ = l_Lean_Expr_letE___override(v_declName_5245_, v_newType_5242_, v_newVal_5243_, v_newBody_5244_, v_nondep_5249_);
return v___x_5257_;
}
else
{
size_t v___x_5258_; size_t v___x_5259_; uint8_t v___x_5260_; 
v___x_5258_ = lean_ptr_addr(v_body_5248_);
v___x_5259_ = lean_ptr_addr(v_newBody_5244_);
v___x_5260_ = lean_usize_dec_eq(v___x_5258_, v___x_5259_);
if (v___x_5260_ == 0)
{
lean_object* v___x_5261_; 
lean_inc(v_declName_5245_);
lean_dec_ref_known(v_e_5241_, 4);
v___x_5261_ = l_Lean_Expr_letE___override(v_declName_5245_, v_newType_5242_, v_newVal_5243_, v_newBody_5244_, v_nondep_5249_);
return v___x_5261_;
}
else
{
lean_dec_ref(v_newBody_5244_);
lean_dec_ref(v_newVal_5243_);
lean_dec_ref(v_newType_5242_);
return v_e_5241_;
}
}
}
}
else
{
lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; 
lean_dec_ref(v_newBody_5244_);
lean_dec_ref(v_newVal_5243_);
lean_dec_ref(v_newType_5242_);
lean_dec_ref(v_e_5241_);
v___x_5262_ = l_Lean_instInhabitedExpr;
v___x_5263_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5264_ = l_panic___redArg(v___x_5262_, v___x_5263_);
return v___x_5264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5265_, lean_object* v_x_5266_){
_start:
{
if (lean_obj_tag(v_x_5265_) == 5)
{
lean_object* v_fn_5267_; lean_object* v_arg_5268_; lean_object* v___x_5269_; size_t v___x_5270_; size_t v___x_5271_; uint8_t v___x_5272_; 
v_fn_5267_ = lean_ctor_get(v_x_5265_, 0);
v_arg_5268_ = lean_ctor_get(v_x_5265_, 1);
lean_inc_ref(v_fn_5267_);
v___x_5269_ = l_Lean_Expr_updateFn(v_fn_5267_, v_x_5266_);
v___x_5270_ = lean_ptr_addr(v_fn_5267_);
v___x_5271_ = lean_ptr_addr(v___x_5269_);
v___x_5272_ = lean_usize_dec_eq(v___x_5270_, v___x_5271_);
if (v___x_5272_ == 0)
{
lean_object* v___x_5273_; 
lean_inc_ref(v_arg_5268_);
lean_dec_ref_known(v_x_5265_, 2);
v___x_5273_ = l_Lean_Expr_app___override(v___x_5269_, v_arg_5268_);
return v___x_5273_;
}
else
{
size_t v___x_5274_; uint8_t v___x_5275_; 
v___x_5274_ = lean_ptr_addr(v_arg_5268_);
v___x_5275_ = lean_usize_dec_eq(v___x_5274_, v___x_5274_);
if (v___x_5275_ == 0)
{
lean_object* v___x_5276_; 
lean_inc_ref(v_arg_5268_);
lean_dec_ref_known(v_x_5265_, 2);
v___x_5276_ = l_Lean_Expr_app___override(v___x_5269_, v_arg_5268_);
return v___x_5276_;
}
else
{
lean_dec_ref(v___x_5269_);
return v_x_5265_;
}
}
}
else
{
lean_dec_ref(v_x_5265_);
lean_inc_ref(v_x_5266_);
return v_x_5266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5277_, lean_object* v_x_5278_){
_start:
{
lean_object* v_res_5279_; 
v_res_5279_ = l_Lean_Expr_updateFn(v_x_5277_, v_x_5278_);
lean_dec_ref(v_x_5278_);
return v_res_5279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5280_){
_start:
{
if (lean_obj_tag(v_e_5280_) == 6)
{
lean_object* v_binderName_5281_; lean_object* v_binderType_5282_; lean_object* v_body_5283_; uint8_t v_binderInfo_5284_; lean_object* v_b_x27_5285_; 
v_binderName_5281_ = lean_ctor_get(v_e_5280_, 0);
v_binderType_5282_ = lean_ctor_get(v_e_5280_, 1);
v_body_5283_ = lean_ctor_get(v_e_5280_, 2);
v_binderInfo_5284_ = lean_ctor_get_uint8(v_e_5280_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5283_);
v_b_x27_5285_ = l_Lean_Expr_eta(v_body_5283_);
if (lean_obj_tag(v_b_x27_5285_) == 5)
{
lean_object* v_arg_5296_; 
v_arg_5296_ = lean_ctor_get(v_b_x27_5285_, 1);
lean_inc_ref(v_arg_5296_);
if (lean_obj_tag(v_arg_5296_) == 0)
{
lean_object* v_fn_5297_; lean_object* v_deBruijnIndex_5298_; lean_object* v___x_5299_; uint8_t v___x_5300_; 
v_fn_5297_ = lean_ctor_get(v_b_x27_5285_, 0);
lean_inc_ref(v_fn_5297_);
v_deBruijnIndex_5298_ = lean_ctor_get(v_arg_5296_, 0);
lean_inc(v_deBruijnIndex_5298_);
lean_dec_ref_known(v_arg_5296_, 1);
v___x_5299_ = lean_unsigned_to_nat(0u);
v___x_5300_ = lean_nat_dec_eq(v_deBruijnIndex_5298_, v___x_5299_);
lean_dec(v_deBruijnIndex_5298_);
if (v___x_5300_ == 0)
{
lean_dec_ref(v_fn_5297_);
goto v___jp_5286_;
}
else
{
uint8_t v___x_5301_; 
v___x_5301_ = lean_expr_has_loose_bvar(v_fn_5297_, v___x_5299_);
if (v___x_5301_ == 0)
{
lean_object* v___x_5302_; lean_object* v___x_5303_; 
lean_dec_ref_known(v_b_x27_5285_, 2);
lean_dec_ref_known(v_e_5280_, 3);
v___x_5302_ = lean_unsigned_to_nat(1u);
v___x_5303_ = lean_expr_lower_loose_bvars(v_fn_5297_, v___x_5302_, v___x_5302_);
lean_dec_ref(v_fn_5297_);
return v___x_5303_;
}
else
{
size_t v___x_5304_; uint8_t v___x_5305_; 
lean_dec_ref(v_fn_5297_);
v___x_5304_ = lean_ptr_addr(v_binderType_5282_);
v___x_5305_ = lean_usize_dec_eq(v___x_5304_, v___x_5304_);
if (v___x_5305_ == 0)
{
lean_object* v___x_5306_; 
lean_inc_ref(v_binderType_5282_);
lean_inc(v_binderName_5281_);
lean_dec_ref_known(v_e_5280_, 3);
v___x_5306_ = l_Lean_Expr_lam___override(v_binderName_5281_, v_binderType_5282_, v_b_x27_5285_, v_binderInfo_5284_);
return v___x_5306_;
}
else
{
size_t v___x_5307_; size_t v___x_5308_; uint8_t v___x_5309_; 
v___x_5307_ = lean_ptr_addr(v_body_5283_);
v___x_5308_ = lean_ptr_addr(v_b_x27_5285_);
v___x_5309_ = lean_usize_dec_eq(v___x_5307_, v___x_5308_);
if (v___x_5309_ == 0)
{
lean_object* v___x_5310_; 
lean_inc_ref(v_binderType_5282_);
lean_inc(v_binderName_5281_);
lean_dec_ref_known(v_e_5280_, 3);
v___x_5310_ = l_Lean_Expr_lam___override(v_binderName_5281_, v_binderType_5282_, v_b_x27_5285_, v_binderInfo_5284_);
return v___x_5310_;
}
else
{
uint8_t v___x_5311_; 
v___x_5311_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5284_, v_binderInfo_5284_);
if (v___x_5311_ == 0)
{
lean_object* v___x_5312_; 
lean_inc_ref(v_binderType_5282_);
lean_inc(v_binderName_5281_);
lean_dec_ref_known(v_e_5280_, 3);
v___x_5312_ = l_Lean_Expr_lam___override(v_binderName_5281_, v_binderType_5282_, v_b_x27_5285_, v_binderInfo_5284_);
return v___x_5312_;
}
else
{
lean_dec_ref_known(v_b_x27_5285_, 2);
return v_e_5280_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_5296_);
goto v___jp_5286_;
}
}
else
{
goto v___jp_5286_;
}
v___jp_5286_:
{
size_t v___x_5287_; uint8_t v___x_5288_; 
v___x_5287_ = lean_ptr_addr(v_binderType_5282_);
v___x_5288_ = lean_usize_dec_eq(v___x_5287_, v___x_5287_);
if (v___x_5288_ == 0)
{
lean_object* v___x_5289_; 
lean_inc_ref(v_binderType_5282_);
lean_inc(v_binderName_5281_);
lean_dec_ref_known(v_e_5280_, 3);
v___x_5289_ = l_Lean_Expr_lam___override(v_binderName_5281_, v_binderType_5282_, v_b_x27_5285_, v_binderInfo_5284_);
return v___x_5289_;
}
else
{
size_t v___x_5290_; size_t v___x_5291_; uint8_t v___x_5292_; 
v___x_5290_ = lean_ptr_addr(v_body_5283_);
v___x_5291_ = lean_ptr_addr(v_b_x27_5285_);
v___x_5292_ = lean_usize_dec_eq(v___x_5290_, v___x_5291_);
if (v___x_5292_ == 0)
{
lean_object* v___x_5293_; 
lean_inc_ref(v_binderType_5282_);
lean_inc(v_binderName_5281_);
lean_dec_ref_known(v_e_5280_, 3);
v___x_5293_ = l_Lean_Expr_lam___override(v_binderName_5281_, v_binderType_5282_, v_b_x27_5285_, v_binderInfo_5284_);
return v___x_5293_;
}
else
{
uint8_t v___x_5294_; 
v___x_5294_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5284_, v_binderInfo_5284_);
if (v___x_5294_ == 0)
{
lean_object* v___x_5295_; 
lean_inc_ref(v_binderType_5282_);
lean_inc(v_binderName_5281_);
lean_dec_ref_known(v_e_5280_, 3);
v___x_5295_ = l_Lean_Expr_lam___override(v_binderName_5281_, v_binderType_5282_, v_b_x27_5285_, v_binderInfo_5284_);
return v___x_5295_;
}
else
{
lean_dec_ref(v_b_x27_5285_);
return v_e_5280_;
}
}
}
}
}
else
{
return v_e_5280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5313_, lean_object* v_optionName_5314_, lean_object* v_inst_5315_, lean_object* v_val_5316_){
_start:
{
lean_object* v_toDataValue_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; 
v_toDataValue_5317_ = lean_ctor_get(v_inst_5315_, 0);
lean_inc_ref(v_toDataValue_5317_);
lean_dec_ref(v_inst_5315_);
v___x_5318_ = lean_box(0);
v___x_5319_ = lean_apply_1(v_toDataValue_5317_, v_val_5316_);
v___x_5320_ = l_Lean_KVMap_insert(v___x_5318_, v_optionName_5314_, v___x_5319_);
v___x_5321_ = l_Lean_Expr_mdata___override(v___x_5320_, v_e_5313_);
return v___x_5321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5322_, lean_object* v_e_5323_, lean_object* v_optionName_5324_, lean_object* v_inst_5325_, lean_object* v_val_5326_){
_start:
{
lean_object* v___x_5327_; 
v___x_5327_ = l_Lean_Expr_setOption___redArg(v_e_5323_, v_optionName_5324_, v_inst_5325_, v_val_5326_);
return v___x_5327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5328_, lean_object* v_optionName_5329_, uint8_t v_val_5330_){
_start:
{
lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; 
v___x_5331_ = lean_box(0);
v___x_5332_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5332_, 0, v_val_5330_);
v___x_5333_ = l_Lean_KVMap_insert(v___x_5331_, v_optionName_5329_, v___x_5332_);
v___x_5334_ = l_Lean_Expr_mdata___override(v___x_5333_, v_e_5328_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5335_, lean_object* v_optionName_5336_, lean_object* v_val_5337_){
_start:
{
uint8_t v_val_boxed_5338_; lean_object* v_res_5339_; 
v_val_boxed_5338_ = lean_unbox(v_val_5337_);
v_res_5339_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5335_, v_optionName_5336_, v_val_boxed_5338_);
return v_res_5339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5345_, uint8_t v_flag_5346_){
_start:
{
lean_object* v___x_5347_; lean_object* v___x_5348_; 
v___x_5347_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5348_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5345_, v___x_5347_, v_flag_5346_);
return v___x_5348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5349_, lean_object* v_flag_5350_){
_start:
{
uint8_t v_flag_boxed_5351_; lean_object* v_res_5352_; 
v_flag_boxed_5351_ = lean_unbox(v_flag_5350_);
v_res_5352_ = l_Lean_Expr_setPPExplicit(v_e_5349_, v_flag_boxed_5351_);
return v_res_5352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5357_, uint8_t v_flag_5358_){
_start:
{
lean_object* v___x_5359_; lean_object* v___x_5360_; 
v___x_5359_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5360_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5357_, v___x_5359_, v_flag_5358_);
return v___x_5360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5361_, lean_object* v_flag_5362_){
_start:
{
uint8_t v_flag_boxed_5363_; lean_object* v_res_5364_; 
v_flag_boxed_5363_ = lean_unbox(v_flag_5362_);
v_res_5364_ = l_Lean_Expr_setPPUniverses(v_e_5361_, v_flag_boxed_5363_);
return v_res_5364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5369_, uint8_t v_flag_5370_){
_start:
{
lean_object* v___x_5371_; lean_object* v___x_5372_; 
v___x_5371_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5372_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5369_, v___x_5371_, v_flag_5370_);
return v___x_5372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5373_, lean_object* v_flag_5374_){
_start:
{
uint8_t v_flag_boxed_5375_; lean_object* v_res_5376_; 
v_flag_boxed_5375_ = lean_unbox(v_flag_5374_);
v_res_5376_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5373_, v_flag_boxed_5375_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5381_, uint8_t v_flag_5382_){
_start:
{
lean_object* v___x_5383_; lean_object* v___x_5384_; 
v___x_5383_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5384_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5381_, v___x_5383_, v_flag_5382_);
return v___x_5384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5385_, lean_object* v_flag_5386_){
_start:
{
uint8_t v_flag_boxed_5387_; lean_object* v_res_5388_; 
v_flag_boxed_5387_ = lean_unbox(v_flag_5386_);
v_res_5388_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5385_, v_flag_boxed_5387_);
return v_res_5388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5393_, uint8_t v_flag_5394_){
_start:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; 
v___x_5395_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5396_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5393_, v___x_5395_, v_flag_5394_);
return v___x_5396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5397_, lean_object* v_flag_5398_){
_start:
{
uint8_t v_flag_boxed_5399_; lean_object* v_res_5400_; 
v_flag_boxed_5399_ = lean_unbox(v_flag_5398_);
v_res_5400_ = l_Lean_Expr_setPPNumericTypes(v_e_5397_, v_flag_boxed_5399_);
return v_res_5400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5401_, size_t v_i_5402_, lean_object* v_bs_5403_){
_start:
{
uint8_t v___x_5404_; 
v___x_5404_ = lean_usize_dec_lt(v_i_5402_, v_sz_5401_);
if (v___x_5404_ == 0)
{
return v_bs_5403_;
}
else
{
uint8_t v___x_5405_; lean_object* v_v_5406_; lean_object* v___x_5407_; lean_object* v_bs_x27_5408_; lean_object* v___x_5409_; size_t v___x_5410_; size_t v___x_5411_; lean_object* v___x_5412_; 
v___x_5405_ = 0;
v_v_5406_ = lean_array_uget(v_bs_5403_, v_i_5402_);
v___x_5407_ = lean_unsigned_to_nat(0u);
v_bs_x27_5408_ = lean_array_uset(v_bs_5403_, v_i_5402_, v___x_5407_);
v___x_5409_ = l_Lean_Expr_setPPExplicit(v_v_5406_, v___x_5405_);
v___x_5410_ = ((size_t)1ULL);
v___x_5411_ = lean_usize_add(v_i_5402_, v___x_5410_);
v___x_5412_ = lean_array_uset(v_bs_x27_5408_, v_i_5402_, v___x_5409_);
v_i_5402_ = v___x_5411_;
v_bs_5403_ = v___x_5412_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5414_, lean_object* v_i_5415_, lean_object* v_bs_5416_){
_start:
{
size_t v_sz_boxed_5417_; size_t v_i_boxed_5418_; lean_object* v_res_5419_; 
v_sz_boxed_5417_ = lean_unbox_usize(v_sz_5414_);
lean_dec(v_sz_5414_);
v_i_boxed_5418_ = lean_unbox_usize(v_i_5415_);
lean_dec(v_i_5415_);
v_res_5419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5417_, v_i_boxed_5418_, v_bs_5416_);
return v_res_5419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5420_){
_start:
{
if (lean_obj_tag(v_e_5420_) == 5)
{
lean_object* v___x_5421_; uint8_t v___x_5422_; lean_object* v_f_5423_; lean_object* v_dummy_5424_; lean_object* v_nargs_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; size_t v_sz_5430_; size_t v___x_5431_; lean_object* v_args_5432_; lean_object* v___x_5433_; uint8_t v___x_5434_; lean_object* v___x_5435_; 
v___x_5421_ = l_Lean_Expr_getAppFn(v_e_5420_);
v___x_5422_ = 0;
v_f_5423_ = l_Lean_Expr_setPPExplicit(v___x_5421_, v___x_5422_);
v_dummy_5424_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5425_ = l_Lean_Expr_getAppNumArgs(v_e_5420_);
lean_inc(v_nargs_5425_);
v___x_5426_ = lean_mk_array(v_nargs_5425_, v_dummy_5424_);
v___x_5427_ = lean_unsigned_to_nat(1u);
v___x_5428_ = lean_nat_sub(v_nargs_5425_, v___x_5427_);
lean_dec(v_nargs_5425_);
v___x_5429_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5420_, v___x_5426_, v___x_5428_);
v_sz_5430_ = lean_array_size(v___x_5429_);
v___x_5431_ = ((size_t)0ULL);
v_args_5432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5430_, v___x_5431_, v___x_5429_);
v___x_5433_ = l_Lean_mkAppN(v_f_5423_, v_args_5432_);
lean_dec_ref(v_args_5432_);
v___x_5434_ = 1;
v___x_5435_ = l_Lean_Expr_setPPExplicit(v___x_5433_, v___x_5434_);
return v___x_5435_;
}
else
{
return v_e_5420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5436_, size_t v_i_5437_, lean_object* v_bs_5438_){
_start:
{
uint8_t v___x_5439_; 
v___x_5439_ = lean_usize_dec_lt(v_i_5437_, v_sz_5436_);
if (v___x_5439_ == 0)
{
return v_bs_5438_;
}
else
{
lean_object* v_v_5440_; lean_object* v___x_5441_; lean_object* v_bs_x27_5442_; lean_object* v___y_5444_; uint8_t v___x_5449_; 
v_v_5440_ = lean_array_uget(v_bs_5438_, v_i_5437_);
v___x_5441_ = lean_unsigned_to_nat(0u);
v_bs_x27_5442_ = lean_array_uset(v_bs_5438_, v_i_5437_, v___x_5441_);
v___x_5449_ = l_Lean_Expr_hasMVar(v_v_5440_);
if (v___x_5449_ == 0)
{
lean_object* v___x_5450_; 
v___x_5450_ = l_Lean_Expr_setPPExplicit(v_v_5440_, v___x_5449_);
v___y_5444_ = v___x_5450_;
goto v___jp_5443_;
}
else
{
v___y_5444_ = v_v_5440_;
goto v___jp_5443_;
}
v___jp_5443_:
{
size_t v___x_5445_; size_t v___x_5446_; lean_object* v___x_5447_; 
v___x_5445_ = ((size_t)1ULL);
v___x_5446_ = lean_usize_add(v_i_5437_, v___x_5445_);
v___x_5447_ = lean_array_uset(v_bs_x27_5442_, v_i_5437_, v___y_5444_);
v_i_5437_ = v___x_5446_;
v_bs_5438_ = v___x_5447_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5451_, lean_object* v_i_5452_, lean_object* v_bs_5453_){
_start:
{
size_t v_sz_boxed_5454_; size_t v_i_boxed_5455_; lean_object* v_res_5456_; 
v_sz_boxed_5454_ = lean_unbox_usize(v_sz_5451_);
lean_dec(v_sz_5451_);
v_i_boxed_5455_ = lean_unbox_usize(v_i_5452_);
lean_dec(v_i_5452_);
v_res_5456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5454_, v_i_boxed_5455_, v_bs_5453_);
return v_res_5456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5457_){
_start:
{
if (lean_obj_tag(v_e_5457_) == 5)
{
lean_object* v___x_5458_; uint8_t v___x_5459_; lean_object* v_f_5460_; lean_object* v_dummy_5461_; lean_object* v_nargs_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; size_t v_sz_5467_; size_t v___x_5468_; lean_object* v_args_5469_; lean_object* v___x_5470_; uint8_t v___x_5471_; lean_object* v___x_5472_; 
v___x_5458_ = l_Lean_Expr_getAppFn(v_e_5457_);
v___x_5459_ = 0;
v_f_5460_ = l_Lean_Expr_setPPExplicit(v___x_5458_, v___x_5459_);
v_dummy_5461_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5462_ = l_Lean_Expr_getAppNumArgs(v_e_5457_);
lean_inc(v_nargs_5462_);
v___x_5463_ = lean_mk_array(v_nargs_5462_, v_dummy_5461_);
v___x_5464_ = lean_unsigned_to_nat(1u);
v___x_5465_ = lean_nat_sub(v_nargs_5462_, v___x_5464_);
lean_dec(v_nargs_5462_);
v___x_5466_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5457_, v___x_5463_, v___x_5465_);
v_sz_5467_ = lean_array_size(v___x_5466_);
v___x_5468_ = ((size_t)0ULL);
v_args_5469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5467_, v___x_5468_, v___x_5466_);
v___x_5470_ = l_Lean_mkAppN(v_f_5460_, v_args_5469_);
lean_dec_ref(v_args_5469_);
v___x_5471_ = 1;
v___x_5472_ = l_Lean_Expr_setPPExplicit(v___x_5470_, v___x_5471_);
return v___x_5472_;
}
else
{
return v_e_5457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5473_, lean_object* v_body_5474_, lean_object* v_x_5475_){
_start:
{
lean_object* v___x_5476_; 
v___x_5476_ = lean_apply_1(v_f_5473_, v_body_5474_);
return v___x_5476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5477_, lean_object* v_binderType_5478_, lean_object* v_x_5479_){
_start:
{
lean_object* v___x_5480_; 
v___x_5480_ = lean_apply_1(v_f_5477_, v_binderType_5478_);
return v___x_5480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5481_, lean_object* v_value_5482_, lean_object* v_x_5483_){
_start:
{
lean_object* v___x_5484_; 
v___x_5484_ = lean_apply_1(v_f_5481_, v_value_5482_);
return v___x_5484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5485_, lean_object* v_type_5486_, lean_object* v_x_5487_){
_start:
{
lean_object* v___x_5488_; 
v___x_5488_ = lean_apply_1(v_f_5485_, v_type_5486_);
return v___x_5488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5489_, lean_object* v_arg_5490_, lean_object* v_x_5491_){
_start:
{
lean_object* v___x_5492_; 
v___x_5492_ = lean_apply_1(v_f_5489_, v_arg_5490_);
return v___x_5492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5493_, lean_object* v_fn_5494_, lean_object* v_x_5495_){
_start:
{
lean_object* v___x_5496_; 
v___x_5496_ = lean_apply_1(v_f_5493_, v_fn_5494_);
return v___x_5496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5497_, lean_object* v_f_5498_, lean_object* v_x_5499_){
_start:
{
switch(lean_obj_tag(v_x_5499_))
{
case 7:
{
lean_object* v_toPure_5500_; lean_object* v_toSeq_5501_; lean_object* v_binderType_5502_; lean_object* v_body_5503_; lean_object* v___f_5504_; lean_object* v___f_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; 
v_toPure_5500_ = lean_ctor_get(v_inst_5497_, 1);
lean_inc(v_toPure_5500_);
v_toSeq_5501_ = lean_ctor_get(v_inst_5497_, 2);
lean_inc_n(v_toSeq_5501_, 2);
lean_dec_ref(v_inst_5497_);
v_binderType_5502_ = lean_ctor_get(v_x_5499_, 1);
v_body_5503_ = lean_ctor_get(v_x_5499_, 2);
lean_inc_ref(v_body_5503_);
lean_inc(v_f_5498_);
v___f_5504_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5504_, 0, v_f_5498_);
lean_closure_set(v___f_5504_, 1, v_body_5503_);
lean_inc_ref(v_binderType_5502_);
v___f_5505_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5505_, 0, v_f_5498_);
lean_closure_set(v___f_5505_, 1, v_binderType_5502_);
v___x_5506_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5506_, 0, v_x_5499_);
v___x_5507_ = lean_apply_2(v_toPure_5500_, lean_box(0), v___x_5506_);
v___x_5508_ = lean_apply_4(v_toSeq_5501_, lean_box(0), lean_box(0), v___x_5507_, v___f_5505_);
v___x_5509_ = lean_apply_4(v_toSeq_5501_, lean_box(0), lean_box(0), v___x_5508_, v___f_5504_);
return v___x_5509_;
}
case 6:
{
lean_object* v_toPure_5510_; lean_object* v_toSeq_5511_; lean_object* v_binderType_5512_; lean_object* v_body_5513_; lean_object* v___f_5514_; lean_object* v___f_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; 
v_toPure_5510_ = lean_ctor_get(v_inst_5497_, 1);
lean_inc(v_toPure_5510_);
v_toSeq_5511_ = lean_ctor_get(v_inst_5497_, 2);
lean_inc_n(v_toSeq_5511_, 2);
lean_dec_ref(v_inst_5497_);
v_binderType_5512_ = lean_ctor_get(v_x_5499_, 1);
v_body_5513_ = lean_ctor_get(v_x_5499_, 2);
lean_inc_ref(v_body_5513_);
lean_inc(v_f_5498_);
v___f_5514_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5514_, 0, v_f_5498_);
lean_closure_set(v___f_5514_, 1, v_body_5513_);
lean_inc_ref(v_binderType_5512_);
v___f_5515_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5515_, 0, v_f_5498_);
lean_closure_set(v___f_5515_, 1, v_binderType_5512_);
v___x_5516_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5516_, 0, v_x_5499_);
v___x_5517_ = lean_apply_2(v_toPure_5510_, lean_box(0), v___x_5516_);
v___x_5518_ = lean_apply_4(v_toSeq_5511_, lean_box(0), lean_box(0), v___x_5517_, v___f_5515_);
v___x_5519_ = lean_apply_4(v_toSeq_5511_, lean_box(0), lean_box(0), v___x_5518_, v___f_5514_);
return v___x_5519_;
}
case 10:
{
lean_object* v_toFunctor_5520_; lean_object* v_expr_5521_; lean_object* v_map_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; 
v_toFunctor_5520_ = lean_ctor_get(v_inst_5497_, 0);
lean_inc_ref(v_toFunctor_5520_);
lean_dec_ref(v_inst_5497_);
v_expr_5521_ = lean_ctor_get(v_x_5499_, 1);
lean_inc_ref(v_expr_5521_);
v_map_5522_ = lean_ctor_get(v_toFunctor_5520_, 0);
lean_inc(v_map_5522_);
lean_dec_ref(v_toFunctor_5520_);
v___x_5523_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5523_, 0, v_x_5499_);
v___x_5524_ = lean_apply_1(v_f_5498_, v_expr_5521_);
v___x_5525_ = lean_apply_4(v_map_5522_, lean_box(0), lean_box(0), v___x_5523_, v___x_5524_);
return v___x_5525_;
}
case 8:
{
lean_object* v_toPure_5526_; lean_object* v_toSeq_5527_; lean_object* v_type_5528_; lean_object* v_value_5529_; lean_object* v_body_5530_; lean_object* v___f_5531_; lean_object* v___f_5532_; lean_object* v___f_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; 
v_toPure_5526_ = lean_ctor_get(v_inst_5497_, 1);
lean_inc(v_toPure_5526_);
v_toSeq_5527_ = lean_ctor_get(v_inst_5497_, 2);
lean_inc_n(v_toSeq_5527_, 3);
lean_dec_ref(v_inst_5497_);
v_type_5528_ = lean_ctor_get(v_x_5499_, 1);
v_value_5529_ = lean_ctor_get(v_x_5499_, 2);
v_body_5530_ = lean_ctor_get(v_x_5499_, 3);
lean_inc_ref(v_body_5530_);
lean_inc_n(v_f_5498_, 2);
v___f_5531_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5531_, 0, v_f_5498_);
lean_closure_set(v___f_5531_, 1, v_body_5530_);
lean_inc_ref(v_value_5529_);
v___f_5532_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5532_, 0, v_f_5498_);
lean_closure_set(v___f_5532_, 1, v_value_5529_);
lean_inc_ref(v_type_5528_);
v___f_5533_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5533_, 0, v_f_5498_);
lean_closure_set(v___f_5533_, 1, v_type_5528_);
v___x_5534_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5534_, 0, v_x_5499_);
v___x_5535_ = lean_apply_2(v_toPure_5526_, lean_box(0), v___x_5534_);
v___x_5536_ = lean_apply_4(v_toSeq_5527_, lean_box(0), lean_box(0), v___x_5535_, v___f_5533_);
v___x_5537_ = lean_apply_4(v_toSeq_5527_, lean_box(0), lean_box(0), v___x_5536_, v___f_5532_);
v___x_5538_ = lean_apply_4(v_toSeq_5527_, lean_box(0), lean_box(0), v___x_5537_, v___f_5531_);
return v___x_5538_;
}
case 5:
{
lean_object* v_toPure_5539_; lean_object* v_toSeq_5540_; lean_object* v_fn_5541_; lean_object* v_arg_5542_; lean_object* v___f_5543_; lean_object* v___f_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; 
v_toPure_5539_ = lean_ctor_get(v_inst_5497_, 1);
lean_inc(v_toPure_5539_);
v_toSeq_5540_ = lean_ctor_get(v_inst_5497_, 2);
lean_inc_n(v_toSeq_5540_, 2);
lean_dec_ref(v_inst_5497_);
v_fn_5541_ = lean_ctor_get(v_x_5499_, 0);
v_arg_5542_ = lean_ctor_get(v_x_5499_, 1);
lean_inc_ref(v_arg_5542_);
lean_inc(v_f_5498_);
v___f_5543_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5543_, 0, v_f_5498_);
lean_closure_set(v___f_5543_, 1, v_arg_5542_);
lean_inc_ref(v_fn_5541_);
v___f_5544_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5544_, 0, v_f_5498_);
lean_closure_set(v___f_5544_, 1, v_fn_5541_);
v___x_5545_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5545_, 0, v_x_5499_);
v___x_5546_ = lean_apply_2(v_toPure_5539_, lean_box(0), v___x_5545_);
v___x_5547_ = lean_apply_4(v_toSeq_5540_, lean_box(0), lean_box(0), v___x_5546_, v___f_5544_);
v___x_5548_ = lean_apply_4(v_toSeq_5540_, lean_box(0), lean_box(0), v___x_5547_, v___f_5543_);
return v___x_5548_;
}
case 11:
{
lean_object* v_toFunctor_5549_; lean_object* v_struct_5550_; lean_object* v_map_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; 
v_toFunctor_5549_ = lean_ctor_get(v_inst_5497_, 0);
lean_inc_ref(v_toFunctor_5549_);
lean_dec_ref(v_inst_5497_);
v_struct_5550_ = lean_ctor_get(v_x_5499_, 2);
lean_inc_ref(v_struct_5550_);
v_map_5551_ = lean_ctor_get(v_toFunctor_5549_, 0);
lean_inc(v_map_5551_);
lean_dec_ref(v_toFunctor_5549_);
v___x_5552_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5552_, 0, v_x_5499_);
v___x_5553_ = lean_apply_1(v_f_5498_, v_struct_5550_);
v___x_5554_ = lean_apply_4(v_map_5551_, lean_box(0), lean_box(0), v___x_5552_, v___x_5553_);
return v___x_5554_;
}
default: 
{
lean_object* v_toPure_5555_; lean_object* v___x_5556_; 
lean_dec(v_f_5498_);
v_toPure_5555_ = lean_ctor_get(v_inst_5497_, 1);
lean_inc(v_toPure_5555_);
lean_dec_ref(v_inst_5497_);
v___x_5556_ = lean_apply_2(v_toPure_5555_, lean_box(0), v_x_5499_);
return v___x_5556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5557_, lean_object* v_inst_5558_, lean_object* v_f_5559_, lean_object* v_x_5560_){
_start:
{
lean_object* v___x_5561_; 
v___x_5561_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5558_, v_f_5559_, v_x_5560_);
return v___x_5561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5562_){
_start:
{
lean_object* v_snd_5563_; 
v_snd_5563_ = lean_ctor_get(v_self_5562_, 1);
lean_inc(v_snd_5563_);
return v_snd_5563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5564_){
_start:
{
lean_object* v_res_5565_; 
v_res_5565_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5564_);
lean_dec_ref(v_self_5564_);
return v_res_5565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5566_, lean_object* v_snd_5567_){
_start:
{
lean_object* v___x_5568_; 
v___x_5568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5568_, 0, v_e_x27_5566_);
lean_ctor_set(v___x_5568_, 1, v_snd_5567_);
return v___x_5568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5569_, lean_object* v_map_5570_, lean_object* v_e_x27_5571_, lean_object* v_a_5572_){
_start:
{
lean_object* v___f_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; 
lean_inc_ref(v_e_x27_5571_);
v___f_5573_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5573_, 0, v_e_x27_5571_);
v___x_5574_ = lean_apply_2(v_f_5569_, v_a_5572_, v_e_x27_5571_);
v___x_5575_ = lean_apply_4(v_map_5570_, lean_box(0), lean_box(0), v___f_5573_, v___x_5574_);
return v___x_5575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5577_, lean_object* v_f_5578_, lean_object* v_init_5579_, lean_object* v_e_5580_){
_start:
{
lean_object* v_toApplicative_5581_; lean_object* v_toFunctor_5582_; lean_object* v___x_5584_; uint8_t v_isShared_5585_; uint8_t v_isSharedCheck_5609_; 
v_toApplicative_5581_ = lean_ctor_get(v_inst_5577_, 0);
lean_inc_ref(v_toApplicative_5581_);
v_toFunctor_5582_ = lean_ctor_get(v_toApplicative_5581_, 0);
v_isSharedCheck_5609_ = !lean_is_exclusive(v_toApplicative_5581_);
if (v_isSharedCheck_5609_ == 0)
{
lean_object* v_unused_5610_; lean_object* v_unused_5611_; lean_object* v_unused_5612_; lean_object* v_unused_5613_; 
v_unused_5610_ = lean_ctor_get(v_toApplicative_5581_, 4);
lean_dec(v_unused_5610_);
v_unused_5611_ = lean_ctor_get(v_toApplicative_5581_, 3);
lean_dec(v_unused_5611_);
v_unused_5612_ = lean_ctor_get(v_toApplicative_5581_, 2);
lean_dec(v_unused_5612_);
v_unused_5613_ = lean_ctor_get(v_toApplicative_5581_, 1);
lean_dec(v_unused_5613_);
v___x_5584_ = v_toApplicative_5581_;
v_isShared_5585_ = v_isSharedCheck_5609_;
goto v_resetjp_5583_;
}
else
{
lean_inc(v_toFunctor_5582_);
lean_dec(v_toApplicative_5581_);
v___x_5584_ = lean_box(0);
v_isShared_5585_ = v_isSharedCheck_5609_;
goto v_resetjp_5583_;
}
v_resetjp_5583_:
{
lean_object* v_map_5586_; lean_object* v___x_5588_; uint8_t v_isShared_5589_; uint8_t v_isSharedCheck_5607_; 
v_map_5586_ = lean_ctor_get(v_toFunctor_5582_, 0);
v_isSharedCheck_5607_ = !lean_is_exclusive(v_toFunctor_5582_);
if (v_isSharedCheck_5607_ == 0)
{
lean_object* v_unused_5608_; 
v_unused_5608_ = lean_ctor_get(v_toFunctor_5582_, 1);
lean_dec(v_unused_5608_);
v___x_5588_ = v_toFunctor_5582_;
v_isShared_5589_ = v_isSharedCheck_5607_;
goto v_resetjp_5587_;
}
else
{
lean_inc(v_map_5586_);
lean_dec(v_toFunctor_5582_);
v___x_5588_ = lean_box(0);
v_isShared_5589_ = v_isSharedCheck_5607_;
goto v_resetjp_5587_;
}
v_resetjp_5587_:
{
lean_object* v___f_5590_; lean_object* v___f_5591_; lean_object* v___f_5592_; lean_object* v___f_5593_; lean_object* v___f_5594_; lean_object* v___f_5595_; lean_object* v___x_5596_; lean_object* v___x_5598_; 
v___f_5590_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5586_);
v___f_5591_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5591_, 0, v_f_5578_);
lean_closure_set(v___f_5591_, 1, v_map_5586_);
lean_inc_ref_n(v_inst_5577_, 5);
v___f_5592_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5592_, 0, v_inst_5577_);
v___f_5593_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5593_, 0, v_inst_5577_);
v___f_5594_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5594_, 0, v_inst_5577_);
v___f_5595_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5595_, 0, v_inst_5577_);
v___x_5596_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5596_, 0, lean_box(0));
lean_closure_set(v___x_5596_, 1, lean_box(0));
lean_closure_set(v___x_5596_, 2, v_inst_5577_);
if (v_isShared_5589_ == 0)
{
lean_ctor_set(v___x_5588_, 1, v___f_5592_);
lean_ctor_set(v___x_5588_, 0, v___x_5596_);
v___x_5598_ = v___x_5588_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v___x_5596_);
lean_ctor_set(v_reuseFailAlloc_5606_, 1, v___f_5592_);
v___x_5598_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
lean_object* v___x_5599_; lean_object* v___x_5601_; 
v___x_5599_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5599_, 0, lean_box(0));
lean_closure_set(v___x_5599_, 1, lean_box(0));
lean_closure_set(v___x_5599_, 2, v_inst_5577_);
if (v_isShared_5585_ == 0)
{
lean_ctor_set(v___x_5584_, 4, v___f_5595_);
lean_ctor_set(v___x_5584_, 3, v___f_5594_);
lean_ctor_set(v___x_5584_, 2, v___f_5593_);
lean_ctor_set(v___x_5584_, 1, v___x_5599_);
lean_ctor_set(v___x_5584_, 0, v___x_5598_);
v___x_5601_ = v___x_5584_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5598_);
lean_ctor_set(v_reuseFailAlloc_5605_, 1, v___x_5599_);
lean_ctor_set(v_reuseFailAlloc_5605_, 2, v___f_5593_);
lean_ctor_set(v_reuseFailAlloc_5605_, 3, v___f_5594_);
lean_ctor_set(v_reuseFailAlloc_5605_, 4, v___f_5595_);
v___x_5601_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
lean_object* v___x_30__overap_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; 
v___x_30__overap_5602_ = l_Lean_Expr_traverseChildren___redArg(v___x_5601_, v___f_5591_, v_e_5580_);
v___x_5603_ = lean_apply_1(v___x_30__overap_5602_, v_init_5579_);
v___x_5604_ = lean_apply_4(v_map_5586_, lean_box(0), lean_box(0), v___f_5590_, v___x_5603_);
return v___x_5604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5614_, lean_object* v_m_5615_, lean_object* v_inst_5616_, lean_object* v_f_5617_, lean_object* v_init_5618_, lean_object* v_e_5619_){
_start:
{
lean_object* v___x_5620_; 
v___x_5620_ = l_Lean_Expr_foldlM___redArg(v_inst_5616_, v_f_5617_, v_init_5618_, v_e_5619_);
return v___x_5620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5621_){
_start:
{
lean_object* v_d_5623_; lean_object* v_b_5624_; 
switch(lean_obj_tag(v_x_5621_))
{
case 5:
{
lean_object* v_fn_5630_; lean_object* v_arg_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; 
v_fn_5630_ = lean_ctor_get(v_x_5621_, 0);
v_arg_5631_ = lean_ctor_get(v_x_5621_, 1);
v___x_5632_ = lean_unsigned_to_nat(1u);
v___x_5633_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5630_);
v___x_5634_ = lean_nat_add(v___x_5632_, v___x_5633_);
lean_dec(v___x_5633_);
v___x_5635_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5631_);
v___x_5636_ = lean_nat_add(v___x_5634_, v___x_5635_);
lean_dec(v___x_5635_);
lean_dec(v___x_5634_);
return v___x_5636_;
}
case 6:
{
lean_object* v_binderType_5637_; lean_object* v_body_5638_; 
v_binderType_5637_ = lean_ctor_get(v_x_5621_, 1);
v_body_5638_ = lean_ctor_get(v_x_5621_, 2);
v_d_5623_ = v_binderType_5637_;
v_b_5624_ = v_body_5638_;
goto v___jp_5622_;
}
case 7:
{
lean_object* v_binderType_5639_; lean_object* v_body_5640_; 
v_binderType_5639_ = lean_ctor_get(v_x_5621_, 1);
v_body_5640_ = lean_ctor_get(v_x_5621_, 2);
v_d_5623_ = v_binderType_5639_;
v_b_5624_ = v_body_5640_;
goto v___jp_5622_;
}
case 8:
{
lean_object* v_type_5641_; lean_object* v_value_5642_; lean_object* v_body_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; 
v_type_5641_ = lean_ctor_get(v_x_5621_, 1);
v_value_5642_ = lean_ctor_get(v_x_5621_, 2);
v_body_5643_ = lean_ctor_get(v_x_5621_, 3);
v___x_5644_ = lean_unsigned_to_nat(1u);
v___x_5645_ = l_Lean_Expr_sizeWithoutSharing(v_type_5641_);
v___x_5646_ = lean_nat_add(v___x_5644_, v___x_5645_);
lean_dec(v___x_5645_);
v___x_5647_ = l_Lean_Expr_sizeWithoutSharing(v_value_5642_);
v___x_5648_ = lean_nat_add(v___x_5646_, v___x_5647_);
lean_dec(v___x_5647_);
lean_dec(v___x_5646_);
v___x_5649_ = l_Lean_Expr_sizeWithoutSharing(v_body_5643_);
v___x_5650_ = lean_nat_add(v___x_5648_, v___x_5649_);
lean_dec(v___x_5649_);
lean_dec(v___x_5648_);
return v___x_5650_;
}
case 10:
{
lean_object* v_expr_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; 
v_expr_5651_ = lean_ctor_get(v_x_5621_, 1);
v___x_5652_ = lean_unsigned_to_nat(1u);
v___x_5653_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5651_);
v___x_5654_ = lean_nat_add(v___x_5652_, v___x_5653_);
lean_dec(v___x_5653_);
return v___x_5654_;
}
case 11:
{
lean_object* v_struct_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; 
v_struct_5655_ = lean_ctor_get(v_x_5621_, 2);
v___x_5656_ = lean_unsigned_to_nat(1u);
v___x_5657_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5655_);
v___x_5658_ = lean_nat_add(v___x_5656_, v___x_5657_);
lean_dec(v___x_5657_);
return v___x_5658_;
}
default: 
{
lean_object* v___x_5659_; 
v___x_5659_ = lean_unsigned_to_nat(1u);
return v___x_5659_;
}
}
v___jp_5622_:
{
lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; 
v___x_5625_ = lean_unsigned_to_nat(1u);
v___x_5626_ = l_Lean_Expr_sizeWithoutSharing(v_d_5623_);
v___x_5627_ = lean_nat_add(v___x_5625_, v___x_5626_);
lean_dec(v___x_5626_);
v___x_5628_ = l_Lean_Expr_sizeWithoutSharing(v_b_5624_);
v___x_5629_ = lean_nat_add(v___x_5627_, v___x_5628_);
lean_dec(v___x_5628_);
lean_dec(v___x_5627_);
return v___x_5629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5660_){
_start:
{
lean_object* v_res_5661_; 
v_res_5661_ = l_Lean_Expr_sizeWithoutSharing(v_x_5660_);
lean_dec_ref(v_x_5660_);
return v_res_5661_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5664_, lean_object* v_e_5665_){
_start:
{
lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; 
v___x_5666_ = l_Lean_KVMap_empty;
v___x_5667_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5668_ = l_Lean_KVMap_insert(v___x_5666_, v_kind_5664_, v___x_5667_);
v___x_5669_ = l_Lean_Expr_mdata___override(v___x_5668_, v_e_5665_);
return v___x_5669_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5670_, lean_object* v_e_5671_){
_start:
{
if (lean_obj_tag(v_e_5671_) == 10)
{
lean_object* v_data_5672_; lean_object* v_expr_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; uint8_t v___x_5676_; 
v_data_5672_ = lean_ctor_get(v_e_5671_, 0);
v_expr_5673_ = lean_ctor_get(v_e_5671_, 1);
v___x_5674_ = l_Lean_KVMap_size(v_data_5672_);
v___x_5675_ = lean_unsigned_to_nat(1u);
v___x_5676_ = lean_nat_dec_eq(v___x_5674_, v___x_5675_);
lean_dec(v___x_5674_);
if (v___x_5676_ == 0)
{
lean_object* v___x_5677_; 
v___x_5677_ = lean_box(0);
return v___x_5677_;
}
else
{
uint8_t v___x_5678_; uint8_t v___x_5679_; 
v___x_5678_ = 0;
v___x_5679_ = l_Lean_KVMap_getBool(v_data_5672_, v_kind_5670_, v___x_5678_);
if (v___x_5679_ == 0)
{
lean_object* v___x_5680_; 
v___x_5680_ = lean_box(0);
return v___x_5680_;
}
else
{
lean_object* v___x_5681_; 
lean_inc_ref(v_expr_5673_);
v___x_5681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5681_, 0, v_expr_5673_);
return v___x_5681_;
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
lean_dec_ref_known(v_val_5705_, 1);
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
lean_dec_ref_known(v___x_5722_, 1);
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
lean_dec_ref_known(v___x_5730_, 1);
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
lean_dec_ref_known(v_x_5850_, 2);
return v_head_5853_;
}
else
{
lean_object* v_head_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; 
lean_inc(v_tail_5852_);
v_head_5854_ = lean_ctor_get(v_x_5850_, 0);
lean_inc(v_head_5854_);
lean_dec_ref_known(v_x_5850_, 2);
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
v___x_6504_ = lean_unsigned_to_nat(2441u);
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
lean_dec_ref_known(v_e_6508_, 2);
v___x_6512_ = l_Lean_Expr_replaceFn(v_fn_6510_, v_declName_6509_);
v___x_6513_ = l_Lean_Expr_app___override(v___x_6512_, v_arg_6511_);
return v___x_6513_;
}
case 4:
{
lean_object* v_us_6514_; lean_object* v___x_6515_; 
v_us_6514_ = lean_ctor_get(v_e_6508_, 1);
lean_inc(v_us_6514_);
lean_dec_ref_known(v_e_6508_, 2);
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
