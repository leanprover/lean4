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
lean_object* l_Lean_Level_hasMVar___boxed(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Level_hasParam___boxed(lean_object*);
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
uint8_t l_Lean_Level_hasMVar(lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
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
lean_object* l_Std_TreeSet_ofList___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_const___override___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_hasMVar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_const___override___closed__0 = (const lean_object*)&l_Lean_Expr_const___override___closed__0_value;
static const lean_closure_object l_Lean_Expr_const___override___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_hasParam___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_const___override___closed__1 = (const lean_object*)&l_Lean_Expr_const___override___closed__1_value;
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
v___x_685_ = lean_nat_add(v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec(v___y_683_);
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
lean_ctor_set(v___x_665_, 3, v___y_682_);
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
lean_ctor_set(v_reuseFailAlloc_690_, 3, v___y_682_);
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
v___y_682_ = v___x_697_;
v___y_683_ = v___x_698_;
v___y_684_ = v_size_699_;
goto v___jp_681_;
}
else
{
lean_object* v___x_700_; 
v___x_700_ = lean_unsigned_to_nat(0u);
v___y_682_ = v___x_697_;
v___y_683_ = v___x_698_;
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
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object* v_l_1022_){
_start:
{
lean_object* v___f_1023_; lean_object* v___x_1024_; 
v___f_1023_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1024_ = l_Std_TreeSet_ofArray___redArg(v_l_1022_, v___f_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object* v_l_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_FVarIdSet_ofArray(v_l_1025_);
lean_dec_ref(v_l_1025_);
return v_res_1026_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_unsigned_to_nat(16u);
v___x_1029_ = lean_mk_array(v___x_1028_, v___x_1027_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0);
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v___x_1030_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet(void){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet(void){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object* v_s_1037_, lean_object* v_fvarId_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1038_, v_a_1039_, v_s_1037_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object* v_00_u03b1_1041_, lean_object* v_s_1042_, lean_object* v_fvarId_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1043_, v_a_1044_, v_s_1042_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1(lean_object* v_00_u03b1_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_box(1);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* v_00_u03b1_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_box(1);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* v_00_u03b1_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_box(1);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId_default(void){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_box(0);
return v___x_1052_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId(void){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_box(0);
return v___x_1053_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMVarId_beq(lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_name_eq(v_x_1054_, v_x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
uint8_t v_res_1059_; lean_object* v_r_1060_; 
v_res_1059_ = l_Lean_instBEqMVarId_beq(v_x_1057_, v_x_1058_);
lean_dec(v_x_1058_);
lean_dec(v_x_1057_);
v_r_1060_ = lean_box(v_res_1059_);
return v_r_1060_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableMVarId_hash(lean_object* v_x_1063_){
_start:
{
uint64_t v___x_1064_; 
v___x_1064_ = 0ULL;
if (lean_obj_tag(v_x_1063_) == 0)
{
uint64_t v___x_1065_; 
v___x_1065_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__1, &l_Lean_instHashableFVarId_hash___closed__1_once, _init_l_Lean_instHashableFVarId_hash___closed__1);
return v___x_1065_;
}
else
{
uint64_t v_hash_1066_; uint64_t v___x_1067_; 
v_hash_1066_ = lean_ctor_get_uint64(v_x_1063_, sizeof(void*)*2);
v___x_1067_ = lean_uint64_mix_hash(v___x_1064_, v_hash_1066_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object* v_x_1068_){
_start:
{
uint64_t v_res_1069_; lean_object* v_r_1070_; 
v_res_1069_ = l_Lean_instHashableMVarId_hash(v_x_1068_);
lean_dec(v_x_1068_);
v_r_1070_ = lean_box_uint64(v_res_1069_);
return v_r_1070_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_box(1);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet(void){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_box(1);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_box(1);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet(void){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_box(1);
return v___x_1077_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object* v_k_1078_, lean_object* v_t_1079_){
_start:
{
if (lean_obj_tag(v_t_1079_) == 0)
{
lean_object* v_k_1080_; lean_object* v_l_1081_; lean_object* v_r_1082_; uint8_t v___x_1083_; 
v_k_1080_ = lean_ctor_get(v_t_1079_, 1);
v_l_1081_ = lean_ctor_get(v_t_1079_, 3);
v_r_1082_ = lean_ctor_get(v_t_1079_, 4);
v___x_1083_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1078_, v_k_1080_);
switch(v___x_1083_)
{
case 0:
{
v_t_1079_ = v_l_1081_;
goto _start;
}
case 1:
{
uint8_t v___x_1085_; 
v___x_1085_ = 1;
return v___x_1085_;
}
default: 
{
v_t_1079_ = v_r_1082_;
goto _start;
}
}
}
else
{
uint8_t v___x_1087_; 
v___x_1087_ = 0;
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object* v_k_1088_, lean_object* v_t_1089_){
_start:
{
uint8_t v_res_1090_; lean_object* v_r_1091_; 
v_res_1090_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1088_, v_t_1089_);
lean_dec(v_t_1089_);
lean_dec(v_k_1088_);
v_r_1091_ = lean_box(v_res_1090_);
return v_r_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object* v_k_1092_, lean_object* v_v_1093_, lean_object* v_t_1094_){
_start:
{
if (lean_obj_tag(v_t_1094_) == 0)
{
lean_object* v_size_1095_; lean_object* v_k_1096_; lean_object* v_v_1097_; lean_object* v_l_1098_; lean_object* v_r_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1379_; 
v_size_1095_ = lean_ctor_get(v_t_1094_, 0);
v_k_1096_ = lean_ctor_get(v_t_1094_, 1);
v_v_1097_ = lean_ctor_get(v_t_1094_, 2);
v_l_1098_ = lean_ctor_get(v_t_1094_, 3);
v_r_1099_ = lean_ctor_get(v_t_1094_, 4);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_t_1094_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1101_ = v_t_1094_;
v_isShared_1102_ = v_isSharedCheck_1379_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_r_1099_);
lean_inc(v_l_1098_);
lean_inc(v_v_1097_);
lean_inc(v_k_1096_);
lean_inc(v_size_1095_);
lean_dec(v_t_1094_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1379_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
uint8_t v___x_1103_; 
v___x_1103_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1092_, v_k_1096_);
switch(v___x_1103_)
{
case 0:
{
lean_object* v_impl_1104_; lean_object* v___x_1105_; 
lean_dec(v_size_1095_);
v_impl_1104_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1092_, v_v_1093_, v_l_1098_);
v___x_1105_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1099_) == 0)
{
lean_object* v_size_1106_; lean_object* v_size_1107_; lean_object* v_k_1108_; lean_object* v_v_1109_; lean_object* v_l_1110_; lean_object* v_r_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_size_1106_ = lean_ctor_get(v_r_1099_, 0);
v_size_1107_ = lean_ctor_get(v_impl_1104_, 0);
lean_inc(v_size_1107_);
v_k_1108_ = lean_ctor_get(v_impl_1104_, 1);
lean_inc(v_k_1108_);
v_v_1109_ = lean_ctor_get(v_impl_1104_, 2);
lean_inc(v_v_1109_);
v_l_1110_ = lean_ctor_get(v_impl_1104_, 3);
lean_inc(v_l_1110_);
v_r_1111_ = lean_ctor_get(v_impl_1104_, 4);
lean_inc(v_r_1111_);
v___x_1112_ = lean_unsigned_to_nat(3u);
v___x_1113_ = lean_nat_mul(v___x_1112_, v_size_1106_);
v___x_1114_ = lean_nat_dec_lt(v___x_1113_, v_size_1107_);
lean_dec(v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
lean_dec(v_r_1111_);
lean_dec(v_l_1110_);
lean_dec(v_v_1109_);
lean_dec(v_k_1108_);
v___x_1115_ = lean_nat_add(v___x_1105_, v_size_1107_);
lean_dec(v_size_1107_);
v___x_1116_ = lean_nat_add(v___x_1115_, v_size_1106_);
lean_dec(v___x_1115_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 3, v_impl_1104_);
lean_ctor_set(v___x_1101_, 0, v___x_1116_);
v___x_1118_ = v___x_1101_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1119_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1119_, 3, v_impl_1104_);
lean_ctor_set(v_reuseFailAlloc_1119_, 4, v_r_1099_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
else
{
lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1185_; 
v_isSharedCheck_1185_ = !lean_is_exclusive(v_impl_1104_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; lean_object* v_unused_1187_; lean_object* v_unused_1188_; lean_object* v_unused_1189_; lean_object* v_unused_1190_; 
v_unused_1186_ = lean_ctor_get(v_impl_1104_, 4);
lean_dec(v_unused_1186_);
v_unused_1187_ = lean_ctor_get(v_impl_1104_, 3);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_impl_1104_, 2);
lean_dec(v_unused_1188_);
v_unused_1189_ = lean_ctor_get(v_impl_1104_, 1);
lean_dec(v_unused_1189_);
v_unused_1190_ = lean_ctor_get(v_impl_1104_, 0);
lean_dec(v_unused_1190_);
v___x_1121_ = v_impl_1104_;
v_isShared_1122_ = v_isSharedCheck_1185_;
goto v_resetjp_1120_;
}
else
{
lean_dec(v_impl_1104_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1185_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v_size_1123_; lean_object* v_size_1124_; lean_object* v_k_1125_; lean_object* v_v_1126_; lean_object* v_l_1127_; lean_object* v_r_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v_size_1123_ = lean_ctor_get(v_l_1110_, 0);
v_size_1124_ = lean_ctor_get(v_r_1111_, 0);
v_k_1125_ = lean_ctor_get(v_r_1111_, 1);
v_v_1126_ = lean_ctor_get(v_r_1111_, 2);
v_l_1127_ = lean_ctor_get(v_r_1111_, 3);
v_r_1128_ = lean_ctor_get(v_r_1111_, 4);
v___x_1129_ = lean_unsigned_to_nat(2u);
v___x_1130_ = lean_nat_mul(v___x_1129_, v_size_1123_);
v___x_1131_ = lean_nat_dec_lt(v_size_1124_, v___x_1130_);
lean_dec(v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1160_; 
lean_inc(v_r_1128_);
lean_inc(v_l_1127_);
lean_inc(v_v_1126_);
lean_inc(v_k_1125_);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_r_1111_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; lean_object* v_unused_1162_; lean_object* v_unused_1163_; lean_object* v_unused_1164_; lean_object* v_unused_1165_; 
v_unused_1161_ = lean_ctor_get(v_r_1111_, 4);
lean_dec(v_unused_1161_);
v_unused_1162_ = lean_ctor_get(v_r_1111_, 3);
lean_dec(v_unused_1162_);
v_unused_1163_ = lean_ctor_get(v_r_1111_, 2);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_r_1111_, 1);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_r_1111_, 0);
lean_dec(v_unused_1165_);
v___x_1133_ = v_r_1111_;
v_isShared_1134_ = v_isSharedCheck_1160_;
goto v_resetjp_1132_;
}
else
{
lean_dec(v_r_1111_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1160_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___x_1148_; lean_object* v___y_1150_; 
v___x_1135_ = lean_nat_add(v___x_1105_, v_size_1107_);
lean_dec(v_size_1107_);
v___x_1136_ = lean_nat_add(v___x_1135_, v_size_1106_);
lean_dec(v___x_1135_);
v___x_1148_ = lean_nat_add(v___x_1105_, v_size_1123_);
if (lean_obj_tag(v_l_1127_) == 0)
{
lean_object* v_size_1158_; 
v_size_1158_ = lean_ctor_get(v_l_1127_, 0);
lean_inc(v_size_1158_);
v___y_1150_ = v_size_1158_;
goto v___jp_1149_;
}
else
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_unsigned_to_nat(0u);
v___y_1150_ = v___x_1159_;
goto v___jp_1149_;
}
v___jp_1137_:
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1141_ = lean_nat_add(v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec(v___y_1139_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 4, v_r_1099_);
lean_ctor_set(v___x_1133_, 3, v_r_1128_);
lean_ctor_set(v___x_1133_, 2, v_v_1097_);
lean_ctor_set(v___x_1133_, 1, v_k_1096_);
lean_ctor_set(v___x_1133_, 0, v___x_1141_);
v___x_1143_ = v___x_1133_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v_r_1128_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v_r_1099_);
v___x_1143_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 4, v___x_1143_);
lean_ctor_set(v___x_1121_, 3, v___y_1138_);
lean_ctor_set(v___x_1121_, 2, v_v_1126_);
lean_ctor_set(v___x_1121_, 1, v_k_1125_);
lean_ctor_set(v___x_1121_, 0, v___x_1136_);
v___x_1145_ = v___x_1121_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_k_1125_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_v_1126_);
lean_ctor_set(v_reuseFailAlloc_1146_, 3, v___y_1138_);
lean_ctor_set(v_reuseFailAlloc_1146_, 4, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
v___jp_1149_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = lean_nat_add(v___x_1148_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec(v___x_1148_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 4, v_l_1127_);
lean_ctor_set(v___x_1101_, 3, v_l_1110_);
lean_ctor_set(v___x_1101_, 2, v_v_1109_);
lean_ctor_set(v___x_1101_, 1, v_k_1108_);
lean_ctor_set(v___x_1101_, 0, v___x_1151_);
v___x_1153_ = v___x_1101_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_k_1108_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_v_1109_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_l_1110_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v_l_1127_);
v___x_1153_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_nat_add(v___x_1105_, v_size_1106_);
if (lean_obj_tag(v_r_1128_) == 0)
{
lean_object* v_size_1155_; 
v_size_1155_ = lean_ctor_get(v_r_1128_, 0);
lean_inc(v_size_1155_);
v___y_1138_ = v___x_1153_;
v___y_1139_ = v___x_1154_;
v___y_1140_ = v_size_1155_;
goto v___jp_1137_;
}
else
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_unsigned_to_nat(0u);
v___y_1138_ = v___x_1153_;
v___y_1139_ = v___x_1154_;
v___y_1140_ = v___x_1156_;
goto v___jp_1137_;
}
}
}
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
lean_del_object(v___x_1101_);
v___x_1166_ = lean_nat_add(v___x_1105_, v_size_1107_);
lean_dec(v_size_1107_);
v___x_1167_ = lean_nat_add(v___x_1166_, v_size_1106_);
lean_dec(v___x_1166_);
v___x_1168_ = lean_nat_add(v___x_1105_, v_size_1106_);
v___x_1169_ = lean_nat_add(v___x_1168_, v_size_1124_);
lean_dec(v___x_1168_);
lean_inc_ref(v_r_1099_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 4, v_r_1099_);
lean_ctor_set(v___x_1121_, 3, v_r_1111_);
lean_ctor_set(v___x_1121_, 2, v_v_1097_);
lean_ctor_set(v___x_1121_, 1, v_k_1096_);
lean_ctor_set(v___x_1121_, 0, v___x_1169_);
v___x_1171_ = v___x_1121_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v_r_1111_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v_r_1099_);
v___x_1171_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v_isSharedCheck_1178_ = !lean_is_exclusive(v_r_1099_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; lean_object* v_unused_1180_; lean_object* v_unused_1181_; lean_object* v_unused_1182_; lean_object* v_unused_1183_; 
v_unused_1179_ = lean_ctor_get(v_r_1099_, 4);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_r_1099_, 3);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_r_1099_, 2);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_r_1099_, 1);
lean_dec(v_unused_1182_);
v_unused_1183_ = lean_ctor_get(v_r_1099_, 0);
lean_dec(v_unused_1183_);
v___x_1173_ = v_r_1099_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_dec(v_r_1099_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 4, v___x_1171_);
lean_ctor_set(v___x_1173_, 3, v_l_1110_);
lean_ctor_set(v___x_1173_, 2, v_v_1109_);
lean_ctor_set(v___x_1173_, 1, v_k_1108_);
lean_ctor_set(v___x_1173_, 0, v___x_1167_);
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_k_1108_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_v_1109_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_l_1110_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v___x_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1191_; 
v_l_1191_ = lean_ctor_get(v_impl_1104_, 3);
lean_inc(v_l_1191_);
if (lean_obj_tag(v_l_1191_) == 0)
{
lean_object* v_r_1192_; lean_object* v_k_1193_; lean_object* v_v_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1205_; 
v_r_1192_ = lean_ctor_get(v_impl_1104_, 4);
v_k_1193_ = lean_ctor_get(v_impl_1104_, 1);
v_v_1194_ = lean_ctor_get(v_impl_1104_, 2);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_impl_1104_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; lean_object* v_unused_1207_; 
v_unused_1206_ = lean_ctor_get(v_impl_1104_, 3);
lean_dec(v_unused_1206_);
v_unused_1207_ = lean_ctor_get(v_impl_1104_, 0);
lean_dec(v_unused_1207_);
v___x_1196_ = v_impl_1104_;
v_isShared_1197_ = v_isSharedCheck_1205_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_r_1192_);
lean_inc(v_v_1194_);
lean_inc(v_k_1193_);
lean_dec(v_impl_1104_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1205_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1192_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 3, v_r_1192_);
lean_ctor_set(v___x_1196_, 2, v_v_1097_);
lean_ctor_set(v___x_1196_, 1, v_k_1096_);
lean_ctor_set(v___x_1196_, 0, v___x_1105_);
v___x_1200_ = v___x_1196_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v_r_1192_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v_r_1192_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 4, v___x_1200_);
lean_ctor_set(v___x_1101_, 3, v_l_1191_);
lean_ctor_set(v___x_1101_, 2, v_v_1194_);
lean_ctor_set(v___x_1101_, 1, v_k_1193_);
lean_ctor_set(v___x_1101_, 0, v___x_1198_);
v___x_1202_ = v___x_1101_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_k_1193_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_v_1194_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_l_1191_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v_r_1208_; 
v_r_1208_ = lean_ctor_get(v_impl_1104_, 4);
lean_inc(v_r_1208_);
if (lean_obj_tag(v_r_1208_) == 0)
{
lean_object* v_k_1209_; lean_object* v_v_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1233_; 
v_k_1209_ = lean_ctor_get(v_impl_1104_, 1);
v_v_1210_ = lean_ctor_get(v_impl_1104_, 2);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_impl_1104_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; lean_object* v_unused_1235_; lean_object* v_unused_1236_; 
v_unused_1234_ = lean_ctor_get(v_impl_1104_, 4);
lean_dec(v_unused_1234_);
v_unused_1235_ = lean_ctor_get(v_impl_1104_, 3);
lean_dec(v_unused_1235_);
v_unused_1236_ = lean_ctor_get(v_impl_1104_, 0);
lean_dec(v_unused_1236_);
v___x_1212_ = v_impl_1104_;
v_isShared_1213_ = v_isSharedCheck_1233_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_v_1210_);
lean_inc(v_k_1209_);
lean_dec(v_impl_1104_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1233_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v_k_1214_; lean_object* v_v_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1229_; 
v_k_1214_ = lean_ctor_get(v_r_1208_, 1);
v_v_1215_ = lean_ctor_get(v_r_1208_, 2);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_r_1208_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; lean_object* v_unused_1231_; lean_object* v_unused_1232_; 
v_unused_1230_ = lean_ctor_get(v_r_1208_, 4);
lean_dec(v_unused_1230_);
v_unused_1231_ = lean_ctor_get(v_r_1208_, 3);
lean_dec(v_unused_1231_);
v_unused_1232_ = lean_ctor_get(v_r_1208_, 0);
lean_dec(v_unused_1232_);
v___x_1217_ = v_r_1208_;
v_isShared_1218_ = v_isSharedCheck_1229_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_v_1215_);
lean_inc(v_k_1214_);
lean_dec(v_r_1208_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1229_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = lean_unsigned_to_nat(3u);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 4, v_l_1191_);
lean_ctor_set(v___x_1217_, 3, v_l_1191_);
lean_ctor_set(v___x_1217_, 2, v_v_1210_);
lean_ctor_set(v___x_1217_, 1, v_k_1209_);
lean_ctor_set(v___x_1217_, 0, v___x_1105_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_k_1209_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_v_1210_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_l_1191_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v_l_1191_);
v___x_1221_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1223_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 4, v_l_1191_);
lean_ctor_set(v___x_1212_, 2, v_v_1097_);
lean_ctor_set(v___x_1212_, 1, v_k_1096_);
lean_ctor_set(v___x_1212_, 0, v___x_1105_);
v___x_1223_ = v___x_1212_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1227_, 3, v_l_1191_);
lean_ctor_set(v_reuseFailAlloc_1227_, 4, v_l_1191_);
v___x_1223_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1225_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 4, v___x_1223_);
lean_ctor_set(v___x_1101_, 3, v___x_1221_);
lean_ctor_set(v___x_1101_, 2, v_v_1215_);
lean_ctor_set(v___x_1101_, 1, v_k_1214_);
lean_ctor_set(v___x_1101_, 0, v___x_1219_);
v___x_1225_ = v___x_1101_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_k_1214_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_v_1215_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1237_ = lean_unsigned_to_nat(2u);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 4, v_r_1208_);
lean_ctor_set(v___x_1101_, 3, v_impl_1104_);
lean_ctor_set(v___x_1101_, 0, v___x_1237_);
v___x_1239_ = v___x_1101_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_impl_1104_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_r_1208_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1242_; 
lean_dec(v_v_1097_);
lean_dec(v_k_1096_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 2, v_v_1093_);
lean_ctor_set(v___x_1101_, 1, v_k_1092_);
v___x_1242_ = v___x_1101_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_size_1095_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_k_1092_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_v_1093_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_l_1098_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_r_1099_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
default: 
{
lean_object* v_impl_1244_; lean_object* v___x_1245_; 
lean_dec(v_size_1095_);
v_impl_1244_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1092_, v_v_1093_, v_r_1099_);
v___x_1245_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1098_) == 0)
{
lean_object* v_size_1246_; lean_object* v_size_1247_; lean_object* v_k_1248_; lean_object* v_v_1249_; lean_object* v_l_1250_; lean_object* v_r_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v_size_1246_ = lean_ctor_get(v_l_1098_, 0);
v_size_1247_ = lean_ctor_get(v_impl_1244_, 0);
lean_inc(v_size_1247_);
v_k_1248_ = lean_ctor_get(v_impl_1244_, 1);
lean_inc(v_k_1248_);
v_v_1249_ = lean_ctor_get(v_impl_1244_, 2);
lean_inc(v_v_1249_);
v_l_1250_ = lean_ctor_get(v_impl_1244_, 3);
lean_inc(v_l_1250_);
v_r_1251_ = lean_ctor_get(v_impl_1244_, 4);
lean_inc(v_r_1251_);
v___x_1252_ = lean_unsigned_to_nat(3u);
v___x_1253_ = lean_nat_mul(v___x_1252_, v_size_1246_);
v___x_1254_ = lean_nat_dec_lt(v___x_1253_, v_size_1247_);
lean_dec(v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
lean_dec(v_r_1251_);
lean_dec(v_l_1250_);
lean_dec(v_v_1249_);
lean_dec(v_k_1248_);
v___x_1255_ = lean_nat_add(v___x_1245_, v_size_1246_);
v___x_1256_ = lean_nat_add(v___x_1255_, v_size_1247_);
lean_dec(v_size_1247_);
lean_dec(v___x_1255_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 4, v_impl_1244_);
lean_ctor_set(v___x_1101_, 0, v___x_1256_);
v___x_1258_ = v___x_1101_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v_l_1098_);
lean_ctor_set(v_reuseFailAlloc_1259_, 4, v_impl_1244_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
else
{
lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1323_; 
v_isSharedCheck_1323_ = !lean_is_exclusive(v_impl_1244_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; lean_object* v_unused_1325_; lean_object* v_unused_1326_; lean_object* v_unused_1327_; lean_object* v_unused_1328_; 
v_unused_1324_ = lean_ctor_get(v_impl_1244_, 4);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v_impl_1244_, 3);
lean_dec(v_unused_1325_);
v_unused_1326_ = lean_ctor_get(v_impl_1244_, 2);
lean_dec(v_unused_1326_);
v_unused_1327_ = lean_ctor_get(v_impl_1244_, 1);
lean_dec(v_unused_1327_);
v_unused_1328_ = lean_ctor_get(v_impl_1244_, 0);
lean_dec(v_unused_1328_);
v___x_1261_ = v_impl_1244_;
v_isShared_1262_ = v_isSharedCheck_1323_;
goto v_resetjp_1260_;
}
else
{
lean_dec(v_impl_1244_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1323_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v_size_1263_; lean_object* v_k_1264_; lean_object* v_v_1265_; lean_object* v_l_1266_; lean_object* v_r_1267_; lean_object* v_size_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v_size_1263_ = lean_ctor_get(v_l_1250_, 0);
v_k_1264_ = lean_ctor_get(v_l_1250_, 1);
v_v_1265_ = lean_ctor_get(v_l_1250_, 2);
v_l_1266_ = lean_ctor_get(v_l_1250_, 3);
v_r_1267_ = lean_ctor_get(v_l_1250_, 4);
v_size_1268_ = lean_ctor_get(v_r_1251_, 0);
v___x_1269_ = lean_unsigned_to_nat(2u);
v___x_1270_ = lean_nat_mul(v___x_1269_, v_size_1268_);
v___x_1271_ = lean_nat_dec_lt(v_size_1263_, v___x_1270_);
lean_dec(v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1299_; 
lean_inc(v_r_1267_);
lean_inc(v_l_1266_);
lean_inc(v_v_1265_);
lean_inc(v_k_1264_);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_l_1250_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; lean_object* v_unused_1301_; lean_object* v_unused_1302_; lean_object* v_unused_1303_; lean_object* v_unused_1304_; 
v_unused_1300_ = lean_ctor_get(v_l_1250_, 4);
lean_dec(v_unused_1300_);
v_unused_1301_ = lean_ctor_get(v_l_1250_, 3);
lean_dec(v_unused_1301_);
v_unused_1302_ = lean_ctor_get(v_l_1250_, 2);
lean_dec(v_unused_1302_);
v_unused_1303_ = lean_ctor_get(v_l_1250_, 1);
lean_dec(v_unused_1303_);
v_unused_1304_ = lean_ctor_get(v_l_1250_, 0);
lean_dec(v_unused_1304_);
v___x_1273_ = v_l_1250_;
v_isShared_1274_ = v_isSharedCheck_1299_;
goto v_resetjp_1272_;
}
else
{
lean_dec(v_l_1250_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1299_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1289_; 
v___x_1275_ = lean_nat_add(v___x_1245_, v_size_1246_);
v___x_1276_ = lean_nat_add(v___x_1275_, v_size_1247_);
lean_dec(v_size_1247_);
if (lean_obj_tag(v_l_1266_) == 0)
{
lean_object* v_size_1297_; 
v_size_1297_ = lean_ctor_get(v_l_1266_, 0);
lean_inc(v_size_1297_);
v___y_1289_ = v_size_1297_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_unsigned_to_nat(0u);
v___y_1289_ = v___x_1298_;
goto v___jp_1288_;
}
v___jp_1277_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_nat_add(v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 4, v_r_1251_);
lean_ctor_set(v___x_1273_, 3, v_r_1267_);
lean_ctor_set(v___x_1273_, 2, v_v_1249_);
lean_ctor_set(v___x_1273_, 1, v_k_1248_);
lean_ctor_set(v___x_1273_, 0, v___x_1281_);
v___x_1283_ = v___x_1273_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_k_1248_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_v_1249_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_r_1267_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_r_1251_);
v___x_1283_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1285_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1283_);
lean_ctor_set(v___x_1261_, 3, v___y_1278_);
lean_ctor_set(v___x_1261_, 2, v_v_1265_);
lean_ctor_set(v___x_1261_, 1, v_k_1264_);
lean_ctor_set(v___x_1261_, 0, v___x_1276_);
v___x_1285_ = v___x_1261_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_k_1264_);
lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_v_1265_);
lean_ctor_set(v_reuseFailAlloc_1286_, 3, v___y_1278_);
lean_ctor_set(v_reuseFailAlloc_1286_, 4, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
v___jp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1290_ = lean_nat_add(v___x_1275_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec(v___x_1275_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 4, v_l_1266_);
lean_ctor_set(v___x_1101_, 0, v___x_1290_);
v___x_1292_ = v___x_1101_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v_l_1098_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v_l_1266_);
v___x_1292_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_nat_add(v___x_1245_, v_size_1268_);
if (lean_obj_tag(v_r_1267_) == 0)
{
lean_object* v_size_1294_; 
v_size_1294_ = lean_ctor_get(v_r_1267_, 0);
lean_inc(v_size_1294_);
v___y_1278_ = v___x_1292_;
v___y_1279_ = v___x_1293_;
v___y_1280_ = v_size_1294_;
goto v___jp_1277_;
}
else
{
lean_object* v___x_1295_; 
v___x_1295_ = lean_unsigned_to_nat(0u);
v___y_1278_ = v___x_1292_;
v___y_1279_ = v___x_1293_;
v___y_1280_ = v___x_1295_;
goto v___jp_1277_;
}
}
}
}
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1309_; 
lean_del_object(v___x_1101_);
v___x_1305_ = lean_nat_add(v___x_1245_, v_size_1246_);
v___x_1306_ = lean_nat_add(v___x_1305_, v_size_1247_);
lean_dec(v_size_1247_);
v___x_1307_ = lean_nat_add(v___x_1305_, v_size_1263_);
lean_dec(v___x_1305_);
lean_inc_ref(v_l_1098_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_l_1250_);
lean_ctor_set(v___x_1261_, 3, v_l_1098_);
lean_ctor_set(v___x_1261_, 2, v_v_1097_);
lean_ctor_set(v___x_1261_, 1, v_k_1096_);
lean_ctor_set(v___x_1261_, 0, v___x_1307_);
v___x_1309_ = v___x_1261_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v_l_1098_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_l_1250_);
v___x_1309_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
v_isSharedCheck_1316_ = !lean_is_exclusive(v_l_1098_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; lean_object* v_unused_1318_; lean_object* v_unused_1319_; lean_object* v_unused_1320_; lean_object* v_unused_1321_; 
v_unused_1317_ = lean_ctor_get(v_l_1098_, 4);
lean_dec(v_unused_1317_);
v_unused_1318_ = lean_ctor_get(v_l_1098_, 3);
lean_dec(v_unused_1318_);
v_unused_1319_ = lean_ctor_get(v_l_1098_, 2);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_l_1098_, 1);
lean_dec(v_unused_1320_);
v_unused_1321_ = lean_ctor_get(v_l_1098_, 0);
lean_dec(v_unused_1321_);
v___x_1311_ = v_l_1098_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_dec(v_l_1098_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 4, v_r_1251_);
lean_ctor_set(v___x_1311_, 3, v___x_1309_);
lean_ctor_set(v___x_1311_, 2, v_v_1249_);
lean_ctor_set(v___x_1311_, 1, v_k_1248_);
lean_ctor_set(v___x_1311_, 0, v___x_1306_);
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_k_1248_);
lean_ctor_set(v_reuseFailAlloc_1315_, 2, v_v_1249_);
lean_ctor_set(v_reuseFailAlloc_1315_, 3, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1315_, 4, v_r_1251_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1329_; 
v_l_1329_ = lean_ctor_get(v_impl_1244_, 3);
lean_inc(v_l_1329_);
if (lean_obj_tag(v_l_1329_) == 0)
{
lean_object* v_r_1330_; lean_object* v_k_1331_; lean_object* v_v_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1355_; 
v_r_1330_ = lean_ctor_get(v_impl_1244_, 4);
v_k_1331_ = lean_ctor_get(v_impl_1244_, 1);
v_v_1332_ = lean_ctor_get(v_impl_1244_, 2);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_impl_1244_);
if (v_isSharedCheck_1355_ == 0)
{
lean_object* v_unused_1356_; lean_object* v_unused_1357_; 
v_unused_1356_ = lean_ctor_get(v_impl_1244_, 3);
lean_dec(v_unused_1356_);
v_unused_1357_ = lean_ctor_get(v_impl_1244_, 0);
lean_dec(v_unused_1357_);
v___x_1334_ = v_impl_1244_;
v_isShared_1335_ = v_isSharedCheck_1355_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_r_1330_);
lean_inc(v_v_1332_);
lean_inc(v_k_1331_);
lean_dec(v_impl_1244_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1355_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v_k_1336_; lean_object* v_v_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1351_; 
v_k_1336_ = lean_ctor_get(v_l_1329_, 1);
v_v_1337_ = lean_ctor_get(v_l_1329_, 2);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_l_1329_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; lean_object* v_unused_1353_; lean_object* v_unused_1354_; 
v_unused_1352_ = lean_ctor_get(v_l_1329_, 4);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_l_1329_, 3);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_l_1329_, 0);
lean_dec(v_unused_1354_);
v___x_1339_ = v_l_1329_;
v_isShared_1340_ = v_isSharedCheck_1351_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_v_1337_);
lean_inc(v_k_1336_);
lean_dec(v_l_1329_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1351_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1341_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1330_, 2);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 4, v_r_1330_);
lean_ctor_set(v___x_1339_, 3, v_r_1330_);
lean_ctor_set(v___x_1339_, 2, v_v_1097_);
lean_ctor_set(v___x_1339_, 1, v_k_1096_);
lean_ctor_set(v___x_1339_, 0, v___x_1245_);
v___x_1343_ = v___x_1339_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_r_1330_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v_r_1330_);
v___x_1343_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1345_; 
lean_inc(v_r_1330_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 3, v_r_1330_);
lean_ctor_set(v___x_1334_, 0, v___x_1245_);
v___x_1345_ = v___x_1334_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_k_1331_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_v_1332_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_r_1330_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v_r_1330_);
v___x_1345_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1347_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 4, v___x_1345_);
lean_ctor_set(v___x_1101_, 3, v___x_1343_);
lean_ctor_set(v___x_1101_, 2, v_v_1337_);
lean_ctor_set(v___x_1101_, 1, v_k_1336_);
lean_ctor_set(v___x_1101_, 0, v___x_1341_);
v___x_1347_ = v___x_1101_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_k_1336_);
lean_ctor_set(v_reuseFailAlloc_1348_, 2, v_v_1337_);
lean_ctor_set(v_reuseFailAlloc_1348_, 3, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1348_, 4, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
}
else
{
lean_object* v_r_1358_; 
v_r_1358_ = lean_ctor_get(v_impl_1244_, 4);
lean_inc(v_r_1358_);
if (lean_obj_tag(v_r_1358_) == 0)
{
lean_object* v_k_1359_; lean_object* v_v_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1371_; 
v_k_1359_ = lean_ctor_get(v_impl_1244_, 1);
v_v_1360_ = lean_ctor_get(v_impl_1244_, 2);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_impl_1244_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; lean_object* v_unused_1373_; lean_object* v_unused_1374_; 
v_unused_1372_ = lean_ctor_get(v_impl_1244_, 4);
lean_dec(v_unused_1372_);
v_unused_1373_ = lean_ctor_get(v_impl_1244_, 3);
lean_dec(v_unused_1373_);
v_unused_1374_ = lean_ctor_get(v_impl_1244_, 0);
lean_dec(v_unused_1374_);
v___x_1362_ = v_impl_1244_;
v_isShared_1363_ = v_isSharedCheck_1371_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_v_1360_);
lean_inc(v_k_1359_);
lean_dec(v_impl_1244_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1371_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = lean_unsigned_to_nat(3u);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v_l_1329_);
lean_ctor_set(v___x_1362_, 2, v_v_1097_);
lean_ctor_set(v___x_1362_, 1, v_k_1096_);
lean_ctor_set(v___x_1362_, 0, v___x_1245_);
v___x_1366_ = v___x_1362_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1370_, 3, v_l_1329_);
lean_ctor_set(v_reuseFailAlloc_1370_, 4, v_l_1329_);
v___x_1366_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1368_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 4, v_r_1358_);
lean_ctor_set(v___x_1101_, 3, v___x_1366_);
lean_ctor_set(v___x_1101_, 2, v_v_1360_);
lean_ctor_set(v___x_1101_, 1, v_k_1359_);
lean_ctor_set(v___x_1101_, 0, v___x_1364_);
v___x_1368_ = v___x_1101_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_k_1359_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_v_1360_);
lean_ctor_set(v_reuseFailAlloc_1369_, 3, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1369_, 4, v_r_1358_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1375_ = lean_unsigned_to_nat(2u);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 4, v_impl_1244_);
lean_ctor_set(v___x_1101_, 3, v_r_1358_);
lean_ctor_set(v___x_1101_, 0, v___x_1375_);
v___x_1377_ = v___x_1101_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1378_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1378_, 3, v_r_1358_);
lean_ctor_set(v_reuseFailAlloc_1378_, 4, v_impl_1244_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
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
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_unsigned_to_nat(1u);
v___x_1381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
lean_ctor_set(v___x_1381_, 1, v_k_1092_);
lean_ctor_set(v___x_1381_, 2, v_v_1093_);
lean_ctor_set(v___x_1381_, 3, v_t_1094_);
lean_ctor_set(v___x_1381_, 4, v_t_1094_);
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object* v_s_1382_, lean_object* v_mvarId_1383_){
_start:
{
uint8_t v___x_1384_; 
v___x_1384_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_mvarId_1383_, v_s_1382_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_box(0);
v___x_1386_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1383_, v___x_1385_, v_s_1382_);
return v___x_1386_;
}
else
{
lean_dec(v_mvarId_1383_);
return v_s_1382_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object* v_00_u03b2_1387_, lean_object* v_k_1388_, lean_object* v_t_1389_){
_start:
{
uint8_t v___x_1390_; 
v___x_1390_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1388_, v_t_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object* v_00_u03b2_1391_, lean_object* v_k_1392_, lean_object* v_t_1393_){
_start:
{
uint8_t v_res_1394_; lean_object* v_r_1395_; 
v_res_1394_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(v_00_u03b2_1391_, v_k_1392_, v_t_1393_);
lean_dec(v_t_1393_);
lean_dec(v_k_1392_);
v_r_1395_ = lean_box(v_res_1394_);
return v_r_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object* v_00_u03b2_1396_, lean_object* v_k_1397_, lean_object* v_v_1398_, lean_object* v_t_1399_, lean_object* v_hl_1400_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1397_, v_v_1398_, v_t_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object* v_l_1402_){
_start:
{
lean_object* v___f_1403_; lean_object* v___x_1404_; 
v___f_1403_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1404_ = l_Std_TreeSet_ofList___redArg(v_l_1402_, v___f_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object* v_l_1405_){
_start:
{
lean_object* v___f_1406_; lean_object* v___x_1407_; 
v___f_1406_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1407_ = l_Std_TreeSet_ofArray___redArg(v_l_1405_, v___f_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object* v_l_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_MVarIdSet_ofArray(v_l_1408_);
lean_dec_ref(v_l_1408_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1410_, lean_object* v_m_1411_, lean_object* v_init_1412_, lean_object* v_f_1413_){
_start:
{
lean_object* v_toApplicative_1414_; lean_object* v_toBind_1415_; lean_object* v_toPure_1416_; lean_object* v___f_1417_; lean_object* v___x_1418_; lean_object* v___f_1419_; lean_object* v___x_1420_; 
v_toApplicative_1414_ = lean_ctor_get(v_inst_1410_, 0);
v_toBind_1415_ = lean_ctor_get(v_inst_1410_, 1);
lean_inc(v_toBind_1415_);
v_toPure_1416_ = lean_ctor_get(v_toApplicative_1414_, 1);
lean_inc(v_toPure_1416_);
v___f_1417_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1417_, 0, v_f_1413_);
v___x_1418_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1410_, v___f_1417_, v_init_1412_, v_m_1411_);
v___f_1419_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1419_, 0, v_toPure_1416_);
v___x_1420_ = lean_apply_4(v_toBind_1415_, lean_box(0), lean_box(0), v___x_1418_, v___f_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1(lean_object* v_m_1421_, lean_object* v_inst_1422_, lean_object* v_00_u03b2_1423_, lean_object* v_m_1424_, lean_object* v_init_1425_, lean_object* v_f_1426_){
_start:
{
lean_object* v_toApplicative_1427_; lean_object* v_toBind_1428_; lean_object* v_toPure_1429_; lean_object* v___f_1430_; lean_object* v___x_1431_; lean_object* v___f_1432_; lean_object* v___x_1433_; 
v_toApplicative_1427_ = lean_ctor_get(v_inst_1422_, 0);
v_toBind_1428_ = lean_ctor_get(v_inst_1422_, 1);
lean_inc(v_toBind_1428_);
v_toPure_1429_ = lean_ctor_get(v_toApplicative_1427_, 1);
lean_inc(v_toPure_1429_);
v___f_1430_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1430_, 0, v_f_1426_);
v___x_1431_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1422_, v___f_1430_, v_init_1425_, v_m_1424_);
v___f_1432_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1432_, 0, v_toPure_1429_);
v___x_1433_ = lean_apply_4(v_toBind_1428_, lean_box(0), lean_box(0), v___x_1431_, v___f_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object* v_inst_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1435_, 0, lean_box(0));
lean_closure_set(v___x_1435_, 1, v_inst_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object* v_m_1436_, lean_object* v_inst_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1438_, 0, lean_box(0));
lean_closure_set(v___x_1438_, 1, v_inst_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object* v_s_1439_, lean_object* v_mvarId_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1440_, v_a_1441_, v_s_1439_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object* v_00_u03b1_1443_, lean_object* v_s_1444_, lean_object* v_mvarId_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1445_, v_a_1446_, v_s_1444_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object* v_00_u03b1_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_box(1);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* v_00_u03b1_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_box(1);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_1452_, lean_object* v_a_1453_, lean_object* v_b_1454_, lean_object* v_c_1455_){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v_a_1453_);
lean_ctor_set(v___x_1456_, 1, v_b_1454_);
v___x_1457_ = lean_apply_2(v_f_1452_, v___x_1456_, v_c_1455_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1458_, lean_object* v_m_1459_, lean_object* v_init_1460_, lean_object* v_f_1461_){
_start:
{
lean_object* v_toApplicative_1462_; lean_object* v_toBind_1463_; lean_object* v_toPure_1464_; lean_object* v___f_1465_; lean_object* v___x_1466_; lean_object* v___f_1467_; lean_object* v___x_1468_; 
v_toApplicative_1462_ = lean_ctor_get(v_inst_1458_, 0);
v_toBind_1463_ = lean_ctor_get(v_inst_1458_, 1);
lean_inc(v_toBind_1463_);
v_toPure_1464_ = lean_ctor_get(v_toApplicative_1462_, 1);
lean_inc(v_toPure_1464_);
v___f_1465_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1465_, 0, v_f_1461_);
v___x_1466_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1458_, v___f_1465_, v_init_1460_, v_m_1459_);
v___f_1467_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1467_, 0, v_toPure_1464_);
v___x_1468_ = lean_apply_4(v_toBind_1463_, lean_box(0), lean_box(0), v___x_1466_, v___f_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object* v_m_1469_, lean_object* v_00_u03b1_1470_, lean_object* v_inst_1471_, lean_object* v_00_u03b2_1472_, lean_object* v_m_1473_, lean_object* v_init_1474_, lean_object* v_f_1475_){
_start:
{
lean_object* v_toApplicative_1476_; lean_object* v_toBind_1477_; lean_object* v_toPure_1478_; lean_object* v___f_1479_; lean_object* v___x_1480_; lean_object* v___f_1481_; lean_object* v___x_1482_; 
v_toApplicative_1476_ = lean_ctor_get(v_inst_1471_, 0);
v_toBind_1477_ = lean_ctor_get(v_inst_1471_, 1);
lean_inc(v_toBind_1477_);
v_toPure_1478_ = lean_ctor_get(v_toApplicative_1476_, 1);
lean_inc(v_toPure_1478_);
v___f_1479_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1479_, 0, v_f_1475_);
v___x_1480_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1471_, v___f_1479_, v_init_1474_, v_m_1473_);
v___f_1481_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1481_, 0, v_toPure_1478_);
v___x_1482_ = lean_apply_4(v_toBind_1477_, lean_box(0), lean_box(0), v___x_1480_, v___f_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object* v_inst_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1484_, 0, lean_box(0));
lean_closure_set(v___x_1484_, 1, lean_box(0));
lean_closure_set(v___x_1484_, 2, v_inst_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object* v_m_1485_, lean_object* v_00_u03b1_1486_, lean_object* v_inst_1487_){
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* v_00_u03b1_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_box(1);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx(lean_object* v_x_1491_){
_start:
{
switch(lean_obj_tag(v_x_1491_))
{
case 0:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_unsigned_to_nat(0u);
return v___x_1492_;
}
case 1:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_unsigned_to_nat(1u);
return v___x_1493_;
}
case 2:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_unsigned_to_nat(2u);
return v___x_1494_;
}
case 3:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_unsigned_to_nat(3u);
return v___x_1495_;
}
case 4:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_unsigned_to_nat(4u);
return v___x_1496_;
}
case 5:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_unsigned_to_nat(5u);
return v___x_1497_;
}
case 6:
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_unsigned_to_nat(6u);
return v___x_1498_;
}
case 7:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_unsigned_to_nat(7u);
return v___x_1499_;
}
case 8:
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_unsigned_to_nat(8u);
return v___x_1500_;
}
case 9:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_unsigned_to_nat(9u);
return v___x_1501_;
}
case 10:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_unsigned_to_nat(10u);
return v___x_1502_;
}
default: 
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_unsigned_to_nat(11u);
return v___x_1503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___boxed(lean_object* v_x_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Expr_ctorIdx(v_x_1504_);
lean_dec_ref(v_x_1504_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object* v_t_1506_, lean_object* v_k_1507_){
_start:
{
switch(lean_obj_tag(v_t_1506_))
{
case 4:
{
lean_object* v_declName_1508_; lean_object* v_us_1509_; lean_object* v___x_1510_; 
v_declName_1508_ = lean_ctor_get(v_t_1506_, 0);
lean_inc(v_declName_1508_);
v_us_1509_ = lean_ctor_get(v_t_1506_, 1);
lean_inc(v_us_1509_);
lean_dec_ref(v_t_1506_);
v___x_1510_ = lean_apply_2(v_k_1507_, v_declName_1508_, v_us_1509_);
return v___x_1510_;
}
case 5:
{
lean_object* v_fn_1511_; lean_object* v_arg_1512_; lean_object* v___x_1513_; 
v_fn_1511_ = lean_ctor_get(v_t_1506_, 0);
lean_inc_ref(v_fn_1511_);
v_arg_1512_ = lean_ctor_get(v_t_1506_, 1);
lean_inc_ref(v_arg_1512_);
lean_dec_ref(v_t_1506_);
v___x_1513_ = lean_apply_2(v_k_1507_, v_fn_1511_, v_arg_1512_);
return v___x_1513_;
}
case 6:
{
lean_object* v_binderName_1514_; lean_object* v_binderType_1515_; lean_object* v_body_1516_; uint8_t v_binderInfo_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_binderName_1514_ = lean_ctor_get(v_t_1506_, 0);
lean_inc(v_binderName_1514_);
v_binderType_1515_ = lean_ctor_get(v_t_1506_, 1);
lean_inc_ref(v_binderType_1515_);
v_body_1516_ = lean_ctor_get(v_t_1506_, 2);
lean_inc_ref(v_body_1516_);
v_binderInfo_1517_ = lean_ctor_get_uint8(v_t_1506_, sizeof(void*)*3);
lean_dec_ref(v_t_1506_);
v___x_1518_ = lean_box(v_binderInfo_1517_);
v___x_1519_ = lean_apply_4(v_k_1507_, v_binderName_1514_, v_binderType_1515_, v_body_1516_, v___x_1518_);
return v___x_1519_;
}
case 7:
{
lean_object* v_binderName_1520_; lean_object* v_binderType_1521_; lean_object* v_body_1522_; uint8_t v_binderInfo_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_binderName_1520_ = lean_ctor_get(v_t_1506_, 0);
lean_inc(v_binderName_1520_);
v_binderType_1521_ = lean_ctor_get(v_t_1506_, 1);
lean_inc_ref(v_binderType_1521_);
v_body_1522_ = lean_ctor_get(v_t_1506_, 2);
lean_inc_ref(v_body_1522_);
v_binderInfo_1523_ = lean_ctor_get_uint8(v_t_1506_, sizeof(void*)*3);
lean_dec_ref(v_t_1506_);
v___x_1524_ = lean_box(v_binderInfo_1523_);
v___x_1525_ = lean_apply_4(v_k_1507_, v_binderName_1520_, v_binderType_1521_, v_body_1522_, v___x_1524_);
return v___x_1525_;
}
case 8:
{
lean_object* v_declName_1526_; lean_object* v_type_1527_; lean_object* v_value_1528_; lean_object* v_body_1529_; uint8_t v_nondep_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v_declName_1526_ = lean_ctor_get(v_t_1506_, 0);
lean_inc(v_declName_1526_);
v_type_1527_ = lean_ctor_get(v_t_1506_, 1);
lean_inc_ref(v_type_1527_);
v_value_1528_ = lean_ctor_get(v_t_1506_, 2);
lean_inc_ref(v_value_1528_);
v_body_1529_ = lean_ctor_get(v_t_1506_, 3);
lean_inc_ref(v_body_1529_);
v_nondep_1530_ = lean_ctor_get_uint8(v_t_1506_, sizeof(void*)*4);
lean_dec_ref(v_t_1506_);
v___x_1531_ = lean_box(v_nondep_1530_);
v___x_1532_ = lean_apply_5(v_k_1507_, v_declName_1526_, v_type_1527_, v_value_1528_, v_body_1529_, v___x_1531_);
return v___x_1532_;
}
case 9:
{
lean_object* v_a_1533_; lean_object* v___x_1534_; 
v_a_1533_ = lean_ctor_get(v_t_1506_, 0);
lean_inc_ref(v_a_1533_);
lean_dec_ref(v_t_1506_);
v___x_1534_ = lean_apply_1(v_k_1507_, v_a_1533_);
return v___x_1534_;
}
case 10:
{
lean_object* v_data_1535_; lean_object* v_expr_1536_; lean_object* v___x_1537_; 
v_data_1535_ = lean_ctor_get(v_t_1506_, 0);
lean_inc(v_data_1535_);
v_expr_1536_ = lean_ctor_get(v_t_1506_, 1);
lean_inc_ref(v_expr_1536_);
lean_dec_ref(v_t_1506_);
v___x_1537_ = lean_apply_2(v_k_1507_, v_data_1535_, v_expr_1536_);
return v___x_1537_;
}
case 11:
{
lean_object* v_typeName_1538_; lean_object* v_idx_1539_; lean_object* v_struct_1540_; lean_object* v___x_1541_; 
v_typeName_1538_ = lean_ctor_get(v_t_1506_, 0);
lean_inc(v_typeName_1538_);
v_idx_1539_ = lean_ctor_get(v_t_1506_, 1);
lean_inc(v_idx_1539_);
v_struct_1540_ = lean_ctor_get(v_t_1506_, 2);
lean_inc_ref(v_struct_1540_);
lean_dec_ref(v_t_1506_);
v___x_1541_ = lean_apply_3(v_k_1507_, v_typeName_1538_, v_idx_1539_, v_struct_1540_);
return v___x_1541_;
}
default: 
{
lean_object* v_deBruijnIndex_1542_; lean_object* v___x_1543_; 
v_deBruijnIndex_1542_ = lean_ctor_get(v_t_1506_, 0);
lean_inc(v_deBruijnIndex_1542_);
lean_dec_ref(v_t_1506_);
v___x_1543_ = lean_apply_1(v_k_1507_, v_deBruijnIndex_1542_);
return v___x_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object* v_motive_1544_, lean_object* v_ctorIdx_1545_, lean_object* v_t_1546_, lean_object* v_h_1547_, lean_object* v_k_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_Expr_ctorElim___redArg(v_t_1546_, v_k_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object* v_motive_1550_, lean_object* v_ctorIdx_1551_, lean_object* v_t_1552_, lean_object* v_h_1553_, lean_object* v_k_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Expr_ctorElim(v_motive_1550_, v_ctorIdx_1551_, v_t_1552_, v_h_1553_, v_k_1554_);
lean_dec(v_ctorIdx_1551_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object* v_t_1556_, lean_object* v_bvar_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_Expr_ctorElim___redArg(v_t_1556_, v_bvar_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object* v_motive_1559_, lean_object* v_t_1560_, lean_object* v_h_1561_, lean_object* v_bvar_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_Expr_ctorElim___redArg(v_t_1560_, v_bvar_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object* v_t_1564_, lean_object* v_fvar_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_Expr_ctorElim___redArg(v_t_1564_, v_fvar_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object* v_motive_1567_, lean_object* v_t_1568_, lean_object* v_h_1569_, lean_object* v_fvar_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_Expr_ctorElim___redArg(v_t_1568_, v_fvar_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object* v_t_1572_, lean_object* v_mvar_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_Expr_ctorElim___redArg(v_t_1572_, v_mvar_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object* v_motive_1575_, lean_object* v_t_1576_, lean_object* v_h_1577_, lean_object* v_mvar_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Expr_ctorElim___redArg(v_t_1576_, v_mvar_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object* v_t_1580_, lean_object* v_sort_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_Expr_ctorElim___redArg(v_t_1580_, v_sort_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object* v_motive_1583_, lean_object* v_t_1584_, lean_object* v_h_1585_, lean_object* v_sort_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Expr_ctorElim___redArg(v_t_1584_, v_sort_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object* v_t_1588_, lean_object* v_const_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Expr_ctorElim___redArg(v_t_1588_, v_const_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object* v_motive_1591_, lean_object* v_t_1592_, lean_object* v_h_1593_, lean_object* v_const_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_Expr_ctorElim___redArg(v_t_1592_, v_const_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object* v_t_1596_, lean_object* v_app_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_Expr_ctorElim___redArg(v_t_1596_, v_app_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object* v_motive_1599_, lean_object* v_t_1600_, lean_object* v_h_1601_, lean_object* v_app_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Expr_ctorElim___redArg(v_t_1600_, v_app_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object* v_t_1604_, lean_object* v_lam_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Expr_ctorElim___redArg(v_t_1604_, v_lam_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object* v_motive_1607_, lean_object* v_t_1608_, lean_object* v_h_1609_, lean_object* v_lam_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Expr_ctorElim___redArg(v_t_1608_, v_lam_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object* v_t_1612_, lean_object* v_forallE_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Expr_ctorElim___redArg(v_t_1612_, v_forallE_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object* v_motive_1615_, lean_object* v_t_1616_, lean_object* v_h_1617_, lean_object* v_forallE_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Expr_ctorElim___redArg(v_t_1616_, v_forallE_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object* v_t_1620_, lean_object* v_letE_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Expr_ctorElim___redArg(v_t_1620_, v_letE_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object* v_motive_1623_, lean_object* v_t_1624_, lean_object* v_h_1625_, lean_object* v_letE_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Expr_ctorElim___redArg(v_t_1624_, v_letE_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object* v_t_1628_, lean_object* v_lit_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Expr_ctorElim___redArg(v_t_1628_, v_lit_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object* v_motive_1631_, lean_object* v_t_1632_, lean_object* v_h_1633_, lean_object* v_lit_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Expr_ctorElim___redArg(v_t_1632_, v_lit_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object* v_t_1636_, lean_object* v_mdata_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Expr_ctorElim___redArg(v_t_1636_, v_mdata_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object* v_motive_1639_, lean_object* v_t_1640_, lean_object* v_h_1641_, lean_object* v_mdata_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Expr_ctorElim___redArg(v_t_1640_, v_mdata_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object* v_t_1644_, lean_object* v_proj_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Expr_ctorElim___redArg(v_t_1644_, v_proj_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object* v_motive_1647_, lean_object* v_t_1648_, lean_object* v_h_1649_, lean_object* v_proj_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_Expr_ctorElim___redArg(v_t_1648_, v_proj_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* v_a_00___x40___internal___hyg_1653_){
_start:
{
uint64_t v_res_1654_; lean_object* v_r_1655_; 
v_res_1654_ = lean_expr_data(v_a_00___x40___internal___hyg_1653_);
lean_dec_ref(v_a_00___x40___internal___hyg_1653_);
v_r_1655_ = lean_box_uint64(v_res_1654_);
return v_r_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object* v_t_1656_, lean_object* v_bvar_1657_, lean_object* v_fvar_1658_, lean_object* v_mvar_1659_, lean_object* v_sort_1660_, lean_object* v_const_1661_, lean_object* v_app_1662_, lean_object* v_lam_1663_, lean_object* v_forallE_1664_, lean_object* v_letE_1665_, lean_object* v_lit_1666_, lean_object* v_mdata_1667_, lean_object* v_proj_1668_){
_start:
{
switch(lean_obj_tag(v_t_1656_))
{
case 0:
{
lean_object* v_deBruijnIndex_1669_; lean_object* v___x_1670_; 
lean_dec(v_proj_1668_);
lean_dec(v_mdata_1667_);
lean_dec(v_lit_1666_);
lean_dec(v_letE_1665_);
lean_dec(v_forallE_1664_);
lean_dec(v_lam_1663_);
lean_dec(v_app_1662_);
lean_dec(v_const_1661_);
lean_dec(v_sort_1660_);
lean_dec(v_mvar_1659_);
lean_dec(v_fvar_1658_);
v_deBruijnIndex_1669_ = lean_ctor_get(v_t_1656_, 0);
lean_inc(v_deBruijnIndex_1669_);
lean_dec_ref(v_t_1656_);
v___x_1670_ = lean_apply_1(v_bvar_1657_, v_deBruijnIndex_1669_);
return v___x_1670_;
}
case 1:
{
lean_object* v_fvarId_1671_; lean_object* v___x_1672_; 
lean_dec(v_proj_1668_);
lean_dec(v_mdata_1667_);
lean_dec(v_lit_1666_);
lean_dec(v_letE_1665_);
lean_dec(v_forallE_1664_);
lean_dec(v_lam_1663_);
lean_dec(v_app_1662_);
lean_dec(v_const_1661_);
lean_dec(v_sort_1660_);
lean_dec(v_mvar_1659_);
lean_dec(v_bvar_1657_);
v_fvarId_1671_ = lean_ctor_get(v_t_1656_, 0);
lean_inc(v_fvarId_1671_);
lean_dec_ref(v_t_1656_);
v___x_1672_ = lean_apply_1(v_fvar_1658_, v_fvarId_1671_);
return v___x_1672_;
}
case 2:
{
lean_object* v_mvarId_1673_; lean_object* v___x_1674_; 
lean_dec(v_proj_1668_);
lean_dec(v_mdata_1667_);
lean_dec(v_lit_1666_);
lean_dec(v_letE_1665_);
lean_dec(v_forallE_1664_);
lean_dec(v_lam_1663_);
lean_dec(v_app_1662_);
lean_dec(v_const_1661_);
lean_dec(v_sort_1660_);
lean_dec(v_fvar_1658_);
lean_dec(v_bvar_1657_);
v_mvarId_1673_ = lean_ctor_get(v_t_1656_, 0);
lean_inc(v_mvarId_1673_);
lean_dec_ref(v_t_1656_);
v___x_1674_ = lean_apply_1(v_mvar_1659_, v_mvarId_1673_);
return v___x_1674_;
}
case 3:
{
lean_object* v_u_1675_; lean_object* v___x_1676_; 
lean_dec(v_proj_1668_);
lean_dec(v_mdata_1667_);
lean_dec(v_lit_1666_);
lean_dec(v_letE_1665_);
lean_dec(v_forallE_1664_);
lean_dec(v_lam_1663_);
lean_dec(v_app_1662_);
lean_dec(v_const_1661_);
lean_dec(v_mvar_1659_);
lean_dec(v_fvar_1658_);
lean_dec(v_bvar_1657_);
v_u_1675_ = lean_ctor_get(v_t_1656_, 0);
lean_inc(v_u_1675_);
lean_dec_ref(v_t_1656_);
v___x_1676_ = lean_apply_1(v_sort_1660_, v_u_1675_);
return v___x_1676_;
}
case 4:
{
lean_object* v_declName_1677_; lean_object* v_us_1678_; lean_object* v___x_1679_; 
lean_dec(v_proj_1668_);
lean_dec(v_mdata_1667_);
lean_dec(v_lit_1666_);
lean_dec(v_letE_1665_);
lean_dec(v_forallE_1664_);
lean_dec(v_lam_1663_);
lean_dec(v_app_1662_);
lean_dec(v_sort_1660_);
lean_dec(v_mvar_1659_);
lean_dec(v_fvar_1658_);
lean_dec(v_bvar_1657_);
v_declName_1677_ = lean_ctor_get(v_t_1656_, 0);
lean_inc(v_declName_1677_);
v_us_1678_ = lean_ctor_get(v_t_1656_, 1);
lean_inc(v_us_1678_);
lean_dec_ref(v_t_1656_);
v___x_1679_ = lean_apply_2(v_const_1661_, v_declName_1677_, v_us_1678_);
return v___x_1679_;
}
case 5:
{
lean_object* v_fn_1680_; lean_object* v_arg_1681_; lean_object* v___x_1682_; 
lean_dec(v_proj_1668_);
lean_dec(v_mdata_1667_);
lean_dec(v_lit_1666_);
lean_dec(v_letE_1665_);
lean_dec(v_forallE_1664_);
lean_dec(v_lam_1663_);
lean_dec(v_const_1661_);
lean_dec(v_sort_1660_);
lean_dec(v_mvar_1659_);
lean_dec(v_fvar_1658_);
lean_dec(v_bvar_1657_);
v_fn_1680_ = lean_ctor_get(v_t_1656_, 0);
lean_inc_ref(v_fn_1680_);
v_arg_1681_ = lean_ctor_get(v_t_1656_, 1);
lean_inc_ref(v_arg_1681_);
lean_dec_ref(v_t_1656_);
v___x_1682_ = lean_apply_2(v_app_1662_, v_fn_1680_, v_arg_1681_);
return v___x_1682_;
}
case 6:
{
lean_object* v_binderName_1683_; lean_object* v_binderType_1684_; lean_object* v_body_1685_; uint8_t v_binderInfo_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec(v_proj_1668_);
lean_dec(v_mdata_1667_);
lean_dec(v_lit_1666_);
lean_dec(v_letE_1665_);
lean_dec(v_forallE_1664_);
lean_dec(v_app_1662_);
lean_dec(v_const_1661_);
lean_dec(v_sort_1660_);
lean_dec(v_mvar_1659_);
lean_dec(v_fvar_1658_);
lean_dec(v_bvar_1657_);
v_binderName_1683_ = lean_ctor_get(v_t_1656_, 0);
lean_inc(v_binderName_1683_);
v_binderType_1684_ = lean_ctor_get(v_t_1656_, 1);
lean_inc_ref(v_binderType_1684_);
v_body_1685_ = lean_ctor_get(v_t_1656_, 2);
lean_inc_ref(v_body_1685_);
v_binderInfo_1686_ = lean_ctor_get_uint8(v_t_1656_, sizeof(void*)*3 + 8);
lean_dec_ref(v_t_1656_);
v___x_1687_ = lean_box(v_binderInfo_1686_);
v___x_1688_ = lean_apply_4(v_lam_1663_, v_binderName_1683_, v_binderType_1684_, v_body_1685_, v___x_1687_);
return v___x_1688_;
}
case 7:
{
lean_object* v_binderName_1689_; lean_object* v_binderType_1690_; lean_object* v_body_1691_; uint8_t v_binderInfo_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_dec(v_proj_1668_);
lean_dec(v_mdata_1667_);
lean_dec(v_lit_1666_);
lean_dec(v_letE_1665_);
lean_dec(v_lam_1663_);
lean_dec(v_app_1662_);
lean_dec(v_const_1661_);
lean_dec(v_sort_1660_);
lean_dec(v_mvar_1659_);
lean_dec(v_fvar_1658_);
lean_dec(v_bvar_1657_);
v_binderName_1689_ = lean_ctor_get(v_t_1656_, 0);
lean_inc(v_binderName_1689_);
v_binderType_1690_ = lean_ctor_get(v_t_1656_, 1);
lean_inc_ref(v_binderType_1690_);
v_body_1691_ = lean_ctor_get(v_t_1656_, 2);
lean_inc_ref(v_body_1691_);
v_binderInfo_1692_ = lean_ctor_get_uint8(v_t_1656_, sizeof(void*)*3 + 8);
lean_dec_ref(v_t_1656_);
v___x_1693_ = lean_box(v_binderInfo_1692_);
v___x_1694_ = lean_apply_4(v_forallE_1664_, v_binderName_1689_, v_binderType_1690_, v_body_1691_, v___x_1693_);
return v___x_1694_;
}
case 8:
{
lean_object* v_declName_1695_; lean_object* v_type_1696_; lean_object* v_value_1697_; lean_object* v_body_1698_; uint8_t v_nondep_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
lean_dec(v_proj_1668_);
lean_dec(v_mdata_1667_);
lean_dec(v_lit_1666_);
lean_dec(v_forallE_1664_);
lean_dec(v_lam_1663_);
lean_dec(v_app_1662_);
lean_dec(v_const_1661_);
lean_dec(v_sort_1660_);
lean_dec(v_mvar_1659_);
lean_dec(v_fvar_1658_);
lean_dec(v_bvar_1657_);
v_declName_1695_ = lean_ctor_get(v_t_1656_, 0);
lean_inc(v_declName_1695_);
v_type_1696_ = lean_ctor_get(v_t_1656_, 1);
lean_inc_ref(v_type_1696_);
v_value_1697_ = lean_ctor_get(v_t_1656_, 2);
lean_inc_ref(v_value_1697_);
v_body_1698_ = lean_ctor_get(v_t_1656_, 3);
lean_inc_ref(v_body_1698_);
v_nondep_1699_ = lean_ctor_get_uint8(v_t_1656_, sizeof(void*)*4 + 8);
lean_dec_ref(v_t_1656_);
v___x_1700_ = lean_box(v_nondep_1699_);
v___x_1701_ = lean_apply_5(v_letE_1665_, v_declName_1695_, v_type_1696_, v_value_1697_, v_body_1698_, v___x_1700_);
return v___x_1701_;
}
case 9:
{
lean_object* v_a_1702_; lean_object* v___x_1703_; 
lean_dec(v_proj_1668_);
lean_dec(v_mdata_1667_);
lean_dec(v_letE_1665_);
lean_dec(v_forallE_1664_);
lean_dec(v_lam_1663_);
lean_dec(v_app_1662_);
lean_dec(v_const_1661_);
lean_dec(v_sort_1660_);
lean_dec(v_mvar_1659_);
lean_dec(v_fvar_1658_);
lean_dec(v_bvar_1657_);
v_a_1702_ = lean_ctor_get(v_t_1656_, 0);
lean_inc_ref(v_a_1702_);
lean_dec_ref(v_t_1656_);
v___x_1703_ = lean_apply_1(v_lit_1666_, v_a_1702_);
return v___x_1703_;
}
case 10:
{
lean_object* v_data_1704_; lean_object* v_expr_1705_; lean_object* v___x_1706_; 
lean_dec(v_proj_1668_);
lean_dec(v_lit_1666_);
lean_dec(v_letE_1665_);
lean_dec(v_forallE_1664_);
lean_dec(v_lam_1663_);
lean_dec(v_app_1662_);
lean_dec(v_const_1661_);
lean_dec(v_sort_1660_);
lean_dec(v_mvar_1659_);
lean_dec(v_fvar_1658_);
lean_dec(v_bvar_1657_);
v_data_1704_ = lean_ctor_get(v_t_1656_, 0);
lean_inc(v_data_1704_);
v_expr_1705_ = lean_ctor_get(v_t_1656_, 1);
lean_inc_ref(v_expr_1705_);
lean_dec_ref(v_t_1656_);
v___x_1706_ = lean_apply_2(v_mdata_1667_, v_data_1704_, v_expr_1705_);
return v___x_1706_;
}
default: 
{
lean_object* v_typeName_1707_; lean_object* v_idx_1708_; lean_object* v_struct_1709_; lean_object* v___x_1710_; 
lean_dec(v_mdata_1667_);
lean_dec(v_lit_1666_);
lean_dec(v_letE_1665_);
lean_dec(v_forallE_1664_);
lean_dec(v_lam_1663_);
lean_dec(v_app_1662_);
lean_dec(v_const_1661_);
lean_dec(v_sort_1660_);
lean_dec(v_mvar_1659_);
lean_dec(v_fvar_1658_);
lean_dec(v_bvar_1657_);
v_typeName_1707_ = lean_ctor_get(v_t_1656_, 0);
lean_inc(v_typeName_1707_);
v_idx_1708_ = lean_ctor_get(v_t_1656_, 1);
lean_inc(v_idx_1708_);
v_struct_1709_ = lean_ctor_get(v_t_1656_, 2);
lean_inc_ref(v_struct_1709_);
lean_dec_ref(v_t_1656_);
v___x_1710_ = lean_apply_3(v_proj_1668_, v_typeName_1707_, v_idx_1708_, v_struct_1709_);
return v___x_1710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* v_motive_1711_, lean_object* v_t_1712_, lean_object* v_bvar_1713_, lean_object* v_fvar_1714_, lean_object* v_mvar_1715_, lean_object* v_sort_1716_, lean_object* v_const_1717_, lean_object* v_app_1718_, lean_object* v_lam_1719_, lean_object* v_forallE_1720_, lean_object* v_letE_1721_, lean_object* v_lit_1722_, lean_object* v_mdata_1723_, lean_object* v_proj_1724_){
_start:
{
switch(lean_obj_tag(v_t_1712_))
{
case 0:
{
lean_object* v_deBruijnIndex_1725_; lean_object* v___x_1726_; 
lean_dec(v_proj_1724_);
lean_dec(v_mdata_1723_);
lean_dec(v_lit_1722_);
lean_dec(v_letE_1721_);
lean_dec(v_forallE_1720_);
lean_dec(v_lam_1719_);
lean_dec(v_app_1718_);
lean_dec(v_const_1717_);
lean_dec(v_sort_1716_);
lean_dec(v_mvar_1715_);
lean_dec(v_fvar_1714_);
v_deBruijnIndex_1725_ = lean_ctor_get(v_t_1712_, 0);
lean_inc(v_deBruijnIndex_1725_);
lean_dec_ref(v_t_1712_);
v___x_1726_ = lean_apply_1(v_bvar_1713_, v_deBruijnIndex_1725_);
return v___x_1726_;
}
case 1:
{
lean_object* v_fvarId_1727_; lean_object* v___x_1728_; 
lean_dec(v_proj_1724_);
lean_dec(v_mdata_1723_);
lean_dec(v_lit_1722_);
lean_dec(v_letE_1721_);
lean_dec(v_forallE_1720_);
lean_dec(v_lam_1719_);
lean_dec(v_app_1718_);
lean_dec(v_const_1717_);
lean_dec(v_sort_1716_);
lean_dec(v_mvar_1715_);
lean_dec(v_bvar_1713_);
v_fvarId_1727_ = lean_ctor_get(v_t_1712_, 0);
lean_inc(v_fvarId_1727_);
lean_dec_ref(v_t_1712_);
v___x_1728_ = lean_apply_1(v_fvar_1714_, v_fvarId_1727_);
return v___x_1728_;
}
case 2:
{
lean_object* v_mvarId_1729_; lean_object* v___x_1730_; 
lean_dec(v_proj_1724_);
lean_dec(v_mdata_1723_);
lean_dec(v_lit_1722_);
lean_dec(v_letE_1721_);
lean_dec(v_forallE_1720_);
lean_dec(v_lam_1719_);
lean_dec(v_app_1718_);
lean_dec(v_const_1717_);
lean_dec(v_sort_1716_);
lean_dec(v_fvar_1714_);
lean_dec(v_bvar_1713_);
v_mvarId_1729_ = lean_ctor_get(v_t_1712_, 0);
lean_inc(v_mvarId_1729_);
lean_dec_ref(v_t_1712_);
v___x_1730_ = lean_apply_1(v_mvar_1715_, v_mvarId_1729_);
return v___x_1730_;
}
case 3:
{
lean_object* v_u_1731_; lean_object* v___x_1732_; 
lean_dec(v_proj_1724_);
lean_dec(v_mdata_1723_);
lean_dec(v_lit_1722_);
lean_dec(v_letE_1721_);
lean_dec(v_forallE_1720_);
lean_dec(v_lam_1719_);
lean_dec(v_app_1718_);
lean_dec(v_const_1717_);
lean_dec(v_mvar_1715_);
lean_dec(v_fvar_1714_);
lean_dec(v_bvar_1713_);
v_u_1731_ = lean_ctor_get(v_t_1712_, 0);
lean_inc(v_u_1731_);
lean_dec_ref(v_t_1712_);
v___x_1732_ = lean_apply_1(v_sort_1716_, v_u_1731_);
return v___x_1732_;
}
case 4:
{
lean_object* v_declName_1733_; lean_object* v_us_1734_; lean_object* v___x_1735_; 
lean_dec(v_proj_1724_);
lean_dec(v_mdata_1723_);
lean_dec(v_lit_1722_);
lean_dec(v_letE_1721_);
lean_dec(v_forallE_1720_);
lean_dec(v_lam_1719_);
lean_dec(v_app_1718_);
lean_dec(v_sort_1716_);
lean_dec(v_mvar_1715_);
lean_dec(v_fvar_1714_);
lean_dec(v_bvar_1713_);
v_declName_1733_ = lean_ctor_get(v_t_1712_, 0);
lean_inc(v_declName_1733_);
v_us_1734_ = lean_ctor_get(v_t_1712_, 1);
lean_inc(v_us_1734_);
lean_dec_ref(v_t_1712_);
v___x_1735_ = lean_apply_2(v_const_1717_, v_declName_1733_, v_us_1734_);
return v___x_1735_;
}
case 5:
{
lean_object* v_fn_1736_; lean_object* v_arg_1737_; lean_object* v___x_1738_; 
lean_dec(v_proj_1724_);
lean_dec(v_mdata_1723_);
lean_dec(v_lit_1722_);
lean_dec(v_letE_1721_);
lean_dec(v_forallE_1720_);
lean_dec(v_lam_1719_);
lean_dec(v_const_1717_);
lean_dec(v_sort_1716_);
lean_dec(v_mvar_1715_);
lean_dec(v_fvar_1714_);
lean_dec(v_bvar_1713_);
v_fn_1736_ = lean_ctor_get(v_t_1712_, 0);
lean_inc_ref(v_fn_1736_);
v_arg_1737_ = lean_ctor_get(v_t_1712_, 1);
lean_inc_ref(v_arg_1737_);
lean_dec_ref(v_t_1712_);
v___x_1738_ = lean_apply_2(v_app_1718_, v_fn_1736_, v_arg_1737_);
return v___x_1738_;
}
case 6:
{
lean_object* v_binderName_1739_; lean_object* v_binderType_1740_; lean_object* v_body_1741_; uint8_t v_binderInfo_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec(v_proj_1724_);
lean_dec(v_mdata_1723_);
lean_dec(v_lit_1722_);
lean_dec(v_letE_1721_);
lean_dec(v_forallE_1720_);
lean_dec(v_app_1718_);
lean_dec(v_const_1717_);
lean_dec(v_sort_1716_);
lean_dec(v_mvar_1715_);
lean_dec(v_fvar_1714_);
lean_dec(v_bvar_1713_);
v_binderName_1739_ = lean_ctor_get(v_t_1712_, 0);
lean_inc(v_binderName_1739_);
v_binderType_1740_ = lean_ctor_get(v_t_1712_, 1);
lean_inc_ref(v_binderType_1740_);
v_body_1741_ = lean_ctor_get(v_t_1712_, 2);
lean_inc_ref(v_body_1741_);
v_binderInfo_1742_ = lean_ctor_get_uint8(v_t_1712_, sizeof(void*)*3 + 8);
lean_dec_ref(v_t_1712_);
v___x_1743_ = lean_box(v_binderInfo_1742_);
v___x_1744_ = lean_apply_4(v_lam_1719_, v_binderName_1739_, v_binderType_1740_, v_body_1741_, v___x_1743_);
return v___x_1744_;
}
case 7:
{
lean_object* v_binderName_1745_; lean_object* v_binderType_1746_; lean_object* v_body_1747_; uint8_t v_binderInfo_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec(v_proj_1724_);
lean_dec(v_mdata_1723_);
lean_dec(v_lit_1722_);
lean_dec(v_letE_1721_);
lean_dec(v_lam_1719_);
lean_dec(v_app_1718_);
lean_dec(v_const_1717_);
lean_dec(v_sort_1716_);
lean_dec(v_mvar_1715_);
lean_dec(v_fvar_1714_);
lean_dec(v_bvar_1713_);
v_binderName_1745_ = lean_ctor_get(v_t_1712_, 0);
lean_inc(v_binderName_1745_);
v_binderType_1746_ = lean_ctor_get(v_t_1712_, 1);
lean_inc_ref(v_binderType_1746_);
v_body_1747_ = lean_ctor_get(v_t_1712_, 2);
lean_inc_ref(v_body_1747_);
v_binderInfo_1748_ = lean_ctor_get_uint8(v_t_1712_, sizeof(void*)*3 + 8);
lean_dec_ref(v_t_1712_);
v___x_1749_ = lean_box(v_binderInfo_1748_);
v___x_1750_ = lean_apply_4(v_forallE_1720_, v_binderName_1745_, v_binderType_1746_, v_body_1747_, v___x_1749_);
return v___x_1750_;
}
case 8:
{
lean_object* v_declName_1751_; lean_object* v_type_1752_; lean_object* v_value_1753_; lean_object* v_body_1754_; uint8_t v_nondep_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec(v_proj_1724_);
lean_dec(v_mdata_1723_);
lean_dec(v_lit_1722_);
lean_dec(v_forallE_1720_);
lean_dec(v_lam_1719_);
lean_dec(v_app_1718_);
lean_dec(v_const_1717_);
lean_dec(v_sort_1716_);
lean_dec(v_mvar_1715_);
lean_dec(v_fvar_1714_);
lean_dec(v_bvar_1713_);
v_declName_1751_ = lean_ctor_get(v_t_1712_, 0);
lean_inc(v_declName_1751_);
v_type_1752_ = lean_ctor_get(v_t_1712_, 1);
lean_inc_ref(v_type_1752_);
v_value_1753_ = lean_ctor_get(v_t_1712_, 2);
lean_inc_ref(v_value_1753_);
v_body_1754_ = lean_ctor_get(v_t_1712_, 3);
lean_inc_ref(v_body_1754_);
v_nondep_1755_ = lean_ctor_get_uint8(v_t_1712_, sizeof(void*)*4 + 8);
lean_dec_ref(v_t_1712_);
v___x_1756_ = lean_box(v_nondep_1755_);
v___x_1757_ = lean_apply_5(v_letE_1721_, v_declName_1751_, v_type_1752_, v_value_1753_, v_body_1754_, v___x_1756_);
return v___x_1757_;
}
case 9:
{
lean_object* v_a_1758_; lean_object* v___x_1759_; 
lean_dec(v_proj_1724_);
lean_dec(v_mdata_1723_);
lean_dec(v_letE_1721_);
lean_dec(v_forallE_1720_);
lean_dec(v_lam_1719_);
lean_dec(v_app_1718_);
lean_dec(v_const_1717_);
lean_dec(v_sort_1716_);
lean_dec(v_mvar_1715_);
lean_dec(v_fvar_1714_);
lean_dec(v_bvar_1713_);
v_a_1758_ = lean_ctor_get(v_t_1712_, 0);
lean_inc_ref(v_a_1758_);
lean_dec_ref(v_t_1712_);
v___x_1759_ = lean_apply_1(v_lit_1722_, v_a_1758_);
return v___x_1759_;
}
case 10:
{
lean_object* v_data_1760_; lean_object* v_expr_1761_; lean_object* v___x_1762_; 
lean_dec(v_proj_1724_);
lean_dec(v_lit_1722_);
lean_dec(v_letE_1721_);
lean_dec(v_forallE_1720_);
lean_dec(v_lam_1719_);
lean_dec(v_app_1718_);
lean_dec(v_const_1717_);
lean_dec(v_sort_1716_);
lean_dec(v_mvar_1715_);
lean_dec(v_fvar_1714_);
lean_dec(v_bvar_1713_);
v_data_1760_ = lean_ctor_get(v_t_1712_, 0);
lean_inc(v_data_1760_);
v_expr_1761_ = lean_ctor_get(v_t_1712_, 1);
lean_inc_ref(v_expr_1761_);
lean_dec_ref(v_t_1712_);
v___x_1762_ = lean_apply_2(v_mdata_1723_, v_data_1760_, v_expr_1761_);
return v___x_1762_;
}
default: 
{
lean_object* v_typeName_1763_; lean_object* v_idx_1764_; lean_object* v_struct_1765_; lean_object* v___x_1766_; 
lean_dec(v_mdata_1723_);
lean_dec(v_lit_1722_);
lean_dec(v_letE_1721_);
lean_dec(v_forallE_1720_);
lean_dec(v_lam_1719_);
lean_dec(v_app_1718_);
lean_dec(v_const_1717_);
lean_dec(v_sort_1716_);
lean_dec(v_mvar_1715_);
lean_dec(v_fvar_1714_);
lean_dec(v_bvar_1713_);
v_typeName_1763_ = lean_ctor_get(v_t_1712_, 0);
lean_inc(v_typeName_1763_);
v_idx_1764_ = lean_ctor_get(v_t_1712_, 1);
lean_inc(v_idx_1764_);
v_struct_1765_ = lean_ctor_get(v_t_1712_, 2);
lean_inc_ref(v_struct_1765_);
lean_dec_ref(v_t_1712_);
v___x_1766_ = lean_apply_3(v_proj_1724_, v_typeName_1763_, v_idx_1764_, v_struct_1765_);
return v___x_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* v_deBruijnIndex_1767_){
_start:
{
uint64_t v___x_1768_; uint64_t v___x_1769_; uint64_t v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; uint32_t v___x_1773_; uint8_t v___x_1774_; uint64_t v___x_1775_; lean_object* v___x_1776_; 
v___x_1768_ = 7ULL;
v___x_1769_ = lean_uint64_of_nat(v_deBruijnIndex_1767_);
v___x_1770_ = lean_uint64_mix_hash(v___x_1768_, v___x_1769_);
v___x_1771_ = lean_unsigned_to_nat(1u);
v___x_1772_ = lean_nat_add(v_deBruijnIndex_1767_, v___x_1771_);
v___x_1773_ = 0;
v___x_1774_ = 0;
v___x_1775_ = lean_expr_mk_data(v___x_1770_, v___x_1772_, v___x_1773_, v___x_1774_, v___x_1774_, v___x_1774_, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1776_, 0, v_deBruijnIndex_1767_);
lean_ctor_set_uint64(v___x_1776_, sizeof(void*)*1, v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* v_fvarId_1777_){
_start:
{
uint64_t v___x_1778_; uint64_t v___x_1779_; uint64_t v___x_1780_; lean_object* v___x_1781_; uint32_t v___x_1782_; uint8_t v___x_1783_; uint8_t v___x_1784_; uint64_t v___x_1785_; lean_object* v___x_1786_; 
v___x_1778_ = 13ULL;
v___x_1779_ = l_Lean_instHashableFVarId_hash(v_fvarId_1777_);
v___x_1780_ = lean_uint64_mix_hash(v___x_1778_, v___x_1779_);
v___x_1781_ = lean_unsigned_to_nat(0u);
v___x_1782_ = 0;
v___x_1783_ = 1;
v___x_1784_ = 0;
v___x_1785_ = lean_expr_mk_data(v___x_1780_, v___x_1781_, v___x_1782_, v___x_1783_, v___x_1784_, v___x_1784_, v___x_1784_);
v___x_1786_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_1786_, 0, v_fvarId_1777_);
lean_ctor_set_uint64(v___x_1786_, sizeof(void*)*1, v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* v_mvarId_1787_){
_start:
{
uint64_t v___x_1788_; uint64_t v___x_1789_; uint64_t v___x_1790_; lean_object* v___x_1791_; uint32_t v___x_1792_; uint8_t v___x_1793_; uint8_t v___x_1794_; uint64_t v___x_1795_; lean_object* v___x_1796_; 
v___x_1788_ = 17ULL;
v___x_1789_ = l_Lean_instHashableMVarId_hash(v_mvarId_1787_);
v___x_1790_ = lean_uint64_mix_hash(v___x_1788_, v___x_1789_);
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = 0;
v___x_1793_ = 0;
v___x_1794_ = 1;
v___x_1795_ = lean_expr_mk_data(v___x_1790_, v___x_1791_, v___x_1792_, v___x_1793_, v___x_1794_, v___x_1793_, v___x_1793_);
v___x_1796_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_1796_, 0, v_mvarId_1787_);
lean_ctor_set_uint64(v___x_1796_, sizeof(void*)*1, v___x_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* v_u_1797_){
_start:
{
uint64_t v___x_1798_; uint64_t v___x_1799_; uint64_t v___x_1800_; lean_object* v___x_1801_; uint32_t v___x_1802_; uint8_t v___x_1803_; uint8_t v___x_1804_; uint8_t v___x_1805_; uint64_t v___x_1806_; lean_object* v___x_1807_; 
v___x_1798_ = 11ULL;
v___x_1799_ = l_Lean_Level_hash(v_u_1797_);
v___x_1800_ = lean_uint64_mix_hash(v___x_1798_, v___x_1799_);
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = 0;
v___x_1803_ = 0;
v___x_1804_ = l_Lean_Level_hasMVar(v_u_1797_);
v___x_1805_ = l_Lean_Level_hasParam(v_u_1797_);
v___x_1806_ = lean_expr_mk_data(v___x_1800_, v___x_1801_, v___x_1802_, v___x_1803_, v___x_1803_, v___x_1804_, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(v___x_1807_, 0, v_u_1797_);
lean_ctor_set_uint64(v___x_1807_, sizeof(void*)*1, v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* v_fn_1808_, lean_object* v_arg_1809_){
_start:
{
uint64_t v___x_1810_; uint64_t v___x_1811_; uint64_t v___x_1812_; lean_object* v___x_1813_; 
v___x_1810_ = lean_expr_data(v_fn_1808_);
v___x_1811_ = lean_expr_data(v_arg_1809_);
v___x_1812_ = lean_expr_mk_app_data(v___x_1810_, v___x_1811_);
v___x_1813_ = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(v___x_1813_, 0, v_fn_1808_);
lean_ctor_set(v___x_1813_, 1, v_arg_1809_);
lean_ctor_set_uint64(v___x_1813_, sizeof(void*)*2, v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object* v_binderName_1814_, lean_object* v_binderType_1815_, lean_object* v_body_1816_, uint8_t v_binderInfo_1817_){
_start:
{
uint64_t v___y_1819_; uint8_t v___y_1820_; uint32_t v___y_1821_; uint8_t v___y_1822_; uint8_t v___y_1823_; lean_object* v___y_1824_; uint8_t v___y_1825_; uint64_t v___x_1828_; uint8_t v___x_1829_; uint32_t v___x_1830_; uint64_t v___x_1831_; uint64_t v___y_1833_; uint8_t v___y_1834_; uint32_t v___y_1835_; uint8_t v___y_1836_; lean_object* v___y_1837_; uint8_t v___y_1838_; uint64_t v___y_1842_; uint8_t v___y_1843_; uint32_t v___y_1844_; lean_object* v___y_1845_; uint8_t v___y_1846_; uint64_t v___y_1850_; uint32_t v___y_1851_; lean_object* v___y_1852_; uint8_t v___y_1853_; uint64_t v___y_1857_; uint32_t v___y_1858_; lean_object* v___y_1859_; uint32_t v___y_1863_; uint8_t v___x_1878_; uint32_t v___x_1879_; uint8_t v___x_1880_; 
v___x_1828_ = lean_expr_data(v_binderType_1815_);
v___x_1829_ = l_Lean_Expr_Data_approxDepth(v___x_1828_);
v___x_1830_ = lean_uint8_to_uint32(v___x_1829_);
v___x_1831_ = lean_expr_data(v_body_1816_);
v___x_1878_ = l_Lean_Expr_Data_approxDepth(v___x_1831_);
v___x_1879_ = lean_uint8_to_uint32(v___x_1878_);
v___x_1880_ = lean_uint32_dec_le(v___x_1830_, v___x_1879_);
if (v___x_1880_ == 0)
{
v___y_1863_ = v___x_1830_;
goto v___jp_1862_;
}
else
{
v___y_1863_ = v___x_1879_;
goto v___jp_1862_;
}
v___jp_1818_:
{
uint64_t v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = lean_expr_mk_data(v___y_1819_, v___y_1824_, v___y_1821_, v___y_1820_, v___y_1822_, v___y_1823_, v___y_1825_);
v___x_1827_ = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(v___x_1827_, 0, v_binderName_1814_);
lean_ctor_set(v___x_1827_, 1, v_binderType_1815_);
lean_ctor_set(v___x_1827_, 2, v_body_1816_);
lean_ctor_set_uint64(v___x_1827_, sizeof(void*)*3, v___x_1826_);
lean_ctor_set_uint8(v___x_1827_, sizeof(void*)*3 + 8, v_binderInfo_1817_);
return v___x_1827_;
}
v___jp_1832_:
{
uint8_t v___x_1839_; 
v___x_1839_ = l_Lean_Expr_Data_hasLevelParam(v___x_1828_);
if (v___x_1839_ == 0)
{
uint8_t v___x_1840_; 
v___x_1840_ = l_Lean_Expr_Data_hasLevelParam(v___x_1831_);
v___y_1819_ = v___y_1833_;
v___y_1820_ = v___y_1834_;
v___y_1821_ = v___y_1835_;
v___y_1822_ = v___y_1836_;
v___y_1823_ = v___y_1838_;
v___y_1824_ = v___y_1837_;
v___y_1825_ = v___x_1840_;
goto v___jp_1818_;
}
else
{
v___y_1819_ = v___y_1833_;
v___y_1820_ = v___y_1834_;
v___y_1821_ = v___y_1835_;
v___y_1822_ = v___y_1836_;
v___y_1823_ = v___y_1838_;
v___y_1824_ = v___y_1837_;
v___y_1825_ = v___x_1839_;
goto v___jp_1818_;
}
}
v___jp_1841_:
{
uint8_t v___x_1847_; 
v___x_1847_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1828_);
if (v___x_1847_ == 0)
{
uint8_t v___x_1848_; 
v___x_1848_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1831_);
v___y_1833_ = v___y_1842_;
v___y_1834_ = v___y_1843_;
v___y_1835_ = v___y_1844_;
v___y_1836_ = v___y_1846_;
v___y_1837_ = v___y_1845_;
v___y_1838_ = v___x_1848_;
goto v___jp_1832_;
}
else
{
v___y_1833_ = v___y_1842_;
v___y_1834_ = v___y_1843_;
v___y_1835_ = v___y_1844_;
v___y_1836_ = v___y_1846_;
v___y_1837_ = v___y_1845_;
v___y_1838_ = v___x_1847_;
goto v___jp_1832_;
}
}
v___jp_1849_:
{
uint8_t v___x_1854_; 
v___x_1854_ = l_Lean_Expr_Data_hasExprMVar(v___x_1828_);
if (v___x_1854_ == 0)
{
uint8_t v___x_1855_; 
v___x_1855_ = l_Lean_Expr_Data_hasExprMVar(v___x_1831_);
v___y_1842_ = v___y_1850_;
v___y_1843_ = v___y_1853_;
v___y_1844_ = v___y_1851_;
v___y_1845_ = v___y_1852_;
v___y_1846_ = v___x_1855_;
goto v___jp_1841_;
}
else
{
v___y_1842_ = v___y_1850_;
v___y_1843_ = v___y_1853_;
v___y_1844_ = v___y_1851_;
v___y_1845_ = v___y_1852_;
v___y_1846_ = v___x_1854_;
goto v___jp_1841_;
}
}
v___jp_1856_:
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Lean_Expr_Data_hasFVar(v___x_1828_);
if (v___x_1860_ == 0)
{
uint8_t v___x_1861_; 
v___x_1861_ = l_Lean_Expr_Data_hasFVar(v___x_1831_);
v___y_1850_ = v___y_1857_;
v___y_1851_ = v___y_1858_;
v___y_1852_ = v___y_1859_;
v___y_1853_ = v___x_1861_;
goto v___jp_1849_;
}
else
{
v___y_1850_ = v___y_1857_;
v___y_1851_ = v___y_1858_;
v___y_1852_ = v___y_1859_;
v___y_1853_ = v___x_1860_;
goto v___jp_1849_;
}
}
v___jp_1862_:
{
lean_object* v___x_1864_; uint32_t v___x_1865_; uint32_t v___x_1866_; uint64_t v___x_1867_; uint64_t v___x_1868_; uint64_t v___x_1869_; uint64_t v___x_1870_; uint64_t v___x_1871_; uint32_t v___x_1872_; lean_object* v___x_1873_; uint32_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1864_ = lean_unsigned_to_nat(1u);
v___x_1865_ = 1;
v___x_1866_ = lean_uint32_add(v___y_1863_, v___x_1865_);
v___x_1867_ = lean_uint32_to_uint64(v___x_1866_);
v___x_1868_ = l_Lean_Expr_Data_hash(v___x_1828_);
v___x_1869_ = l_Lean_Expr_Data_hash(v___x_1831_);
v___x_1870_ = lean_uint64_mix_hash(v___x_1868_, v___x_1869_);
v___x_1871_ = lean_uint64_mix_hash(v___x_1867_, v___x_1870_);
v___x_1872_ = l_Lean_Expr_Data_looseBVarRange(v___x_1828_);
v___x_1873_ = lean_uint32_to_nat(v___x_1872_);
v___x_1874_ = l_Lean_Expr_Data_looseBVarRange(v___x_1831_);
v___x_1875_ = lean_uint32_to_nat(v___x_1874_);
v___x_1876_ = lean_nat_sub(v___x_1875_, v___x_1864_);
lean_dec(v___x_1875_);
v___x_1877_ = lean_nat_dec_le(v___x_1873_, v___x_1876_);
if (v___x_1877_ == 0)
{
lean_dec(v___x_1876_);
v___y_1857_ = v___x_1871_;
v___y_1858_ = v___x_1866_;
v___y_1859_ = v___x_1873_;
goto v___jp_1856_;
}
else
{
lean_dec(v___x_1873_);
v___y_1857_ = v___x_1871_;
v___y_1858_ = v___x_1866_;
v___y_1859_ = v___x_1876_;
goto v___jp_1856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* v_binderName_1881_, lean_object* v_binderType_1882_, lean_object* v_body_1883_, lean_object* v_binderInfo_1884_){
_start:
{
uint8_t v_binderInfo_boxed_1885_; lean_object* v_res_1886_; 
v_binderInfo_boxed_1885_ = lean_unbox(v_binderInfo_1884_);
v_res_1886_ = l_Lean_Expr_lam___override(v_binderName_1881_, v_binderType_1882_, v_body_1883_, v_binderInfo_boxed_1885_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object* v_binderName_1887_, lean_object* v_binderType_1888_, lean_object* v_body_1889_, uint8_t v_binderInfo_1890_){
_start:
{
uint64_t v___y_1892_; uint8_t v___y_1893_; uint32_t v___y_1894_; lean_object* v___y_1895_; uint8_t v___y_1896_; uint8_t v___y_1897_; uint8_t v___y_1898_; uint64_t v___x_1901_; uint8_t v___x_1902_; uint32_t v___x_1903_; uint64_t v___x_1904_; uint64_t v___y_1906_; uint32_t v___y_1907_; uint8_t v___y_1908_; lean_object* v___y_1909_; uint8_t v___y_1910_; uint8_t v___y_1911_; uint64_t v___y_1915_; uint32_t v___y_1916_; lean_object* v___y_1917_; uint8_t v___y_1918_; uint8_t v___y_1919_; uint64_t v___y_1923_; uint32_t v___y_1924_; lean_object* v___y_1925_; uint8_t v___y_1926_; uint64_t v___y_1930_; uint32_t v___y_1931_; lean_object* v___y_1932_; uint32_t v___y_1936_; uint8_t v___x_1951_; uint32_t v___x_1952_; uint8_t v___x_1953_; 
v___x_1901_ = lean_expr_data(v_binderType_1888_);
v___x_1902_ = l_Lean_Expr_Data_approxDepth(v___x_1901_);
v___x_1903_ = lean_uint8_to_uint32(v___x_1902_);
v___x_1904_ = lean_expr_data(v_body_1889_);
v___x_1951_ = l_Lean_Expr_Data_approxDepth(v___x_1904_);
v___x_1952_ = lean_uint8_to_uint32(v___x_1951_);
v___x_1953_ = lean_uint32_dec_le(v___x_1903_, v___x_1952_);
if (v___x_1953_ == 0)
{
v___y_1936_ = v___x_1903_;
goto v___jp_1935_;
}
else
{
v___y_1936_ = v___x_1952_;
goto v___jp_1935_;
}
v___jp_1891_:
{
uint64_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_expr_mk_data(v___y_1892_, v___y_1895_, v___y_1894_, v___y_1896_, v___y_1893_, v___y_1897_, v___y_1898_);
v___x_1900_ = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(v___x_1900_, 0, v_binderName_1887_);
lean_ctor_set(v___x_1900_, 1, v_binderType_1888_);
lean_ctor_set(v___x_1900_, 2, v_body_1889_);
lean_ctor_set_uint64(v___x_1900_, sizeof(void*)*3, v___x_1899_);
lean_ctor_set_uint8(v___x_1900_, sizeof(void*)*3 + 8, v_binderInfo_1890_);
return v___x_1900_;
}
v___jp_1905_:
{
uint8_t v___x_1912_; 
v___x_1912_ = l_Lean_Expr_Data_hasLevelParam(v___x_1901_);
if (v___x_1912_ == 0)
{
uint8_t v___x_1913_; 
v___x_1913_ = l_Lean_Expr_Data_hasLevelParam(v___x_1904_);
v___y_1892_ = v___y_1906_;
v___y_1893_ = v___y_1908_;
v___y_1894_ = v___y_1907_;
v___y_1895_ = v___y_1909_;
v___y_1896_ = v___y_1910_;
v___y_1897_ = v___y_1911_;
v___y_1898_ = v___x_1913_;
goto v___jp_1891_;
}
else
{
v___y_1892_ = v___y_1906_;
v___y_1893_ = v___y_1908_;
v___y_1894_ = v___y_1907_;
v___y_1895_ = v___y_1909_;
v___y_1896_ = v___y_1910_;
v___y_1897_ = v___y_1911_;
v___y_1898_ = v___x_1912_;
goto v___jp_1891_;
}
}
v___jp_1914_:
{
uint8_t v___x_1920_; 
v___x_1920_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1901_);
if (v___x_1920_ == 0)
{
uint8_t v___x_1921_; 
v___x_1921_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1904_);
v___y_1906_ = v___y_1915_;
v___y_1907_ = v___y_1916_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1917_;
v___y_1910_ = v___y_1918_;
v___y_1911_ = v___x_1921_;
goto v___jp_1905_;
}
else
{
v___y_1906_ = v___y_1915_;
v___y_1907_ = v___y_1916_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1917_;
v___y_1910_ = v___y_1918_;
v___y_1911_ = v___x_1920_;
goto v___jp_1905_;
}
}
v___jp_1922_:
{
uint8_t v___x_1927_; 
v___x_1927_ = l_Lean_Expr_Data_hasExprMVar(v___x_1901_);
if (v___x_1927_ == 0)
{
uint8_t v___x_1928_; 
v___x_1928_ = l_Lean_Expr_Data_hasExprMVar(v___x_1904_);
v___y_1915_ = v___y_1923_;
v___y_1916_ = v___y_1924_;
v___y_1917_ = v___y_1925_;
v___y_1918_ = v___y_1926_;
v___y_1919_ = v___x_1928_;
goto v___jp_1914_;
}
else
{
v___y_1915_ = v___y_1923_;
v___y_1916_ = v___y_1924_;
v___y_1917_ = v___y_1925_;
v___y_1918_ = v___y_1926_;
v___y_1919_ = v___x_1927_;
goto v___jp_1914_;
}
}
v___jp_1929_:
{
uint8_t v___x_1933_; 
v___x_1933_ = l_Lean_Expr_Data_hasFVar(v___x_1901_);
if (v___x_1933_ == 0)
{
uint8_t v___x_1934_; 
v___x_1934_ = l_Lean_Expr_Data_hasFVar(v___x_1904_);
v___y_1923_ = v___y_1930_;
v___y_1924_ = v___y_1931_;
v___y_1925_ = v___y_1932_;
v___y_1926_ = v___x_1934_;
goto v___jp_1922_;
}
else
{
v___y_1923_ = v___y_1930_;
v___y_1924_ = v___y_1931_;
v___y_1925_ = v___y_1932_;
v___y_1926_ = v___x_1933_;
goto v___jp_1922_;
}
}
v___jp_1935_:
{
lean_object* v___x_1937_; uint32_t v___x_1938_; uint32_t v___x_1939_; uint64_t v___x_1940_; uint64_t v___x_1941_; uint64_t v___x_1942_; uint64_t v___x_1943_; uint64_t v___x_1944_; uint32_t v___x_1945_; lean_object* v___x_1946_; uint32_t v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1937_ = lean_unsigned_to_nat(1u);
v___x_1938_ = 1;
v___x_1939_ = lean_uint32_add(v___y_1936_, v___x_1938_);
v___x_1940_ = lean_uint32_to_uint64(v___x_1939_);
v___x_1941_ = l_Lean_Expr_Data_hash(v___x_1901_);
v___x_1942_ = l_Lean_Expr_Data_hash(v___x_1904_);
v___x_1943_ = lean_uint64_mix_hash(v___x_1941_, v___x_1942_);
v___x_1944_ = lean_uint64_mix_hash(v___x_1940_, v___x_1943_);
v___x_1945_ = l_Lean_Expr_Data_looseBVarRange(v___x_1901_);
v___x_1946_ = lean_uint32_to_nat(v___x_1945_);
v___x_1947_ = l_Lean_Expr_Data_looseBVarRange(v___x_1904_);
v___x_1948_ = lean_uint32_to_nat(v___x_1947_);
v___x_1949_ = lean_nat_sub(v___x_1948_, v___x_1937_);
lean_dec(v___x_1948_);
v___x_1950_ = lean_nat_dec_le(v___x_1946_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_dec(v___x_1949_);
v___y_1930_ = v___x_1944_;
v___y_1931_ = v___x_1939_;
v___y_1932_ = v___x_1946_;
goto v___jp_1929_;
}
else
{
lean_dec(v___x_1946_);
v___y_1930_ = v___x_1944_;
v___y_1931_ = v___x_1939_;
v___y_1932_ = v___x_1949_;
goto v___jp_1929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* v_binderName_1954_, lean_object* v_binderType_1955_, lean_object* v_body_1956_, lean_object* v_binderInfo_1957_){
_start:
{
uint8_t v_binderInfo_boxed_1958_; lean_object* v_res_1959_; 
v_binderInfo_boxed_1958_ = lean_unbox(v_binderInfo_1957_);
v_res_1959_ = l_Lean_Expr_forallE___override(v_binderName_1954_, v_binderType_1955_, v_body_1956_, v_binderInfo_boxed_1958_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object* v_declName_1960_, lean_object* v_type_1961_, lean_object* v_value_1962_, lean_object* v_body_1963_, uint8_t v_nondep_1964_){
_start:
{
uint64_t v___y_1966_; lean_object* v___y_1967_; uint8_t v___y_1968_; uint8_t v___y_1969_; uint8_t v___y_1970_; uint32_t v___y_1971_; uint8_t v___y_1972_; uint64_t v___y_1976_; uint64_t v___y_1977_; lean_object* v___y_1978_; uint8_t v___y_1979_; uint8_t v___y_1980_; uint32_t v___y_1981_; uint8_t v___y_1982_; uint8_t v___y_1983_; uint64_t v___x_1985_; uint8_t v___x_1986_; uint32_t v___x_1987_; uint64_t v___x_1988_; uint64_t v___y_1990_; uint64_t v___y_1991_; lean_object* v___y_1992_; uint8_t v___y_1993_; uint32_t v___y_1994_; uint8_t v___y_1995_; uint8_t v___y_1996_; uint64_t v___y_2000_; uint64_t v___y_2001_; lean_object* v___y_2002_; uint8_t v___y_2003_; uint8_t v___y_2004_; uint32_t v___y_2005_; uint8_t v___y_2006_; uint64_t v___y_2009_; uint64_t v___y_2010_; lean_object* v___y_2011_; uint8_t v___y_2012_; uint32_t v___y_2013_; uint8_t v___y_2014_; uint64_t v___y_2018_; uint64_t v___y_2019_; lean_object* v___y_2020_; uint8_t v___y_2021_; uint32_t v___y_2022_; uint8_t v___y_2023_; uint64_t v___y_2026_; uint64_t v___y_2027_; lean_object* v___y_2028_; uint32_t v___y_2029_; uint8_t v___y_2030_; uint64_t v___y_2034_; uint64_t v___y_2035_; lean_object* v___y_2036_; uint32_t v___y_2037_; uint8_t v___y_2038_; uint64_t v___y_2041_; uint64_t v___y_2042_; uint32_t v___y_2043_; lean_object* v___y_2044_; uint64_t v___y_2048_; uint64_t v___y_2049_; lean_object* v___y_2050_; uint32_t v___y_2051_; lean_object* v___y_2052_; uint64_t v___y_2058_; uint32_t v___y_2059_; uint32_t v___y_2076_; uint8_t v___x_2081_; uint32_t v___x_2082_; uint8_t v___x_2083_; 
v___x_1985_ = lean_expr_data(v_type_1961_);
v___x_1986_ = l_Lean_Expr_Data_approxDepth(v___x_1985_);
v___x_1987_ = lean_uint8_to_uint32(v___x_1986_);
v___x_1988_ = lean_expr_data(v_value_1962_);
v___x_2081_ = l_Lean_Expr_Data_approxDepth(v___x_1988_);
v___x_2082_ = lean_uint8_to_uint32(v___x_2081_);
v___x_2083_ = lean_uint32_dec_le(v___x_1987_, v___x_2082_);
if (v___x_2083_ == 0)
{
v___y_2076_ = v___x_1987_;
goto v___jp_2075_;
}
else
{
v___y_2076_ = v___x_2082_;
goto v___jp_2075_;
}
v___jp_1965_:
{
uint64_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = lean_expr_mk_data(v___y_1966_, v___y_1967_, v___y_1971_, v___y_1969_, v___y_1970_, v___y_1968_, v___y_1972_);
v___x_1974_ = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(v___x_1974_, 0, v_declName_1960_);
lean_ctor_set(v___x_1974_, 1, v_type_1961_);
lean_ctor_set(v___x_1974_, 2, v_value_1962_);
lean_ctor_set(v___x_1974_, 3, v_body_1963_);
lean_ctor_set_uint64(v___x_1974_, sizeof(void*)*4, v___x_1973_);
lean_ctor_set_uint8(v___x_1974_, sizeof(void*)*4 + 8, v_nondep_1964_);
return v___x_1974_;
}
v___jp_1975_:
{
if (v___y_1983_ == 0)
{
uint8_t v___x_1984_; 
v___x_1984_ = l_Lean_Expr_Data_hasLevelParam(v___y_1976_);
v___y_1966_ = v___y_1977_;
v___y_1967_ = v___y_1978_;
v___y_1968_ = v___y_1980_;
v___y_1969_ = v___y_1979_;
v___y_1970_ = v___y_1982_;
v___y_1971_ = v___y_1981_;
v___y_1972_ = v___x_1984_;
goto v___jp_1965_;
}
else
{
v___y_1966_ = v___y_1977_;
v___y_1967_ = v___y_1978_;
v___y_1968_ = v___y_1980_;
v___y_1969_ = v___y_1979_;
v___y_1970_ = v___y_1982_;
v___y_1971_ = v___y_1981_;
v___y_1972_ = v___y_1983_;
goto v___jp_1965_;
}
}
v___jp_1989_:
{
uint8_t v___x_1997_; 
v___x_1997_ = l_Lean_Expr_Data_hasLevelParam(v___x_1985_);
if (v___x_1997_ == 0)
{
uint8_t v___x_1998_; 
v___x_1998_ = l_Lean_Expr_Data_hasLevelParam(v___x_1988_);
v___y_1976_ = v___y_1990_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1992_;
v___y_1979_ = v___y_1993_;
v___y_1980_ = v___y_1996_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___y_1995_;
v___y_1983_ = v___x_1998_;
goto v___jp_1975_;
}
else
{
v___y_1976_ = v___y_1990_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1992_;
v___y_1979_ = v___y_1993_;
v___y_1980_ = v___y_1996_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___y_1995_;
v___y_1983_ = v___x_1997_;
goto v___jp_1975_;
}
}
v___jp_1999_:
{
if (v___y_2006_ == 0)
{
uint8_t v___x_2007_; 
v___x_2007_ = l_Lean_Expr_Data_hasLevelMVar(v___y_2000_);
v___y_1990_ = v___y_2000_;
v___y_1991_ = v___y_2001_;
v___y_1992_ = v___y_2002_;
v___y_1993_ = v___y_2003_;
v___y_1994_ = v___y_2005_;
v___y_1995_ = v___y_2004_;
v___y_1996_ = v___x_2007_;
goto v___jp_1989_;
}
else
{
v___y_1990_ = v___y_2000_;
v___y_1991_ = v___y_2001_;
v___y_1992_ = v___y_2002_;
v___y_1993_ = v___y_2003_;
v___y_1994_ = v___y_2005_;
v___y_1995_ = v___y_2004_;
v___y_1996_ = v___y_2006_;
goto v___jp_1989_;
}
}
v___jp_2008_:
{
uint8_t v___x_2015_; 
v___x_2015_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1985_);
if (v___x_2015_ == 0)
{
uint8_t v___x_2016_; 
v___x_2016_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1988_);
v___y_2000_ = v___y_2009_;
v___y_2001_ = v___y_2010_;
v___y_2002_ = v___y_2011_;
v___y_2003_ = v___y_2012_;
v___y_2004_ = v___y_2014_;
v___y_2005_ = v___y_2013_;
v___y_2006_ = v___x_2016_;
goto v___jp_1999_;
}
else
{
v___y_2000_ = v___y_2009_;
v___y_2001_ = v___y_2010_;
v___y_2002_ = v___y_2011_;
v___y_2003_ = v___y_2012_;
v___y_2004_ = v___y_2014_;
v___y_2005_ = v___y_2013_;
v___y_2006_ = v___x_2015_;
goto v___jp_1999_;
}
}
v___jp_2017_:
{
if (v___y_2023_ == 0)
{
uint8_t v___x_2024_; 
v___x_2024_ = l_Lean_Expr_Data_hasExprMVar(v___y_2018_);
v___y_2009_ = v___y_2018_;
v___y_2010_ = v___y_2019_;
v___y_2011_ = v___y_2020_;
v___y_2012_ = v___y_2021_;
v___y_2013_ = v___y_2022_;
v___y_2014_ = v___x_2024_;
goto v___jp_2008_;
}
else
{
v___y_2009_ = v___y_2018_;
v___y_2010_ = v___y_2019_;
v___y_2011_ = v___y_2020_;
v___y_2012_ = v___y_2021_;
v___y_2013_ = v___y_2022_;
v___y_2014_ = v___y_2023_;
goto v___jp_2008_;
}
}
v___jp_2025_:
{
uint8_t v___x_2031_; 
v___x_2031_ = l_Lean_Expr_Data_hasExprMVar(v___x_1985_);
if (v___x_2031_ == 0)
{
uint8_t v___x_2032_; 
v___x_2032_ = l_Lean_Expr_Data_hasExprMVar(v___x_1988_);
v___y_2018_ = v___y_2026_;
v___y_2019_ = v___y_2027_;
v___y_2020_ = v___y_2028_;
v___y_2021_ = v___y_2030_;
v___y_2022_ = v___y_2029_;
v___y_2023_ = v___x_2032_;
goto v___jp_2017_;
}
else
{
v___y_2018_ = v___y_2026_;
v___y_2019_ = v___y_2027_;
v___y_2020_ = v___y_2028_;
v___y_2021_ = v___y_2030_;
v___y_2022_ = v___y_2029_;
v___y_2023_ = v___x_2031_;
goto v___jp_2017_;
}
}
v___jp_2033_:
{
if (v___y_2038_ == 0)
{
uint8_t v___x_2039_; 
v___x_2039_ = l_Lean_Expr_Data_hasFVar(v___y_2034_);
v___y_2026_ = v___y_2034_;
v___y_2027_ = v___y_2035_;
v___y_2028_ = v___y_2036_;
v___y_2029_ = v___y_2037_;
v___y_2030_ = v___x_2039_;
goto v___jp_2025_;
}
else
{
v___y_2026_ = v___y_2034_;
v___y_2027_ = v___y_2035_;
v___y_2028_ = v___y_2036_;
v___y_2029_ = v___y_2037_;
v___y_2030_ = v___y_2038_;
goto v___jp_2025_;
}
}
v___jp_2040_:
{
uint8_t v___x_2045_; 
v___x_2045_ = l_Lean_Expr_Data_hasFVar(v___x_1985_);
if (v___x_2045_ == 0)
{
uint8_t v___x_2046_; 
v___x_2046_ = l_Lean_Expr_Data_hasFVar(v___x_1988_);
v___y_2034_ = v___y_2041_;
v___y_2035_ = v___y_2042_;
v___y_2036_ = v___y_2044_;
v___y_2037_ = v___y_2043_;
v___y_2038_ = v___x_2046_;
goto v___jp_2033_;
}
else
{
v___y_2034_ = v___y_2041_;
v___y_2035_ = v___y_2042_;
v___y_2036_ = v___y_2044_;
v___y_2037_ = v___y_2043_;
v___y_2038_ = v___x_2045_;
goto v___jp_2033_;
}
}
v___jp_2047_:
{
uint32_t v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v___x_2053_ = l_Lean_Expr_Data_looseBVarRange(v___y_2048_);
v___x_2054_ = lean_uint32_to_nat(v___x_2053_);
v___x_2055_ = lean_nat_sub(v___x_2054_, v___y_2050_);
lean_dec(v___x_2054_);
v___x_2056_ = lean_nat_dec_le(v___y_2052_, v___x_2055_);
if (v___x_2056_ == 0)
{
lean_dec(v___x_2055_);
v___y_2041_ = v___y_2048_;
v___y_2042_ = v___y_2049_;
v___y_2043_ = v___y_2051_;
v___y_2044_ = v___y_2052_;
goto v___jp_2040_;
}
else
{
lean_dec(v___y_2052_);
v___y_2041_ = v___y_2048_;
v___y_2042_ = v___y_2049_;
v___y_2043_ = v___y_2051_;
v___y_2044_ = v___x_2055_;
goto v___jp_2040_;
}
}
v___jp_2057_:
{
lean_object* v___x_2060_; uint32_t v___x_2061_; uint32_t v___x_2062_; uint64_t v___x_2063_; uint64_t v___x_2064_; uint64_t v___x_2065_; uint64_t v___x_2066_; uint64_t v___x_2067_; uint64_t v___x_2068_; uint64_t v___x_2069_; uint32_t v___x_2070_; lean_object* v___x_2071_; uint32_t v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2060_ = lean_unsigned_to_nat(1u);
v___x_2061_ = 1;
v___x_2062_ = lean_uint32_add(v___y_2059_, v___x_2061_);
v___x_2063_ = lean_uint32_to_uint64(v___x_2062_);
v___x_2064_ = l_Lean_Expr_Data_hash(v___x_1985_);
v___x_2065_ = l_Lean_Expr_Data_hash(v___x_1988_);
v___x_2066_ = l_Lean_Expr_Data_hash(v___y_2058_);
v___x_2067_ = lean_uint64_mix_hash(v___x_2065_, v___x_2066_);
v___x_2068_ = lean_uint64_mix_hash(v___x_2064_, v___x_2067_);
v___x_2069_ = lean_uint64_mix_hash(v___x_2063_, v___x_2068_);
v___x_2070_ = l_Lean_Expr_Data_looseBVarRange(v___x_1985_);
v___x_2071_ = lean_uint32_to_nat(v___x_2070_);
v___x_2072_ = l_Lean_Expr_Data_looseBVarRange(v___x_1988_);
v___x_2073_ = lean_uint32_to_nat(v___x_2072_);
v___x_2074_ = lean_nat_dec_le(v___x_2071_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_dec(v___x_2073_);
v___y_2048_ = v___y_2058_;
v___y_2049_ = v___x_2069_;
v___y_2050_ = v___x_2060_;
v___y_2051_ = v___x_2062_;
v___y_2052_ = v___x_2071_;
goto v___jp_2047_;
}
else
{
lean_dec(v___x_2071_);
v___y_2048_ = v___y_2058_;
v___y_2049_ = v___x_2069_;
v___y_2050_ = v___x_2060_;
v___y_2051_ = v___x_2062_;
v___y_2052_ = v___x_2073_;
goto v___jp_2047_;
}
}
v___jp_2075_:
{
uint64_t v___x_2077_; uint8_t v___x_2078_; uint32_t v___x_2079_; uint8_t v___x_2080_; 
v___x_2077_ = lean_expr_data(v_body_1963_);
v___x_2078_ = l_Lean_Expr_Data_approxDepth(v___x_2077_);
v___x_2079_ = lean_uint8_to_uint32(v___x_2078_);
v___x_2080_ = lean_uint32_dec_le(v___y_2076_, v___x_2079_);
if (v___x_2080_ == 0)
{
v___y_2058_ = v___x_2077_;
v___y_2059_ = v___y_2076_;
goto v___jp_2057_;
}
else
{
v___y_2058_ = v___x_2077_;
v___y_2059_ = v___x_2079_;
goto v___jp_2057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* v_declName_2084_, lean_object* v_type_2085_, lean_object* v_value_2086_, lean_object* v_body_2087_, lean_object* v_nondep_2088_){
_start:
{
uint8_t v_nondep_boxed_2089_; lean_object* v_res_2090_; 
v_nondep_boxed_2089_ = lean_unbox(v_nondep_2088_);
v_res_2090_ = l_Lean_Expr_letE___override(v_declName_2084_, v_type_2085_, v_value_2086_, v_body_2087_, v_nondep_boxed_2089_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* v_a_2091_){
_start:
{
uint64_t v___x_2092_; uint64_t v___x_2093_; uint64_t v___x_2094_; lean_object* v___x_2095_; uint32_t v___x_2096_; uint8_t v___x_2097_; uint64_t v___x_2098_; lean_object* v___x_2099_; 
v___x_2092_ = 3ULL;
v___x_2093_ = l_Lean_Literal_hash(v_a_2091_);
v___x_2094_ = lean_uint64_mix_hash(v___x_2092_, v___x_2093_);
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = 0;
v___x_2097_ = 0;
v___x_2098_ = lean_expr_mk_data(v___x_2094_, v___x_2095_, v___x_2096_, v___x_2097_, v___x_2097_, v___x_2097_, v___x_2097_);
v___x_2099_ = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(v___x_2099_, 0, v_a_2091_);
lean_ctor_set_uint64(v___x_2099_, sizeof(void*)*1, v___x_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* v_data_2100_, lean_object* v_expr_2101_){
_start:
{
uint64_t v___x_2102_; uint8_t v___x_2103_; uint32_t v___x_2104_; uint32_t v___x_2105_; uint32_t v___x_2106_; uint64_t v___x_2107_; uint64_t v___x_2108_; uint64_t v___x_2109_; uint32_t v___x_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; uint8_t v___x_2113_; uint8_t v___x_2114_; uint8_t v___x_2115_; uint64_t v___x_2116_; lean_object* v___x_2117_; 
v___x_2102_ = lean_expr_data(v_expr_2101_);
v___x_2103_ = l_Lean_Expr_Data_approxDepth(v___x_2102_);
v___x_2104_ = lean_uint8_to_uint32(v___x_2103_);
v___x_2105_ = 1;
v___x_2106_ = lean_uint32_add(v___x_2104_, v___x_2105_);
v___x_2107_ = lean_uint32_to_uint64(v___x_2106_);
v___x_2108_ = l_Lean_Expr_Data_hash(v___x_2102_);
v___x_2109_ = lean_uint64_mix_hash(v___x_2107_, v___x_2108_);
v___x_2110_ = l_Lean_Expr_Data_looseBVarRange(v___x_2102_);
v___x_2111_ = lean_uint32_to_nat(v___x_2110_);
v___x_2112_ = l_Lean_Expr_Data_hasFVar(v___x_2102_);
v___x_2113_ = l_Lean_Expr_Data_hasExprMVar(v___x_2102_);
v___x_2114_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2102_);
v___x_2115_ = l_Lean_Expr_Data_hasLevelParam(v___x_2102_);
v___x_2116_ = lean_expr_mk_data(v___x_2109_, v___x_2111_, v___x_2106_, v___x_2112_, v___x_2113_, v___x_2114_, v___x_2115_);
v___x_2117_ = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(v___x_2117_, 0, v_data_2100_);
lean_ctor_set(v___x_2117_, 1, v_expr_2101_);
lean_ctor_set_uint64(v___x_2117_, sizeof(void*)*2, v___x_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* v_typeName_2118_, lean_object* v_idx_2119_, lean_object* v_struct_2120_){
_start:
{
uint64_t v___x_2121_; uint8_t v___x_2122_; uint32_t v___x_2123_; uint32_t v___x_2124_; uint32_t v___x_2125_; uint64_t v___x_2126_; uint64_t v___y_2128_; 
v___x_2121_ = lean_expr_data(v_struct_2120_);
v___x_2122_ = l_Lean_Expr_Data_approxDepth(v___x_2121_);
v___x_2123_ = lean_uint8_to_uint32(v___x_2122_);
v___x_2124_ = 1;
v___x_2125_ = lean_uint32_add(v___x_2123_, v___x_2124_);
v___x_2126_ = lean_uint32_to_uint64(v___x_2125_);
if (lean_obj_tag(v_typeName_2118_) == 0)
{
uint64_t v___x_2142_; 
v___x_2142_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
v___y_2128_ = v___x_2142_;
goto v___jp_2127_;
}
else
{
uint64_t v_hash_2143_; 
v_hash_2143_ = lean_ctor_get_uint64(v_typeName_2118_, sizeof(void*)*2);
v___y_2128_ = v_hash_2143_;
goto v___jp_2127_;
}
v___jp_2127_:
{
uint64_t v___x_2129_; uint64_t v___x_2130_; uint64_t v___x_2131_; uint64_t v___x_2132_; uint64_t v___x_2133_; uint32_t v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; uint8_t v___x_2137_; uint8_t v___x_2138_; uint8_t v___x_2139_; uint64_t v___x_2140_; lean_object* v___x_2141_; 
v___x_2129_ = lean_uint64_of_nat(v_idx_2119_);
v___x_2130_ = l_Lean_Expr_Data_hash(v___x_2121_);
v___x_2131_ = lean_uint64_mix_hash(v___x_2129_, v___x_2130_);
v___x_2132_ = lean_uint64_mix_hash(v___y_2128_, v___x_2131_);
v___x_2133_ = lean_uint64_mix_hash(v___x_2126_, v___x_2132_);
v___x_2134_ = l_Lean_Expr_Data_looseBVarRange(v___x_2121_);
v___x_2135_ = lean_uint32_to_nat(v___x_2134_);
v___x_2136_ = l_Lean_Expr_Data_hasFVar(v___x_2121_);
v___x_2137_ = l_Lean_Expr_Data_hasExprMVar(v___x_2121_);
v___x_2138_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2121_);
v___x_2139_ = l_Lean_Expr_Data_hasLevelParam(v___x_2121_);
v___x_2140_ = lean_expr_mk_data(v___x_2133_, v___x_2135_, v___x_2125_, v___x_2136_, v___x_2137_, v___x_2138_, v___x_2139_);
v___x_2141_ = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(v___x_2141_, 0, v_typeName_2118_);
lean_ctor_set(v___x_2141_, 1, v_idx_2119_);
lean_ctor_set(v___x_2141_, 2, v_struct_2120_);
lean_ctor_set_uint64(v___x_2141_, sizeof(void*)*3, v___x_2140_);
return v___x_2141_;
}
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t v_x_2144_, lean_object* v_x_2145_){
_start:
{
if (lean_obj_tag(v_x_2145_) == 0)
{
return v_x_2144_;
}
else
{
lean_object* v_head_2146_; lean_object* v_tail_2147_; uint64_t v___x_2148_; uint64_t v___x_2149_; 
v_head_2146_ = lean_ctor_get(v_x_2145_, 0);
v_tail_2147_ = lean_ctor_get(v_x_2145_, 1);
v___x_2148_ = l_Lean_Level_hash(v_head_2146_);
v___x_2149_ = lean_uint64_mix_hash(v_x_2144_, v___x_2148_);
v_x_2144_ = v___x_2149_;
v_x_2145_ = v_tail_2147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object* v_x_2151_, lean_object* v_x_2152_){
_start:
{
uint64_t v_x_1680__boxed_2153_; uint64_t v_res_2154_; lean_object* v_r_2155_; 
v_x_1680__boxed_2153_ = lean_unbox_uint64(v_x_2151_);
lean_dec_ref(v_x_2151_);
v_res_2154_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_1680__boxed_2153_, v_x_2152_);
lean_dec(v_x_2152_);
v_r_2155_ = lean_box_uint64(v_res_2154_);
return v_r_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* v_declName_2158_, lean_object* v_us_2159_){
_start:
{
uint64_t v___x_2160_; uint64_t v___y_2162_; 
v___x_2160_ = 5ULL;
if (lean_obj_tag(v_declName_2158_) == 0)
{
uint64_t v___x_2176_; 
v___x_2176_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
v___y_2162_ = v___x_2176_;
goto v___jp_2161_;
}
else
{
uint64_t v_hash_2177_; 
v_hash_2177_ = lean_ctor_get_uint64(v_declName_2158_, sizeof(void*)*2);
v___y_2162_ = v_hash_2177_;
goto v___jp_2161_;
}
v___jp_2161_:
{
uint64_t v___x_2163_; uint64_t v___x_2164_; uint64_t v___x_2165_; uint64_t v___x_2166_; lean_object* v___x_2167_; uint32_t v___x_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; uint64_t v___x_2174_; lean_object* v___x_2175_; 
v___x_2163_ = 7ULL;
v___x_2164_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v___x_2163_, v_us_2159_);
v___x_2165_ = lean_uint64_mix_hash(v___y_2162_, v___x_2164_);
v___x_2166_ = lean_uint64_mix_hash(v___x_2160_, v___x_2165_);
v___x_2167_ = lean_unsigned_to_nat(0u);
v___x_2168_ = 0;
v___x_2169_ = 0;
v___x_2170_ = ((lean_object*)(l_Lean_Expr_const___override___closed__0));
lean_inc_n(v_us_2159_, 2);
v___x_2171_ = l_List_any___redArg(v_us_2159_, v___x_2170_);
v___x_2172_ = ((lean_object*)(l_Lean_Expr_const___override___closed__1));
v___x_2173_ = l_List_any___redArg(v_us_2159_, v___x_2172_);
v___x_2174_ = lean_expr_mk_data(v___x_2166_, v___x_2167_, v___x_2168_, v___x_2169_, v___x_2169_, v___x_2171_, v___x_2173_);
v___x_2175_ = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(v___x_2175_, 0, v_declName_2158_);
lean_ctor_set(v___x_2175_, 1, v_us_2159_);
lean_ctor_set_uint64(v___x_2175_, sizeof(void*)*2, v___x_2174_);
return v___x_2175_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_unsigned_to_nat(0u);
v___x_2180_ = l_Lean_instReprLevel_repr(v___y_2178_, v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2181_, lean_object* v_x_2182_, lean_object* v_x_2183_){
_start:
{
if (lean_obj_tag(v_x_2183_) == 0)
{
lean_dec(v_x_2181_);
return v_x_2182_;
}
else
{
lean_object* v_head_2184_; lean_object* v_tail_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2196_; 
v_head_2184_ = lean_ctor_get(v_x_2183_, 0);
v_tail_2185_ = lean_ctor_get(v_x_2183_, 1);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_x_2183_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2187_ = v_x_2183_;
v_isShared_2188_ = v_isSharedCheck_2196_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_tail_2185_);
lean_inc(v_head_2184_);
lean_dec(v_x_2183_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2196_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
lean_inc(v_x_2181_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set_tag(v___x_2187_, 5);
lean_ctor_set(v___x_2187_, 1, v_x_2181_);
lean_ctor_set(v___x_2187_, 0, v_x_2182_);
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_x_2182_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_x_2181_);
v___x_2190_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = l_Lean_instReprLevel_repr(v_head_2184_, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2190_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v_x_2182_ = v___x_2193_;
v_x_2183_ = v_tail_2185_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object* v_x_2197_, lean_object* v_x_2198_, lean_object* v_x_2199_){
_start:
{
if (lean_obj_tag(v_x_2199_) == 0)
{
lean_dec(v_x_2197_);
return v_x_2198_;
}
else
{
lean_object* v_head_2200_; lean_object* v_tail_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2212_; 
v_head_2200_ = lean_ctor_get(v_x_2199_, 0);
v_tail_2201_ = lean_ctor_get(v_x_2199_, 1);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_x_2199_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2203_ = v_x_2199_;
v_isShared_2204_ = v_isSharedCheck_2212_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_tail_2201_);
lean_inc(v_head_2200_);
lean_dec(v_x_2199_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2212_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
lean_inc(v_x_2197_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set_tag(v___x_2203_, 5);
lean_ctor_set(v___x_2203_, 1, v_x_2197_);
lean_ctor_set(v___x_2203_, 0, v_x_2198_);
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_x_2198_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_x_2197_);
v___x_2206_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2207_ = lean_unsigned_to_nat(0u);
v___x_2208_ = l_Lean_instReprLevel_repr(v_head_2200_, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2206_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(v_x_2197_, v___x_2209_, v_tail_2201_);
return v___x_2210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object* v_x_2213_, lean_object* v_x_2214_){
_start:
{
if (lean_obj_tag(v_x_2213_) == 0)
{
lean_object* v___x_2215_; 
lean_dec(v_x_2214_);
v___x_2215_ = lean_box(0);
return v___x_2215_;
}
else
{
lean_object* v_tail_2216_; 
v_tail_2216_ = lean_ctor_get(v_x_2213_, 1);
if (lean_obj_tag(v_tail_2216_) == 0)
{
lean_object* v_head_2217_; lean_object* v___x_2218_; 
lean_dec(v_x_2214_);
v_head_2217_ = lean_ctor_get(v_x_2213_, 0);
lean_inc(v_head_2217_);
lean_dec_ref(v_x_2213_);
v___x_2218_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2217_);
return v___x_2218_;
}
else
{
lean_object* v_head_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_inc(v_tail_2216_);
v_head_2219_ = lean_ctor_get(v_x_2213_, 0);
lean_inc(v_head_2219_);
lean_dec_ref(v_x_2213_);
v___x_2220_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2219_);
v___x_2221_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(v_x_2214_, v___x_2220_, v_tail_2216_);
return v___x_2221_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2));
v___x_2234_ = lean_string_length(v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7);
v___x_2236_ = lean_nat_to_int(v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object* v_a_2241_){
_start:
{
if (lean_obj_tag(v_a_2241_) == 0)
{
lean_object* v___x_2242_; 
v___x_2242_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1));
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; lean_object* v___x_2252_; 
v___x_2243_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5));
v___x_2244_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(v_a_2241_, v___x_2243_);
v___x_2245_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8);
v___x_2246_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9));
v___x_2247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
lean_ctor_set(v___x_2247_, 1, v___x_2244_);
v___x_2248_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10));
v___x_2249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2247_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2245_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = 0;
v___x_2252_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2252_, 0, v___x_2250_);
lean_ctor_set_uint8(v___x_2252_, sizeof(void*)*1, v___x_2251_);
return v___x_2252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object* v_x_2325_, lean_object* v_prec_2326_){
_start:
{
switch(lean_obj_tag(v_x_2325_))
{
case 0:
{
lean_object* v_deBruijnIndex_2327_; lean_object* v___y_2329_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v_deBruijnIndex_2327_ = lean_ctor_get(v_x_2325_, 0);
lean_inc(v_deBruijnIndex_2327_);
lean_dec_ref(v_x_2325_);
v___x_2338_ = lean_unsigned_to_nat(1024u);
v___x_2339_ = lean_nat_dec_le(v___x_2338_, v_prec_2326_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2329_ = v___x_2340_;
goto v___jp_2328_;
}
else
{
lean_object* v___x_2341_; 
v___x_2341_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2329_ = v___x_2341_;
goto v___jp_2328_;
}
v___jp_2328_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2330_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__2));
v___x_2331_ = l_Nat_reprFast(v_deBruijnIndex_2327_);
v___x_2332_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
v___x_2333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2330_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
lean_inc(v___y_2329_);
v___x_2334_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___y_2329_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = 0;
v___x_2336_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set_uint8(v___x_2336_, sizeof(void*)*1, v___x_2335_);
v___x_2337_ = l_Repr_addAppParen(v___x_2336_, v_prec_2326_);
return v___x_2337_;
}
}
case 1:
{
lean_object* v_fvarId_2342_; lean_object* v___y_2344_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v_fvarId_2342_ = lean_ctor_get(v_x_2325_, 0);
lean_inc(v_fvarId_2342_);
lean_dec_ref(v_x_2325_);
v___x_2353_ = lean_unsigned_to_nat(1024u);
v___x_2354_ = lean_nat_dec_le(v___x_2353_, v_prec_2326_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2344_ = v___x_2355_;
goto v___jp_2343_;
}
else
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2344_ = v___x_2356_;
goto v___jp_2343_;
}
v___jp_2343_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; uint8_t v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2345_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__5));
v___x_2346_ = lean_unsigned_to_nat(1024u);
v___x_2347_ = l_Lean_Name_reprPrec(v_fvarId_2342_, v___x_2346_);
v___x_2348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2345_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
lean_inc(v___y_2344_);
v___x_2349_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___y_2344_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = 0;
v___x_2351_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2351_, 0, v___x_2349_);
lean_ctor_set_uint8(v___x_2351_, sizeof(void*)*1, v___x_2350_);
v___x_2352_ = l_Repr_addAppParen(v___x_2351_, v_prec_2326_);
return v___x_2352_;
}
}
case 2:
{
lean_object* v_mvarId_2357_; lean_object* v___y_2359_; lean_object* v___x_2368_; uint8_t v___x_2369_; 
v_mvarId_2357_ = lean_ctor_get(v_x_2325_, 0);
lean_inc(v_mvarId_2357_);
lean_dec_ref(v_x_2325_);
v___x_2368_ = lean_unsigned_to_nat(1024u);
v___x_2369_ = lean_nat_dec_le(v___x_2368_, v_prec_2326_);
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
v___x_2360_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__8));
v___x_2361_ = lean_unsigned_to_nat(1024u);
v___x_2362_ = l_Lean_Name_reprPrec(v_mvarId_2357_, v___x_2361_);
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
v___x_2367_ = l_Repr_addAppParen(v___x_2366_, v_prec_2326_);
return v___x_2367_;
}
}
case 3:
{
lean_object* v_u_2372_; lean_object* v___y_2374_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v_u_2372_ = lean_ctor_get(v_x_2325_, 0);
lean_inc(v_u_2372_);
lean_dec_ref(v_x_2325_);
v___x_2383_ = lean_unsigned_to_nat(1024u);
v___x_2384_ = lean_nat_dec_le(v___x_2383_, v_prec_2326_);
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
v___x_2375_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__11));
v___x_2376_ = lean_unsigned_to_nat(1024u);
v___x_2377_ = l_Lean_instReprLevel_repr(v_u_2372_, v___x_2376_);
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
v___x_2382_ = l_Repr_addAppParen(v___x_2381_, v_prec_2326_);
return v___x_2382_;
}
}
case 4:
{
lean_object* v_declName_2387_; lean_object* v_us_2388_; lean_object* v___y_2390_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v_declName_2387_ = lean_ctor_get(v_x_2325_, 0);
lean_inc(v_declName_2387_);
v_us_2388_ = lean_ctor_get(v_x_2325_, 1);
lean_inc(v_us_2388_);
lean_dec_ref(v_x_2325_);
v___x_2403_ = lean_unsigned_to_nat(1024u);
v___x_2404_ = lean_nat_dec_le(v___x_2403_, v_prec_2326_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; 
v___x_2405_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2390_ = v___x_2405_;
goto v___jp_2389_;
}
else
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2390_ = v___x_2406_;
goto v___jp_2389_;
}
v___jp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2391_ = lean_box(1);
v___x_2392_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__14));
v___x_2393_ = lean_unsigned_to_nat(1024u);
v___x_2394_ = l_Lean_Name_reprPrec(v_declName_2387_, v___x_2393_);
v___x_2395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2392_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
lean_ctor_set(v___x_2396_, 1, v___x_2391_);
v___x_2397_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_us_2388_);
v___x_2398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2396_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
lean_inc(v___y_2390_);
v___x_2399_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___y_2390_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = 0;
v___x_2401_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set_uint8(v___x_2401_, sizeof(void*)*1, v___x_2400_);
v___x_2402_ = l_Repr_addAppParen(v___x_2401_, v_prec_2326_);
return v___x_2402_;
}
}
case 5:
{
lean_object* v_fn_2407_; lean_object* v_arg_2408_; lean_object* v___x_2409_; lean_object* v___y_2411_; uint8_t v___x_2423_; 
v_fn_2407_ = lean_ctor_get(v_x_2325_, 0);
lean_inc_ref(v_fn_2407_);
v_arg_2408_ = lean_ctor_get(v_x_2325_, 1);
lean_inc_ref(v_arg_2408_);
lean_dec_ref(v_x_2325_);
v___x_2409_ = lean_unsigned_to_nat(1024u);
v___x_2423_ = lean_nat_dec_le(v___x_2409_, v_prec_2326_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2411_ = v___x_2424_;
goto v___jp_2410_;
}
else
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2411_ = v___x_2425_;
goto v___jp_2410_;
}
v___jp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2412_ = lean_box(1);
v___x_2413_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__17));
v___x_2414_ = l_Lean_instReprExpr_repr(v_fn_2407_, v___x_2409_);
v___x_2415_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2413_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
lean_ctor_set(v___x_2416_, 1, v___x_2412_);
v___x_2417_ = l_Lean_instReprExpr_repr(v_arg_2408_, v___x_2409_);
v___x_2418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
lean_inc(v___y_2411_);
v___x_2419_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___y_2411_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
v___x_2420_ = 0;
v___x_2421_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2421_, 0, v___x_2419_);
lean_ctor_set_uint8(v___x_2421_, sizeof(void*)*1, v___x_2420_);
v___x_2422_ = l_Repr_addAppParen(v___x_2421_, v_prec_2326_);
return v___x_2422_;
}
}
case 6:
{
lean_object* v_binderName_2426_; lean_object* v_binderType_2427_; lean_object* v_body_2428_; uint8_t v_binderInfo_2429_; lean_object* v___x_2430_; lean_object* v___y_2432_; uint8_t v___x_2450_; 
v_binderName_2426_ = lean_ctor_get(v_x_2325_, 0);
lean_inc(v_binderName_2426_);
v_binderType_2427_ = lean_ctor_get(v_x_2325_, 1);
lean_inc_ref(v_binderType_2427_);
v_body_2428_ = lean_ctor_get(v_x_2325_, 2);
lean_inc_ref(v_body_2428_);
v_binderInfo_2429_ = lean_ctor_get_uint8(v_x_2325_, sizeof(void*)*3 + 8);
lean_dec_ref(v_x_2325_);
v___x_2430_ = lean_unsigned_to_nat(1024u);
v___x_2450_ = lean_nat_dec_le(v___x_2430_, v_prec_2326_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2432_ = v___x_2451_;
goto v___jp_2431_;
}
else
{
lean_object* v___x_2452_; 
v___x_2452_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2432_ = v___x_2452_;
goto v___jp_2431_;
}
v___jp_2431_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2433_ = lean_box(1);
v___x_2434_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__20));
v___x_2435_ = l_Lean_Name_reprPrec(v_binderName_2426_, v___x_2430_);
v___x_2436_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
lean_ctor_set(v___x_2437_, 1, v___x_2433_);
v___x_2438_ = l_Lean_instReprExpr_repr(v_binderType_2427_, v___x_2430_);
v___x_2439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
lean_ctor_set(v___x_2440_, 1, v___x_2433_);
v___x_2441_ = l_Lean_instReprExpr_repr(v_body_2428_, v___x_2430_);
v___x_2442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2440_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
lean_ctor_set(v___x_2443_, 1, v___x_2433_);
v___x_2444_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2429_, v___x_2430_);
v___x_2445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2443_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
lean_inc(v___y_2432_);
v___x_2446_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___y_2432_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = 0;
v___x_2448_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*1, v___x_2447_);
v___x_2449_ = l_Repr_addAppParen(v___x_2448_, v_prec_2326_);
return v___x_2449_;
}
}
case 7:
{
lean_object* v_binderName_2453_; lean_object* v_binderType_2454_; lean_object* v_body_2455_; uint8_t v_binderInfo_2456_; lean_object* v___x_2457_; lean_object* v___y_2459_; uint8_t v___x_2477_; 
v_binderName_2453_ = lean_ctor_get(v_x_2325_, 0);
lean_inc(v_binderName_2453_);
v_binderType_2454_ = lean_ctor_get(v_x_2325_, 1);
lean_inc_ref(v_binderType_2454_);
v_body_2455_ = lean_ctor_get(v_x_2325_, 2);
lean_inc_ref(v_body_2455_);
v_binderInfo_2456_ = lean_ctor_get_uint8(v_x_2325_, sizeof(void*)*3 + 8);
lean_dec_ref(v_x_2325_);
v___x_2457_ = lean_unsigned_to_nat(1024u);
v___x_2477_ = lean_nat_dec_le(v___x_2457_, v_prec_2326_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; 
v___x_2478_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2459_ = v___x_2478_;
goto v___jp_2458_;
}
else
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2459_ = v___x_2479_;
goto v___jp_2458_;
}
v___jp_2458_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2460_ = lean_box(1);
v___x_2461_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__23));
v___x_2462_ = l_Lean_Name_reprPrec(v_binderName_2453_, v___x_2457_);
v___x_2463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v___x_2460_);
v___x_2465_ = l_Lean_instReprExpr_repr(v_binderType_2454_, v___x_2457_);
v___x_2466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
lean_ctor_set(v___x_2467_, 1, v___x_2460_);
v___x_2468_ = l_Lean_instReprExpr_repr(v_body_2455_, v___x_2457_);
v___x_2469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
lean_ctor_set(v___x_2470_, 1, v___x_2460_);
v___x_2471_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2456_, v___x_2457_);
v___x_2472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
lean_inc(v___y_2459_);
v___x_2473_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___y_2459_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = 0;
v___x_2475_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*1, v___x_2474_);
v___x_2476_ = l_Repr_addAppParen(v___x_2475_, v_prec_2326_);
return v___x_2476_;
}
}
case 8:
{
lean_object* v_declName_2480_; lean_object* v_type_2481_; lean_object* v_value_2482_; lean_object* v_body_2483_; uint8_t v_nondep_2484_; lean_object* v___x_2485_; lean_object* v___y_2487_; uint8_t v___x_2508_; 
v_declName_2480_ = lean_ctor_get(v_x_2325_, 0);
lean_inc(v_declName_2480_);
v_type_2481_ = lean_ctor_get(v_x_2325_, 1);
lean_inc_ref(v_type_2481_);
v_value_2482_ = lean_ctor_get(v_x_2325_, 2);
lean_inc_ref(v_value_2482_);
v_body_2483_ = lean_ctor_get(v_x_2325_, 3);
lean_inc_ref(v_body_2483_);
v_nondep_2484_ = lean_ctor_get_uint8(v_x_2325_, sizeof(void*)*4 + 8);
lean_dec_ref(v_x_2325_);
v___x_2485_ = lean_unsigned_to_nat(1024u);
v___x_2508_ = lean_nat_dec_le(v___x_2485_, v_prec_2326_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2487_ = v___x_2509_;
goto v___jp_2486_;
}
else
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2487_ = v___x_2510_;
goto v___jp_2486_;
}
v___jp_2486_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2488_ = lean_box(1);
v___x_2489_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__26));
v___x_2490_ = l_Lean_Name_reprPrec(v_declName_2480_, v___x_2485_);
v___x_2491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2489_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
v___x_2492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
lean_ctor_set(v___x_2492_, 1, v___x_2488_);
v___x_2493_ = l_Lean_instReprExpr_repr(v_type_2481_, v___x_2485_);
v___x_2494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2492_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
lean_ctor_set(v___x_2495_, 1, v___x_2488_);
v___x_2496_ = l_Lean_instReprExpr_repr(v_value_2482_, v___x_2485_);
v___x_2497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2495_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
lean_ctor_set(v___x_2498_, 1, v___x_2488_);
v___x_2499_ = l_Lean_instReprExpr_repr(v_body_2483_, v___x_2485_);
v___x_2500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2498_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
lean_ctor_set(v___x_2501_, 1, v___x_2488_);
v___x_2502_ = l_Bool_repr___redArg(v_nondep_2484_);
v___x_2503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
lean_inc(v___y_2487_);
v___x_2504_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___y_2487_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = 0;
v___x_2506_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2506_, 0, v___x_2504_);
lean_ctor_set_uint8(v___x_2506_, sizeof(void*)*1, v___x_2505_);
v___x_2507_ = l_Repr_addAppParen(v___x_2506_, v_prec_2326_);
return v___x_2507_;
}
}
case 9:
{
lean_object* v_a_2511_; lean_object* v___y_2513_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v_a_2511_ = lean_ctor_get(v_x_2325_, 0);
lean_inc_ref(v_a_2511_);
lean_dec_ref(v_x_2325_);
v___x_2522_ = lean_unsigned_to_nat(1024u);
v___x_2523_ = lean_nat_dec_le(v___x_2522_, v_prec_2326_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2513_ = v___x_2524_;
goto v___jp_2512_;
}
else
{
lean_object* v___x_2525_; 
v___x_2525_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2513_ = v___x_2525_;
goto v___jp_2512_;
}
v___jp_2512_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2514_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__29));
v___x_2515_ = lean_unsigned_to_nat(1024u);
v___x_2516_ = l_Lean_instReprLiteral_repr(v_a_2511_, v___x_2515_);
v___x_2517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2514_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
lean_inc(v___y_2513_);
v___x_2518_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___y_2513_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = 0;
v___x_2520_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set_uint8(v___x_2520_, sizeof(void*)*1, v___x_2519_);
v___x_2521_ = l_Repr_addAppParen(v___x_2520_, v_prec_2326_);
return v___x_2521_;
}
}
case 10:
{
lean_object* v_data_2526_; lean_object* v_expr_2527_; lean_object* v___x_2528_; lean_object* v___y_2530_; uint8_t v___x_2542_; 
v_data_2526_ = lean_ctor_get(v_x_2325_, 0);
lean_inc(v_data_2526_);
v_expr_2527_ = lean_ctor_get(v_x_2325_, 1);
lean_inc_ref(v_expr_2527_);
lean_dec_ref(v_x_2325_);
v___x_2528_ = lean_unsigned_to_nat(1024u);
v___x_2542_ = lean_nat_dec_le(v___x_2528_, v_prec_2326_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2530_ = v___x_2543_;
goto v___jp_2529_;
}
else
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2530_ = v___x_2544_;
goto v___jp_2529_;
}
v___jp_2529_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2531_ = lean_box(1);
v___x_2532_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__32));
v___x_2533_ = l_Lean_instReprKVMap_repr___redArg(v_data_2526_);
v___x_2534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2532_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
lean_ctor_set(v___x_2535_, 1, v___x_2531_);
v___x_2536_ = l_Lean_instReprExpr_repr(v_expr_2527_, v___x_2528_);
v___x_2537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
lean_inc(v___y_2530_);
v___x_2538_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___y_2530_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = 0;
v___x_2540_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2540_, 0, v___x_2538_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*1, v___x_2539_);
v___x_2541_ = l_Repr_addAppParen(v___x_2540_, v_prec_2326_);
return v___x_2541_;
}
}
default: 
{
lean_object* v_typeName_2545_; lean_object* v_idx_2546_; lean_object* v_struct_2547_; lean_object* v___x_2548_; lean_object* v___y_2550_; uint8_t v___x_2566_; 
v_typeName_2545_ = lean_ctor_get(v_x_2325_, 0);
lean_inc(v_typeName_2545_);
v_idx_2546_ = lean_ctor_get(v_x_2325_, 1);
lean_inc(v_idx_2546_);
v_struct_2547_ = lean_ctor_get(v_x_2325_, 2);
lean_inc_ref(v_struct_2547_);
lean_dec_ref(v_x_2325_);
v___x_2548_ = lean_unsigned_to_nat(1024u);
v___x_2566_ = lean_nat_dec_le(v___x_2548_, v_prec_2326_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2550_ = v___x_2567_;
goto v___jp_2549_;
}
else
{
lean_object* v___x_2568_; 
v___x_2568_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2550_ = v___x_2568_;
goto v___jp_2549_;
}
v___jp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2551_ = lean_box(1);
v___x_2552_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__35));
v___x_2553_ = l_Lean_Name_reprPrec(v_typeName_2545_, v___x_2548_);
v___x_2554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set(v___x_2555_, 1, v___x_2551_);
v___x_2556_ = l_Nat_reprFast(v_idx_2546_);
v___x_2557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
v___x_2558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2555_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set(v___x_2559_, 1, v___x_2551_);
v___x_2560_ = l_Lean_instReprExpr_repr(v_struct_2547_, v___x_2548_);
v___x_2561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2559_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
lean_inc(v___y_2550_);
v___x_2562_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___y_2550_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___x_2563_ = 0;
v___x_2564_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2564_, 0, v___x_2562_);
lean_ctor_set_uint8(v___x_2564_, sizeof(void*)*1, v___x_2563_);
v___x_2565_ = l_Repr_addAppParen(v___x_2564_, v_prec_2326_);
return v___x_2565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object* v_x_2569_, lean_object* v_prec_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_instReprExpr_repr(v_x_2569_, v_prec_2570_);
lean_dec(v_prec_2570_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object* v_a_2572_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_nat_to_int(v_a_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object* v_a_2574_, lean_object* v_n_2575_){
_start:
{
lean_object* v___x_2576_; 
v___x_2576_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_a_2574_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object* v_a_2577_, lean_object* v_n_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0(v_a_2577_, v_n_2578_);
lean_dec(v_n_2578_);
return v_res_2579_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__2(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = lean_box(0);
v___x_2586_ = ((lean_object*)(l_Lean_instInhabitedExpr___closed__1));
v___x_2587_ = l_Lean_Expr_const___override(v___x_2586_, v___x_2585_);
return v___x_2587_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr(void){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* v_x_2601_){
_start:
{
switch(lean_obj_tag(v_x_2601_))
{
case 0:
{
lean_object* v___x_2602_; 
v___x_2602_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__0));
return v___x_2602_;
}
case 1:
{
lean_object* v___x_2603_; 
v___x_2603_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__1));
return v___x_2603_;
}
case 2:
{
lean_object* v___x_2604_; 
v___x_2604_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__2));
return v___x_2604_;
}
case 3:
{
lean_object* v___x_2605_; 
v___x_2605_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__3));
return v___x_2605_;
}
case 4:
{
lean_object* v___x_2606_; 
v___x_2606_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__4));
return v___x_2606_;
}
case 5:
{
lean_object* v___x_2607_; 
v___x_2607_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__5));
return v___x_2607_;
}
case 6:
{
lean_object* v___x_2608_; 
v___x_2608_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__6));
return v___x_2608_;
}
case 7:
{
lean_object* v___x_2609_; 
v___x_2609_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__7));
return v___x_2609_;
}
case 8:
{
lean_object* v___x_2610_; 
v___x_2610_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__8));
return v___x_2610_;
}
case 9:
{
lean_object* v___x_2611_; 
v___x_2611_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__9));
return v___x_2611_;
}
case 10:
{
lean_object* v___x_2612_; 
v___x_2612_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__10));
return v___x_2612_;
}
default: 
{
lean_object* v___x_2613_; 
v___x_2613_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__11));
return v___x_2613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* v_x_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_Expr_ctorName(v_x_2614_);
lean_dec_ref(v_x_2614_);
return v_res_2615_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object* v_e_2616_){
_start:
{
uint64_t v___x_2617_; uint64_t v___x_2618_; 
v___x_2617_ = lean_expr_data(v_e_2616_);
v___x_2618_ = l_Lean_Expr_Data_hash(v___x_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* v_e_2619_){
_start:
{
uint64_t v_res_2620_; lean_object* v_r_2621_; 
v_res_2620_ = l_Lean_Expr_hash(v_e_2619_);
lean_dec_ref(v_e_2619_);
v_r_2621_ = lean_box_uint64(v_res_2620_);
return v_r_2621_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object* v_e_2624_){
_start:
{
uint64_t v___x_2625_; uint8_t v___x_2626_; 
v___x_2625_ = lean_expr_data(v_e_2624_);
v___x_2626_ = l_Lean_Expr_Data_hasFVar(v___x_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* v_e_2627_){
_start:
{
uint8_t v_res_2628_; lean_object* v_r_2629_; 
v_res_2628_ = l_Lean_Expr_hasFVar(v_e_2627_);
lean_dec_ref(v_e_2627_);
v_r_2629_ = lean_box(v_res_2628_);
return v_r_2629_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object* v_e_2630_){
_start:
{
uint64_t v___x_2631_; uint8_t v___x_2632_; 
v___x_2631_ = lean_expr_data(v_e_2630_);
v___x_2632_ = l_Lean_Expr_Data_hasExprMVar(v___x_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* v_e_2633_){
_start:
{
uint8_t v_res_2634_; lean_object* v_r_2635_; 
v_res_2634_ = l_Lean_Expr_hasExprMVar(v_e_2633_);
lean_dec_ref(v_e_2633_);
v_r_2635_ = lean_box(v_res_2634_);
return v_r_2635_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object* v_e_2636_){
_start:
{
uint64_t v___x_2637_; uint8_t v___x_2638_; 
v___x_2637_ = lean_expr_data(v_e_2636_);
v___x_2638_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* v_e_2639_){
_start:
{
uint8_t v_res_2640_; lean_object* v_r_2641_; 
v_res_2640_ = l_Lean_Expr_hasLevelMVar(v_e_2639_);
lean_dec_ref(v_e_2639_);
v_r_2641_ = lean_box(v_res_2640_);
return v_r_2641_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object* v_e_2642_){
_start:
{
uint64_t v_d_2643_; uint8_t v___x_2644_; 
v_d_2643_ = lean_expr_data(v_e_2642_);
v___x_2644_ = l_Lean_Expr_Data_hasExprMVar(v_d_2643_);
if (v___x_2644_ == 0)
{
uint8_t v___x_2645_; 
v___x_2645_ = l_Lean_Expr_Data_hasLevelMVar(v_d_2643_);
return v___x_2645_;
}
else
{
return v___x_2644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* v_e_2646_){
_start:
{
uint8_t v_res_2647_; lean_object* v_r_2648_; 
v_res_2647_ = l_Lean_Expr_hasMVar(v_e_2646_);
lean_dec_ref(v_e_2646_);
v_r_2648_ = lean_box(v_res_2647_);
return v_r_2648_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object* v_e_2649_){
_start:
{
uint64_t v___x_2650_; uint8_t v___x_2651_; 
v___x_2650_ = lean_expr_data(v_e_2649_);
v___x_2651_ = l_Lean_Expr_Data_hasLevelParam(v___x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* v_e_2652_){
_start:
{
uint8_t v_res_2653_; lean_object* v_r_2654_; 
v_res_2653_ = l_Lean_Expr_hasLevelParam(v_e_2652_);
lean_dec_ref(v_e_2652_);
v_r_2654_ = lean_box(v_res_2653_);
return v_r_2654_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object* v_e_2655_){
_start:
{
uint64_t v___x_2656_; uint8_t v___x_2657_; uint32_t v___x_2658_; 
v___x_2656_ = lean_expr_data(v_e_2655_);
v___x_2657_ = l_Lean_Expr_Data_approxDepth(v___x_2656_);
v___x_2658_ = lean_uint8_to_uint32(v___x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* v_e_2659_){
_start:
{
uint32_t v_res_2660_; lean_object* v_r_2661_; 
v_res_2660_ = l_Lean_Expr_approxDepth(v_e_2659_);
lean_dec_ref(v_e_2659_);
v_r_2661_ = lean_box_uint32(v_res_2660_);
return v_r_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* v_e_2662_){
_start:
{
uint64_t v___x_2663_; uint32_t v___x_2664_; lean_object* v___x_2665_; 
v___x_2663_ = lean_expr_data(v_e_2662_);
v___x_2664_ = l_Lean_Expr_Data_looseBVarRange(v___x_2663_);
v___x_2665_ = lean_uint32_to_nat(v___x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* v_e_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_Expr_looseBVarRange(v_e_2666_);
lean_dec_ref(v_e_2666_);
return v_res_2667_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object* v_e_2668_){
_start:
{
switch(lean_obj_tag(v_e_2668_))
{
case 7:
{
uint8_t v_binderInfo_2669_; 
v_binderInfo_2669_ = lean_ctor_get_uint8(v_e_2668_, sizeof(void*)*3 + 8);
return v_binderInfo_2669_;
}
case 6:
{
uint8_t v_binderInfo_2670_; 
v_binderInfo_2670_ = lean_ctor_get_uint8(v_e_2668_, sizeof(void*)*3 + 8);
return v_binderInfo_2670_;
}
default: 
{
uint8_t v___x_2671_; 
v___x_2671_ = 0;
return v___x_2671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* v_e_2672_){
_start:
{
uint8_t v_res_2673_; lean_object* v_r_2674_; 
v_res_2673_ = l_Lean_Expr_binderInfo(v_e_2672_);
lean_dec_ref(v_e_2672_);
v_r_2674_ = lean_box(v_res_2673_);
return v_r_2674_;
}
}
LEAN_EXPORT uint64_t lean_expr_hash(lean_object* v_a_2675_){
_start:
{
uint64_t v___x_2676_; 
v___x_2676_ = l_Lean_Expr_hash(v_a_2675_);
lean_dec_ref(v_a_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* v_a_2677_){
_start:
{
uint64_t v_res_2678_; lean_object* v_r_2679_; 
v_res_2678_ = lean_expr_hash(v_a_2677_);
v_r_2679_ = lean_box_uint64(v_res_2678_);
return v_r_2679_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object* v_e_2680_){
_start:
{
uint8_t v___x_2681_; 
v___x_2681_ = l_Lean_Expr_hasFVar(v_e_2680_);
lean_dec_ref(v_e_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* v_e_2682_){
_start:
{
uint8_t v_res_2683_; lean_object* v_r_2684_; 
v_res_2683_ = lean_expr_has_fvar(v_e_2682_);
v_r_2684_ = lean_box(v_res_2683_);
return v_r_2684_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object* v_e_2685_){
_start:
{
uint8_t v___x_2686_; 
v___x_2686_ = l_Lean_Expr_hasExprMVar(v_e_2685_);
lean_dec_ref(v_e_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* v_e_2687_){
_start:
{
uint8_t v_res_2688_; lean_object* v_r_2689_; 
v_res_2688_ = lean_expr_has_expr_mvar(v_e_2687_);
v_r_2689_ = lean_box(v_res_2688_);
return v_r_2689_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object* v_e_2690_){
_start:
{
uint8_t v___x_2691_; 
v___x_2691_ = l_Lean_Expr_hasLevelMVar(v_e_2690_);
lean_dec_ref(v_e_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* v_e_2692_){
_start:
{
uint8_t v_res_2693_; lean_object* v_r_2694_; 
v_res_2693_ = lean_expr_has_level_mvar(v_e_2692_);
v_r_2694_ = lean_box(v_res_2693_);
return v_r_2694_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_mvar(lean_object* v_e_2695_){
_start:
{
uint8_t v___x_2696_; 
v___x_2696_ = l_Lean_Expr_hasMVar(v_e_2695_);
lean_dec_ref(v_e_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVarEx___boxed(lean_object* v_e_2697_){
_start:
{
uint8_t v_res_2698_; lean_object* v_r_2699_; 
v_res_2698_ = lean_expr_has_mvar(v_e_2697_);
v_r_2699_ = lean_box(v_res_2698_);
return v_r_2699_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* v_e_2700_){
_start:
{
uint8_t v___x_2701_; 
v___x_2701_ = l_Lean_Expr_hasLevelParam(v_e_2700_);
lean_dec_ref(v_e_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* v_e_2702_){
_start:
{
uint8_t v_res_2703_; lean_object* v_r_2704_; 
v_res_2703_ = lean_expr_has_level_param(v_e_2702_);
v_r_2704_ = lean_box(v_res_2703_);
return v_r_2704_;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* v_e_2705_){
_start:
{
uint64_t v___x_2706_; uint32_t v___x_2707_; 
v___x_2706_ = lean_expr_data(v_e_2705_);
lean_dec_ref(v_e_2705_);
v___x_2707_ = l_Lean_Expr_Data_looseBVarRange(v___x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* v_e_2708_){
_start:
{
uint32_t v_res_2709_; lean_object* v_r_2710_; 
v_res_2709_ = lean_expr_loose_bvar_range(v_e_2708_);
v_r_2710_ = lean_box_uint32(v_res_2709_);
return v_r_2710_;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* v_e_2711_){
_start:
{
uint8_t v___x_2712_; 
v___x_2712_ = l_Lean_Expr_binderInfo(v_e_2711_);
lean_dec_ref(v_e_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* v_e_2713_){
_start:
{
uint8_t v_res_2714_; lean_object* v_r_2715_; 
v_res_2714_ = lean_expr_binder_info(v_e_2713_);
v_r_2715_ = lean_box(v_res_2714_);
return v_r_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* v_declName_2716_, lean_object* v_us_2717_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_Expr_const___override(v_declName_2716_, v_us_2717_);
return v___x_2718_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2722_ = lean_box(0);
v___x_2723_ = ((lean_object*)(l_Lean_Literal_type___closed__1));
v___x_2724_ = l_Lean_Expr_const___override(v___x_2723_, v___x_2722_);
return v___x_2724_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2728_ = lean_box(0);
v___x_2729_ = ((lean_object*)(l_Lean_Literal_type___closed__4));
v___x_2730_ = l_Lean_Expr_const___override(v___x_2729_, v___x_2728_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* v_x_2731_){
_start:
{
if (lean_obj_tag(v_x_2731_) == 0)
{
lean_object* v___x_2732_; 
v___x_2732_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_2732_;
}
else
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_obj_once(&l_Lean_Literal_type___closed__5, &l_Lean_Literal_type___closed__5_once, _init_l_Lean_Literal_type___closed__5);
return v___x_2733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* v_x_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_Literal_type(v_x_2734_);
lean_dec_ref(v_x_2734_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* v_a_2736_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Lean_Literal_type(v_a_2736_);
lean_dec_ref(v_a_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* v_idx_2738_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_Expr_bvar___override(v_idx_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* v_u_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_Expr_sort___override(v_u_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* v_fvarId_2742_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_Expr_fvar___override(v_fvarId_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* v_mvarId_2744_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_Expr_mvar___override(v_mvarId_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* v_m_2746_, lean_object* v_e_2747_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_Expr_mdata___override(v_m_2746_, v_e_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* v_structName_2749_, lean_object* v_idx_2750_, lean_object* v_struct_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Lean_Expr_proj___override(v_structName_2749_, v_idx_2750_, v_struct_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* v_f_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_Expr_app___override(v_f_2753_, v_a_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* v_x_2756_, uint8_t v_bi_2757_, lean_object* v_t_2758_, lean_object* v_b_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_Expr_lam___override(v_x_2756_, v_t_2758_, v_b_2759_, v_bi_2757_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* v_x_2761_, lean_object* v_bi_2762_, lean_object* v_t_2763_, lean_object* v_b_2764_){
_start:
{
uint8_t v_bi_boxed_2765_; lean_object* v_res_2766_; 
v_bi_boxed_2765_ = lean_unbox(v_bi_2762_);
v_res_2766_ = l_Lean_mkLambda(v_x_2761_, v_bi_boxed_2765_, v_t_2763_, v_b_2764_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* v_x_2767_, uint8_t v_bi_2768_, lean_object* v_t_2769_, lean_object* v_b_2770_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_Expr_forallE___override(v_x_2767_, v_t_2769_, v_b_2770_, v_bi_2768_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* v_x_2772_, lean_object* v_bi_2773_, lean_object* v_t_2774_, lean_object* v_b_2775_){
_start:
{
uint8_t v_bi_boxed_2776_; lean_object* v_res_2777_; 
v_bi_boxed_2776_ = lean_unbox(v_bi_2773_);
v_res_2777_ = l_Lean_mkForall(v_x_2772_, v_bi_boxed_2776_, v_t_2774_, v_b_2775_);
return v_res_2777_;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__2(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2781_ = lean_box(0);
v___x_2782_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2783_ = l_Lean_Expr_const___override(v___x_2782_, v___x_2781_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* v_type_2784_){
_start:
{
lean_object* v___x_2785_; uint8_t v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2785_ = lean_box(0);
v___x_2786_ = 0;
v___x_2787_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__2, &l_Lean_mkSimpleThunkType___closed__2_once, _init_l_Lean_mkSimpleThunkType___closed__2);
v___x_2788_ = l_Lean_Expr_forallE___override(v___x_2785_, v___x_2787_, v_type_2784_, v___x_2786_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* v_type_2792_){
_start:
{
lean_object* v___x_2793_; uint8_t v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2793_ = ((lean_object*)(l_Lean_mkSimpleThunk___closed__1));
v___x_2794_ = 0;
v___x_2795_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__2, &l_Lean_mkSimpleThunkType___closed__2_once, _init_l_Lean_mkSimpleThunkType___closed__2);
v___x_2796_ = l_Lean_Expr_lam___override(v___x_2793_, v___x_2795_, v_type_2792_, v___x_2794_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* v_x_2797_, lean_object* v_t_2798_, lean_object* v_v_2799_, lean_object* v_b_2800_, uint8_t v_nondep_2801_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l_Lean_Expr_letE___override(v_x_2797_, v_t_2798_, v_v_2799_, v_b_2800_, v_nondep_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* v_x_2803_, lean_object* v_t_2804_, lean_object* v_v_2805_, lean_object* v_b_2806_, lean_object* v_nondep_2807_){
_start:
{
uint8_t v_nondep_boxed_2808_; lean_object* v_res_2809_; 
v_nondep_boxed_2808_ = lean_unbox(v_nondep_2807_);
v_res_2809_ = l_Lean_mkLet(v_x_2803_, v_t_2804_, v_v_2805_, v_b_2806_, v_nondep_boxed_2808_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object* v_x_2810_, lean_object* v_t_2811_, lean_object* v_v_2812_, lean_object* v_b_2813_){
_start:
{
uint8_t v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = 1;
v___x_2815_ = l_Lean_Expr_letE___override(v_x_2810_, v_t_2811_, v_v_2812_, v_b_2813_, v___x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* v_f_2816_, lean_object* v_a_2817_, lean_object* v_b_2818_){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = l_Lean_Expr_app___override(v_f_2816_, v_a_2817_);
v___x_2820_ = l_Lean_Expr_app___override(v___x_2819_, v_b_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* v_f_2821_, lean_object* v_a_2822_, lean_object* v_b_2823_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_mkAppB(v_f_2821_, v_a_2822_, v_b_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* v_f_2825_, lean_object* v_a_2826_, lean_object* v_b_2827_, lean_object* v_c_2828_){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = l_Lean_mkAppB(v_f_2825_, v_a_2826_, v_b_2827_);
v___x_2830_ = l_Lean_Expr_app___override(v___x_2829_, v_c_2828_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* v_f_2831_, lean_object* v_a_2832_, lean_object* v_b_2833_, lean_object* v_c_2834_, lean_object* v_d_2835_){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = l_Lean_mkAppB(v_f_2831_, v_a_2832_, v_b_2833_);
v___x_2837_ = l_Lean_mkAppB(v___x_2836_, v_c_2834_, v_d_2835_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* v_f_2838_, lean_object* v_a_2839_, lean_object* v_b_2840_, lean_object* v_c_2841_, lean_object* v_d_2842_, lean_object* v_e_2843_){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = l_Lean_mkApp4(v_f_2838_, v_a_2839_, v_b_2840_, v_c_2841_, v_d_2842_);
v___x_2845_ = l_Lean_Expr_app___override(v___x_2844_, v_e_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* v_f_2846_, lean_object* v_a_2847_, lean_object* v_b_2848_, lean_object* v_c_2849_, lean_object* v_d_2850_, lean_object* v_e_u2081_2851_, lean_object* v_e_u2082_2852_){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = l_Lean_mkApp4(v_f_2846_, v_a_2847_, v_b_2848_, v_c_2849_, v_d_2850_);
v___x_2854_ = l_Lean_mkAppB(v___x_2853_, v_e_u2081_2851_, v_e_u2082_2852_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* v_f_2855_, lean_object* v_a_2856_, lean_object* v_b_2857_, lean_object* v_c_2858_, lean_object* v_d_2859_, lean_object* v_e_u2081_2860_, lean_object* v_e_u2082_2861_, lean_object* v_e_u2083_2862_){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = l_Lean_mkApp4(v_f_2855_, v_a_2856_, v_b_2857_, v_c_2858_, v_d_2859_);
v___x_2864_ = l_Lean_mkApp3(v___x_2863_, v_e_u2081_2860_, v_e_u2082_2861_, v_e_u2083_2862_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* v_f_2865_, lean_object* v_a_2866_, lean_object* v_b_2867_, lean_object* v_c_2868_, lean_object* v_d_2869_, lean_object* v_e_u2081_2870_, lean_object* v_e_u2082_2871_, lean_object* v_e_u2083_2872_, lean_object* v_e_u2084_2873_){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = l_Lean_mkApp4(v_f_2865_, v_a_2866_, v_b_2867_, v_c_2868_, v_d_2869_);
v___x_2875_ = l_Lean_mkApp4(v___x_2874_, v_e_u2081_2870_, v_e_u2082_2871_, v_e_u2083_2872_, v_e_u2084_2873_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* v_f_2876_, lean_object* v_a_2877_, lean_object* v_b_2878_, lean_object* v_c_2879_, lean_object* v_d_2880_, lean_object* v_e_u2081_2881_, lean_object* v_e_u2082_2882_, lean_object* v_e_u2083_2883_, lean_object* v_e_u2084_2884_, lean_object* v_e_u2085_2885_){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = l_Lean_mkApp4(v_f_2876_, v_a_2877_, v_b_2878_, v_c_2879_, v_d_2880_);
v___x_2887_ = l_Lean_mkApp5(v___x_2886_, v_e_u2081_2881_, v_e_u2082_2882_, v_e_u2083_2883_, v_e_u2084_2884_, v_e_u2085_2885_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* v_f_2888_, lean_object* v_a_2889_, lean_object* v_b_2890_, lean_object* v_c_2891_, lean_object* v_d_2892_, lean_object* v_e_u2081_2893_, lean_object* v_e_u2082_2894_, lean_object* v_e_u2083_2895_, lean_object* v_e_u2084_2896_, lean_object* v_e_u2085_2897_, lean_object* v_e_u2086_2898_){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = l_Lean_mkApp4(v_f_2888_, v_a_2889_, v_b_2890_, v_c_2891_, v_d_2892_);
v___x_2900_ = l_Lean_mkApp6(v___x_2899_, v_e_u2081_2893_, v_e_u2082_2894_, v_e_u2083_2895_, v_e_u2084_2896_, v_e_u2085_2897_, v_e_u2086_2898_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* v_l_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Lean_Expr_lit___override(v_l_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* v_n_2903_){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2904_, 0, v_n_2903_);
v___x_2905_ = l_Lean_Expr_lit___override(v___x_2904_);
return v___x_2905_;
}
}
static lean_object* _init_l_Lean_mkInstOfNatNat___closed__2(void){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2909_ = lean_box(0);
v___x_2910_ = ((lean_object*)(l_Lean_mkInstOfNatNat___closed__1));
v___x_2911_ = l_Lean_Expr_const___override(v___x_2910_, v___x_2909_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object* v_n_2912_){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_obj_once(&l_Lean_mkInstOfNatNat___closed__2, &l_Lean_mkInstOfNatNat___closed__2_once, _init_l_Lean_mkInstOfNatNat___closed__2);
v___x_2914_ = l_Lean_Expr_app___override(v___x_2913_, v_n_2912_);
return v___x_2914_;
}
}
static lean_object* _init_l_Lean_mkNatLitCore___closed__4(void){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2923_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_2924_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_2925_ = l_Lean_Expr_const___override(v___x_2924_, v___x_2923_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object* v_n_2926_){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2927_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_2928_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
lean_inc_ref(v_n_2926_);
v___x_2929_ = l_Lean_mkInstOfNatNat(v_n_2926_);
v___x_2930_ = l_Lean_mkApp3(v___x_2927_, v___x_2928_, v_n_2926_, v___x_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* v_n_2931_){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = l_Lean_mkRawNatLit(v_n_2931_);
v___x_2933_ = l_Lean_mkNatLitCore(v___x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* v_s_2934_){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2935_, 0, v_s_2934_);
v___x_2936_ = l_Lean_Expr_lit___override(v___x_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* v_idx_2937_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_Expr_bvar___override(v_idx_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* v_fvarId_2939_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_Expr_fvar___override(v_fvarId_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object* v_mvarId_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_Expr_mvar___override(v_mvarId_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Expr_sort___override(v_u_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_2945_, lean_object* v_lvls_2946_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = l_Lean_Expr_const___override(v_c_2945_, v_lvls_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_2948_, lean_object* v_a_2949_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Lean_Expr_app___override(v_f_2948_, v_a_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* v_n_2951_, lean_object* v_d_2952_, lean_object* v_b_2953_, uint8_t v_bi_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Expr_lam___override(v_n_2951_, v_d_2952_, v_b_2953_, v_bi_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_2956_, lean_object* v_d_2957_, lean_object* v_b_2958_, lean_object* v_bi_2959_){
_start:
{
uint8_t v_bi_boxed_2960_; lean_object* v_res_2961_; 
v_bi_boxed_2960_ = lean_unbox(v_bi_2959_);
v_res_2961_ = lean_expr_mk_lambda(v_n_2956_, v_d_2957_, v_b_2958_, v_bi_boxed_2960_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* v_n_2962_, lean_object* v_d_2963_, lean_object* v_b_2964_, uint8_t v_bi_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_Expr_forallE___override(v_n_2962_, v_d_2963_, v_b_2964_, v_bi_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_2967_, lean_object* v_d_2968_, lean_object* v_b_2969_, lean_object* v_bi_2970_){
_start:
{
uint8_t v_bi_boxed_2971_; lean_object* v_res_2972_; 
v_bi_boxed_2971_ = lean_unbox(v_bi_2970_);
v_res_2972_ = lean_expr_mk_forall(v_n_2967_, v_d_2968_, v_b_2969_, v_bi_boxed_2971_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* v_n_2973_, lean_object* v_t_2974_, lean_object* v_v_2975_, lean_object* v_b_2976_, uint8_t v_nondep_2977_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Lean_Expr_letE___override(v_n_2973_, v_t_2974_, v_v_2975_, v_b_2976_, v_nondep_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_2979_, lean_object* v_t_2980_, lean_object* v_v_2981_, lean_object* v_b_2982_, lean_object* v_nondep_2983_){
_start:
{
uint8_t v_nondep_boxed_2984_; lean_object* v_res_2985_; 
v_nondep_boxed_2984_ = lean_unbox(v_nondep_2983_);
v_res_2985_ = lean_expr_mk_let(v_n_2979_, v_t_2980_, v_v_2981_, v_b_2982_, v_nondep_boxed_2984_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Lean_Expr_lit___override(v_l_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_2988_, lean_object* v_e_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_Expr_mdata___override(v_m_2988_, v_e_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_2991_, lean_object* v_idx_2992_, lean_object* v_struct_2993_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Lean_Expr_proj___override(v_structName_2991_, v_idx_2992_, v_struct_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_2995_, size_t v_i_2996_, size_t v_stop_2997_, lean_object* v_b_2998_){
_start:
{
uint8_t v___x_2999_; 
v___x_2999_ = lean_usize_dec_eq(v_i_2996_, v_stop_2997_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; lean_object* v___x_3001_; size_t v___x_3002_; size_t v___x_3003_; 
v___x_3000_ = lean_array_uget_borrowed(v_as_2995_, v_i_2996_);
lean_inc(v___x_3000_);
v___x_3001_ = l_Lean_Expr_app___override(v_b_2998_, v___x_3000_);
v___x_3002_ = ((size_t)1ULL);
v___x_3003_ = lean_usize_add(v_i_2996_, v___x_3002_);
v_i_2996_ = v___x_3003_;
v_b_2998_ = v___x_3001_;
goto _start;
}
else
{
return v_b_2998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_3005_, lean_object* v_i_3006_, lean_object* v_stop_3007_, lean_object* v_b_3008_){
_start:
{
size_t v_i_boxed_3009_; size_t v_stop_boxed_3010_; lean_object* v_res_3011_; 
v_i_boxed_3009_ = lean_unbox_usize(v_i_3006_);
lean_dec(v_i_3006_);
v_stop_boxed_3010_ = lean_unbox_usize(v_stop_3007_);
lean_dec(v_stop_3007_);
v_res_3011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_3005_, v_i_boxed_3009_, v_stop_boxed_3010_, v_b_3008_);
lean_dec_ref(v_as_3005_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_3012_, lean_object* v_args_3013_){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v___x_3014_ = lean_unsigned_to_nat(0u);
v___x_3015_ = lean_array_get_size(v_args_3013_);
v___x_3016_ = lean_nat_dec_lt(v___x_3014_, v___x_3015_);
if (v___x_3016_ == 0)
{
return v_f_3012_;
}
else
{
uint8_t v___x_3017_; 
v___x_3017_ = lean_nat_dec_le(v___x_3015_, v___x_3015_);
if (v___x_3017_ == 0)
{
if (v___x_3016_ == 0)
{
return v_f_3012_;
}
else
{
size_t v___x_3018_; size_t v___x_3019_; lean_object* v___x_3020_; 
v___x_3018_ = ((size_t)0ULL);
v___x_3019_ = lean_usize_of_nat(v___x_3015_);
v___x_3020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3013_, v___x_3018_, v___x_3019_, v_f_3012_);
return v___x_3020_;
}
}
else
{
size_t v___x_3021_; size_t v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = ((size_t)0ULL);
v___x_3022_ = lean_usize_of_nat(v___x_3015_);
v___x_3023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3013_, v___x_3021_, v___x_3022_, v_f_3012_);
return v___x_3023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_3024_, lean_object* v_args_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_mkAppN(v_f_3024_, v_args_3025_);
lean_dec_ref(v_args_3025_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_3027_, lean_object* v_args_3028_, lean_object* v_i_3029_, lean_object* v_e_3030_){
_start:
{
uint8_t v___x_3031_; 
v___x_3031_ = lean_nat_dec_lt(v_i_3029_, v_n_3027_);
if (v___x_3031_ == 0)
{
lean_dec(v_i_3029_);
return v_e_3030_;
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3032_ = lean_unsigned_to_nat(1u);
v___x_3033_ = lean_nat_add(v_i_3029_, v___x_3032_);
v___x_3034_ = l_Lean_instInhabitedExpr;
v___x_3035_ = lean_array_get_borrowed(v___x_3034_, v_args_3028_, v_i_3029_);
lean_dec(v_i_3029_);
lean_inc(v___x_3035_);
v___x_3036_ = l_Lean_Expr_app___override(v_e_3030_, v___x_3035_);
v_i_3029_ = v___x_3033_;
v_e_3030_ = v___x_3036_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_3038_, lean_object* v_args_3039_, lean_object* v_i_3040_, lean_object* v_e_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_3038_, v_args_3039_, v_i_3040_, v_e_3041_);
lean_dec_ref(v_args_3039_);
lean_dec(v_n_3038_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_3043_, lean_object* v_i_3044_, lean_object* v_j_3045_, lean_object* v_args_3046_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_3045_, v_args_3046_, v_i_3044_, v_f_3043_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_3048_, lean_object* v_i_3049_, lean_object* v_j_3050_, lean_object* v_args_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_mkAppRange(v_f_3048_, v_i_3049_, v_j_3050_, v_args_3051_);
lean_dec_ref(v_args_3051_);
lean_dec(v_j_3050_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_3053_, size_t v_i_3054_, size_t v_stop_3055_, lean_object* v_b_3056_){
_start:
{
uint8_t v___x_3057_; 
v___x_3057_ = lean_usize_dec_eq(v_i_3054_, v_stop_3055_);
if (v___x_3057_ == 0)
{
size_t v___x_3058_; size_t v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3058_ = ((size_t)1ULL);
v___x_3059_ = lean_usize_sub(v_i_3054_, v___x_3058_);
v___x_3060_ = lean_array_uget_borrowed(v_as_3053_, v___x_3059_);
lean_inc(v___x_3060_);
v___x_3061_ = l_Lean_Expr_app___override(v_b_3056_, v___x_3060_);
v_i_3054_ = v___x_3059_;
v_b_3056_ = v___x_3061_;
goto _start;
}
else
{
return v_b_3056_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_3063_, lean_object* v_i_3064_, lean_object* v_stop_3065_, lean_object* v_b_3066_){
_start:
{
size_t v_i_boxed_3067_; size_t v_stop_boxed_3068_; lean_object* v_res_3069_; 
v_i_boxed_3067_ = lean_unbox_usize(v_i_3064_);
lean_dec(v_i_3064_);
v_stop_boxed_3068_ = lean_unbox_usize(v_stop_3065_);
lean_dec(v_stop_3065_);
v_res_3069_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3063_, v_i_boxed_3067_, v_stop_boxed_3068_, v_b_3066_);
lean_dec_ref(v_as_3063_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_3070_, lean_object* v_revArgs_3071_){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; uint8_t v___x_3074_; 
v___x_3072_ = lean_array_get_size(v_revArgs_3071_);
v___x_3073_ = lean_unsigned_to_nat(0u);
v___x_3074_ = lean_nat_dec_lt(v___x_3073_, v___x_3072_);
if (v___x_3074_ == 0)
{
return v_fn_3070_;
}
else
{
size_t v___x_3075_; size_t v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = lean_usize_of_nat(v___x_3072_);
v___x_3076_ = ((size_t)0ULL);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_3071_, v___x_3075_, v___x_3076_, v_fn_3070_);
return v___x_3077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_3078_, lean_object* v_revArgs_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Lean_mkAppRev(v_fn_3078_, v_revArgs_3079_);
lean_dec_ref(v_revArgs_3079_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = lean_expr_dbg_to_string(v_e_3082_);
lean_dec_ref(v_e_3082_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_3086_, lean_object* v_b_3087_){
_start:
{
uint8_t v_res_3088_; lean_object* v_r_3089_; 
v_res_3088_ = lean_expr_quick_lt(v_a_3086_, v_b_3087_);
lean_dec_ref(v_b_3087_);
lean_dec_ref(v_a_3086_);
v_r_3089_ = lean_box(v_res_3088_);
return v_r_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_3092_, lean_object* v_b_3093_){
_start:
{
uint8_t v_res_3094_; lean_object* v_r_3095_; 
v_res_3094_ = lean_expr_lt(v_a_3092_, v_b_3093_);
lean_dec_ref(v_b_3093_);
lean_dec_ref(v_a_3092_);
v_r_3095_ = lean_box(v_res_3094_);
return v_r_3095_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* v_a_3096_, lean_object* v_b_3097_){
_start:
{
uint8_t v___x_3098_; 
v___x_3098_ = lean_expr_quick_lt(v_a_3096_, v_b_3097_);
if (v___x_3098_ == 0)
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_expr_quick_lt(v_b_3097_, v_a_3096_);
if (v___x_3099_ == 0)
{
uint8_t v___x_3100_; 
v___x_3100_ = 1;
return v___x_3100_;
}
else
{
uint8_t v___x_3101_; 
v___x_3101_ = 2;
return v___x_3101_;
}
}
else
{
uint8_t v___x_3102_; 
v___x_3102_ = 0;
return v___x_3102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_3103_, lean_object* v_b_3104_){
_start:
{
uint8_t v_res_3105_; lean_object* v_r_3106_; 
v_res_3105_ = l_Lean_Expr_quickComp(v_a_3103_, v_b_3104_);
lean_dec_ref(v_b_3104_);
lean_dec_ref(v_a_3103_);
v_r_3106_ = lean_box(v_res_3105_);
return v_r_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_3109_, lean_object* v_b_3110_){
_start:
{
uint8_t v_res_3111_; lean_object* v_r_3112_; 
v_res_3111_ = lean_expr_eqv(v_a_3109_, v_b_3110_);
lean_dec_ref(v_b_3110_);
lean_dec_ref(v_a_3109_);
v_r_3112_ = lean_box(v_res_3111_);
return v_r_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3117_, lean_object* v_b_3118_){
_start:
{
uint8_t v_res_3119_; lean_object* v_r_3120_; 
v_res_3119_ = lean_expr_equal(v_a_3117_, v_b_3118_);
lean_dec_ref(v_b_3118_);
lean_dec_ref(v_a_3117_);
v_r_3120_ = lean_box(v_res_3119_);
return v_r_3120_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* v_x_3121_){
_start:
{
if (lean_obj_tag(v_x_3121_) == 3)
{
uint8_t v___x_3122_; 
v___x_3122_ = 1;
return v___x_3122_;
}
else
{
uint8_t v___x_3123_; 
v___x_3123_ = 0;
return v___x_3123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3124_){
_start:
{
uint8_t v_res_3125_; lean_object* v_r_3126_; 
v_res_3125_ = l_Lean_Expr_isSort(v_x_3124_);
lean_dec_ref(v_x_3124_);
v_r_3126_ = lean_box(v_res_3125_);
return v_r_3126_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* v_x_3127_){
_start:
{
if (lean_obj_tag(v_x_3127_) == 3)
{
lean_object* v_u_3128_; 
v_u_3128_ = lean_ctor_get(v_x_3127_, 0);
if (lean_obj_tag(v_u_3128_) == 1)
{
uint8_t v___x_3129_; 
v___x_3129_ = 1;
return v___x_3129_;
}
else
{
uint8_t v___x_3130_; 
v___x_3130_ = 0;
return v___x_3130_;
}
}
else
{
uint8_t v___x_3131_; 
v___x_3131_ = 0;
return v___x_3131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3132_){
_start:
{
uint8_t v_res_3133_; lean_object* v_r_3134_; 
v_res_3133_ = l_Lean_Expr_isType(v_x_3132_);
lean_dec_ref(v_x_3132_);
v_r_3134_ = lean_box(v_res_3133_);
return v_r_3134_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* v_x_3135_){
_start:
{
if (lean_obj_tag(v_x_3135_) == 3)
{
lean_object* v_u_3136_; 
v_u_3136_ = lean_ctor_get(v_x_3135_, 0);
if (lean_obj_tag(v_u_3136_) == 1)
{
lean_object* v_a_3137_; 
v_a_3137_ = lean_ctor_get(v_u_3136_, 0);
if (lean_obj_tag(v_a_3137_) == 0)
{
uint8_t v___x_3138_; 
v___x_3138_ = 1;
return v___x_3138_;
}
else
{
uint8_t v___x_3139_; 
v___x_3139_ = 0;
return v___x_3139_;
}
}
else
{
uint8_t v___x_3140_; 
v___x_3140_ = 0;
return v___x_3140_;
}
}
else
{
uint8_t v___x_3141_; 
v___x_3141_ = 0;
return v___x_3141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3142_){
_start:
{
uint8_t v_res_3143_; lean_object* v_r_3144_; 
v_res_3143_ = l_Lean_Expr_isType0(v_x_3142_);
lean_dec_ref(v_x_3142_);
v_r_3144_ = lean_box(v_res_3143_);
return v_r_3144_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* v_x_3145_){
_start:
{
if (lean_obj_tag(v_x_3145_) == 3)
{
lean_object* v_u_3146_; 
v_u_3146_ = lean_ctor_get(v_x_3145_, 0);
if (lean_obj_tag(v_u_3146_) == 0)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3150_){
_start:
{
uint8_t v_res_3151_; lean_object* v_r_3152_; 
v_res_3151_ = l_Lean_Expr_isProp(v_x_3150_);
lean_dec_ref(v_x_3150_);
v_r_3152_ = lean_box(v_res_3151_);
return v_r_3152_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3153_){
_start:
{
if (lean_obj_tag(v_x_3153_) == 0)
{
uint8_t v___x_3154_; 
v___x_3154_ = 1;
return v___x_3154_;
}
else
{
uint8_t v___x_3155_; 
v___x_3155_ = 0;
return v___x_3155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3156_){
_start:
{
uint8_t v_res_3157_; lean_object* v_r_3158_; 
v_res_3157_ = l_Lean_Expr_isBVar(v_x_3156_);
lean_dec_ref(v_x_3156_);
v_r_3158_ = lean_box(v_res_3157_);
return v_r_3158_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3159_){
_start:
{
if (lean_obj_tag(v_x_3159_) == 2)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3162_){
_start:
{
uint8_t v_res_3163_; lean_object* v_r_3164_; 
v_res_3163_ = l_Lean_Expr_isMVar(v_x_3162_);
lean_dec_ref(v_x_3162_);
v_r_3164_ = lean_box(v_res_3163_);
return v_r_3164_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3165_){
_start:
{
if (lean_obj_tag(v_x_3165_) == 1)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3168_){
_start:
{
uint8_t v_res_3169_; lean_object* v_r_3170_; 
v_res_3169_ = l_Lean_Expr_isFVar(v_x_3168_);
lean_dec_ref(v_x_3168_);
v_r_3170_ = lean_box(v_res_3169_);
return v_r_3170_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* v_x_3171_){
_start:
{
if (lean_obj_tag(v_x_3171_) == 5)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3174_){
_start:
{
uint8_t v_res_3175_; lean_object* v_r_3176_; 
v_res_3175_ = l_Lean_Expr_isApp(v_x_3174_);
lean_dec_ref(v_x_3174_);
v_r_3176_ = lean_box(v_res_3175_);
return v_r_3176_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* v_x_3177_){
_start:
{
if (lean_obj_tag(v_x_3177_) == 11)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3180_){
_start:
{
uint8_t v_res_3181_; lean_object* v_r_3182_; 
v_res_3181_ = l_Lean_Expr_isProj(v_x_3180_);
lean_dec_ref(v_x_3180_);
v_r_3182_ = lean_box(v_res_3181_);
return v_r_3182_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* v_x_3183_){
_start:
{
if (lean_obj_tag(v_x_3183_) == 4)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3186_){
_start:
{
uint8_t v_res_3187_; lean_object* v_r_3188_; 
v_res_3187_ = l_Lean_Expr_isConst(v_x_3186_);
lean_dec_ref(v_x_3186_);
v_r_3188_ = lean_box(v_res_3187_);
return v_r_3188_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3189_, lean_object* v_x_3190_){
_start:
{
if (lean_obj_tag(v_x_3189_) == 4)
{
lean_object* v_declName_3191_; uint8_t v___x_3192_; 
v_declName_3191_ = lean_ctor_get(v_x_3189_, 0);
v___x_3192_ = lean_name_eq(v_declName_3191_, v_x_3190_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3194_, lean_object* v_x_3195_){
_start:
{
uint8_t v_res_3196_; lean_object* v_r_3197_; 
v_res_3196_ = l_Lean_Expr_isConstOf(v_x_3194_, v_x_3195_);
lean_dec(v_x_3195_);
lean_dec_ref(v_x_3194_);
v_r_3197_ = lean_box(v_res_3196_);
return v_r_3197_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3198_, lean_object* v_x_3199_){
_start:
{
if (lean_obj_tag(v_x_3198_) == 1)
{
lean_object* v_fvarId_3200_; uint8_t v___x_3201_; 
v_fvarId_3200_ = lean_ctor_get(v_x_3198_, 0);
v___x_3201_ = lean_name_eq(v_fvarId_3200_, v_x_3199_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3203_, lean_object* v_x_3204_){
_start:
{
uint8_t v_res_3205_; lean_object* v_r_3206_; 
v_res_3205_ = l_Lean_Expr_isFVarOf(v_x_3203_, v_x_3204_);
lean_dec(v_x_3204_);
lean_dec_ref(v_x_3203_);
v_r_3206_ = lean_box(v_res_3205_);
return v_r_3206_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* v_x_3207_){
_start:
{
if (lean_obj_tag(v_x_3207_) == 7)
{
uint8_t v___x_3208_; 
v___x_3208_ = 1;
return v___x_3208_;
}
else
{
uint8_t v___x_3209_; 
v___x_3209_ = 0;
return v___x_3209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3210_){
_start:
{
uint8_t v_res_3211_; lean_object* v_r_3212_; 
v_res_3211_ = l_Lean_Expr_isForall(v_x_3210_);
lean_dec_ref(v_x_3210_);
v_r_3212_ = lean_box(v_res_3211_);
return v_r_3212_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3213_){
_start:
{
if (lean_obj_tag(v_x_3213_) == 6)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3216_){
_start:
{
uint8_t v_res_3217_; lean_object* v_r_3218_; 
v_res_3217_ = l_Lean_Expr_isLambda(v_x_3216_);
lean_dec_ref(v_x_3216_);
v_r_3218_ = lean_box(v_res_3217_);
return v_r_3218_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3219_){
_start:
{
switch(lean_obj_tag(v_x_3219_))
{
case 6:
{
uint8_t v___x_3220_; 
v___x_3220_ = 1;
return v___x_3220_;
}
case 7:
{
uint8_t v___x_3221_; 
v___x_3221_ = 1;
return v___x_3221_;
}
default: 
{
uint8_t v___x_3222_; 
v___x_3222_ = 0;
return v___x_3222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3223_){
_start:
{
uint8_t v_res_3224_; lean_object* v_r_3225_; 
v_res_3224_ = l_Lean_Expr_isBinding(v_x_3223_);
lean_dec_ref(v_x_3223_);
v_r_3225_ = lean_box(v_res_3224_);
return v_r_3225_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* v_x_3226_){
_start:
{
if (lean_obj_tag(v_x_3226_) == 8)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3229_){
_start:
{
uint8_t v_res_3230_; lean_object* v_r_3231_; 
v_res_3230_ = l_Lean_Expr_isLet(v_x_3229_);
lean_dec_ref(v_x_3229_);
v_r_3231_ = lean_box(v_res_3230_);
return v_r_3231_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object* v_x_3232_){
_start:
{
if (lean_obj_tag(v_x_3232_) == 8)
{
uint8_t v_nondep_3233_; 
v_nondep_3233_ = lean_ctor_get_uint8(v_x_3232_, sizeof(void*)*4 + 8);
return v_nondep_3233_;
}
else
{
uint8_t v___x_3234_; 
v___x_3234_ = 0;
return v___x_3234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3235_){
_start:
{
uint8_t v_res_3236_; lean_object* v_r_3237_; 
v_res_3236_ = l_Lean_Expr_isHave(v_x_3235_);
lean_dec_ref(v_x_3235_);
v_r_3237_ = lean_box(v_res_3236_);
return v_r_3237_;
}
}
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object* v_a_3238_){
_start:
{
uint8_t v___x_3239_; 
v___x_3239_ = l_Lean_Expr_isHave(v_a_3238_);
lean_dec_ref(v_a_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3240_){
_start:
{
uint8_t v_res_3241_; lean_object* v_r_3242_; 
v_res_3241_ = lean_expr_is_have(v_a_3240_);
v_r_3242_ = lean_box(v_res_3241_);
return v_r_3242_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* v_x_3243_){
_start:
{
if (lean_obj_tag(v_x_3243_) == 10)
{
uint8_t v___x_3244_; 
v___x_3244_ = 1;
return v___x_3244_;
}
else
{
uint8_t v___x_3245_; 
v___x_3245_ = 0;
return v___x_3245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3246_){
_start:
{
uint8_t v_res_3247_; lean_object* v_r_3248_; 
v_res_3247_ = l_Lean_Expr_isMData(v_x_3246_);
lean_dec_ref(v_x_3246_);
v_r_3248_ = lean_box(v_res_3247_);
return v_r_3248_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* v_x_3249_){
_start:
{
if (lean_obj_tag(v_x_3249_) == 9)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3252_){
_start:
{
uint8_t v_res_3253_; lean_object* v_r_3254_; 
v_res_3253_ = l_Lean_Expr_isLit(v_x_3252_);
lean_dec_ref(v_x_3252_);
v_r_3254_ = lean_box(v_res_3253_);
return v_r_3254_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3255_){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = l_Lean_instInhabitedExpr;
v___x_3257_ = lean_panic_fn_borrowed(v___x_3256_, v_msg_3255_);
return v___x_3257_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3261_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3262_ = lean_unsigned_to_nat(15u);
v___x_3263_ = lean_unsigned_to_nat(922u);
v___x_3264_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3265_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3266_ = l_mkPanicMessageWithDecl(v___x_3265_, v___x_3264_, v___x_3263_, v___x_3262_, v___x_3261_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3267_){
_start:
{
if (lean_obj_tag(v_x_3267_) == 5)
{
lean_object* v_fn_3268_; 
v_fn_3268_ = lean_ctor_get(v_x_3267_, 0);
lean_inc_ref(v_fn_3268_);
return v_fn_3268_;
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3270_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3269_);
return v___x_3270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_Expr_appFn_x21(v_x_3271_);
lean_dec_ref(v_x_3271_);
return v_res_3272_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3274_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3275_ = lean_unsigned_to_nat(15u);
v___x_3276_ = lean_unsigned_to_nat(926u);
v___x_3277_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3278_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3279_ = l_mkPanicMessageWithDecl(v___x_3278_, v___x_3277_, v___x_3276_, v___x_3275_, v___x_3274_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3280_){
_start:
{
if (lean_obj_tag(v_x_3280_) == 5)
{
lean_object* v_arg_3281_; 
v_arg_3281_ = lean_ctor_get(v_x_3280_, 1);
lean_inc_ref(v_arg_3281_);
return v_arg_3281_;
}
else
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3283_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3282_);
return v___x_3283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_Expr_appArg_x21(v_x_3284_);
lean_dec_ref(v_x_3284_);
return v_res_3285_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3287_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3288_ = lean_unsigned_to_nat(17u);
v___x_3289_ = lean_unsigned_to_nat(931u);
v___x_3290_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3291_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3292_ = l_mkPanicMessageWithDecl(v___x_3291_, v___x_3290_, v___x_3289_, v___x_3288_, v___x_3287_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3293_){
_start:
{
switch(lean_obj_tag(v_x_3293_))
{
case 10:
{
lean_object* v_expr_3294_; 
v_expr_3294_ = lean_ctor_get(v_x_3293_, 1);
v_x_3293_ = v_expr_3294_;
goto _start;
}
case 5:
{
lean_object* v_fn_3296_; 
v_fn_3296_ = lean_ctor_get(v_x_3293_, 0);
lean_inc_ref(v_fn_3296_);
return v_fn_3296_;
}
default: 
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3298_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3297_);
return v___x_3298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_Expr_appFn_x21_x27(v_x_3299_);
lean_dec_ref(v_x_3299_);
return v_res_3300_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3302_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3303_ = lean_unsigned_to_nat(17u);
v___x_3304_ = lean_unsigned_to_nat(936u);
v___x_3305_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3306_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3307_ = l_mkPanicMessageWithDecl(v___x_3306_, v___x_3305_, v___x_3304_, v___x_3303_, v___x_3302_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3308_){
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
lean_object* v_arg_3311_; 
v_arg_3311_ = lean_ctor_get(v_x_3308_, 1);
lean_inc_ref(v_arg_3311_);
return v_arg_3311_;
}
default: 
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3313_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3312_);
return v___x_3313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lean_Expr_appArg_x21_x27(v_x_3314_);
lean_dec_ref(v_x_3314_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3316_){
_start:
{
lean_object* v_arg_3317_; 
v_arg_3317_ = lean_ctor_get(v_e_3316_, 1);
lean_inc_ref(v_arg_3317_);
return v_arg_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_Expr_appArg___redArg(v_e_3318_);
lean_dec_ref(v_e_3318_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3320_, lean_object* v_h_3321_){
_start:
{
lean_object* v_arg_3322_; 
v_arg_3322_ = lean_ctor_get(v_e_3320_, 1);
lean_inc_ref(v_arg_3322_);
return v_arg_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3323_, lean_object* v_h_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Lean_Expr_appArg(v_e_3323_, v_h_3324_);
lean_dec_ref(v_e_3323_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3326_){
_start:
{
lean_object* v_fn_3327_; 
v_fn_3327_ = lean_ctor_get(v_e_3326_, 0);
lean_inc_ref(v_fn_3327_);
return v_fn_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Lean_Expr_appFn___redArg(v_e_3328_);
lean_dec_ref(v_e_3328_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3330_, lean_object* v_h_3331_){
_start:
{
lean_object* v_fn_3332_; 
v_fn_3332_ = lean_ctor_get(v_e_3330_, 0);
lean_inc_ref(v_fn_3332_);
return v_fn_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3333_, lean_object* v_h_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_Expr_appFn(v_e_3333_, v_h_3334_);
lean_dec_ref(v_e_3333_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3336_){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = lean_box(0);
v___x_3338_ = lean_panic_fn_borrowed(v___x_3337_, v_msg_3336_);
return v___x_3338_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3341_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3342_ = lean_unsigned_to_nat(14u);
v___x_3343_ = lean_unsigned_to_nat(948u);
v___x_3344_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3345_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3346_ = l_mkPanicMessageWithDecl(v___x_3345_, v___x_3344_, v___x_3343_, v___x_3342_, v___x_3341_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3347_){
_start:
{
if (lean_obj_tag(v_x_3347_) == 3)
{
lean_object* v_u_3348_; 
v_u_3348_ = lean_ctor_get(v_x_3347_, 0);
lean_inc(v_u_3348_);
return v_u_3348_;
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3350_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3349_);
return v___x_3350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_Expr_sortLevel_x21(v_x_3351_);
lean_dec_ref(v_x_3351_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3353_){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3354_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3355_ = lean_panic_fn_borrowed(v___x_3354_, v_msg_3353_);
return v___x_3355_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3358_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3359_ = lean_unsigned_to_nat(13u);
v___x_3360_ = lean_unsigned_to_nat(952u);
v___x_3361_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3362_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3363_ = l_mkPanicMessageWithDecl(v___x_3362_, v___x_3361_, v___x_3360_, v___x_3359_, v___x_3358_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3364_){
_start:
{
if (lean_obj_tag(v_x_3364_) == 9)
{
lean_object* v_a_3365_; 
v_a_3365_ = lean_ctor_get(v_x_3364_, 0);
lean_inc_ref(v_a_3365_);
return v_a_3365_;
}
else
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3367_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3366_);
return v___x_3367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_Lean_Expr_litValue_x21(v_x_3368_);
lean_dec_ref(v_x_3368_);
return v_res_3369_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3370_){
_start:
{
if (lean_obj_tag(v_x_3370_) == 9)
{
lean_object* v_a_3371_; 
v_a_3371_ = lean_ctor_get(v_x_3370_, 0);
if (lean_obj_tag(v_a_3371_) == 0)
{
uint8_t v___x_3372_; 
v___x_3372_ = 1;
return v___x_3372_;
}
else
{
uint8_t v___x_3373_; 
v___x_3373_ = 0;
return v___x_3373_;
}
}
else
{
uint8_t v___x_3374_; 
v___x_3374_ = 0;
return v___x_3374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3375_){
_start:
{
uint8_t v_res_3376_; lean_object* v_r_3377_; 
v_res_3376_ = l_Lean_Expr_isRawNatLit(v_x_3375_);
lean_dec_ref(v_x_3375_);
v_r_3377_ = lean_box(v_res_3376_);
return v_r_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3378_){
_start:
{
if (lean_obj_tag(v_x_3378_) == 9)
{
lean_object* v_a_3379_; 
v_a_3379_ = lean_ctor_get(v_x_3378_, 0);
lean_inc_ref(v_a_3379_);
lean_dec_ref(v_x_3378_);
if (lean_obj_tag(v_a_3379_) == 0)
{
lean_object* v_val_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
v_val_3380_ = lean_ctor_get(v_a_3379_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v_a_3379_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v_a_3379_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_val_3380_);
lean_dec(v_a_3379_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
lean_ctor_set_tag(v___x_3382_, 1);
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_val_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
else
{
lean_object* v___x_3388_; 
lean_dec_ref(v_a_3379_);
v___x_3388_ = lean_box(0);
return v___x_3388_;
}
}
else
{
lean_object* v___x_3389_; 
lean_dec_ref(v_x_3378_);
v___x_3389_ = lean_box(0);
return v___x_3389_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3390_){
_start:
{
if (lean_obj_tag(v_x_3390_) == 9)
{
lean_object* v_a_3391_; 
v_a_3391_ = lean_ctor_get(v_x_3390_, 0);
if (lean_obj_tag(v_a_3391_) == 1)
{
uint8_t v___x_3392_; 
v___x_3392_ = 1;
return v___x_3392_;
}
else
{
uint8_t v___x_3393_; 
v___x_3393_ = 0;
return v___x_3393_;
}
}
else
{
uint8_t v___x_3394_; 
v___x_3394_ = 0;
return v___x_3394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3395_){
_start:
{
uint8_t v_res_3396_; lean_object* v_r_3397_; 
v_res_3396_ = l_Lean_Expr_isStringLit(v_x_3395_);
lean_dec_ref(v_x_3395_);
v_r_3397_ = lean_box(v_res_3396_);
return v_r_3397_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3402_){
_start:
{
if (lean_obj_tag(v_x_3402_) == 5)
{
lean_object* v_fn_3403_; 
v_fn_3403_ = lean_ctor_get(v_x_3402_, 0);
if (lean_obj_tag(v_fn_3403_) == 4)
{
lean_object* v_arg_3404_; lean_object* v_declName_3405_; lean_object* v___x_3406_; uint8_t v___x_3407_; 
v_arg_3404_ = lean_ctor_get(v_x_3402_, 1);
v_declName_3405_ = lean_ctor_get(v_fn_3403_, 0);
v___x_3406_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3407_ = lean_name_eq(v_declName_3405_, v___x_3406_);
if (v___x_3407_ == 0)
{
return v___x_3407_;
}
else
{
uint8_t v___x_3408_; 
v___x_3408_ = l_Lean_Expr_isRawNatLit(v_arg_3404_);
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
else
{
uint8_t v___x_3410_; 
v___x_3410_ = 0;
return v___x_3410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3411_){
_start:
{
uint8_t v_res_3412_; lean_object* v_r_3413_; 
v_res_3412_ = l_Lean_Expr_isCharLit(v_x_3411_);
lean_dec_ref(v_x_3411_);
v_r_3413_ = lean_box(v_res_3412_);
return v_r_3413_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3414_){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = lean_box(0);
v___x_3416_ = lean_panic_fn_borrowed(v___x_3415_, v_msg_3414_);
return v___x_3416_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3419_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3420_ = lean_unsigned_to_nat(17u);
v___x_3421_ = lean_unsigned_to_nat(976u);
v___x_3422_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3423_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3424_ = l_mkPanicMessageWithDecl(v___x_3423_, v___x_3422_, v___x_3421_, v___x_3420_, v___x_3419_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3425_){
_start:
{
if (lean_obj_tag(v_x_3425_) == 4)
{
lean_object* v_declName_3426_; 
v_declName_3426_ = lean_ctor_get(v_x_3425_, 0);
lean_inc(v_declName_3426_);
return v_declName_3426_;
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3428_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3427_);
return v___x_3428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_Expr_constName_x21(v_x_3429_);
lean_dec_ref(v_x_3429_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3431_){
_start:
{
if (lean_obj_tag(v_x_3431_) == 4)
{
lean_object* v_declName_3432_; lean_object* v___x_3433_; 
v_declName_3432_ = lean_ctor_get(v_x_3431_, 0);
lean_inc(v_declName_3432_);
v___x_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3433_, 0, v_declName_3432_);
return v___x_3433_;
}
else
{
lean_object* v___x_3434_; 
v___x_3434_ = lean_box(0);
return v___x_3434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_Expr_constName_x3f(v_x_3435_);
lean_dec_ref(v_x_3435_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3437_){
_start:
{
lean_object* v___x_3438_; 
v___x_3438_ = l_Lean_Expr_constName_x3f(v_e_3437_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v___x_3439_; 
v___x_3439_ = lean_box(0);
return v___x_3439_;
}
else
{
lean_object* v_val_3440_; 
v_val_3440_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_val_3440_);
lean_dec_ref(v___x_3438_);
return v_val_3440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_Expr_constName(v_e_3441_);
lean_dec_ref(v_e_3441_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3443_){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = lean_box(0);
v___x_3445_ = lean_panic_fn_borrowed(v___x_3444_, v_msg_3443_);
return v___x_3445_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3447_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3448_ = lean_unsigned_to_nat(18u);
v___x_3449_ = lean_unsigned_to_nat(996u);
v___x_3450_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3451_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3452_ = l_mkPanicMessageWithDecl(v___x_3451_, v___x_3450_, v___x_3449_, v___x_3448_, v___x_3447_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3453_){
_start:
{
if (lean_obj_tag(v_x_3453_) == 4)
{
lean_object* v_us_3454_; 
v_us_3454_ = lean_ctor_get(v_x_3453_, 1);
lean_inc(v_us_3454_);
return v_us_3454_;
}
else
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3456_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3455_);
return v___x_3456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_Expr_constLevels_x21(v_x_3457_);
lean_dec_ref(v_x_3457_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3459_){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3460_ = lean_unsigned_to_nat(0u);
v___x_3461_ = lean_panic_fn_borrowed(v___x_3460_, v_msg_3459_);
return v___x_3461_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3464_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3465_ = lean_unsigned_to_nat(16u);
v___x_3466_ = lean_unsigned_to_nat(1000u);
v___x_3467_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3468_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3469_ = l_mkPanicMessageWithDecl(v___x_3468_, v___x_3467_, v___x_3466_, v___x_3465_, v___x_3464_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3470_){
_start:
{
if (lean_obj_tag(v_x_3470_) == 0)
{
lean_object* v_deBruijnIndex_3471_; 
v_deBruijnIndex_3471_ = lean_ctor_get(v_x_3470_, 0);
lean_inc(v_deBruijnIndex_3471_);
return v_deBruijnIndex_3471_;
}
else
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3473_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3472_);
return v___x_3473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Lean_Expr_bvarIdx_x21(v_x_3474_);
lean_dec_ref(v_x_3474_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3476_){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = lean_box(0);
v___x_3478_ = lean_panic_fn_borrowed(v___x_3477_, v_msg_3476_);
return v___x_3478_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3481_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3482_ = lean_unsigned_to_nat(14u);
v___x_3483_ = lean_unsigned_to_nat(1004u);
v___x_3484_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3485_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3486_ = l_mkPanicMessageWithDecl(v___x_3485_, v___x_3484_, v___x_3483_, v___x_3482_, v___x_3481_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3487_){
_start:
{
if (lean_obj_tag(v_x_3487_) == 1)
{
lean_object* v_fvarId_3488_; 
v_fvarId_3488_ = lean_ctor_get(v_x_3487_, 0);
lean_inc(v_fvarId_3488_);
return v_fvarId_3488_;
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3490_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3489_);
return v___x_3490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Lean_Expr_fvarId_x21(v_x_3491_);
lean_dec_ref(v_x_3491_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3493_){
_start:
{
if (lean_obj_tag(v_x_3493_) == 1)
{
lean_object* v_fvarId_3494_; lean_object* v___x_3495_; 
v_fvarId_3494_ = lean_ctor_get(v_x_3493_, 0);
lean_inc(v_fvarId_3494_);
v___x_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3495_, 0, v_fvarId_3494_);
return v___x_3495_;
}
else
{
lean_object* v___x_3496_; 
v___x_3496_ = lean_box(0);
return v___x_3496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Lean_Expr_fvarId_x3f(v_x_3497_);
lean_dec_ref(v_x_3497_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3499_){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = lean_box(0);
v___x_3501_ = lean_panic_fn_borrowed(v___x_3500_, v_msg_3499_);
return v___x_3501_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3504_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3505_ = lean_unsigned_to_nat(14u);
v___x_3506_ = lean_unsigned_to_nat(1012u);
v___x_3507_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3508_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3509_ = l_mkPanicMessageWithDecl(v___x_3508_, v___x_3507_, v___x_3506_, v___x_3505_, v___x_3504_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3510_){
_start:
{
if (lean_obj_tag(v_x_3510_) == 2)
{
lean_object* v_mvarId_3511_; 
v_mvarId_3511_ = lean_ctor_get(v_x_3510_, 0);
lean_inc(v_mvarId_3511_);
return v_mvarId_3511_;
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3512_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3513_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3512_);
return v___x_3513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Lean_Expr_mvarId_x21(v_x_3514_);
lean_dec_ref(v_x_3514_);
return v_res_3515_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3518_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3519_ = lean_unsigned_to_nat(23u);
v___x_3520_ = lean_unsigned_to_nat(1017u);
v___x_3521_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3522_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3523_ = l_mkPanicMessageWithDecl(v___x_3522_, v___x_3521_, v___x_3520_, v___x_3519_, v___x_3518_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3524_){
_start:
{
switch(lean_obj_tag(v_x_3524_))
{
case 7:
{
lean_object* v_binderName_3525_; 
v_binderName_3525_ = lean_ctor_get(v_x_3524_, 0);
lean_inc(v_binderName_3525_);
return v_binderName_3525_;
}
case 6:
{
lean_object* v_binderName_3526_; 
v_binderName_3526_ = lean_ctor_get(v_x_3524_, 0);
lean_inc(v_binderName_3526_);
return v_binderName_3526_;
}
default: 
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3527_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3528_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3527_);
return v___x_3528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Lean_Expr_bindingName_x21(v_x_3529_);
lean_dec_ref(v_x_3529_);
return v_res_3530_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3532_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3533_ = lean_unsigned_to_nat(23u);
v___x_3534_ = lean_unsigned_to_nat(1022u);
v___x_3535_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3536_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3537_ = l_mkPanicMessageWithDecl(v___x_3536_, v___x_3535_, v___x_3534_, v___x_3533_, v___x_3532_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3538_){
_start:
{
switch(lean_obj_tag(v_x_3538_))
{
case 7:
{
lean_object* v_binderType_3539_; 
v_binderType_3539_ = lean_ctor_get(v_x_3538_, 1);
lean_inc_ref(v_binderType_3539_);
return v_binderType_3539_;
}
case 6:
{
lean_object* v_binderType_3540_; 
v_binderType_3540_ = lean_ctor_get(v_x_3538_, 1);
lean_inc_ref(v_binderType_3540_);
return v_binderType_3540_;
}
default: 
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3542_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3541_);
return v___x_3542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_Expr_bindingDomain_x21(v_x_3543_);
lean_dec_ref(v_x_3543_);
return v_res_3544_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3546_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3547_ = lean_unsigned_to_nat(23u);
v___x_3548_ = lean_unsigned_to_nat(1027u);
v___x_3549_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3550_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3551_ = l_mkPanicMessageWithDecl(v___x_3550_, v___x_3549_, v___x_3548_, v___x_3547_, v___x_3546_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3552_){
_start:
{
switch(lean_obj_tag(v_x_3552_))
{
case 7:
{
lean_object* v_body_3553_; 
v_body_3553_ = lean_ctor_get(v_x_3552_, 2);
lean_inc_ref(v_body_3553_);
return v_body_3553_;
}
case 6:
{
lean_object* v_body_3554_; 
v_body_3554_ = lean_ctor_get(v_x_3552_, 2);
lean_inc_ref(v_body_3554_);
return v_body_3554_;
}
default: 
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3556_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3555_);
return v___x_3556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_Lean_Expr_bindingBody_x21(v_x_3557_);
lean_dec_ref(v_x_3557_);
return v_res_3558_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3559_){
_start:
{
uint8_t v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; uint8_t v___x_3563_; 
v___x_3560_ = 0;
v___x_3561_ = lean_box(v___x_3560_);
v___x_3562_ = lean_panic_fn_borrowed(v___x_3561_, v_msg_3559_);
lean_dec(v___x_3561_);
v___x_3563_ = lean_unbox(v___x_3562_);
lean_dec(v___x_3562_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3564_){
_start:
{
uint8_t v_res_3565_; lean_object* v_r_3566_; 
v_res_3565_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3564_);
v_r_3566_ = lean_box(v_res_3565_);
return v_r_3566_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3568_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3569_ = lean_unsigned_to_nat(24u);
v___x_3570_ = lean_unsigned_to_nat(1032u);
v___x_3571_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3572_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3573_ = l_mkPanicMessageWithDecl(v___x_3572_, v___x_3571_, v___x_3570_, v___x_3569_, v___x_3568_);
return v___x_3573_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3574_){
_start:
{
switch(lean_obj_tag(v_x_3574_))
{
case 7:
{
uint8_t v_binderInfo_3575_; 
v_binderInfo_3575_ = lean_ctor_get_uint8(v_x_3574_, sizeof(void*)*3 + 8);
return v_binderInfo_3575_;
}
case 6:
{
uint8_t v_binderInfo_3576_; 
v_binderInfo_3576_ = lean_ctor_get_uint8(v_x_3574_, sizeof(void*)*3 + 8);
return v_binderInfo_3576_;
}
default: 
{
lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3577_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3578_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3577_);
return v___x_3578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3579_){
_start:
{
uint8_t v_res_3580_; lean_object* v_r_3581_; 
v_res_3580_ = l_Lean_Expr_bindingInfo_x21(v_x_3579_);
lean_dec_ref(v_x_3579_);
v_r_3581_ = lean_box(v_res_3580_);
return v_r_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3582_){
_start:
{
lean_object* v_binderName_3583_; 
v_binderName_3583_ = lean_ctor_get(v_x_3582_, 0);
lean_inc(v_binderName_3583_);
return v_binderName_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Lean_Expr_forallName___redArg(v_x_3584_);
lean_dec_ref(v_x_3584_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3586_, lean_object* v_x_3587_){
_start:
{
lean_object* v_binderName_3588_; 
v_binderName_3588_ = lean_ctor_get(v_x_3586_, 0);
lean_inc(v_binderName_3588_);
return v_binderName_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3589_, lean_object* v_x_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Lean_Expr_forallName(v_x_3589_, v_x_3590_);
lean_dec_ref(v_x_3589_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3592_){
_start:
{
lean_object* v_binderType_3593_; 
v_binderType_3593_ = lean_ctor_get(v_x_3592_, 1);
lean_inc_ref(v_binderType_3593_);
return v_binderType_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_Expr_forallDomain___redArg(v_x_3594_);
lean_dec_ref(v_x_3594_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3596_, lean_object* v_x_3597_){
_start:
{
lean_object* v_binderType_3598_; 
v_binderType_3598_ = lean_ctor_get(v_x_3596_, 1);
lean_inc_ref(v_binderType_3598_);
return v_binderType_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3599_, lean_object* v_x_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lean_Expr_forallDomain(v_x_3599_, v_x_3600_);
lean_dec_ref(v_x_3599_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3602_){
_start:
{
lean_object* v_body_3603_; 
v_body_3603_ = lean_ctor_get(v_x_3602_, 2);
lean_inc_ref(v_body_3603_);
return v_body_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lean_Expr_forallBody___redArg(v_x_3604_);
lean_dec_ref(v_x_3604_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3606_, lean_object* v_x_3607_){
_start:
{
lean_object* v_body_3608_; 
v_body_3608_ = lean_ctor_get(v_x_3606_, 2);
lean_inc_ref(v_body_3608_);
return v_body_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3609_, lean_object* v_x_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_Expr_forallBody(v_x_3609_, v_x_3610_);
lean_dec_ref(v_x_3609_);
return v_res_3611_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3612_){
_start:
{
uint8_t v_binderInfo_3613_; 
v_binderInfo_3613_ = lean_ctor_get_uint8(v_x_3612_, sizeof(void*)*3 + 8);
return v_binderInfo_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3614_){
_start:
{
uint8_t v_res_3615_; lean_object* v_r_3616_; 
v_res_3615_ = l_Lean_Expr_forallInfo___redArg(v_x_3614_);
lean_dec_ref(v_x_3614_);
v_r_3616_ = lean_box(v_res_3615_);
return v_r_3616_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3617_, lean_object* v_x_3618_){
_start:
{
uint8_t v_binderInfo_3619_; 
v_binderInfo_3619_ = lean_ctor_get_uint8(v_x_3617_, sizeof(void*)*3 + 8);
return v_binderInfo_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3620_, lean_object* v_x_3621_){
_start:
{
uint8_t v_res_3622_; lean_object* v_r_3623_; 
v_res_3622_ = l_Lean_Expr_forallInfo(v_x_3620_, v_x_3621_);
lean_dec_ref(v_x_3620_);
v_r_3623_ = lean_box(v_res_3622_);
return v_r_3623_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3626_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3627_ = lean_unsigned_to_nat(17u);
v___x_3628_ = lean_unsigned_to_nat(1048u);
v___x_3629_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3630_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3631_ = l_mkPanicMessageWithDecl(v___x_3630_, v___x_3629_, v___x_3628_, v___x_3627_, v___x_3626_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3632_){
_start:
{
if (lean_obj_tag(v_x_3632_) == 8)
{
lean_object* v_declName_3633_; 
v_declName_3633_ = lean_ctor_get(v_x_3632_, 0);
lean_inc(v_declName_3633_);
return v_declName_3633_;
}
else
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3635_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3634_);
return v___x_3635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Lean_Expr_letName_x21(v_x_3636_);
lean_dec_ref(v_x_3636_);
return v_res_3637_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3639_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3640_ = lean_unsigned_to_nat(19u);
v___x_3641_ = lean_unsigned_to_nat(1052u);
v___x_3642_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3643_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3644_ = l_mkPanicMessageWithDecl(v___x_3643_, v___x_3642_, v___x_3641_, v___x_3640_, v___x_3639_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3645_){
_start:
{
if (lean_obj_tag(v_x_3645_) == 8)
{
lean_object* v_type_3646_; 
v_type_3646_ = lean_ctor_get(v_x_3645_, 1);
lean_inc_ref(v_type_3646_);
return v_type_3646_;
}
else
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3648_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3647_);
return v___x_3648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Lean_Expr_letType_x21(v_x_3649_);
lean_dec_ref(v_x_3649_);
return v_res_3650_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3652_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3653_ = lean_unsigned_to_nat(21u);
v___x_3654_ = lean_unsigned_to_nat(1056u);
v___x_3655_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3656_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3657_ = l_mkPanicMessageWithDecl(v___x_3656_, v___x_3655_, v___x_3654_, v___x_3653_, v___x_3652_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3658_){
_start:
{
if (lean_obj_tag(v_x_3658_) == 8)
{
lean_object* v_value_3659_; 
v_value_3659_ = lean_ctor_get(v_x_3658_, 2);
lean_inc_ref(v_value_3659_);
return v_value_3659_;
}
else
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3661_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3660_);
return v___x_3661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l_Lean_Expr_letValue_x21(v_x_3662_);
lean_dec_ref(v_x_3662_);
return v_res_3663_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3665_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3666_ = lean_unsigned_to_nat(23u);
v___x_3667_ = lean_unsigned_to_nat(1060u);
v___x_3668_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3669_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3670_ = l_mkPanicMessageWithDecl(v___x_3669_, v___x_3668_, v___x_3667_, v___x_3666_, v___x_3665_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3671_){
_start:
{
if (lean_obj_tag(v_x_3671_) == 8)
{
lean_object* v_body_3672_; 
v_body_3672_ = lean_ctor_get(v_x_3671_, 3);
lean_inc_ref(v_body_3672_);
return v_body_3672_;
}
else
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3674_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3673_);
return v___x_3674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Lean_Expr_letBody_x21(v_x_3675_);
lean_dec_ref(v_x_3675_);
return v_res_3676_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3677_){
_start:
{
uint8_t v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; 
v___x_3678_ = 0;
v___x_3679_ = lean_box(v___x_3678_);
v___x_3680_ = lean_panic_fn_borrowed(v___x_3679_, v_msg_3677_);
lean_dec(v___x_3679_);
v___x_3681_ = lean_unbox(v___x_3680_);
lean_dec(v___x_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3682_){
_start:
{
uint8_t v_res_3683_; lean_object* v_r_3684_; 
v_res_3683_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3682_);
v_r_3684_ = lean_box(v_res_3683_);
return v_r_3684_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3686_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3687_ = lean_unsigned_to_nat(27u);
v___x_3688_ = lean_unsigned_to_nat(1064u);
v___x_3689_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3690_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3691_ = l_mkPanicMessageWithDecl(v___x_3690_, v___x_3689_, v___x_3688_, v___x_3687_, v___x_3686_);
return v___x_3691_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3692_){
_start:
{
if (lean_obj_tag(v_x_3692_) == 8)
{
uint8_t v_nondep_3693_; 
v_nondep_3693_ = lean_ctor_get_uint8(v_x_3692_, sizeof(void*)*4 + 8);
return v_nondep_3693_;
}
else
{
lean_object* v___x_3694_; uint8_t v___x_3695_; 
v___x_3694_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3695_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3694_);
return v___x_3695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3696_){
_start:
{
uint8_t v_res_3697_; lean_object* v_r_3698_; 
v_res_3697_ = l_Lean_Expr_letNondep_x21(v_x_3696_);
lean_dec_ref(v_x_3696_);
v_r_3698_ = lean_box(v_res_3697_);
return v_r_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3699_){
_start:
{
if (lean_obj_tag(v_x_3699_) == 10)
{
lean_object* v_expr_3700_; 
v_expr_3700_ = lean_ctor_get(v_x_3699_, 1);
v_x_3699_ = v_expr_3700_;
goto _start;
}
else
{
lean_inc_ref(v_x_3699_);
return v_x_3699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Lean_Expr_consumeMData(v_x_3702_);
lean_dec_ref(v_x_3702_);
return v_res_3703_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3706_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3707_ = lean_unsigned_to_nat(17u);
v___x_3708_ = lean_unsigned_to_nat(1072u);
v___x_3709_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3710_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3711_ = l_mkPanicMessageWithDecl(v___x_3710_, v___x_3709_, v___x_3708_, v___x_3707_, v___x_3706_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3712_){
_start:
{
if (lean_obj_tag(v_x_3712_) == 10)
{
lean_object* v_expr_3713_; 
v_expr_3713_ = lean_ctor_get(v_x_3712_, 1);
lean_inc_ref(v_expr_3713_);
return v_expr_3713_;
}
else
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3715_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3714_);
return v___x_3715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lean_Expr_mdataExpr_x21(v_x_3716_);
lean_dec_ref(v_x_3716_);
return v_res_3717_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3720_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3721_ = lean_unsigned_to_nat(18u);
v___x_3722_ = lean_unsigned_to_nat(1076u);
v___x_3723_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3724_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3725_ = l_mkPanicMessageWithDecl(v___x_3724_, v___x_3723_, v___x_3722_, v___x_3721_, v___x_3720_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3726_){
_start:
{
if (lean_obj_tag(v_x_3726_) == 11)
{
lean_object* v_struct_3727_; 
v_struct_3727_ = lean_ctor_get(v_x_3726_, 2);
lean_inc_ref(v_struct_3727_);
return v_struct_3727_;
}
else
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3729_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3728_);
return v___x_3729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Lean_Expr_projExpr_x21(v_x_3730_);
lean_dec_ref(v_x_3730_);
return v_res_3731_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3733_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3734_ = lean_unsigned_to_nat(18u);
v___x_3735_ = lean_unsigned_to_nat(1080u);
v___x_3736_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3737_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3738_ = l_mkPanicMessageWithDecl(v___x_3737_, v___x_3736_, v___x_3735_, v___x_3734_, v___x_3733_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3739_){
_start:
{
if (lean_obj_tag(v_x_3739_) == 11)
{
lean_object* v_idx_3740_; 
v_idx_3740_ = lean_ctor_get(v_x_3739_, 1);
lean_inc(v_idx_3740_);
return v_idx_3740_;
}
else
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3741_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3742_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3741_);
return v___x_3742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l_Lean_Expr_projIdx_x21(v_x_3743_);
lean_dec_ref(v_x_3743_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3745_){
_start:
{
if (lean_obj_tag(v_x_3745_) == 7)
{
lean_object* v_body_3746_; 
v_body_3746_ = lean_ctor_get(v_x_3745_, 2);
v_x_3745_ = v_body_3746_;
goto _start;
}
else
{
lean_inc_ref(v_x_3745_);
return v_x_3745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l_Lean_Expr_getForallBody(v_x_3748_);
lean_dec_ref(v_x_3748_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3750_, lean_object* v_x_3751_){
_start:
{
lean_object* v_zero_3752_; uint8_t v_isZero_3753_; 
v_zero_3752_ = lean_unsigned_to_nat(0u);
v_isZero_3753_ = lean_nat_dec_eq(v_x_3750_, v_zero_3752_);
if (v_isZero_3753_ == 1)
{
lean_dec(v_x_3750_);
lean_inc_ref(v_x_3751_);
return v_x_3751_;
}
else
{
if (lean_obj_tag(v_x_3751_) == 7)
{
lean_object* v_body_3754_; lean_object* v_one_3755_; lean_object* v_n_3756_; 
v_body_3754_ = lean_ctor_get(v_x_3751_, 2);
v_one_3755_ = lean_unsigned_to_nat(1u);
v_n_3756_ = lean_nat_sub(v_x_3750_, v_one_3755_);
lean_dec(v_x_3750_);
v_x_3750_ = v_n_3756_;
v_x_3751_ = v_body_3754_;
goto _start;
}
else
{
lean_dec(v_x_3750_);
lean_inc_ref(v_x_3751_);
return v_x_3751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3758_, lean_object* v_x_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3758_, v_x_3759_);
lean_dec_ref(v_x_3759_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3761_){
_start:
{
if (lean_obj_tag(v_x_3761_) == 7)
{
lean_object* v_binderName_3762_; lean_object* v_body_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v_binderName_3762_ = lean_ctor_get(v_x_3761_, 0);
v_body_3763_ = lean_ctor_get(v_x_3761_, 2);
v___x_3764_ = l_Lean_Expr_getForallBinderNames(v_body_3763_);
lean_inc(v_binderName_3762_);
v___x_3765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3765_, 0, v_binderName_3762_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
return v___x_3765_;
}
else
{
lean_object* v___x_3766_; 
v___x_3766_ = lean_box(0);
return v___x_3766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_Expr_getForallBinderNames(v_x_3767_);
lean_dec_ref(v_x_3767_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3769_){
_start:
{
switch(lean_obj_tag(v_x_3769_))
{
case 10:
{
lean_object* v_expr_3770_; 
v_expr_3770_ = lean_ctor_get(v_x_3769_, 1);
v_x_3769_ = v_expr_3770_;
goto _start;
}
case 7:
{
lean_object* v_body_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v_body_3772_ = lean_ctor_get(v_x_3769_, 2);
v___x_3773_ = l_Lean_Expr_getNumHeadForalls(v_body_3772_);
v___x_3774_ = lean_unsigned_to_nat(1u);
v___x_3775_ = lean_nat_add(v___x_3773_, v___x_3774_);
lean_dec(v___x_3773_);
return v___x_3775_;
}
default: 
{
lean_object* v___x_3776_; 
v___x_3776_ = lean_unsigned_to_nat(0u);
return v___x_3776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l_Lean_Expr_getNumHeadForalls(v_x_3777_);
lean_dec_ref(v_x_3777_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3779_){
_start:
{
if (lean_obj_tag(v_x_3779_) == 5)
{
lean_object* v_fn_3780_; 
v_fn_3780_ = lean_ctor_get(v_x_3779_, 0);
v_x_3779_ = v_fn_3780_;
goto _start;
}
else
{
lean_inc_ref(v_x_3779_);
return v_x_3779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Expr_getAppFn(v_x_3782_);
lean_dec_ref(v_x_3782_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3784_){
_start:
{
switch(lean_obj_tag(v_x_3784_))
{
case 5:
{
lean_object* v_fn_3785_; 
v_fn_3785_ = lean_ctor_get(v_x_3784_, 0);
v_x_3784_ = v_fn_3785_;
goto _start;
}
case 10:
{
lean_object* v_expr_3787_; 
v_expr_3787_ = lean_ctor_get(v_x_3784_, 1);
v_x_3784_ = v_expr_3787_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3784_);
return v_x_3784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l_Lean_Expr_getAppFn_x27(v_x_3789_);
lean_dec_ref(v_x_3789_);
return v_res_3790_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3791_, lean_object* v_n_3792_){
_start:
{
lean_object* v___x_3793_; 
v___x_3793_ = l_Lean_Expr_getAppFn(v_e_3791_);
if (lean_obj_tag(v___x_3793_) == 4)
{
lean_object* v_declName_3794_; uint8_t v___x_3795_; 
v_declName_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_declName_3794_);
lean_dec_ref(v___x_3793_);
v___x_3795_ = lean_name_eq(v_declName_3794_, v_n_3792_);
lean_dec(v_declName_3794_);
return v___x_3795_;
}
else
{
uint8_t v___x_3796_; 
lean_dec_ref(v___x_3793_);
v___x_3796_ = 0;
return v___x_3796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3797_, lean_object* v_n_3798_){
_start:
{
uint8_t v_res_3799_; lean_object* v_r_3800_; 
v_res_3799_ = l_Lean_Expr_isAppOf(v_e_3797_, v_n_3798_);
lean_dec(v_n_3798_);
lean_dec_ref(v_e_3797_);
v_r_3800_ = lean_box(v_res_3799_);
return v_r_3800_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3801_, lean_object* v_x_3802_, lean_object* v_x_3803_){
_start:
{
switch(lean_obj_tag(v_x_3801_))
{
case 4:
{
lean_object* v_declName_3804_; lean_object* v___x_3805_; uint8_t v___x_3806_; 
v_declName_3804_ = lean_ctor_get(v_x_3801_, 0);
v___x_3805_ = lean_unsigned_to_nat(0u);
v___x_3806_ = lean_nat_dec_eq(v_x_3803_, v___x_3805_);
lean_dec(v_x_3803_);
if (v___x_3806_ == 0)
{
return v___x_3806_;
}
else
{
uint8_t v___x_3807_; 
v___x_3807_ = lean_name_eq(v_declName_3804_, v_x_3802_);
return v___x_3807_;
}
}
case 5:
{
lean_object* v_fn_3808_; lean_object* v_zero_3809_; uint8_t v_isZero_3810_; 
v_fn_3808_ = lean_ctor_get(v_x_3801_, 0);
v_zero_3809_ = lean_unsigned_to_nat(0u);
v_isZero_3810_ = lean_nat_dec_eq(v_x_3803_, v_zero_3809_);
if (v_isZero_3810_ == 0)
{
lean_object* v_one_3811_; lean_object* v_n_3812_; 
v_one_3811_ = lean_unsigned_to_nat(1u);
v_n_3812_ = lean_nat_sub(v_x_3803_, v_one_3811_);
lean_dec(v_x_3803_);
v_x_3801_ = v_fn_3808_;
v_x_3803_ = v_n_3812_;
goto _start;
}
else
{
uint8_t v___x_3814_; 
lean_dec(v_x_3803_);
v___x_3814_ = 0;
return v___x_3814_;
}
}
default: 
{
uint8_t v___x_3815_; 
lean_dec(v_x_3803_);
v___x_3815_ = 0;
return v___x_3815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3816_, lean_object* v_x_3817_, lean_object* v_x_3818_){
_start:
{
uint8_t v_res_3819_; lean_object* v_r_3820_; 
v_res_3819_ = l_Lean_Expr_isAppOfArity(v_x_3816_, v_x_3817_, v_x_3818_);
lean_dec(v_x_3817_);
lean_dec_ref(v_x_3816_);
v_r_3820_ = lean_box(v_res_3819_);
return v_r_3820_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3821_, lean_object* v_x_3822_, lean_object* v_x_3823_){
_start:
{
switch(lean_obj_tag(v_x_3821_))
{
case 10:
{
lean_object* v_expr_3824_; 
v_expr_3824_ = lean_ctor_get(v_x_3821_, 1);
v_x_3821_ = v_expr_3824_;
goto _start;
}
case 4:
{
lean_object* v_declName_3826_; lean_object* v___x_3827_; uint8_t v___x_3828_; 
v_declName_3826_ = lean_ctor_get(v_x_3821_, 0);
v___x_3827_ = lean_unsigned_to_nat(0u);
v___x_3828_ = lean_nat_dec_eq(v_x_3823_, v___x_3827_);
lean_dec(v_x_3823_);
if (v___x_3828_ == 0)
{
return v___x_3828_;
}
else
{
uint8_t v___x_3829_; 
v___x_3829_ = lean_name_eq(v_declName_3826_, v_x_3822_);
return v___x_3829_;
}
}
case 5:
{
lean_object* v_fn_3830_; lean_object* v_zero_3831_; uint8_t v_isZero_3832_; 
v_fn_3830_ = lean_ctor_get(v_x_3821_, 0);
v_zero_3831_ = lean_unsigned_to_nat(0u);
v_isZero_3832_ = lean_nat_dec_eq(v_x_3823_, v_zero_3831_);
if (v_isZero_3832_ == 0)
{
lean_object* v_one_3833_; lean_object* v_n_3834_; 
v_one_3833_ = lean_unsigned_to_nat(1u);
v_n_3834_ = lean_nat_sub(v_x_3823_, v_one_3833_);
lean_dec(v_x_3823_);
v_x_3821_ = v_fn_3830_;
v_x_3823_ = v_n_3834_;
goto _start;
}
else
{
uint8_t v___x_3836_; 
lean_dec(v_x_3823_);
v___x_3836_ = 0;
return v___x_3836_;
}
}
default: 
{
uint8_t v___x_3837_; 
lean_dec(v_x_3823_);
v___x_3837_ = 0;
return v___x_3837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3838_, lean_object* v_x_3839_, lean_object* v_x_3840_){
_start:
{
uint8_t v_res_3841_; lean_object* v_r_3842_; 
v_res_3841_ = l_Lean_Expr_isAppOfArity_x27(v_x_3838_, v_x_3839_, v_x_3840_);
lean_dec(v_x_3839_);
lean_dec_ref(v_x_3838_);
v_r_3842_ = lean_box(v_res_3841_);
return v_r_3842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3843_, lean_object* v_x_3844_){
_start:
{
if (lean_obj_tag(v_x_3843_) == 5)
{
lean_object* v_fn_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v_fn_3845_ = lean_ctor_get(v_x_3843_, 0);
v___x_3846_ = lean_unsigned_to_nat(1u);
v___x_3847_ = lean_nat_add(v_x_3844_, v___x_3846_);
lean_dec(v_x_3844_);
v_x_3843_ = v_fn_3845_;
v_x_3844_ = v___x_3847_;
goto _start;
}
else
{
return v_x_3844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3849_, lean_object* v_x_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3849_, v_x_3850_);
lean_dec_ref(v_x_3849_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3852_){
_start:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3853_ = lean_unsigned_to_nat(0u);
v___x_3854_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3852_, v___x_3853_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lean_Expr_getAppNumArgs(v_e_3855_);
lean_dec_ref(v_e_3855_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3857_, lean_object* v_a_3858_){
_start:
{
switch(lean_obj_tag(v_a_3857_))
{
case 10:
{
lean_object* v_expr_3859_; 
v_expr_3859_ = lean_ctor_get(v_a_3857_, 1);
v_a_3857_ = v_expr_3859_;
goto _start;
}
case 5:
{
lean_object* v_fn_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v_fn_3861_ = lean_ctor_get(v_a_3857_, 0);
v___x_3862_ = lean_unsigned_to_nat(1u);
v___x_3863_ = lean_nat_add(v_a_3858_, v___x_3862_);
lean_dec(v_a_3858_);
v_a_3857_ = v_fn_3861_;
v_a_3858_ = v___x_3863_;
goto _start;
}
default: 
{
return v_a_3858_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3865_, v_a_3866_);
lean_dec_ref(v_a_3865_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3868_){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = lean_unsigned_to_nat(0u);
v___x_3870_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3868_, v___x_3869_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3871_);
lean_dec_ref(v_e_3871_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3873_, lean_object* v_x_3874_){
_start:
{
lean_object* v_zero_3875_; uint8_t v_isZero_3876_; 
v_zero_3875_ = lean_unsigned_to_nat(0u);
v_isZero_3876_ = lean_nat_dec_eq(v_x_3873_, v_zero_3875_);
if (v_isZero_3876_ == 0)
{
if (lean_obj_tag(v_x_3874_) == 5)
{
lean_object* v_fn_3877_; lean_object* v_one_3878_; lean_object* v_n_3879_; 
v_fn_3877_ = lean_ctor_get(v_x_3874_, 0);
v_one_3878_ = lean_unsigned_to_nat(1u);
v_n_3879_ = lean_nat_sub(v_x_3873_, v_one_3878_);
lean_dec(v_x_3873_);
v_x_3873_ = v_n_3879_;
v_x_3874_ = v_fn_3877_;
goto _start;
}
else
{
lean_dec(v_x_3873_);
lean_inc_ref(v_x_3874_);
return v_x_3874_;
}
}
else
{
lean_dec(v_x_3873_);
lean_inc_ref(v_x_3874_);
return v_x_3874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_3881_, lean_object* v_x_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_Lean_Expr_getBoundedAppFn(v_x_3881_, v_x_3882_);
lean_dec_ref(v_x_3882_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_3884_, lean_object* v_x_3885_, lean_object* v_x_3886_){
_start:
{
if (lean_obj_tag(v_x_3884_) == 5)
{
lean_object* v_fn_3887_; lean_object* v_arg_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v_fn_3887_ = lean_ctor_get(v_x_3884_, 0);
lean_inc_ref(v_fn_3887_);
v_arg_3888_ = lean_ctor_get(v_x_3884_, 1);
lean_inc_ref(v_arg_3888_);
lean_dec_ref(v_x_3884_);
v___x_3889_ = lean_array_set(v_x_3885_, v_x_3886_, v_arg_3888_);
v___x_3890_ = lean_unsigned_to_nat(1u);
v___x_3891_ = lean_nat_sub(v_x_3886_, v___x_3890_);
lean_dec(v_x_3886_);
v_x_3884_ = v_fn_3887_;
v_x_3885_ = v___x_3889_;
v_x_3886_ = v___x_3891_;
goto _start;
}
else
{
lean_dec(v_x_3886_);
lean_dec_ref(v_x_3884_);
return v_x_3885_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_3893_; lean_object* v_dummy_3894_; 
v___x_3893_ = lean_box(0);
v_dummy_3894_ = l_Lean_Expr_sort___override(v___x_3893_);
return v_dummy_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_3895_){
_start:
{
lean_object* v_dummy_3896_; lean_object* v_nargs_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v_dummy_3896_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3897_ = l_Lean_Expr_getAppNumArgs(v_e_3895_);
lean_inc(v_nargs_3897_);
v___x_3898_ = lean_mk_array(v_nargs_3897_, v_dummy_3896_);
v___x_3899_ = lean_unsigned_to_nat(1u);
v___x_3900_ = lean_nat_sub(v_nargs_3897_, v___x_3899_);
lean_dec(v_nargs_3897_);
v___x_3901_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3895_, v___x_3898_, v___x_3900_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_3902_, lean_object* v_x_3903_, lean_object* v_x_3904_){
_start:
{
if (lean_obj_tag(v_x_3902_) == 5)
{
lean_object* v_fn_3905_; lean_object* v_arg_3906_; lean_object* v_zero_3907_; uint8_t v_isZero_3908_; 
v_fn_3905_ = lean_ctor_get(v_x_3902_, 0);
lean_inc_ref(v_fn_3905_);
v_arg_3906_ = lean_ctor_get(v_x_3902_, 1);
lean_inc_ref(v_arg_3906_);
lean_dec_ref(v_x_3902_);
v_zero_3907_ = lean_unsigned_to_nat(0u);
v_isZero_3908_ = lean_nat_dec_eq(v_x_3904_, v_zero_3907_);
if (v_isZero_3908_ == 0)
{
lean_object* v_one_3909_; lean_object* v_n_3910_; lean_object* v___x_3911_; 
v_one_3909_ = lean_unsigned_to_nat(1u);
v_n_3910_ = lean_nat_sub(v_x_3904_, v_one_3909_);
lean_dec(v_x_3904_);
v___x_3911_ = lean_array_set(v_x_3903_, v_n_3910_, v_arg_3906_);
v_x_3902_ = v_fn_3905_;
v_x_3903_ = v___x_3911_;
v_x_3904_ = v_n_3910_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3906_);
lean_dec_ref(v_fn_3905_);
lean_dec(v_x_3904_);
return v_x_3903_;
}
}
else
{
lean_dec(v_x_3904_);
lean_dec_ref(v_x_3902_);
return v_x_3903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_3913_, lean_object* v_e_3914_){
_start:
{
lean_object* v_dummy_3915_; lean_object* v___y_3917_; lean_object* v___x_3920_; uint8_t v___x_3921_; 
v_dummy_3915_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_3920_ = l_Lean_Expr_getAppNumArgs(v_e_3914_);
v___x_3921_ = lean_nat_dec_le(v_maxArgs_3913_, v___x_3920_);
if (v___x_3921_ == 0)
{
lean_dec(v_maxArgs_3913_);
v___y_3917_ = v___x_3920_;
goto v___jp_3916_;
}
else
{
lean_dec(v___x_3920_);
v___y_3917_ = v_maxArgs_3913_;
goto v___jp_3916_;
}
v___jp_3916_:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
lean_inc(v___y_3917_);
v___x_3918_ = lean_mk_array(v___y_3917_, v_dummy_3915_);
v___x_3919_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_3914_, v___x_3918_, v___y_3917_);
return v___x_3919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_3922_, lean_object* v_x_3923_){
_start:
{
if (lean_obj_tag(v_x_3922_) == 5)
{
lean_object* v_fn_3924_; lean_object* v_arg_3925_; lean_object* v___x_3926_; 
v_fn_3924_ = lean_ctor_get(v_x_3922_, 0);
lean_inc_ref(v_fn_3924_);
v_arg_3925_ = lean_ctor_get(v_x_3922_, 1);
lean_inc_ref(v_arg_3925_);
lean_dec_ref(v_x_3922_);
v___x_3926_ = lean_array_push(v_x_3923_, v_arg_3925_);
v_x_3922_ = v_fn_3924_;
v_x_3923_ = v___x_3926_;
goto _start;
}
else
{
lean_dec_ref(v_x_3922_);
return v_x_3923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_3928_){
_start:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3929_ = l_Lean_Expr_getAppNumArgs(v_e_3928_);
v___x_3930_ = lean_mk_empty_array_with_capacity(v___x_3929_);
lean_dec(v___x_3929_);
v___x_3931_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3928_, v___x_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_3932_, lean_object* v_x_3933_, lean_object* v_x_3934_, lean_object* v_x_3935_){
_start:
{
if (lean_obj_tag(v_x_3933_) == 5)
{
lean_object* v_fn_3936_; lean_object* v_arg_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v_fn_3936_ = lean_ctor_get(v_x_3933_, 0);
lean_inc_ref(v_fn_3936_);
v_arg_3937_ = lean_ctor_get(v_x_3933_, 1);
lean_inc_ref(v_arg_3937_);
lean_dec_ref(v_x_3933_);
v___x_3938_ = lean_array_set(v_x_3934_, v_x_3935_, v_arg_3937_);
v___x_3939_ = lean_unsigned_to_nat(1u);
v___x_3940_ = lean_nat_sub(v_x_3935_, v___x_3939_);
lean_dec(v_x_3935_);
v_x_3933_ = v_fn_3936_;
v_x_3934_ = v___x_3938_;
v_x_3935_ = v___x_3940_;
goto _start;
}
else
{
lean_object* v___x_3942_; 
lean_dec(v_x_3935_);
v___x_3942_ = lean_apply_2(v_k_3932_, v_x_3933_, v_x_3934_);
return v___x_3942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_3943_, lean_object* v_k_3944_, lean_object* v_x_3945_, lean_object* v_x_3946_, lean_object* v_x_3947_){
_start:
{
lean_object* v___x_3948_; 
v___x_3948_ = l_Lean_Expr_withAppAux___redArg(v_k_3944_, v_x_3945_, v_x_3946_, v_x_3947_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_3949_, lean_object* v_k_3950_){
_start:
{
lean_object* v_dummy_3951_; lean_object* v_nargs_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v_dummy_3951_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3952_ = l_Lean_Expr_getAppNumArgs(v_e_3949_);
lean_inc(v_nargs_3952_);
v___x_3953_ = lean_mk_array(v_nargs_3952_, v_dummy_3951_);
v___x_3954_ = lean_unsigned_to_nat(1u);
v___x_3955_ = lean_nat_sub(v_nargs_3952_, v___x_3954_);
lean_dec(v_nargs_3952_);
v___x_3956_ = l_Lean_Expr_withAppAux___redArg(v_k_3950_, v_e_3949_, v___x_3953_, v___x_3955_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_3957_, lean_object* v_e_3958_, lean_object* v_k_3959_){
_start:
{
lean_object* v_dummy_3960_; lean_object* v_nargs_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v_dummy_3960_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3961_ = l_Lean_Expr_getAppNumArgs(v_e_3958_);
lean_inc(v_nargs_3961_);
v___x_3962_ = lean_mk_array(v_nargs_3961_, v_dummy_3960_);
v___x_3963_ = lean_unsigned_to_nat(1u);
v___x_3964_ = lean_nat_sub(v_nargs_3961_, v___x_3963_);
lean_dec(v_nargs_3961_);
v___x_3965_ = l_Lean_Expr_withAppAux___redArg(v_k_3959_, v_e_3958_, v___x_3962_, v___x_3964_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_3966_, lean_object* v_x_3967_, lean_object* v_x_3968_){
_start:
{
if (lean_obj_tag(v_x_3966_) == 5)
{
lean_object* v_fn_3969_; lean_object* v_arg_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v_fn_3969_ = lean_ctor_get(v_x_3966_, 0);
lean_inc_ref(v_fn_3969_);
v_arg_3970_ = lean_ctor_get(v_x_3966_, 1);
lean_inc_ref(v_arg_3970_);
lean_dec_ref(v_x_3966_);
v___x_3971_ = lean_array_set(v_x_3967_, v_x_3968_, v_arg_3970_);
v___x_3972_ = lean_unsigned_to_nat(1u);
v___x_3973_ = lean_nat_sub(v_x_3968_, v___x_3972_);
lean_dec(v_x_3968_);
v_x_3966_ = v_fn_3969_;
v_x_3967_ = v___x_3971_;
v_x_3968_ = v___x_3973_;
goto _start;
}
else
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
lean_dec(v_x_3968_);
v___x_3975_ = l_Lean_Expr_constName(v_x_3966_);
lean_dec_ref(v_x_3966_);
v___x_3976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
lean_ctor_set(v___x_3976_, 1, v_x_3967_);
return v___x_3976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_3977_){
_start:
{
lean_object* v_dummy_3978_; lean_object* v_nargs_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v_dummy_3978_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3979_ = l_Lean_Expr_getAppNumArgs(v_e_3977_);
lean_inc(v_nargs_3979_);
v___x_3980_ = lean_mk_array(v_nargs_3979_, v_dummy_3978_);
v___x_3981_ = lean_unsigned_to_nat(1u);
v___x_3982_ = lean_nat_sub(v_nargs_3979_, v___x_3981_);
lean_dec(v_nargs_3979_);
v___x_3983_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_3977_, v___x_3980_, v___x_3982_);
return v___x_3983_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Array_instInhabited(lean_box(0));
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_3985_){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3986_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_3987_ = lean_panic_fn_borrowed(v___x_3986_, v_msg_3985_);
return v___x_3987_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3990_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_3991_ = lean_unsigned_to_nat(27u);
v___x_3992_ = lean_unsigned_to_nat(1237u);
v___x_3993_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_3994_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3995_ = l_mkPanicMessageWithDecl(v___x_3994_, v___x_3993_, v___x_3992_, v___x_3991_, v___x_3990_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_){
_start:
{
lean_object* v_zero_3999_; uint8_t v_isZero_4000_; 
v_zero_3999_ = lean_unsigned_to_nat(0u);
v_isZero_4000_ = lean_nat_dec_eq(v_a_3996_, v_zero_3999_);
if (v_isZero_4000_ == 1)
{
lean_dec_ref(v_a_3997_);
lean_dec(v_a_3996_);
return v_a_3998_;
}
else
{
if (lean_obj_tag(v_a_3997_) == 5)
{
lean_object* v_fn_4001_; lean_object* v_arg_4002_; lean_object* v_one_4003_; lean_object* v_n_4004_; lean_object* v___x_4005_; 
v_fn_4001_ = lean_ctor_get(v_a_3997_, 0);
lean_inc_ref(v_fn_4001_);
v_arg_4002_ = lean_ctor_get(v_a_3997_, 1);
lean_inc_ref(v_arg_4002_);
lean_dec_ref(v_a_3997_);
v_one_4003_ = lean_unsigned_to_nat(1u);
v_n_4004_ = lean_nat_sub(v_a_3996_, v_one_4003_);
lean_dec(v_a_3996_);
v___x_4005_ = lean_array_set(v_a_3998_, v_n_4004_, v_arg_4002_);
v_a_3996_ = v_n_4004_;
v_a_3997_ = v_fn_4001_;
v_a_3998_ = v___x_4005_;
goto _start;
}
else
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
lean_dec_ref(v_a_3998_);
lean_dec_ref(v_a_3997_);
lean_dec(v_a_3996_);
v___x_4007_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_4008_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_4007_);
return v___x_4008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_4009_, lean_object* v_n_4010_){
_start:
{
lean_object* v_dummy_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v_dummy_4011_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_4010_);
v___x_4012_ = lean_mk_array(v_n_4010_, v_dummy_4011_);
v___x_4013_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_4010_, v_e_4009_, v___x_4012_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_4014_, lean_object* v_n_4015_){
_start:
{
lean_object* v_zero_4016_; uint8_t v_isZero_4017_; 
v_zero_4016_ = lean_unsigned_to_nat(0u);
v_isZero_4017_ = lean_nat_dec_eq(v_n_4015_, v_zero_4016_);
if (v_isZero_4017_ == 1)
{
lean_dec(v_n_4015_);
lean_inc_ref(v_e_4014_);
return v_e_4014_;
}
else
{
if (lean_obj_tag(v_e_4014_) == 5)
{
lean_object* v_fn_4018_; lean_object* v_one_4019_; lean_object* v_n_4020_; 
v_fn_4018_ = lean_ctor_get(v_e_4014_, 0);
v_one_4019_ = lean_unsigned_to_nat(1u);
v_n_4020_ = lean_nat_sub(v_n_4015_, v_one_4019_);
lean_dec(v_n_4015_);
v_e_4014_ = v_fn_4018_;
v_n_4015_ = v_n_4020_;
goto _start;
}
else
{
lean_dec(v_n_4015_);
lean_inc_ref(v_e_4014_);
return v_e_4014_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_4022_, lean_object* v_n_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l_Lean_Expr_stripArgsN(v_e_4022_, v_n_4023_);
lean_dec_ref(v_e_4022_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_4025_, lean_object* v_n_4026_){
_start:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4027_ = l_Lean_Expr_getAppNumArgs(v_e_4025_);
v___x_4028_ = lean_nat_sub(v___x_4027_, v_n_4026_);
lean_dec(v___x_4027_);
v___x_4029_ = l_Lean_Expr_stripArgsN(v_e_4025_, v___x_4028_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_4030_, lean_object* v_n_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l_Lean_Expr_getAppPrefix(v_e_4030_, v_n_4031_);
lean_dec(v_n_4031_);
lean_dec_ref(v_e_4030_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_4033_, lean_object* v_inst_4034_, lean_object* v_f_4035_, lean_object* v_x_4036_){
_start:
{
size_t v_sz_4037_; size_t v___x_4038_; lean_object* v___x_4039_; 
v_sz_4037_ = lean_array_size(v_args_4033_);
v___x_4038_ = ((size_t)0ULL);
v___x_4039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4034_, v_f_4035_, v_sz_4037_, v___x_4038_, v_args_4033_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_4041_, lean_object* v_inst_4042_, lean_object* v_f_4043_, lean_object* v_toSeq_4044_, lean_object* v_fn_4045_, lean_object* v_args_4046_){
_start:
{
lean_object* v_map_4047_; lean_object* v___f_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v_map_4047_ = lean_ctor_get(v_toFunctor_4041_, 0);
lean_inc(v_map_4047_);
lean_dec_ref(v_toFunctor_4041_);
lean_inc(v_f_4043_);
v___f_4048_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4048_, 0, v_args_4046_);
lean_closure_set(v___f_4048_, 1, v_inst_4042_);
lean_closure_set(v___f_4048_, 2, v_f_4043_);
v___x_4049_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_4050_ = lean_apply_1(v_f_4043_, v_fn_4045_);
v___x_4051_ = lean_apply_4(v_map_4047_, lean_box(0), lean_box(0), v___x_4049_, v___x_4050_);
v___x_4052_ = lean_apply_4(v_toSeq_4044_, lean_box(0), lean_box(0), v___x_4051_, v___f_4048_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_4053_, lean_object* v_f_4054_, lean_object* v_e_4055_){
_start:
{
lean_object* v_toApplicative_4056_; lean_object* v_toFunctor_4057_; lean_object* v_toSeq_4058_; lean_object* v___f_4059_; lean_object* v_dummy_4060_; lean_object* v_nargs_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v_toApplicative_4056_ = lean_ctor_get(v_inst_4053_, 0);
v_toFunctor_4057_ = lean_ctor_get(v_toApplicative_4056_, 0);
lean_inc_ref(v_toFunctor_4057_);
v_toSeq_4058_ = lean_ctor_get(v_toApplicative_4056_, 2);
lean_inc(v_toSeq_4058_);
v___f_4059_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_4059_, 0, v_toFunctor_4057_);
lean_closure_set(v___f_4059_, 1, v_inst_4053_);
lean_closure_set(v___f_4059_, 2, v_f_4054_);
lean_closure_set(v___f_4059_, 3, v_toSeq_4058_);
v_dummy_4060_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4061_ = l_Lean_Expr_getAppNumArgs(v_e_4055_);
lean_inc(v_nargs_4061_);
v___x_4062_ = lean_mk_array(v_nargs_4061_, v_dummy_4060_);
v___x_4063_ = lean_unsigned_to_nat(1u);
v___x_4064_ = lean_nat_sub(v_nargs_4061_, v___x_4063_);
lean_dec(v_nargs_4061_);
v___x_4065_ = l_Lean_Expr_withAppAux___redArg(v___f_4059_, v_e_4055_, v___x_4062_, v___x_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_4066_, lean_object* v_inst_4067_, lean_object* v_f_4068_, lean_object* v_e_4069_){
_start:
{
lean_object* v___x_4070_; 
v___x_4070_ = l_Lean_Expr_traverseApp___redArg(v_inst_4067_, v_f_4068_, v_e_4069_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_4071_, lean_object* v_x_4072_, lean_object* v_x_4073_){
_start:
{
if (lean_obj_tag(v_x_4072_) == 5)
{
lean_object* v_fn_4074_; lean_object* v_arg_4075_; lean_object* v___x_4076_; 
v_fn_4074_ = lean_ctor_get(v_x_4072_, 0);
lean_inc_ref(v_fn_4074_);
v_arg_4075_ = lean_ctor_get(v_x_4072_, 1);
lean_inc_ref(v_arg_4075_);
lean_dec_ref(v_x_4072_);
v___x_4076_ = lean_array_push(v_x_4073_, v_arg_4075_);
v_x_4072_ = v_fn_4074_;
v_x_4073_ = v___x_4076_;
goto _start;
}
else
{
lean_object* v___x_4078_; 
v___x_4078_ = lean_apply_2(v_k_4071_, v_x_4072_, v_x_4073_);
return v___x_4078_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_4079_, lean_object* v_k_4080_, lean_object* v_x_4081_, lean_object* v_x_4082_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4080_, v_x_4081_, v_x_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_4084_, lean_object* v_k_4085_){
_start:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4086_ = l_Lean_Expr_getAppNumArgs(v_e_4084_);
v___x_4087_ = lean_mk_empty_array_with_capacity(v___x_4086_);
lean_dec(v___x_4086_);
v___x_4088_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4085_, v_e_4084_, v___x_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_4089_, lean_object* v_e_4090_, lean_object* v_k_4091_){
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
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_4095_, lean_object* v_x_4096_, lean_object* v_x_4097_){
_start:
{
if (lean_obj_tag(v_x_4095_) == 5)
{
lean_object* v_fn_4098_; lean_object* v_arg_4099_; lean_object* v_zero_4100_; uint8_t v_isZero_4101_; 
v_fn_4098_ = lean_ctor_get(v_x_4095_, 0);
v_arg_4099_ = lean_ctor_get(v_x_4095_, 1);
v_zero_4100_ = lean_unsigned_to_nat(0u);
v_isZero_4101_ = lean_nat_dec_eq(v_x_4096_, v_zero_4100_);
if (v_isZero_4101_ == 1)
{
lean_dec(v_x_4096_);
lean_inc_ref(v_arg_4099_);
return v_arg_4099_;
}
else
{
lean_object* v_one_4102_; lean_object* v_n_4103_; 
v_one_4102_ = lean_unsigned_to_nat(1u);
v_n_4103_ = lean_nat_sub(v_x_4096_, v_one_4102_);
lean_dec(v_x_4096_);
v_x_4095_ = v_fn_4098_;
v_x_4096_ = v_n_4103_;
goto _start;
}
}
else
{
lean_dec(v_x_4096_);
lean_inc_ref(v_x_4097_);
return v_x_4097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_4105_, lean_object* v_x_4106_, lean_object* v_x_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Lean_Expr_getRevArgD(v_x_4105_, v_x_4106_, v_x_4107_);
lean_dec_ref(v_x_4107_);
lean_dec_ref(v_x_4105_);
return v_res_4108_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4111_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4112_ = lean_unsigned_to_nat(20u);
v___x_4113_ = lean_unsigned_to_nat(1278u);
v___x_4114_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4115_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4116_ = l_mkPanicMessageWithDecl(v___x_4115_, v___x_4114_, v___x_4113_, v___x_4112_, v___x_4111_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4117_, lean_object* v_x_4118_){
_start:
{
if (lean_obj_tag(v_x_4117_) == 5)
{
lean_object* v_fn_4119_; lean_object* v_arg_4120_; lean_object* v_zero_4121_; uint8_t v_isZero_4122_; 
v_fn_4119_ = lean_ctor_get(v_x_4117_, 0);
v_arg_4120_ = lean_ctor_get(v_x_4117_, 1);
v_zero_4121_ = lean_unsigned_to_nat(0u);
v_isZero_4122_ = lean_nat_dec_eq(v_x_4118_, v_zero_4121_);
if (v_isZero_4122_ == 1)
{
lean_dec(v_x_4118_);
lean_inc_ref(v_arg_4120_);
return v_arg_4120_;
}
else
{
lean_object* v_one_4123_; lean_object* v_n_4124_; 
v_one_4123_ = lean_unsigned_to_nat(1u);
v_n_4124_ = lean_nat_sub(v_x_4118_, v_one_4123_);
lean_dec(v_x_4118_);
v_x_4117_ = v_fn_4119_;
v_x_4118_ = v_n_4124_;
goto _start;
}
}
else
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
lean_dec(v_x_4118_);
v___x_4126_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4127_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4126_);
return v___x_4127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4128_, lean_object* v_x_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_Lean_Expr_getRevArg_x21(v_x_4128_, v_x_4129_);
lean_dec_ref(v_x_4128_);
return v_res_4130_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4132_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4133_ = lean_unsigned_to_nat(20u);
v___x_4134_ = lean_unsigned_to_nat(1285u);
v___x_4135_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4136_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4137_ = l_mkPanicMessageWithDecl(v___x_4136_, v___x_4135_, v___x_4134_, v___x_4133_, v___x_4132_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4138_, lean_object* v_x_4139_){
_start:
{
switch(lean_obj_tag(v_x_4138_))
{
case 10:
{
lean_object* v_expr_4140_; 
v_expr_4140_ = lean_ctor_get(v_x_4138_, 1);
v_x_4138_ = v_expr_4140_;
goto _start;
}
case 5:
{
lean_object* v_fn_4142_; lean_object* v_arg_4143_; lean_object* v_zero_4144_; uint8_t v_isZero_4145_; 
v_fn_4142_ = lean_ctor_get(v_x_4138_, 0);
v_arg_4143_ = lean_ctor_get(v_x_4138_, 1);
v_zero_4144_ = lean_unsigned_to_nat(0u);
v_isZero_4145_ = lean_nat_dec_eq(v_x_4139_, v_zero_4144_);
if (v_isZero_4145_ == 1)
{
lean_dec(v_x_4139_);
lean_inc_ref(v_arg_4143_);
return v_arg_4143_;
}
else
{
lean_object* v_one_4146_; lean_object* v_n_4147_; 
v_one_4146_ = lean_unsigned_to_nat(1u);
v_n_4147_ = lean_nat_sub(v_x_4139_, v_one_4146_);
lean_dec(v_x_4139_);
v_x_4138_ = v_fn_4142_;
v_x_4139_ = v_n_4147_;
goto _start;
}
}
default: 
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
lean_dec(v_x_4139_);
v___x_4149_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4150_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4149_);
return v___x_4150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4151_, lean_object* v_x_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4151_, v_x_4152_);
lean_dec_ref(v_x_4151_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4154_, lean_object* v_i_4155_, lean_object* v_n_4156_){
_start:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4157_ = lean_nat_sub(v_n_4156_, v_i_4155_);
v___x_4158_ = lean_unsigned_to_nat(1u);
v___x_4159_ = lean_nat_sub(v___x_4157_, v___x_4158_);
lean_dec(v___x_4157_);
v___x_4160_ = l_Lean_Expr_getRevArg_x21(v_e_4154_, v___x_4159_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4161_, lean_object* v_i_4162_, lean_object* v_n_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_Expr_getArg_x21(v_e_4161_, v_i_4162_, v_n_4163_);
lean_dec(v_n_4163_);
lean_dec(v_i_4162_);
lean_dec_ref(v_e_4161_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4165_, lean_object* v_i_4166_, lean_object* v_n_4167_){
_start:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4168_ = lean_nat_sub(v_n_4167_, v_i_4166_);
v___x_4169_ = lean_unsigned_to_nat(1u);
v___x_4170_ = lean_nat_sub(v___x_4168_, v___x_4169_);
lean_dec(v___x_4168_);
v___x_4171_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4165_, v___x_4170_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4172_, lean_object* v_i_4173_, lean_object* v_n_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Lean_Expr_getArg_x21_x27(v_e_4172_, v_i_4173_, v_n_4174_);
lean_dec(v_n_4174_);
lean_dec(v_i_4173_);
lean_dec_ref(v_e_4172_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4176_, lean_object* v_i_4177_, lean_object* v_v_u2080_4178_, lean_object* v_n_4179_){
_start:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4180_ = lean_nat_sub(v_n_4179_, v_i_4177_);
v___x_4181_ = lean_unsigned_to_nat(1u);
v___x_4182_ = lean_nat_sub(v___x_4180_, v___x_4181_);
lean_dec(v___x_4180_);
v___x_4183_ = l_Lean_Expr_getRevArgD(v_e_4176_, v___x_4182_, v_v_u2080_4178_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4184_, lean_object* v_i_4185_, lean_object* v_v_u2080_4186_, lean_object* v_n_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_Lean_Expr_getArgD(v_e_4184_, v_i_4185_, v_v_u2080_4186_, v_n_4187_);
lean_dec(v_n_4187_);
lean_dec_ref(v_v_u2080_4186_);
lean_dec(v_i_4185_);
lean_dec_ref(v_e_4184_);
return v_res_4188_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4189_){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; uint8_t v___x_4192_; 
v___x_4190_ = lean_unsigned_to_nat(0u);
v___x_4191_ = l_Lean_Expr_looseBVarRange(v_e_4189_);
v___x_4192_ = lean_nat_dec_lt(v___x_4190_, v___x_4191_);
lean_dec(v___x_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4193_){
_start:
{
uint8_t v_res_4194_; lean_object* v_r_4195_; 
v_res_4194_ = l_Lean_Expr_hasLooseBVars(v_e_4193_);
lean_dec_ref(v_e_4193_);
v_r_4195_ = lean_box(v_res_4194_);
return v_r_4195_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4196_){
_start:
{
if (lean_obj_tag(v_e_4196_) == 7)
{
lean_object* v_body_4197_; uint8_t v___x_4198_; 
v_body_4197_ = lean_ctor_get(v_e_4196_, 2);
v___x_4198_ = l_Lean_Expr_hasLooseBVars(v_body_4197_);
if (v___x_4198_ == 0)
{
uint8_t v___x_4199_; 
v___x_4199_ = 1;
return v___x_4199_;
}
else
{
uint8_t v___x_4200_; 
v___x_4200_ = 0;
return v___x_4200_;
}
}
else
{
uint8_t v___x_4201_; 
v___x_4201_ = 0;
return v___x_4201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4202_){
_start:
{
uint8_t v_res_4203_; lean_object* v_r_4204_; 
v_res_4203_ = l_Lean_Expr_isArrow(v_e_4202_);
lean_dec_ref(v_e_4202_);
v_r_4204_ = lean_box(v_res_4203_);
return v_r_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4207_, lean_object* v_bvarIdx_4208_){
_start:
{
uint8_t v_res_4209_; lean_object* v_r_4210_; 
v_res_4209_ = lean_expr_has_loose_bvar(v_e_4207_, v_bvarIdx_4208_);
lean_dec(v_bvarIdx_4208_);
lean_dec_ref(v_e_4207_);
v_r_4210_ = lean_box(v_res_4209_);
return v_r_4210_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4211_, lean_object* v_bvarIdx_4212_, uint8_t v_considerRange_4213_){
_start:
{
if (lean_obj_tag(v_e_4211_) == 7)
{
lean_object* v_binderType_4214_; lean_object* v_body_4215_; uint8_t v_binderInfo_4216_; uint8_t v___y_4218_; uint8_t v___x_4222_; 
v_binderType_4214_ = lean_ctor_get(v_e_4211_, 1);
v_body_4215_ = lean_ctor_get(v_e_4211_, 2);
v_binderInfo_4216_ = lean_ctor_get_uint8(v_e_4211_, sizeof(void*)*3 + 8);
v___x_4222_ = lean_expr_has_loose_bvar(v_binderType_4214_, v_bvarIdx_4212_);
if (v___x_4222_ == 0)
{
v___y_4218_ = v___x_4222_;
goto v___jp_4217_;
}
else
{
uint8_t v___x_4223_; 
v___x_4223_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4216_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4224_; uint8_t v___x_4225_; 
v___x_4224_ = lean_unsigned_to_nat(0u);
v___x_4225_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4215_, v___x_4224_, v_considerRange_4213_);
v___y_4218_ = v___x_4225_;
goto v___jp_4217_;
}
else
{
v___y_4218_ = v___x_4223_;
goto v___jp_4217_;
}
}
v___jp_4217_:
{
if (v___y_4218_ == 0)
{
lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4219_ = lean_unsigned_to_nat(1u);
v___x_4220_ = lean_nat_add(v_bvarIdx_4212_, v___x_4219_);
lean_dec(v_bvarIdx_4212_);
v_e_4211_ = v_body_4215_;
v_bvarIdx_4212_ = v___x_4220_;
goto _start;
}
else
{
lean_dec(v_bvarIdx_4212_);
return v___y_4218_;
}
}
}
else
{
if (v_considerRange_4213_ == 0)
{
lean_dec(v_bvarIdx_4212_);
return v_considerRange_4213_;
}
else
{
uint8_t v___x_4226_; 
v___x_4226_ = lean_expr_has_loose_bvar(v_e_4211_, v_bvarIdx_4212_);
lean_dec(v_bvarIdx_4212_);
return v___x_4226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4227_, lean_object* v_bvarIdx_4228_, lean_object* v_considerRange_4229_){
_start:
{
uint8_t v_considerRange_boxed_4230_; uint8_t v_res_4231_; lean_object* v_r_4232_; 
v_considerRange_boxed_4230_ = lean_unbox(v_considerRange_4229_);
v_res_4231_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4227_, v_bvarIdx_4228_, v_considerRange_boxed_4230_);
lean_dec_ref(v_e_4227_);
v_r_4232_ = lean_box(v_res_4231_);
return v_r_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4236_, lean_object* v_s_4237_, lean_object* v_d_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = lean_expr_lower_loose_bvars(v_e_4236_, v_s_4237_, v_d_4238_);
lean_dec(v_d_4238_);
lean_dec(v_s_4237_);
lean_dec_ref(v_e_4236_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4243_, lean_object* v_s_4244_, lean_object* v_d_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = lean_expr_lift_loose_bvars(v_e_4243_, v_s_4244_, v_d_4245_);
lean_dec(v_d_4245_);
lean_dec(v_s_4244_);
lean_dec_ref(v_e_4243_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4247_, lean_object* v_numParams_4248_, uint8_t v_considerRange_4249_){
_start:
{
if (lean_obj_tag(v_e_4247_) == 7)
{
lean_object* v_binderName_4250_; lean_object* v_binderType_4251_; lean_object* v_body_4252_; uint8_t v_binderInfo_4253_; lean_object* v_zero_4254_; uint8_t v_isZero_4255_; 
v_binderName_4250_ = lean_ctor_get(v_e_4247_, 0);
v_binderType_4251_ = lean_ctor_get(v_e_4247_, 1);
v_body_4252_ = lean_ctor_get(v_e_4247_, 2);
v_binderInfo_4253_ = lean_ctor_get_uint8(v_e_4247_, sizeof(void*)*3 + 8);
v_zero_4254_ = lean_unsigned_to_nat(0u);
v_isZero_4255_ = lean_nat_dec_eq(v_numParams_4248_, v_zero_4254_);
if (v_isZero_4255_ == 0)
{
lean_object* v_one_4256_; lean_object* v_n_4257_; lean_object* v_b_4258_; uint8_t v___y_4260_; uint8_t v___x_4264_; 
lean_inc_ref(v_body_4252_);
lean_inc_ref(v_binderType_4251_);
lean_inc(v_binderName_4250_);
lean_dec_ref(v_e_4247_);
v_one_4256_ = lean_unsigned_to_nat(1u);
v_n_4257_ = lean_nat_sub(v_numParams_4248_, v_one_4256_);
v_b_4258_ = l_Lean_Expr_inferImplicit(v_body_4252_, v_n_4257_, v_considerRange_4249_);
lean_dec(v_n_4257_);
v___x_4264_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4253_);
if (v___x_4264_ == 0)
{
v___y_4260_ = v___x_4264_;
goto v___jp_4259_;
}
else
{
uint8_t v___x_4265_; 
v___x_4265_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4258_, v_zero_4254_, v_considerRange_4249_);
v___y_4260_ = v___x_4265_;
goto v___jp_4259_;
}
v___jp_4259_:
{
if (v___y_4260_ == 0)
{
lean_object* v___x_4261_; 
v___x_4261_ = l_Lean_Expr_forallE___override(v_binderName_4250_, v_binderType_4251_, v_b_4258_, v_binderInfo_4253_);
return v___x_4261_;
}
else
{
uint8_t v___x_4262_; lean_object* v___x_4263_; 
v___x_4262_ = 1;
v___x_4263_ = l_Lean_Expr_forallE___override(v_binderName_4250_, v_binderType_4251_, v_b_4258_, v___x_4262_);
return v___x_4263_;
}
}
}
else
{
return v_e_4247_;
}
}
else
{
return v_e_4247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4266_, lean_object* v_numParams_4267_, lean_object* v_considerRange_4268_){
_start:
{
uint8_t v_considerRange_boxed_4269_; lean_object* v_res_4270_; 
v_considerRange_boxed_4269_ = lean_unbox(v_considerRange_4268_);
v_res_4270_ = l_Lean_Expr_inferImplicit(v_e_4266_, v_numParams_4267_, v_considerRange_boxed_4269_);
lean_dec(v_numParams_4267_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4271_, lean_object* v_binderInfos_x3f_4272_){
_start:
{
if (lean_obj_tag(v_e_4271_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4272_) == 1)
{
lean_object* v_binderName_4273_; lean_object* v_binderType_4274_; lean_object* v_body_4275_; uint8_t v_binderInfo_4276_; lean_object* v_head_4277_; lean_object* v_tail_4278_; lean_object* v_b_4279_; 
v_binderName_4273_ = lean_ctor_get(v_e_4271_, 0);
lean_inc(v_binderName_4273_);
v_binderType_4274_ = lean_ctor_get(v_e_4271_, 1);
lean_inc_ref(v_binderType_4274_);
v_body_4275_ = lean_ctor_get(v_e_4271_, 2);
lean_inc_ref(v_body_4275_);
v_binderInfo_4276_ = lean_ctor_get_uint8(v_e_4271_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_4271_);
v_head_4277_ = lean_ctor_get(v_binderInfos_x3f_4272_, 0);
v_tail_4278_ = lean_ctor_get(v_binderInfos_x3f_4272_, 1);
v_b_4279_ = l_Lean_Expr_updateForallBinderInfos(v_body_4275_, v_tail_4278_);
if (lean_obj_tag(v_head_4277_) == 0)
{
lean_object* v___x_4280_; 
v___x_4280_ = l_Lean_Expr_forallE___override(v_binderName_4273_, v_binderType_4274_, v_b_4279_, v_binderInfo_4276_);
return v___x_4280_;
}
else
{
lean_object* v_val_4281_; uint8_t v___x_4282_; lean_object* v___x_4283_; 
v_val_4281_ = lean_ctor_get(v_head_4277_, 0);
v___x_4282_ = lean_unbox(v_val_4281_);
v___x_4283_ = l_Lean_Expr_forallE___override(v_binderName_4273_, v_binderType_4274_, v_b_4279_, v___x_4282_);
return v___x_4283_;
}
}
else
{
return v_e_4271_;
}
}
else
{
return v_e_4271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4284_, lean_object* v_binderInfos_x3f_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Lean_Expr_updateForallBinderInfos(v_e_4284_, v_binderInfos_x3f_4285_);
lean_dec(v_binderInfos_x3f_4285_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4287_, lean_object* v_binderNames_x3f_4288_){
_start:
{
switch(lean_obj_tag(v_e_4287_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4288_) == 1)
{
lean_object* v_binderName_4289_; lean_object* v_binderType_4290_; lean_object* v_body_4291_; uint8_t v_binderInfo_4292_; lean_object* v_head_4293_; lean_object* v_tail_4294_; lean_object* v_b_4295_; 
v_binderName_4289_ = lean_ctor_get(v_e_4287_, 0);
lean_inc(v_binderName_4289_);
v_binderType_4290_ = lean_ctor_get(v_e_4287_, 1);
lean_inc_ref(v_binderType_4290_);
v_body_4291_ = lean_ctor_get(v_e_4287_, 2);
lean_inc_ref(v_body_4291_);
v_binderInfo_4292_ = lean_ctor_get_uint8(v_e_4287_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_4287_);
v_head_4293_ = lean_ctor_get(v_binderNames_x3f_4288_, 0);
lean_inc(v_head_4293_);
v_tail_4294_ = lean_ctor_get(v_binderNames_x3f_4288_, 1);
lean_inc(v_tail_4294_);
lean_dec_ref(v_binderNames_x3f_4288_);
v_b_4295_ = l_Lean_Expr_updateBinderNames(v_body_4291_, v_tail_4294_);
if (lean_obj_tag(v_head_4293_) == 0)
{
lean_object* v___x_4296_; 
v___x_4296_ = l_Lean_Expr_forallE___override(v_binderName_4289_, v_binderType_4290_, v_b_4295_, v_binderInfo_4292_);
return v___x_4296_;
}
else
{
lean_object* v_val_4297_; lean_object* v___x_4298_; 
lean_dec(v_binderName_4289_);
v_val_4297_ = lean_ctor_get(v_head_4293_, 0);
lean_inc(v_val_4297_);
lean_dec_ref(v_head_4293_);
v___x_4298_ = l_Lean_Expr_forallE___override(v_val_4297_, v_binderType_4290_, v_b_4295_, v_binderInfo_4292_);
return v___x_4298_;
}
}
else
{
lean_dec(v_binderNames_x3f_4288_);
return v_e_4287_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4288_) == 1)
{
lean_object* v_binderName_4299_; lean_object* v_binderType_4300_; lean_object* v_body_4301_; uint8_t v_binderInfo_4302_; lean_object* v_head_4303_; lean_object* v_tail_4304_; lean_object* v_b_4305_; 
v_binderName_4299_ = lean_ctor_get(v_e_4287_, 0);
lean_inc(v_binderName_4299_);
v_binderType_4300_ = lean_ctor_get(v_e_4287_, 1);
lean_inc_ref(v_binderType_4300_);
v_body_4301_ = lean_ctor_get(v_e_4287_, 2);
lean_inc_ref(v_body_4301_);
v_binderInfo_4302_ = lean_ctor_get_uint8(v_e_4287_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_4287_);
v_head_4303_ = lean_ctor_get(v_binderNames_x3f_4288_, 0);
lean_inc(v_head_4303_);
v_tail_4304_ = lean_ctor_get(v_binderNames_x3f_4288_, 1);
lean_inc(v_tail_4304_);
lean_dec_ref(v_binderNames_x3f_4288_);
v_b_4305_ = l_Lean_Expr_updateBinderNames(v_body_4301_, v_tail_4304_);
if (lean_obj_tag(v_head_4303_) == 0)
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Lean_Expr_lam___override(v_binderName_4299_, v_binderType_4300_, v_b_4305_, v_binderInfo_4302_);
return v___x_4306_;
}
else
{
lean_object* v_val_4307_; lean_object* v___x_4308_; 
lean_dec(v_binderName_4299_);
v_val_4307_ = lean_ctor_get(v_head_4303_, 0);
lean_inc(v_val_4307_);
lean_dec_ref(v_head_4303_);
v___x_4308_ = l_Lean_Expr_lam___override(v_val_4307_, v_binderType_4300_, v_b_4305_, v_binderInfo_4302_);
return v___x_4308_;
}
}
else
{
lean_dec(v_binderNames_x3f_4288_);
return v_e_4287_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4288_);
return v_e_4287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4311_, lean_object* v_subst_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = lean_expr_instantiate(v_e_4311_, v_subst_4312_);
lean_dec_ref(v_subst_4312_);
lean_dec_ref(v_e_4311_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4316_, lean_object* v_subst_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = lean_expr_instantiate1(v_e_4316_, v_subst_4317_);
lean_dec_ref(v_subst_4317_);
lean_dec_ref(v_e_4316_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4321_, lean_object* v_subst_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = lean_expr_instantiate_rev(v_e_4321_, v_subst_4322_);
lean_dec_ref(v_subst_4322_);
lean_dec_ref(v_e_4321_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4328_, lean_object* v_beginIdx_4329_, lean_object* v_endIdx_4330_, lean_object* v_subst_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = lean_expr_instantiate_range(v_e_4328_, v_beginIdx_4329_, v_endIdx_4330_, v_subst_4331_);
lean_dec_ref(v_subst_4331_);
lean_dec(v_endIdx_4330_);
lean_dec(v_beginIdx_4329_);
lean_dec_ref(v_e_4328_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4337_, lean_object* v_beginIdx_4338_, lean_object* v_endIdx_4339_, lean_object* v_subst_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = lean_expr_instantiate_rev_range(v_e_4337_, v_beginIdx_4338_, v_endIdx_4339_, v_subst_4340_);
lean_dec_ref(v_subst_4340_);
lean_dec(v_endIdx_4339_);
lean_dec(v_beginIdx_4338_);
lean_dec_ref(v_e_4337_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4344_, lean_object* v_xs_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = lean_expr_abstract(v_e_4344_, v_xs_4345_);
lean_dec_ref(v_xs_4345_);
lean_dec_ref(v_e_4344_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4350_, lean_object* v_n_4351_, lean_object* v_xs_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = lean_expr_abstract_range(v_e_4350_, v_n_4351_, v_xs_4352_);
lean_dec_ref(v_xs_4352_);
lean_dec(v_n_4351_);
lean_dec_ref(v_e_4350_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4354_, lean_object* v_fvar_4355_, lean_object* v_v_4356_){
_start:
{
lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4357_ = lean_unsigned_to_nat(1u);
v___x_4358_ = lean_mk_empty_array_with_capacity(v___x_4357_);
v___x_4359_ = lean_array_push(v___x_4358_, v_fvar_4355_);
v___x_4360_ = lean_expr_abstract(v_e_4354_, v___x_4359_);
lean_dec_ref(v___x_4359_);
v___x_4361_ = lean_expr_instantiate1(v___x_4360_, v_v_4356_);
lean_dec_ref(v___x_4360_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4362_, lean_object* v_fvar_4363_, lean_object* v_v_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_Expr_replaceFVar(v_e_4362_, v_fvar_4363_, v_v_4364_);
lean_dec_ref(v_v_4364_);
lean_dec_ref(v_e_4362_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4366_, lean_object* v_fvarId_4367_, lean_object* v_v_4368_){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4369_ = l_Lean_Expr_fvar___override(v_fvarId_4367_);
v___x_4370_ = l_Lean_Expr_replaceFVar(v_e_4366_, v___x_4369_, v_v_4368_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4371_, lean_object* v_fvarId_4372_, lean_object* v_v_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l_Lean_Expr_replaceFVarId(v_e_4371_, v_fvarId_4372_, v_v_4373_);
lean_dec_ref(v_v_4373_);
lean_dec_ref(v_e_4371_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4375_, lean_object* v_fvars_4376_, lean_object* v_vs_4377_){
_start:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4378_ = lean_expr_abstract(v_e_4375_, v_fvars_4376_);
v___x_4379_ = lean_expr_instantiate_rev(v___x_4378_, v_vs_4377_);
lean_dec_ref(v___x_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4380_, lean_object* v_fvars_4381_, lean_object* v_vs_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_Lean_Expr_replaceFVars(v_e_4380_, v_fvars_4381_, v_vs_4382_);
lean_dec_ref(v_vs_4382_);
lean_dec_ref(v_fvars_4381_);
lean_dec_ref(v_e_4380_);
return v_res_4383_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4386_){
_start:
{
switch(lean_obj_tag(v_x_4386_))
{
case 4:
{
uint8_t v___x_4387_; 
v___x_4387_ = 1;
return v___x_4387_;
}
case 3:
{
uint8_t v___x_4388_; 
v___x_4388_ = 1;
return v___x_4388_;
}
case 0:
{
uint8_t v___x_4389_; 
v___x_4389_ = 1;
return v___x_4389_;
}
case 9:
{
uint8_t v___x_4390_; 
v___x_4390_ = 1;
return v___x_4390_;
}
case 2:
{
uint8_t v___x_4391_; 
v___x_4391_ = 1;
return v___x_4391_;
}
case 1:
{
uint8_t v___x_4392_; 
v___x_4392_ = 1;
return v___x_4392_;
}
default: 
{
uint8_t v___x_4393_; 
v___x_4393_ = 0;
return v___x_4393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4394_){
_start:
{
uint8_t v_res_4395_; lean_object* v_r_4396_; 
v_res_4395_ = l_Lean_Expr_isAtomic(v_x_4394_);
lean_dec_ref(v_x_4394_);
v_r_4396_ = lean_box(v_res_4395_);
return v_r_4396_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4402_ = lean_box(0);
v___x_4403_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4404_ = l_Lean_Expr_const___override(v___x_4403_, v___x_4402_);
return v___x_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4405_, lean_object* v_proof_4406_){
_start:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4407_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4408_ = l_Lean_mkAppB(v___x_4407_, v_pred_4405_, v_proof_4406_);
return v___x_4408_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4413_ = lean_box(0);
v___x_4414_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4415_ = l_Lean_Expr_const___override(v___x_4414_, v___x_4413_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4416_, lean_object* v_proof_4417_){
_start:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4418_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4419_ = l_Lean_mkAppB(v___x_4418_, v_pred_4416_, v_proof_4417_);
return v___x_4419_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4420_; 
v___x_4420_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4420_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4421_; 
v___x_4421_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4422_){
_start:
{
lean_inc_ref(v_val_4422_);
return v_val_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4423_){
_start:
{
lean_object* v_res_4424_; 
v_res_4424_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4423_);
lean_dec_ref(v_val_4423_);
return v_res_4424_;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4427_, lean_object* v_x_4428_){
_start:
{
uint8_t v___x_4429_; 
v___x_4429_ = lean_expr_equal(v_x_4427_, v_x_4428_);
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4430_, lean_object* v_x_4431_){
_start:
{
uint8_t v_res_4432_; lean_object* v_r_4433_; 
v_res_4432_ = l_Lean_ExprStructEq_beq(v_x_4430_, v_x_4431_);
lean_dec_ref(v_x_4431_);
lean_dec_ref(v_x_4430_);
v_r_4433_ = lean_box(v_res_4432_);
return v_r_4433_;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4434_){
_start:
{
uint64_t v___x_4435_; 
v___x_4435_ = l_Lean_Expr_hash(v_x_4434_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4436_){
_start:
{
uint64_t v_res_4437_; lean_object* v_r_4438_; 
v_res_4437_ = l_Lean_ExprStructEq_hash(v_x_4436_);
lean_dec_ref(v_x_4436_);
v_r_4438_ = lean_box_uint64(v_res_4437_);
return v_r_4438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4445_, lean_object* v_start_4446_, lean_object* v_b_4447_, lean_object* v_i_4448_){
_start:
{
uint8_t v___x_4449_; 
v___x_4449_ = lean_nat_dec_le(v_i_4448_, v_start_4446_);
if (v___x_4449_ == 0)
{
lean_object* v___x_4450_; lean_object* v_i_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4450_ = lean_unsigned_to_nat(1u);
v_i_4451_ = lean_nat_sub(v_i_4448_, v___x_4450_);
lean_dec(v_i_4448_);
v___x_4452_ = l_Lean_instInhabitedExpr;
v___x_4453_ = lean_array_get_borrowed(v___x_4452_, v_revArgs_4445_, v_i_4451_);
lean_inc(v___x_4453_);
v___x_4454_ = l_Lean_Expr_app___override(v_b_4447_, v___x_4453_);
v_b_4447_ = v___x_4454_;
v_i_4448_ = v_i_4451_;
goto _start;
}
else
{
lean_dec(v_i_4448_);
return v_b_4447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4456_, lean_object* v_start_4457_, lean_object* v_b_4458_, lean_object* v_i_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4456_, v_start_4457_, v_b_4458_, v_i_4459_);
lean_dec(v_start_4457_);
lean_dec_ref(v_revArgs_4456_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4461_, lean_object* v_beginIdx_4462_, lean_object* v_endIdx_4463_, lean_object* v_revArgs_4464_){
_start:
{
lean_object* v___x_4465_; 
v___x_4465_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4464_, v_beginIdx_4462_, v_f_4461_, v_endIdx_4463_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4466_, lean_object* v_beginIdx_4467_, lean_object* v_endIdx_4468_, lean_object* v_revArgs_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l_Lean_Expr_mkAppRevRange(v_f_4466_, v_beginIdx_4467_, v_endIdx_4468_, v_revArgs_4469_);
lean_dec_ref(v_revArgs_4469_);
lean_dec(v_beginIdx_4467_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4471_, uint8_t v_useZeta_4472_, uint8_t v_preserveMData_4473_, lean_object* v_sz_4474_, lean_object* v_e_4475_, lean_object* v_i_4476_){
_start:
{
switch(lean_obj_tag(v_e_4475_))
{
case 6:
{
lean_object* v_body_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; uint8_t v___x_4485_; 
v_body_4482_ = lean_ctor_get(v_e_4475_, 2);
lean_inc_ref(v_body_4482_);
lean_dec_ref(v_e_4475_);
v___x_4483_ = lean_unsigned_to_nat(1u);
v___x_4484_ = lean_nat_add(v_i_4476_, v___x_4483_);
lean_dec(v_i_4476_);
v___x_4485_ = lean_nat_dec_lt(v___x_4484_, v_sz_4474_);
if (v___x_4485_ == 0)
{
lean_object* v___x_4486_; 
lean_dec(v___x_4484_);
v___x_4486_ = lean_expr_instantiate(v_body_4482_, v_revArgs_4471_);
lean_dec_ref(v_body_4482_);
return v___x_4486_;
}
else
{
v_e_4475_ = v_body_4482_;
v_i_4476_ = v___x_4484_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4472_ == 0)
{
goto v___jp_4477_;
}
else
{
lean_object* v_value_4488_; lean_object* v_body_4489_; uint8_t v___x_4490_; 
v_value_4488_ = lean_ctor_get(v_e_4475_, 2);
v_body_4489_ = lean_ctor_get(v_e_4475_, 3);
v___x_4490_ = lean_nat_dec_lt(v_i_4476_, v_sz_4474_);
if (v___x_4490_ == 0)
{
goto v___jp_4477_;
}
else
{
lean_object* v___x_4491_; 
lean_inc_ref(v_body_4489_);
lean_inc_ref(v_value_4488_);
lean_dec_ref(v_e_4475_);
v___x_4491_ = lean_expr_instantiate1(v_body_4489_, v_value_4488_);
lean_dec_ref(v_value_4488_);
lean_dec_ref(v_body_4489_);
v_e_4475_ = v___x_4491_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4473_ == 0)
{
lean_object* v_expr_4493_; 
v_expr_4493_ = lean_ctor_get(v_e_4475_, 1);
lean_inc_ref(v_expr_4493_);
lean_dec_ref(v_e_4475_);
v_e_4475_ = v_expr_4493_;
goto _start;
}
else
{
goto v___jp_4477_;
}
}
default: 
{
goto v___jp_4477_;
}
}
v___jp_4477_:
{
lean_object* v_n_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v_n_4478_ = lean_nat_sub(v_sz_4474_, v_i_4476_);
lean_dec(v_i_4476_);
v___x_4479_ = lean_expr_instantiate_range(v_e_4475_, v_n_4478_, v_sz_4474_, v_revArgs_4471_);
lean_dec_ref(v_e_4475_);
v___x_4480_ = lean_unsigned_to_nat(0u);
v___x_4481_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4471_, v___x_4480_, v___x_4479_, v_n_4478_);
return v___x_4481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4495_, lean_object* v_useZeta_4496_, lean_object* v_preserveMData_4497_, lean_object* v_sz_4498_, lean_object* v_e_4499_, lean_object* v_i_4500_){
_start:
{
uint8_t v_useZeta_boxed_4501_; uint8_t v_preserveMData_boxed_4502_; lean_object* v_res_4503_; 
v_useZeta_boxed_4501_ = lean_unbox(v_useZeta_4496_);
v_preserveMData_boxed_4502_ = lean_unbox(v_preserveMData_4497_);
v_res_4503_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4495_, v_useZeta_boxed_4501_, v_preserveMData_boxed_4502_, v_sz_4498_, v_e_4499_, v_i_4500_);
lean_dec(v_sz_4498_);
lean_dec_ref(v_revArgs_4495_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4504_, lean_object* v_revArgs_4505_, uint8_t v_useZeta_4506_, uint8_t v_preserveMData_4507_){
_start:
{
lean_object* v_sz_4508_; lean_object* v___x_4509_; uint8_t v___x_4510_; 
v_sz_4508_ = lean_array_get_size(v_revArgs_4505_);
v___x_4509_ = lean_unsigned_to_nat(0u);
v___x_4510_ = lean_nat_dec_eq(v_sz_4508_, v___x_4509_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; 
v___x_4511_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4505_, v_useZeta_4506_, v_preserveMData_4507_, v_sz_4508_, v_f_4504_, v___x_4509_);
return v___x_4511_;
}
else
{
return v_f_4504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4512_, lean_object* v_revArgs_4513_, lean_object* v_useZeta_4514_, lean_object* v_preserveMData_4515_){
_start:
{
uint8_t v_useZeta_boxed_4516_; uint8_t v_preserveMData_boxed_4517_; lean_object* v_res_4518_; 
v_useZeta_boxed_4516_ = lean_unbox(v_useZeta_4514_);
v_preserveMData_boxed_4517_ = lean_unbox(v_preserveMData_4515_);
v_res_4518_ = l_Lean_Expr_betaRev(v_f_4512_, v_revArgs_4513_, v_useZeta_boxed_4516_, v_preserveMData_boxed_4517_);
lean_dec_ref(v_revArgs_4513_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4519_, lean_object* v_args_4520_){
_start:
{
lean_object* v___x_4521_; uint8_t v___x_4522_; lean_object* v___x_4523_; 
v___x_4521_ = l_Array_reverse___redArg(v_args_4520_);
v___x_4522_ = 0;
v___x_4523_ = l_Lean_Expr_betaRev(v_f_4519_, v___x_4521_, v___x_4522_, v___x_4522_);
lean_dec_ref(v___x_4521_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4524_){
_start:
{
switch(lean_obj_tag(v_x_4524_))
{
case 6:
{
lean_object* v_body_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v_body_4525_ = lean_ctor_get(v_x_4524_, 2);
v___x_4526_ = l_Lean_Expr_getNumHeadLambdas(v_body_4525_);
v___x_4527_ = lean_unsigned_to_nat(1u);
v___x_4528_ = lean_nat_add(v___x_4526_, v___x_4527_);
lean_dec(v___x_4526_);
return v___x_4528_;
}
case 10:
{
lean_object* v_expr_4529_; 
v_expr_4529_ = lean_ctor_get(v_x_4524_, 1);
v_x_4524_ = v_expr_4529_;
goto _start;
}
default: 
{
lean_object* v___x_4531_; 
v___x_4531_ = lean_unsigned_to_nat(0u);
return v___x_4531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l_Lean_Expr_getNumHeadLambdas(v_x_4532_);
lean_dec_ref(v_x_4532_);
return v_res_4533_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4534_, lean_object* v_x_4535_){
_start:
{
switch(lean_obj_tag(v_x_4535_))
{
case 6:
{
uint8_t v___x_4536_; 
v___x_4536_ = 1;
return v___x_4536_;
}
case 8:
{
if (v_useZeta_4534_ == 0)
{
return v_useZeta_4534_;
}
else
{
lean_object* v_body_4537_; 
v_body_4537_ = lean_ctor_get(v_x_4535_, 3);
v_x_4535_ = v_body_4537_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4539_; 
v_expr_4539_ = lean_ctor_get(v_x_4535_, 1);
v_x_4535_ = v_expr_4539_;
goto _start;
}
default: 
{
uint8_t v___x_4541_; 
v___x_4541_ = 0;
return v___x_4541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4542_, lean_object* v_x_4543_){
_start:
{
uint8_t v_useZeta_boxed_4544_; uint8_t v_res_4545_; lean_object* v_r_4546_; 
v_useZeta_boxed_4544_ = lean_unbox(v_useZeta_4542_);
v_res_4545_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4544_, v_x_4543_);
lean_dec_ref(v_x_4543_);
v_r_4546_ = lean_box(v_res_4545_);
return v_r_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4547_){
_start:
{
lean_object* v_f_4548_; uint8_t v___x_4549_; uint8_t v___x_4550_; 
v_f_4548_ = l_Lean_Expr_getAppFn(v_e_4547_);
v___x_4549_ = 0;
v___x_4550_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4549_, v_f_4548_);
if (v___x_4550_ == 0)
{
lean_dec_ref(v_f_4548_);
return v_e_4547_;
}
else
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4551_ = l_Lean_Expr_getAppNumArgs(v_e_4547_);
v___x_4552_ = lean_mk_empty_array_with_capacity(v___x_4551_);
lean_dec(v___x_4551_);
v___x_4553_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4547_, v___x_4552_);
v___x_4554_ = l_Lean_Expr_betaRev(v_f_4548_, v___x_4553_, v___x_4549_, v___x_4549_);
lean_dec_ref(v___x_4553_);
return v___x_4554_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4555_, uint8_t v_useZeta_4556_){
_start:
{
uint8_t v___x_4557_; 
v___x_4557_ = l_Lean_Expr_isApp(v_e_4555_);
if (v___x_4557_ == 0)
{
return v___x_4557_;
}
else
{
lean_object* v___x_4558_; uint8_t v___x_4559_; 
v___x_4558_ = l_Lean_Expr_getAppFn(v_e_4555_);
v___x_4559_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4556_, v___x_4558_);
lean_dec_ref(v___x_4558_);
return v___x_4559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4560_, lean_object* v_useZeta_4561_){
_start:
{
uint8_t v_useZeta_boxed_4562_; uint8_t v_res_4563_; lean_object* v_r_4564_; 
v_useZeta_boxed_4562_ = lean_unbox(v_useZeta_4561_);
v_res_4563_ = l_Lean_Expr_isHeadBetaTarget(v_e_4560_, v_useZeta_boxed_4562_);
lean_dec_ref(v_e_4560_);
v_r_4564_ = lean_box(v_res_4563_);
return v_r_4564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4565_, lean_object* v_x_4566_, lean_object* v_x_4567_){
_start:
{
lean_object* v_f_4569_; 
if (lean_obj_tag(v_x_4565_) == 5)
{
lean_object* v_arg_4573_; 
v_arg_4573_ = lean_ctor_get(v_x_4565_, 1);
if (lean_obj_tag(v_arg_4573_) == 0)
{
lean_object* v_fn_4574_; lean_object* v_deBruijnIndex_4575_; lean_object* v_zero_4576_; uint8_t v_isZero_4577_; 
v_fn_4574_ = lean_ctor_get(v_x_4565_, 0);
v_deBruijnIndex_4575_ = lean_ctor_get(v_arg_4573_, 0);
v_zero_4576_ = lean_unsigned_to_nat(0u);
v_isZero_4577_ = lean_nat_dec_eq(v_x_4566_, v_zero_4576_);
if (v_isZero_4577_ == 1)
{
lean_dec(v_x_4567_);
lean_dec(v_x_4566_);
v_f_4569_ = v_x_4565_;
goto v___jp_4568_;
}
else
{
uint8_t v___x_4578_; 
lean_inc(v_deBruijnIndex_4575_);
lean_inc_ref(v_fn_4574_);
lean_dec_ref(v_x_4565_);
v___x_4578_ = lean_nat_dec_eq(v_deBruijnIndex_4575_, v_x_4567_);
lean_dec(v_deBruijnIndex_4575_);
if (v___x_4578_ == 0)
{
lean_object* v___x_4579_; 
lean_dec_ref(v_fn_4574_);
lean_dec(v_x_4567_);
lean_dec(v_x_4566_);
v___x_4579_ = lean_box(0);
return v___x_4579_;
}
else
{
lean_object* v_one_4580_; lean_object* v_n_4581_; lean_object* v___x_4582_; 
v_one_4580_ = lean_unsigned_to_nat(1u);
v_n_4581_ = lean_nat_sub(v_x_4566_, v_one_4580_);
lean_dec(v_x_4566_);
v___x_4582_ = lean_nat_add(v_x_4567_, v_one_4580_);
lean_dec(v_x_4567_);
v_x_4565_ = v_fn_4574_;
v_x_4566_ = v_n_4581_;
v_x_4567_ = v___x_4582_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4584_; uint8_t v_isZero_4585_; 
lean_dec(v_x_4567_);
v_zero_4584_ = lean_unsigned_to_nat(0u);
v_isZero_4585_ = lean_nat_dec_eq(v_x_4566_, v_zero_4584_);
lean_dec(v_x_4566_);
if (v_isZero_4585_ == 1)
{
v_f_4569_ = v_x_4565_;
goto v___jp_4568_;
}
else
{
lean_object* v___x_4586_; 
lean_dec_ref(v_x_4565_);
v___x_4586_ = lean_box(0);
return v___x_4586_;
}
}
}
else
{
lean_object* v_zero_4587_; uint8_t v_isZero_4588_; 
lean_dec(v_x_4567_);
v_zero_4587_ = lean_unsigned_to_nat(0u);
v_isZero_4588_ = lean_nat_dec_eq(v_x_4566_, v_zero_4587_);
lean_dec(v_x_4566_);
if (v_isZero_4588_ == 1)
{
v_f_4569_ = v_x_4565_;
goto v___jp_4568_;
}
else
{
lean_object* v___x_4589_; 
lean_dec_ref(v_x_4565_);
v___x_4589_ = lean_box(0);
return v___x_4589_;
}
}
v___jp_4568_:
{
uint8_t v___x_4570_; 
v___x_4570_ = l_Lean_Expr_hasLooseBVars(v_f_4569_);
if (v___x_4570_ == 0)
{
lean_object* v___x_4571_; 
v___x_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4571_, 0, v_f_4569_);
return v___x_4571_;
}
else
{
lean_object* v___x_4572_; 
lean_dec_ref(v_f_4569_);
v___x_4572_ = lean_box(0);
return v___x_4572_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4590_, lean_object* v_x_4591_){
_start:
{
if (lean_obj_tag(v_x_4590_) == 6)
{
lean_object* v_body_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; 
v_body_4592_ = lean_ctor_get(v_x_4590_, 2);
lean_inc_ref(v_body_4592_);
lean_dec_ref(v_x_4590_);
v___x_4593_ = lean_unsigned_to_nat(1u);
v___x_4594_ = lean_nat_add(v_x_4591_, v___x_4593_);
lean_dec(v_x_4591_);
v_x_4590_ = v_body_4592_;
v_x_4591_ = v___x_4594_;
goto _start;
}
else
{
lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4596_ = lean_unsigned_to_nat(0u);
v___x_4597_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4590_, v_x_4591_, v___x_4596_);
return v___x_4597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4598_){
_start:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4599_ = lean_unsigned_to_nat(0u);
v___x_4600_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4598_, v___x_4599_);
return v___x_4600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4601_){
_start:
{
if (lean_obj_tag(v_x_4601_) == 6)
{
lean_object* v_body_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; 
v_body_4602_ = lean_ctor_get(v_x_4601_, 2);
lean_inc_ref(v_body_4602_);
lean_dec_ref(v_x_4601_);
v___x_4603_ = lean_unsigned_to_nat(1u);
v___x_4604_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4602_, v___x_4603_);
return v___x_4604_;
}
else
{
lean_object* v___x_4605_; 
lean_dec_ref(v_x_4601_);
v___x_4605_ = lean_box(0);
return v___x_4605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4609_){
_start:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; uint8_t v___x_4612_; 
v___x_4610_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4611_ = lean_unsigned_to_nat(2u);
v___x_4612_ = l_Lean_Expr_isAppOfArity(v_e_4609_, v___x_4610_, v___x_4611_);
if (v___x_4612_ == 0)
{
lean_object* v___x_4613_; 
v___x_4613_ = lean_box(0);
return v___x_4613_;
}
else
{
lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4614_ = l_Lean_Expr_appArg_x21(v_e_4609_);
v___x_4615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
return v___x_4615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4616_){
_start:
{
lean_object* v_res_4617_; 
v_res_4617_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4616_);
lean_dec_ref(v_e_4616_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4621_){
_start:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; uint8_t v___x_4624_; 
v___x_4622_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4623_ = lean_unsigned_to_nat(2u);
v___x_4624_ = l_Lean_Expr_isAppOfArity(v_e_4621_, v___x_4622_, v___x_4623_);
if (v___x_4624_ == 0)
{
lean_object* v___x_4625_; 
v___x_4625_ = lean_box(0);
return v___x_4625_;
}
else
{
lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___x_4626_ = l_Lean_Expr_appArg_x21(v_e_4621_);
v___x_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4627_, 0, v___x_4626_);
return v___x_4627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4628_);
lean_dec_ref(v_e_4628_);
return v_res_4629_;
}
}
LEAN_EXPORT uint8_t lean_is_out_param(lean_object* v_e_4633_){
_start:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; uint8_t v___x_4636_; 
v___x_4634_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4635_ = lean_unsigned_to_nat(1u);
v___x_4636_ = l_Lean_Expr_isAppOfArity(v_e_4633_, v___x_4634_, v___x_4635_);
lean_dec_ref(v_e_4633_);
return v___x_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4637_){
_start:
{
uint8_t v_res_4638_; lean_object* v_r_4639_; 
v_res_4638_ = lean_is_out_param(v_e_4637_);
v_r_4639_ = lean_box(v_res_4638_);
return v_r_4639_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4643_){
_start:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; uint8_t v___x_4646_; 
v___x_4644_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4645_ = lean_unsigned_to_nat(1u);
v___x_4646_ = l_Lean_Expr_isAppOfArity(v_e_4643_, v___x_4644_, v___x_4645_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4647_){
_start:
{
uint8_t v_res_4648_; lean_object* v_r_4649_; 
v_res_4648_ = l_Lean_Expr_isSemiOutParam(v_e_4647_);
lean_dec_ref(v_e_4647_);
v_r_4649_ = lean_box(v_res_4648_);
return v_r_4649_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4650_){
_start:
{
lean_object* v___x_4651_; lean_object* v___x_4652_; uint8_t v___x_4653_; 
v___x_4651_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4652_ = lean_unsigned_to_nat(2u);
v___x_4653_ = l_Lean_Expr_isAppOfArity(v_e_4650_, v___x_4651_, v___x_4652_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4654_){
_start:
{
uint8_t v_res_4655_; lean_object* v_r_4656_; 
v_res_4655_ = l_Lean_Expr_isOptParam(v_e_4654_);
lean_dec_ref(v_e_4654_);
v_r_4656_ = lean_box(v_res_4655_);
return v_r_4656_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4657_){
_start:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; uint8_t v___x_4660_; 
v___x_4658_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4659_ = lean_unsigned_to_nat(2u);
v___x_4660_ = l_Lean_Expr_isAppOfArity(v_e_4657_, v___x_4658_, v___x_4659_);
return v___x_4660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4661_){
_start:
{
uint8_t v_res_4662_; lean_object* v_r_4663_; 
v_res_4662_ = l_Lean_Expr_isAutoParam(v_e_4661_);
lean_dec_ref(v_e_4661_);
v_r_4663_ = lean_box(v_res_4662_);
return v_r_4663_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4664_){
_start:
{
lean_object* v___x_4665_; 
v___x_4665_ = l_Lean_Expr_getAppFn(v_e_4664_);
if (lean_obj_tag(v___x_4665_) == 4)
{
lean_object* v_declName_4666_; uint8_t v___y_4668_; lean_object* v___x_4673_; uint8_t v___x_4674_; 
v_declName_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_declName_4666_);
lean_dec_ref(v___x_4665_);
v___x_4673_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4674_ = lean_name_eq(v_declName_4666_, v___x_4673_);
if (v___x_4674_ == 0)
{
lean_object* v___x_4675_; uint8_t v___x_4676_; 
v___x_4675_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4676_ = lean_name_eq(v_declName_4666_, v___x_4675_);
v___y_4668_ = v___x_4676_;
goto v___jp_4667_;
}
else
{
v___y_4668_ = v___x_4674_;
goto v___jp_4667_;
}
v___jp_4667_:
{
if (v___y_4668_ == 0)
{
lean_object* v___x_4669_; uint8_t v___x_4670_; 
v___x_4669_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4670_ = lean_name_eq(v_declName_4666_, v___x_4669_);
if (v___x_4670_ == 0)
{
lean_object* v___x_4671_; uint8_t v___x_4672_; 
v___x_4671_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4672_ = lean_name_eq(v_declName_4666_, v___x_4671_);
lean_dec(v_declName_4666_);
return v___x_4672_;
}
else
{
lean_dec(v_declName_4666_);
return v___x_4670_;
}
}
else
{
lean_dec(v_declName_4666_);
return v___y_4668_;
}
}
}
else
{
uint8_t v___x_4677_; 
lean_dec_ref(v___x_4665_);
v___x_4677_ = 0;
return v___x_4677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4678_){
_start:
{
uint8_t v_res_4679_; lean_object* v_r_4680_; 
v_res_4679_ = l_Lean_Expr_isTypeAnnotation(v_e_4678_);
lean_dec_ref(v_e_4678_);
v_r_4680_ = lean_box(v_res_4679_);
return v_r_4680_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4681_){
_start:
{
uint8_t v___y_4683_; uint8_t v___y_4687_; uint8_t v___x_4693_; 
v___x_4693_ = l_Lean_Expr_isOptParam(v_e_4681_);
if (v___x_4693_ == 0)
{
uint8_t v___x_4694_; 
v___x_4694_ = l_Lean_Expr_isAutoParam(v_e_4681_);
v___y_4687_ = v___x_4694_;
goto v___jp_4686_;
}
else
{
v___y_4687_ = v___x_4693_;
goto v___jp_4686_;
}
v___jp_4682_:
{
if (v___y_4683_ == 0)
{
return v_e_4681_;
}
else
{
lean_object* v___x_4684_; 
v___x_4684_ = l_Lean_Expr_appArg_x21(v_e_4681_);
lean_dec_ref(v_e_4681_);
v_e_4681_ = v___x_4684_;
goto _start;
}
}
v___jp_4686_:
{
if (v___y_4687_ == 0)
{
uint8_t v___x_4688_; 
lean_inc_ref(v_e_4681_);
v___x_4688_ = lean_is_out_param(v_e_4681_);
if (v___x_4688_ == 0)
{
uint8_t v___x_4689_; 
v___x_4689_ = l_Lean_Expr_isSemiOutParam(v_e_4681_);
v___y_4683_ = v___x_4689_;
goto v___jp_4682_;
}
else
{
v___y_4683_ = v___x_4688_;
goto v___jp_4682_;
}
}
else
{
lean_object* v___x_4690_; lean_object* v___x_4691_; 
v___x_4690_ = l_Lean_Expr_appFn_x21(v_e_4681_);
lean_dec_ref(v_e_4681_);
v___x_4691_ = l_Lean_Expr_appArg_x21(v___x_4690_);
lean_dec_ref(v___x_4690_);
v_e_4681_ = v___x_4691_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4695_){
_start:
{
lean_object* v___x_4696_; lean_object* v_e_x27_4697_; uint8_t v___x_4698_; 
v___x_4696_ = l_Lean_Expr_consumeMData(v_e_4695_);
v_e_x27_4697_ = lean_expr_consume_type_annotations(v___x_4696_);
v___x_4698_ = lean_expr_eqv(v_e_x27_4697_, v_e_4695_);
if (v___x_4698_ == 0)
{
lean_dec_ref(v_e_4695_);
v_e_4695_ = v_e_x27_4697_;
goto _start;
}
else
{
lean_dec_ref(v_e_x27_4697_);
return v_e_4695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4700_){
_start:
{
lean_object* v_fn_4701_; lean_object* v___x_4702_; 
v_fn_4701_ = lean_ctor_get(v_e_4700_, 0);
lean_inc_ref(v_fn_4701_);
lean_dec_ref(v_e_4700_);
v___x_4702_ = l_Lean_Expr_cleanupAnnotations(v_fn_4701_);
return v___x_4702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* v_e_4703_, lean_object* v_h_4704_){
_start:
{
lean_object* v___x_4705_; 
v___x_4705_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4703_);
return v___x_4705_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4709_){
_start:
{
lean_object* v___x_4710_; lean_object* v___x_4711_; uint8_t v___x_4712_; 
v___x_4710_ = l_Lean_Expr_cleanupAnnotations(v_e_4709_);
v___x_4711_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4712_ = l_Lean_Expr_isConstOf(v___x_4710_, v___x_4711_);
lean_dec_ref(v___x_4710_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4713_){
_start:
{
uint8_t v_res_4714_; lean_object* v_r_4715_; 
v_res_4714_ = l_Lean_Expr_isFalse(v_e_4713_);
v_r_4715_ = lean_box(v_res_4714_);
return v_r_4715_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4719_){
_start:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; uint8_t v___x_4722_; 
v___x_4720_ = l_Lean_Expr_cleanupAnnotations(v_e_4719_);
v___x_4721_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4722_ = l_Lean_Expr_isConstOf(v___x_4720_, v___x_4721_);
lean_dec_ref(v___x_4720_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4723_){
_start:
{
uint8_t v_res_4724_; lean_object* v_r_4725_; 
v_res_4724_ = l_Lean_Expr_isTrue(v_e_4723_);
v_r_4725_ = lean_box(v_res_4724_);
return v_r_4725_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object* v_e_4730_){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; uint8_t v___x_4733_; 
v___x_4731_ = l_Lean_Expr_cleanupAnnotations(v_e_4730_);
v___x_4732_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_4733_ = l_Lean_Expr_isConstOf(v___x_4731_, v___x_4732_);
lean_dec_ref(v___x_4731_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object* v_e_4734_){
_start:
{
uint8_t v_res_4735_; lean_object* v_r_4736_; 
v_res_4735_ = l_Lean_Expr_isBoolFalse(v_e_4734_);
v_r_4736_ = lean_box(v_res_4735_);
return v_r_4736_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object* v_e_4740_){
_start:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; uint8_t v___x_4743_; 
v___x_4741_ = l_Lean_Expr_cleanupAnnotations(v_e_4740_);
v___x_4742_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_4743_ = l_Lean_Expr_isConstOf(v___x_4741_, v___x_4742_);
lean_dec_ref(v___x_4741_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object* v_e_4744_){
_start:
{
uint8_t v_res_4745_; lean_object* v_r_4746_; 
v_res_4745_ = l_Lean_Expr_isBoolTrue(v_e_4744_);
v_r_4746_ = lean_box(v_res_4745_);
return v_r_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* v_x_4747_){
_start:
{
switch(lean_obj_tag(v_x_4747_))
{
case 10:
{
lean_object* v_expr_4748_; 
v_expr_4748_ = lean_ctor_get(v_x_4747_, 1);
lean_inc_ref(v_expr_4748_);
lean_dec_ref(v_x_4747_);
v_x_4747_ = v_expr_4748_;
goto _start;
}
case 7:
{
lean_object* v_body_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v_body_4750_ = lean_ctor_get(v_x_4747_, 2);
lean_inc_ref(v_body_4750_);
lean_dec_ref(v_x_4747_);
v___x_4751_ = l_Lean_Expr_getForallArity(v_body_4750_);
v___x_4752_ = lean_unsigned_to_nat(1u);
v___x_4753_ = lean_nat_add(v___x_4751_, v___x_4752_);
lean_dec(v___x_4751_);
return v___x_4753_;
}
default: 
{
uint8_t v___x_4754_; uint8_t v___x_4755_; 
v___x_4754_ = 0;
v___x_4755_ = l_Lean_Expr_isHeadBetaTarget(v_x_4747_, v___x_4754_);
if (v___x_4755_ == 0)
{
lean_object* v_e_x27_4756_; uint8_t v___x_4757_; 
lean_inc_ref(v_x_4747_);
v_e_x27_4756_ = l_Lean_Expr_cleanupAnnotations(v_x_4747_);
v___x_4757_ = lean_expr_eqv(v_x_4747_, v_e_x27_4756_);
lean_dec_ref(v_x_4747_);
if (v___x_4757_ == 0)
{
v_x_4747_ = v_e_x27_4756_;
goto _start;
}
else
{
lean_object* v___x_4759_; 
lean_dec_ref(v_e_x27_4756_);
v___x_4759_ = lean_unsigned_to_nat(0u);
return v___x_4759_;
}
}
else
{
lean_object* v___x_4760_; 
v___x_4760_ = l_Lean_Expr_headBeta(v_x_4747_);
v_x_4747_ = v___x_4760_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4762_){
_start:
{
lean_object* v___x_4763_; uint8_t v___x_4764_; 
v___x_4763_ = l_Lean_Expr_cleanupAnnotations(v_e_4762_);
v___x_4764_ = l_Lean_Expr_isApp(v___x_4763_);
if (v___x_4764_ == 0)
{
lean_object* v___x_4765_; 
lean_dec_ref(v___x_4763_);
v___x_4765_ = lean_box(0);
return v___x_4765_;
}
else
{
lean_object* v___x_4766_; uint8_t v___x_4767_; 
v___x_4766_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4763_);
v___x_4767_ = l_Lean_Expr_isApp(v___x_4766_);
if (v___x_4767_ == 0)
{
lean_object* v___x_4768_; 
lean_dec_ref(v___x_4766_);
v___x_4768_ = lean_box(0);
return v___x_4768_;
}
else
{
lean_object* v_arg_4769_; lean_object* v___x_4770_; uint8_t v___x_4771_; 
v_arg_4769_ = lean_ctor_get(v___x_4766_, 1);
lean_inc_ref(v_arg_4769_);
v___x_4770_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4766_);
v___x_4771_ = l_Lean_Expr_isApp(v___x_4770_);
if (v___x_4771_ == 0)
{
lean_object* v___x_4772_; 
lean_dec_ref(v___x_4770_);
lean_dec_ref(v_arg_4769_);
v___x_4772_ = lean_box(0);
return v___x_4772_;
}
else
{
lean_object* v___x_4773_; lean_object* v___x_4774_; uint8_t v___x_4775_; 
v___x_4773_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4770_);
v___x_4774_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4775_ = l_Lean_Expr_isConstOf(v___x_4773_, v___x_4774_);
lean_dec_ref(v___x_4773_);
if (v___x_4775_ == 0)
{
lean_object* v___x_4776_; 
lean_dec_ref(v_arg_4769_);
v___x_4776_ = lean_box(0);
return v___x_4776_;
}
else
{
if (lean_obj_tag(v_arg_4769_) == 9)
{
lean_object* v_a_4777_; 
v_a_4777_ = lean_ctor_get(v_arg_4769_, 0);
lean_inc_ref(v_a_4777_);
lean_dec_ref(v_arg_4769_);
if (lean_obj_tag(v_a_4777_) == 0)
{
lean_object* v_val_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4785_; 
v_val_4778_ = lean_ctor_get(v_a_4777_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v_a_4777_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4780_ = v_a_4777_;
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_val_4778_);
lean_dec(v_a_4777_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4781_ == 0)
{
lean_ctor_set_tag(v___x_4780_, 1);
v___x_4783_ = v___x_4780_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_val_4778_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
else
{
lean_object* v___x_4786_; 
lean_dec_ref(v_a_4777_);
v___x_4786_ = lean_box(0);
return v___x_4786_;
}
}
else
{
lean_object* v___x_4787_; 
lean_dec_ref(v_arg_4769_);
v___x_4787_ = lean_box(0);
return v___x_4787_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4793_){
_start:
{
lean_object* v___x_4806_; uint8_t v___x_4807_; 
lean_inc_ref(v_e_4793_);
v___x_4806_ = l_Lean_Expr_cleanupAnnotations(v_e_4793_);
v___x_4807_ = l_Lean_Expr_isApp(v___x_4806_);
if (v___x_4807_ == 0)
{
lean_dec_ref(v___x_4806_);
goto v___jp_4794_;
}
else
{
lean_object* v_arg_4808_; lean_object* v___x_4809_; uint8_t v___x_4810_; 
v_arg_4808_ = lean_ctor_get(v___x_4806_, 1);
lean_inc_ref(v_arg_4808_);
v___x_4809_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4806_);
v___x_4810_ = l_Lean_Expr_isApp(v___x_4809_);
if (v___x_4810_ == 0)
{
lean_dec_ref(v___x_4809_);
lean_dec_ref(v_arg_4808_);
goto v___jp_4794_;
}
else
{
lean_object* v___x_4811_; uint8_t v___x_4812_; 
v___x_4811_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4809_);
v___x_4812_ = l_Lean_Expr_isApp(v___x_4811_);
if (v___x_4812_ == 0)
{
lean_dec_ref(v___x_4811_);
lean_dec_ref(v_arg_4808_);
goto v___jp_4794_;
}
else
{
lean_object* v___x_4813_; lean_object* v___x_4814_; uint8_t v___x_4815_; 
v___x_4813_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4811_);
v___x_4814_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4815_ = l_Lean_Expr_isConstOf(v___x_4813_, v___x_4814_);
lean_dec_ref(v___x_4813_);
if (v___x_4815_ == 0)
{
lean_dec_ref(v_arg_4808_);
goto v___jp_4794_;
}
else
{
lean_object* v___x_4816_; 
lean_dec_ref(v_e_4793_);
v___x_4816_ = l_Lean_Expr_nat_x3f(v_arg_4808_);
if (lean_obj_tag(v___x_4816_) == 0)
{
lean_object* v___x_4817_; 
v___x_4817_ = lean_box(0);
return v___x_4817_;
}
else
{
lean_object* v_val_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4830_; 
v_val_4818_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4820_ = v___x_4816_;
v_isShared_4821_ = v_isSharedCheck_4830_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_val_4818_);
lean_dec(v___x_4816_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4830_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4822_; uint8_t v___x_4823_; 
v___x_4822_ = lean_unsigned_to_nat(0u);
v___x_4823_ = lean_nat_dec_eq(v_val_4818_, v___x_4822_);
if (v___x_4823_ == 0)
{
lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4827_; 
v___x_4824_ = lean_nat_to_int(v_val_4818_);
v___x_4825_ = lean_int_neg(v___x_4824_);
lean_dec(v___x_4824_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 0, v___x_4825_);
v___x_4827_ = v___x_4820_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v___x_4825_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
else
{
lean_object* v___x_4829_; 
lean_del_object(v___x_4820_);
lean_dec(v_val_4818_);
v___x_4829_ = lean_box(0);
return v___x_4829_;
}
}
}
}
}
}
}
v___jp_4794_:
{
lean_object* v___x_4795_; 
v___x_4795_ = l_Lean_Expr_nat_x3f(v_e_4793_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v___x_4796_; 
v___x_4796_ = lean_box(0);
return v___x_4796_;
}
else
{
lean_object* v_val_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4805_; 
v_val_4797_ = lean_ctor_get(v___x_4795_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4799_ = v___x_4795_;
v_isShared_4800_ = v_isSharedCheck_4805_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_val_4797_);
lean_dec(v___x_4795_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4805_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4801_; lean_object* v___x_4803_; 
v___x_4801_ = lean_nat_to_int(v_val_4797_);
if (v_isShared_4800_ == 0)
{
lean_ctor_set(v___x_4799_, 0, v___x_4801_);
v___x_4803_ = v___x_4799_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v___x_4801_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4831_, lean_object* v_e_4832_){
_start:
{
uint8_t v___x_4833_; lean_object* v_d_4835_; lean_object* v_b_4836_; 
v___x_4833_ = l_Lean_Expr_hasFVar(v_e_4832_);
if (v___x_4833_ == 0)
{
lean_dec_ref(v_e_4832_);
lean_dec_ref(v_p_4831_);
return v___x_4833_;
}
else
{
switch(lean_obj_tag(v_e_4832_))
{
case 7:
{
lean_object* v_binderType_4839_; lean_object* v_body_4840_; 
v_binderType_4839_ = lean_ctor_get(v_e_4832_, 1);
lean_inc_ref(v_binderType_4839_);
v_body_4840_ = lean_ctor_get(v_e_4832_, 2);
lean_inc_ref(v_body_4840_);
lean_dec_ref(v_e_4832_);
v_d_4835_ = v_binderType_4839_;
v_b_4836_ = v_body_4840_;
goto v___jp_4834_;
}
case 6:
{
lean_object* v_binderType_4841_; lean_object* v_body_4842_; 
v_binderType_4841_ = lean_ctor_get(v_e_4832_, 1);
lean_inc_ref(v_binderType_4841_);
v_body_4842_ = lean_ctor_get(v_e_4832_, 2);
lean_inc_ref(v_body_4842_);
lean_dec_ref(v_e_4832_);
v_d_4835_ = v_binderType_4841_;
v_b_4836_ = v_body_4842_;
goto v___jp_4834_;
}
case 10:
{
lean_object* v_expr_4843_; 
v_expr_4843_ = lean_ctor_get(v_e_4832_, 1);
lean_inc_ref(v_expr_4843_);
lean_dec_ref(v_e_4832_);
v_e_4832_ = v_expr_4843_;
goto _start;
}
case 8:
{
lean_object* v_type_4845_; lean_object* v_value_4846_; lean_object* v_body_4847_; uint8_t v___x_4848_; 
v_type_4845_ = lean_ctor_get(v_e_4832_, 1);
lean_inc_ref(v_type_4845_);
v_value_4846_ = lean_ctor_get(v_e_4832_, 2);
lean_inc_ref(v_value_4846_);
v_body_4847_ = lean_ctor_get(v_e_4832_, 3);
lean_inc_ref(v_body_4847_);
lean_dec_ref(v_e_4832_);
lean_inc_ref(v_p_4831_);
v___x_4848_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4831_, v_type_4845_);
if (v___x_4848_ == 0)
{
uint8_t v___x_4849_; 
lean_inc_ref(v_p_4831_);
v___x_4849_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4831_, v_value_4846_);
if (v___x_4849_ == 0)
{
v_e_4832_ = v_body_4847_;
goto _start;
}
else
{
lean_dec_ref(v_body_4847_);
lean_dec_ref(v_p_4831_);
return v___x_4833_;
}
}
else
{
lean_dec_ref(v_body_4847_);
lean_dec_ref(v_value_4846_);
lean_dec_ref(v_p_4831_);
return v___x_4833_;
}
}
case 5:
{
lean_object* v_fn_4851_; lean_object* v_arg_4852_; uint8_t v___x_4853_; 
v_fn_4851_ = lean_ctor_get(v_e_4832_, 0);
lean_inc_ref(v_fn_4851_);
v_arg_4852_ = lean_ctor_get(v_e_4832_, 1);
lean_inc_ref(v_arg_4852_);
lean_dec_ref(v_e_4832_);
lean_inc_ref(v_p_4831_);
v___x_4853_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4831_, v_fn_4851_);
if (v___x_4853_ == 0)
{
v_e_4832_ = v_arg_4852_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4852_);
lean_dec_ref(v_p_4831_);
return v___x_4833_;
}
}
case 11:
{
lean_object* v_struct_4855_; 
v_struct_4855_ = lean_ctor_get(v_e_4832_, 2);
lean_inc_ref(v_struct_4855_);
lean_dec_ref(v_e_4832_);
v_e_4832_ = v_struct_4855_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4857_; lean_object* v___x_4858_; uint8_t v___x_4859_; 
v_fvarId_4857_ = lean_ctor_get(v_e_4832_, 0);
lean_inc(v_fvarId_4857_);
lean_dec_ref(v_e_4832_);
v___x_4858_ = lean_apply_1(v_p_4831_, v_fvarId_4857_);
v___x_4859_ = lean_unbox(v___x_4858_);
return v___x_4859_;
}
default: 
{
uint8_t v___x_4860_; 
lean_dec_ref(v_e_4832_);
lean_dec_ref(v_p_4831_);
v___x_4860_ = 0;
return v___x_4860_;
}
}
}
v___jp_4834_:
{
uint8_t v___x_4837_; 
lean_inc_ref(v_p_4831_);
v___x_4837_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4831_, v_d_4835_);
if (v___x_4837_ == 0)
{
v_e_4832_ = v_b_4836_;
goto _start;
}
else
{
lean_dec_ref(v_b_4836_);
lean_dec_ref(v_p_4831_);
return v___x_4833_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_4861_, lean_object* v_e_4862_){
_start:
{
uint8_t v_res_4863_; lean_object* v_r_4864_; 
v_res_4863_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4861_, v_e_4862_);
v_r_4864_ = lean_box(v_res_4863_);
return v_r_4864_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_4865_, lean_object* v_p_4866_){
_start:
{
uint8_t v___x_4867_; 
v___x_4867_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4866_, v_e_4865_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_4868_, lean_object* v_p_4869_){
_start:
{
uint8_t v_res_4870_; lean_object* v_r_4871_; 
v_res_4870_ = l_Lean_Expr_hasAnyFVar(v_e_4868_, v_p_4869_);
v_r_4871_ = lean_box(v_res_4870_);
return v_r_4871_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_4872_, lean_object* v_e_4873_){
_start:
{
uint8_t v___x_4874_; lean_object* v_d_4876_; lean_object* v_b_4877_; 
v___x_4874_ = l_Lean_Expr_hasFVar(v_e_4873_);
if (v___x_4874_ == 0)
{
return v___x_4874_;
}
else
{
switch(lean_obj_tag(v_e_4873_))
{
case 7:
{
lean_object* v_binderType_4880_; lean_object* v_body_4881_; 
v_binderType_4880_ = lean_ctor_get(v_e_4873_, 1);
v_body_4881_ = lean_ctor_get(v_e_4873_, 2);
v_d_4876_ = v_binderType_4880_;
v_b_4877_ = v_body_4881_;
goto v___jp_4875_;
}
case 6:
{
lean_object* v_binderType_4882_; lean_object* v_body_4883_; 
v_binderType_4882_ = lean_ctor_get(v_e_4873_, 1);
v_body_4883_ = lean_ctor_get(v_e_4873_, 2);
v_d_4876_ = v_binderType_4882_;
v_b_4877_ = v_body_4883_;
goto v___jp_4875_;
}
case 10:
{
lean_object* v_expr_4884_; 
v_expr_4884_ = lean_ctor_get(v_e_4873_, 1);
v_e_4873_ = v_expr_4884_;
goto _start;
}
case 8:
{
lean_object* v_type_4886_; lean_object* v_value_4887_; lean_object* v_body_4888_; uint8_t v___x_4889_; 
v_type_4886_ = lean_ctor_get(v_e_4873_, 1);
v_value_4887_ = lean_ctor_get(v_e_4873_, 2);
v_body_4888_ = lean_ctor_get(v_e_4873_, 3);
v___x_4889_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4872_, v_type_4886_);
if (v___x_4889_ == 0)
{
uint8_t v___x_4890_; 
v___x_4890_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4872_, v_value_4887_);
if (v___x_4890_ == 0)
{
v_e_4873_ = v_body_4888_;
goto _start;
}
else
{
return v___x_4874_;
}
}
else
{
return v___x_4874_;
}
}
case 5:
{
lean_object* v_fn_4892_; lean_object* v_arg_4893_; uint8_t v___x_4894_; 
v_fn_4892_ = lean_ctor_get(v_e_4873_, 0);
v_arg_4893_ = lean_ctor_get(v_e_4873_, 1);
v___x_4894_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4872_, v_fn_4892_);
if (v___x_4894_ == 0)
{
v_e_4873_ = v_arg_4893_;
goto _start;
}
else
{
return v___x_4874_;
}
}
case 11:
{
lean_object* v_struct_4896_; 
v_struct_4896_ = lean_ctor_get(v_e_4873_, 2);
v_e_4873_ = v_struct_4896_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4898_; uint8_t v___x_4899_; 
v_fvarId_4898_ = lean_ctor_get(v_e_4873_, 0);
v___x_4899_ = lean_name_eq(v_fvarId_4898_, v_fvarId_4872_);
return v___x_4899_;
}
default: 
{
uint8_t v___x_4900_; 
v___x_4900_ = 0;
return v___x_4900_;
}
}
}
v___jp_4875_:
{
uint8_t v___x_4878_; 
v___x_4878_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4872_, v_d_4876_);
if (v___x_4878_ == 0)
{
v_e_4873_ = v_b_4877_;
goto _start;
}
else
{
return v___x_4874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_4901_, lean_object* v_e_4902_){
_start:
{
uint8_t v_res_4903_; lean_object* v_r_4904_; 
v_res_4903_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4901_, v_e_4902_);
lean_dec_ref(v_e_4902_);
lean_dec(v_fvarId_4901_);
v_r_4904_ = lean_box(v_res_4903_);
return v_r_4904_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_4905_, lean_object* v_fvarId_4906_){
_start:
{
uint8_t v___x_4907_; 
v___x_4907_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4906_, v_e_4905_);
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_4908_, lean_object* v_fvarId_4909_){
_start:
{
uint8_t v_res_4910_; lean_object* v_r_4911_; 
v_res_4910_ = l_Lean_Expr_containsFVar(v_e_4908_, v_fvarId_4909_);
lean_dec(v_fvarId_4909_);
lean_dec_ref(v_e_4908_);
v_r_4911_ = lean_box(v_res_4910_);
return v_r_4911_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4913_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_4914_ = lean_unsigned_to_nat(18u);
v___x_4915_ = lean_unsigned_to_nat(1829u);
v___x_4916_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_4917_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4918_ = l_mkPanicMessageWithDecl(v___x_4917_, v___x_4916_, v___x_4915_, v___x_4914_, v___x_4913_);
return v___x_4918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_4919_, lean_object* v_newFn_4920_, lean_object* v_newArg_4921_){
_start:
{
uint8_t v___y_4923_; 
if (lean_obj_tag(v_e_4919_) == 5)
{
lean_object* v_fn_4925_; lean_object* v_arg_4926_; size_t v___x_4927_; size_t v___x_4928_; uint8_t v___x_4929_; 
v_fn_4925_ = lean_ctor_get(v_e_4919_, 0);
v_arg_4926_ = lean_ctor_get(v_e_4919_, 1);
v___x_4927_ = lean_ptr_addr(v_fn_4925_);
v___x_4928_ = lean_ptr_addr(v_newFn_4920_);
v___x_4929_ = lean_usize_dec_eq(v___x_4927_, v___x_4928_);
if (v___x_4929_ == 0)
{
v___y_4923_ = v___x_4929_;
goto v___jp_4922_;
}
else
{
size_t v___x_4930_; size_t v___x_4931_; uint8_t v___x_4932_; 
v___x_4930_ = lean_ptr_addr(v_arg_4926_);
v___x_4931_ = lean_ptr_addr(v_newArg_4921_);
v___x_4932_ = lean_usize_dec_eq(v___x_4930_, v___x_4931_);
v___y_4923_ = v___x_4932_;
goto v___jp_4922_;
}
}
else
{
lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; 
lean_dec_ref(v_newArg_4921_);
lean_dec_ref(v_newFn_4920_);
v___x_4933_ = l_Lean_instInhabitedExpr;
v___x_4934_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_4935_ = l_panic___redArg(v___x_4933_, v___x_4934_);
return v___x_4935_;
}
v___jp_4922_:
{
if (v___y_4923_ == 0)
{
lean_object* v___x_4924_; 
v___x_4924_ = l_Lean_Expr_app___override(v_newFn_4920_, v_newArg_4921_);
return v___x_4924_;
}
else
{
lean_dec_ref(v_newArg_4921_);
lean_dec_ref(v_newFn_4920_);
lean_inc_ref(v_e_4919_);
return v_e_4919_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_4936_, lean_object* v_newFn_4937_, lean_object* v_newArg_4938_){
_start:
{
lean_object* v_res_4939_; 
v_res_4939_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_4936_, v_newFn_4937_, v_newArg_4938_);
lean_dec_ref(v_e_4936_);
return v_res_4939_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; 
v___x_4941_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_4942_ = lean_unsigned_to_nat(20u);
v___x_4943_ = lean_unsigned_to_nat(1840u);
v___x_4944_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_4945_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4946_ = l_mkPanicMessageWithDecl(v___x_4945_, v___x_4944_, v___x_4943_, v___x_4942_, v___x_4941_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_4947_, lean_object* v_fvarIdNew_4948_){
_start:
{
if (lean_obj_tag(v_e_4947_) == 1)
{
lean_object* v_fvarId_4949_; uint8_t v___x_4950_; 
v_fvarId_4949_ = lean_ctor_get(v_e_4947_, 0);
v___x_4950_ = lean_name_eq(v_fvarId_4949_, v_fvarIdNew_4948_);
if (v___x_4950_ == 0)
{
lean_object* v___x_4951_; 
v___x_4951_ = l_Lean_Expr_fvar___override(v_fvarIdNew_4948_);
return v___x_4951_;
}
else
{
lean_dec(v_fvarIdNew_4948_);
lean_inc_ref(v_e_4947_);
return v_e_4947_;
}
}
else
{
lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
lean_dec(v_fvarIdNew_4948_);
v___x_4952_ = l_Lean_instInhabitedExpr;
v___x_4953_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_4954_ = l_panic___redArg(v___x_4952_, v___x_4953_);
return v___x_4954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_4955_, lean_object* v_fvarIdNew_4956_){
_start:
{
lean_object* v_res_4957_; 
v_res_4957_ = l_Lean_Expr_updateFVar_x21(v_e_4955_, v_fvarIdNew_4956_);
lean_dec_ref(v_e_4955_);
return v_res_4957_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
v___x_4959_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_4960_ = lean_unsigned_to_nat(18u);
v___x_4961_ = lean_unsigned_to_nat(1845u);
v___x_4962_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_4963_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4964_ = l_mkPanicMessageWithDecl(v___x_4963_, v___x_4962_, v___x_4961_, v___x_4960_, v___x_4959_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_4965_, lean_object* v_newLevels_4966_){
_start:
{
if (lean_obj_tag(v_e_4965_) == 4)
{
lean_object* v_declName_4967_; lean_object* v_us_4968_; uint8_t v___x_4969_; 
v_declName_4967_ = lean_ctor_get(v_e_4965_, 0);
v_us_4968_ = lean_ctor_get(v_e_4965_, 1);
v___x_4969_ = l_ptrEqList___redArg(v_us_4968_, v_newLevels_4966_);
if (v___x_4969_ == 0)
{
lean_object* v___x_4970_; 
lean_inc(v_declName_4967_);
lean_dec_ref(v_e_4965_);
v___x_4970_ = l_Lean_Expr_const___override(v_declName_4967_, v_newLevels_4966_);
return v___x_4970_;
}
else
{
lean_dec(v_newLevels_4966_);
return v_e_4965_;
}
}
else
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
lean_dec(v_newLevels_4966_);
lean_dec_ref(v_e_4965_);
v___x_4971_ = l_Lean_instInhabitedExpr;
v___x_4972_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_4973_ = l_panic___redArg(v___x_4971_, v___x_4972_);
return v___x_4973_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4976_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_4977_ = lean_unsigned_to_nat(14u);
v___x_4978_ = lean_unsigned_to_nat(1856u);
v___x_4979_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_4980_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4981_ = l_mkPanicMessageWithDecl(v___x_4980_, v___x_4979_, v___x_4978_, v___x_4977_, v___x_4976_);
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_4982_, lean_object* v_u_x27_4983_){
_start:
{
if (lean_obj_tag(v_e_4982_) == 3)
{
lean_object* v_u_4984_; size_t v___x_4985_; size_t v___x_4986_; uint8_t v___x_4987_; 
v_u_4984_ = lean_ctor_get(v_e_4982_, 0);
v___x_4985_ = lean_ptr_addr(v_u_4984_);
v___x_4986_ = lean_ptr_addr(v_u_x27_4983_);
v___x_4987_ = lean_usize_dec_eq(v___x_4985_, v___x_4986_);
if (v___x_4987_ == 0)
{
lean_object* v___x_4988_; 
v___x_4988_ = l_Lean_Expr_sort___override(v_u_x27_4983_);
return v___x_4988_;
}
else
{
lean_dec(v_u_x27_4983_);
lean_inc_ref(v_e_4982_);
return v_e_4982_;
}
}
else
{
lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
lean_dec(v_u_x27_4983_);
v___x_4989_ = l_Lean_instInhabitedExpr;
v___x_4990_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_4991_ = l_panic___redArg(v___x_4989_, v___x_4990_);
return v___x_4991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_4992_, lean_object* v_u_x27_4993_){
_start:
{
lean_object* v_res_4994_; 
v_res_4994_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_4992_, v_u_x27_4993_);
lean_dec_ref(v_e_4992_);
return v_res_4994_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_4997_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_4998_ = lean_unsigned_to_nat(17u);
v___x_4999_ = lean_unsigned_to_nat(1867u);
v___x_5000_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_5001_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5002_ = l_mkPanicMessageWithDecl(v___x_5001_, v___x_5000_, v___x_4999_, v___x_4998_, v___x_4997_);
return v___x_5002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_5003_, lean_object* v_newExpr_5004_){
_start:
{
if (lean_obj_tag(v_e_5003_) == 10)
{
lean_object* v_data_5005_; lean_object* v_expr_5006_; size_t v___x_5007_; size_t v___x_5008_; uint8_t v___x_5009_; 
v_data_5005_ = lean_ctor_get(v_e_5003_, 0);
v_expr_5006_ = lean_ctor_get(v_e_5003_, 1);
v___x_5007_ = lean_ptr_addr(v_expr_5006_);
v___x_5008_ = lean_ptr_addr(v_newExpr_5004_);
v___x_5009_ = lean_usize_dec_eq(v___x_5007_, v___x_5008_);
if (v___x_5009_ == 0)
{
lean_object* v___x_5010_; 
lean_inc(v_data_5005_);
lean_dec_ref(v_e_5003_);
v___x_5010_ = l_Lean_Expr_mdata___override(v_data_5005_, v_newExpr_5004_);
return v___x_5010_;
}
else
{
lean_dec_ref(v_newExpr_5004_);
return v_e_5003_;
}
}
else
{
lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; 
lean_dec_ref(v_newExpr_5004_);
lean_dec_ref(v_e_5003_);
v___x_5011_ = l_Lean_instInhabitedExpr;
v___x_5012_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_5013_ = l_panic___redArg(v___x_5011_, v___x_5012_);
return v___x_5013_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5016_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_5017_ = lean_unsigned_to_nat(18u);
v___x_5018_ = lean_unsigned_to_nat(1878u);
v___x_5019_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_5020_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5021_ = l_mkPanicMessageWithDecl(v___x_5020_, v___x_5019_, v___x_5018_, v___x_5017_, v___x_5016_);
return v___x_5021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_5022_, lean_object* v_newExpr_5023_){
_start:
{
if (lean_obj_tag(v_e_5022_) == 11)
{
lean_object* v_typeName_5024_; lean_object* v_idx_5025_; lean_object* v_struct_5026_; size_t v___x_5027_; size_t v___x_5028_; uint8_t v___x_5029_; 
v_typeName_5024_ = lean_ctor_get(v_e_5022_, 0);
v_idx_5025_ = lean_ctor_get(v_e_5022_, 1);
v_struct_5026_ = lean_ctor_get(v_e_5022_, 2);
v___x_5027_ = lean_ptr_addr(v_struct_5026_);
v___x_5028_ = lean_ptr_addr(v_newExpr_5023_);
v___x_5029_ = lean_usize_dec_eq(v___x_5027_, v___x_5028_);
if (v___x_5029_ == 0)
{
lean_object* v___x_5030_; 
lean_inc(v_idx_5025_);
lean_inc(v_typeName_5024_);
lean_dec_ref(v_e_5022_);
v___x_5030_ = l_Lean_Expr_proj___override(v_typeName_5024_, v_idx_5025_, v_newExpr_5023_);
return v___x_5030_;
}
else
{
lean_dec_ref(v_newExpr_5023_);
return v_e_5022_;
}
}
else
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; 
lean_dec_ref(v_newExpr_5023_);
lean_dec_ref(v_e_5022_);
v___x_5031_ = l_Lean_instInhabitedExpr;
v___x_5032_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_5033_ = l_panic___redArg(v___x_5031_, v___x_5032_);
return v___x_5033_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5036_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5037_ = lean_unsigned_to_nat(23u);
v___x_5038_ = lean_unsigned_to_nat(1893u);
v___x_5039_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_5040_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5041_ = l_mkPanicMessageWithDecl(v___x_5040_, v___x_5039_, v___x_5038_, v___x_5037_, v___x_5036_);
return v___x_5041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_5042_, uint8_t v_newBinfo_5043_, lean_object* v_newDomain_5044_, lean_object* v_newBody_5045_){
_start:
{
if (lean_obj_tag(v_e_5042_) == 7)
{
lean_object* v_binderName_5046_; lean_object* v_binderType_5047_; lean_object* v_body_5048_; uint8_t v_binderInfo_5049_; uint8_t v___y_5051_; size_t v___x_5055_; size_t v___x_5056_; uint8_t v___x_5057_; 
v_binderName_5046_ = lean_ctor_get(v_e_5042_, 0);
v_binderType_5047_ = lean_ctor_get(v_e_5042_, 1);
v_body_5048_ = lean_ctor_get(v_e_5042_, 2);
v_binderInfo_5049_ = lean_ctor_get_uint8(v_e_5042_, sizeof(void*)*3 + 8);
v___x_5055_ = lean_ptr_addr(v_binderType_5047_);
v___x_5056_ = lean_ptr_addr(v_newDomain_5044_);
v___x_5057_ = lean_usize_dec_eq(v___x_5055_, v___x_5056_);
if (v___x_5057_ == 0)
{
v___y_5051_ = v___x_5057_;
goto v___jp_5050_;
}
else
{
size_t v___x_5058_; size_t v___x_5059_; uint8_t v___x_5060_; 
v___x_5058_ = lean_ptr_addr(v_body_5048_);
v___x_5059_ = lean_ptr_addr(v_newBody_5045_);
v___x_5060_ = lean_usize_dec_eq(v___x_5058_, v___x_5059_);
v___y_5051_ = v___x_5060_;
goto v___jp_5050_;
}
v___jp_5050_:
{
if (v___y_5051_ == 0)
{
lean_object* v___x_5052_; 
lean_inc(v_binderName_5046_);
lean_dec_ref(v_e_5042_);
v___x_5052_ = l_Lean_Expr_forallE___override(v_binderName_5046_, v_newDomain_5044_, v_newBody_5045_, v_newBinfo_5043_);
return v___x_5052_;
}
else
{
uint8_t v___x_5053_; 
v___x_5053_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5049_, v_newBinfo_5043_);
if (v___x_5053_ == 0)
{
lean_object* v___x_5054_; 
lean_inc(v_binderName_5046_);
lean_dec_ref(v_e_5042_);
v___x_5054_ = l_Lean_Expr_forallE___override(v_binderName_5046_, v_newDomain_5044_, v_newBody_5045_, v_newBinfo_5043_);
return v___x_5054_;
}
else
{
lean_dec_ref(v_newBody_5045_);
lean_dec_ref(v_newDomain_5044_);
return v_e_5042_;
}
}
}
}
else
{
lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
lean_dec_ref(v_newBody_5045_);
lean_dec_ref(v_newDomain_5044_);
lean_dec_ref(v_e_5042_);
v___x_5061_ = l_Lean_instInhabitedExpr;
v___x_5062_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_5063_ = l_panic___redArg(v___x_5061_, v___x_5062_);
return v___x_5063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_5064_, lean_object* v_newBinfo_5065_, lean_object* v_newDomain_5066_, lean_object* v_newBody_5067_){
_start:
{
uint8_t v_newBinfo_boxed_5068_; lean_object* v_res_5069_; 
v_newBinfo_boxed_5068_ = lean_unbox(v_newBinfo_5065_);
v_res_5069_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5064_, v_newBinfo_boxed_5068_, v_newDomain_5066_, v_newBody_5067_);
return v_res_5069_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___x_5071_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5072_ = lean_unsigned_to_nat(24u);
v___x_5073_ = lean_unsigned_to_nat(1904u);
v___x_5074_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_5075_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5076_ = l_mkPanicMessageWithDecl(v___x_5075_, v___x_5074_, v___x_5073_, v___x_5072_, v___x_5071_);
return v___x_5076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_5077_, lean_object* v_newDomain_5078_, lean_object* v_newBody_5079_){
_start:
{
if (lean_obj_tag(v_e_5077_) == 7)
{
lean_object* v_binderName_5080_; lean_object* v_binderType_5081_; lean_object* v_body_5082_; uint8_t v_binderInfo_5083_; uint8_t v___y_5085_; size_t v___x_5089_; size_t v___x_5090_; uint8_t v___x_5091_; 
v_binderName_5080_ = lean_ctor_get(v_e_5077_, 0);
v_binderType_5081_ = lean_ctor_get(v_e_5077_, 1);
v_body_5082_ = lean_ctor_get(v_e_5077_, 2);
v_binderInfo_5083_ = lean_ctor_get_uint8(v_e_5077_, sizeof(void*)*3 + 8);
v___x_5089_ = lean_ptr_addr(v_binderType_5081_);
v___x_5090_ = lean_ptr_addr(v_newDomain_5078_);
v___x_5091_ = lean_usize_dec_eq(v___x_5089_, v___x_5090_);
if (v___x_5091_ == 0)
{
v___y_5085_ = v___x_5091_;
goto v___jp_5084_;
}
else
{
size_t v___x_5092_; size_t v___x_5093_; uint8_t v___x_5094_; 
v___x_5092_ = lean_ptr_addr(v_body_5082_);
v___x_5093_ = lean_ptr_addr(v_newBody_5079_);
v___x_5094_ = lean_usize_dec_eq(v___x_5092_, v___x_5093_);
v___y_5085_ = v___x_5094_;
goto v___jp_5084_;
}
v___jp_5084_:
{
if (v___y_5085_ == 0)
{
lean_object* v___x_5086_; 
lean_inc(v_binderName_5080_);
lean_dec_ref(v_e_5077_);
v___x_5086_ = l_Lean_Expr_forallE___override(v_binderName_5080_, v_newDomain_5078_, v_newBody_5079_, v_binderInfo_5083_);
return v___x_5086_;
}
else
{
uint8_t v___x_5087_; 
v___x_5087_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5083_, v_binderInfo_5083_);
if (v___x_5087_ == 0)
{
lean_object* v___x_5088_; 
lean_inc(v_binderName_5080_);
lean_dec_ref(v_e_5077_);
v___x_5088_ = l_Lean_Expr_forallE___override(v_binderName_5080_, v_newDomain_5078_, v_newBody_5079_, v_binderInfo_5083_);
return v___x_5088_;
}
else
{
lean_dec_ref(v_newBody_5079_);
lean_dec_ref(v_newDomain_5078_);
return v_e_5077_;
}
}
}
}
else
{
lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; 
lean_dec_ref(v_newBody_5079_);
lean_dec_ref(v_newDomain_5078_);
lean_dec_ref(v_e_5077_);
v___x_5095_ = l_Lean_instInhabitedExpr;
v___x_5096_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_5097_ = l_panic___redArg(v___x_5095_, v___x_5096_);
return v___x_5097_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5100_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5101_ = lean_unsigned_to_nat(19u);
v___x_5102_ = lean_unsigned_to_nat(1913u);
v___x_5103_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_5104_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5105_ = l_mkPanicMessageWithDecl(v___x_5104_, v___x_5103_, v___x_5102_, v___x_5101_, v___x_5100_);
return v___x_5105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_5106_, uint8_t v_newBinfo_5107_, lean_object* v_newDomain_5108_, lean_object* v_newBody_5109_){
_start:
{
if (lean_obj_tag(v_e_5106_) == 6)
{
lean_object* v_binderName_5110_; lean_object* v_binderType_5111_; lean_object* v_body_5112_; uint8_t v_binderInfo_5113_; uint8_t v___y_5115_; size_t v___x_5119_; size_t v___x_5120_; uint8_t v___x_5121_; 
v_binderName_5110_ = lean_ctor_get(v_e_5106_, 0);
v_binderType_5111_ = lean_ctor_get(v_e_5106_, 1);
v_body_5112_ = lean_ctor_get(v_e_5106_, 2);
v_binderInfo_5113_ = lean_ctor_get_uint8(v_e_5106_, sizeof(void*)*3 + 8);
v___x_5119_ = lean_ptr_addr(v_binderType_5111_);
v___x_5120_ = lean_ptr_addr(v_newDomain_5108_);
v___x_5121_ = lean_usize_dec_eq(v___x_5119_, v___x_5120_);
if (v___x_5121_ == 0)
{
v___y_5115_ = v___x_5121_;
goto v___jp_5114_;
}
else
{
size_t v___x_5122_; size_t v___x_5123_; uint8_t v___x_5124_; 
v___x_5122_ = lean_ptr_addr(v_body_5112_);
v___x_5123_ = lean_ptr_addr(v_newBody_5109_);
v___x_5124_ = lean_usize_dec_eq(v___x_5122_, v___x_5123_);
v___y_5115_ = v___x_5124_;
goto v___jp_5114_;
}
v___jp_5114_:
{
if (v___y_5115_ == 0)
{
lean_object* v___x_5116_; 
lean_inc(v_binderName_5110_);
lean_dec_ref(v_e_5106_);
v___x_5116_ = l_Lean_Expr_lam___override(v_binderName_5110_, v_newDomain_5108_, v_newBody_5109_, v_newBinfo_5107_);
return v___x_5116_;
}
else
{
uint8_t v___x_5117_; 
v___x_5117_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5113_, v_newBinfo_5107_);
if (v___x_5117_ == 0)
{
lean_object* v___x_5118_; 
lean_inc(v_binderName_5110_);
lean_dec_ref(v_e_5106_);
v___x_5118_ = l_Lean_Expr_lam___override(v_binderName_5110_, v_newDomain_5108_, v_newBody_5109_, v_newBinfo_5107_);
return v___x_5118_;
}
else
{
lean_dec_ref(v_newBody_5109_);
lean_dec_ref(v_newDomain_5108_);
return v_e_5106_;
}
}
}
}
else
{
lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; 
lean_dec_ref(v_newBody_5109_);
lean_dec_ref(v_newDomain_5108_);
lean_dec_ref(v_e_5106_);
v___x_5125_ = l_Lean_instInhabitedExpr;
v___x_5126_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_5127_ = l_panic___redArg(v___x_5125_, v___x_5126_);
return v___x_5127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_5128_, lean_object* v_newBinfo_5129_, lean_object* v_newDomain_5130_, lean_object* v_newBody_5131_){
_start:
{
uint8_t v_newBinfo_boxed_5132_; lean_object* v_res_5133_; 
v_newBinfo_boxed_5132_ = lean_unbox(v_newBinfo_5129_);
v_res_5133_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5128_, v_newBinfo_boxed_5132_, v_newDomain_5130_, v_newBody_5131_);
return v_res_5133_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; 
v___x_5135_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5136_ = lean_unsigned_to_nat(20u);
v___x_5137_ = lean_unsigned_to_nat(1924u);
v___x_5138_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5139_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5140_ = l_mkPanicMessageWithDecl(v___x_5139_, v___x_5138_, v___x_5137_, v___x_5136_, v___x_5135_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5141_, lean_object* v_newDomain_5142_, lean_object* v_newBody_5143_){
_start:
{
if (lean_obj_tag(v_e_5141_) == 6)
{
lean_object* v_binderName_5144_; lean_object* v_binderType_5145_; lean_object* v_body_5146_; uint8_t v_binderInfo_5147_; uint8_t v___y_5149_; size_t v___x_5153_; size_t v___x_5154_; uint8_t v___x_5155_; 
v_binderName_5144_ = lean_ctor_get(v_e_5141_, 0);
v_binderType_5145_ = lean_ctor_get(v_e_5141_, 1);
v_body_5146_ = lean_ctor_get(v_e_5141_, 2);
v_binderInfo_5147_ = lean_ctor_get_uint8(v_e_5141_, sizeof(void*)*3 + 8);
v___x_5153_ = lean_ptr_addr(v_binderType_5145_);
v___x_5154_ = lean_ptr_addr(v_newDomain_5142_);
v___x_5155_ = lean_usize_dec_eq(v___x_5153_, v___x_5154_);
if (v___x_5155_ == 0)
{
v___y_5149_ = v___x_5155_;
goto v___jp_5148_;
}
else
{
size_t v___x_5156_; size_t v___x_5157_; uint8_t v___x_5158_; 
v___x_5156_ = lean_ptr_addr(v_body_5146_);
v___x_5157_ = lean_ptr_addr(v_newBody_5143_);
v___x_5158_ = lean_usize_dec_eq(v___x_5156_, v___x_5157_);
v___y_5149_ = v___x_5158_;
goto v___jp_5148_;
}
v___jp_5148_:
{
if (v___y_5149_ == 0)
{
lean_object* v___x_5150_; 
lean_inc(v_binderName_5144_);
lean_dec_ref(v_e_5141_);
v___x_5150_ = l_Lean_Expr_lam___override(v_binderName_5144_, v_newDomain_5142_, v_newBody_5143_, v_binderInfo_5147_);
return v___x_5150_;
}
else
{
uint8_t v___x_5151_; 
v___x_5151_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5147_, v_binderInfo_5147_);
if (v___x_5151_ == 0)
{
lean_object* v___x_5152_; 
lean_inc(v_binderName_5144_);
lean_dec_ref(v_e_5141_);
v___x_5152_ = l_Lean_Expr_lam___override(v_binderName_5144_, v_newDomain_5142_, v_newBody_5143_, v_binderInfo_5147_);
return v___x_5152_;
}
else
{
lean_dec_ref(v_newBody_5143_);
lean_dec_ref(v_newDomain_5142_);
return v_e_5141_;
}
}
}
}
else
{
lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; 
lean_dec_ref(v_newBody_5143_);
lean_dec_ref(v_newDomain_5142_);
lean_dec_ref(v_e_5141_);
v___x_5159_ = l_Lean_instInhabitedExpr;
v___x_5160_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5161_ = l_panic___redArg(v___x_5159_, v___x_5160_);
return v___x_5161_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; 
v___x_5163_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5164_ = lean_unsigned_to_nat(22u);
v___x_5165_ = lean_unsigned_to_nat(1933u);
v___x_5166_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5167_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5168_ = l_mkPanicMessageWithDecl(v___x_5167_, v___x_5166_, v___x_5165_, v___x_5164_, v___x_5163_);
return v___x_5168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5169_, lean_object* v_newType_5170_, lean_object* v_newVal_5171_, lean_object* v_newBody_5172_, uint8_t v_newNondep_5173_){
_start:
{
if (lean_obj_tag(v_e_5169_) == 8)
{
lean_object* v_declName_5174_; lean_object* v_type_5175_; lean_object* v_value_5176_; lean_object* v_body_5177_; uint8_t v_nondep_5178_; uint8_t v___y_5180_; size_t v___x_5188_; size_t v___x_5189_; uint8_t v___x_5190_; 
v_declName_5174_ = lean_ctor_get(v_e_5169_, 0);
v_type_5175_ = lean_ctor_get(v_e_5169_, 1);
v_value_5176_ = lean_ctor_get(v_e_5169_, 2);
v_body_5177_ = lean_ctor_get(v_e_5169_, 3);
v_nondep_5178_ = lean_ctor_get_uint8(v_e_5169_, sizeof(void*)*4 + 8);
v___x_5188_ = lean_ptr_addr(v_type_5175_);
v___x_5189_ = lean_ptr_addr(v_newType_5170_);
v___x_5190_ = lean_usize_dec_eq(v___x_5188_, v___x_5189_);
if (v___x_5190_ == 0)
{
v___y_5180_ = v___x_5190_;
goto v___jp_5179_;
}
else
{
size_t v___x_5191_; size_t v___x_5192_; uint8_t v___x_5193_; 
v___x_5191_ = lean_ptr_addr(v_value_5176_);
v___x_5192_ = lean_ptr_addr(v_newVal_5171_);
v___x_5193_ = lean_usize_dec_eq(v___x_5191_, v___x_5192_);
v___y_5180_ = v___x_5193_;
goto v___jp_5179_;
}
v___jp_5179_:
{
if (v___y_5180_ == 0)
{
lean_object* v___x_5181_; 
lean_inc(v_declName_5174_);
lean_dec_ref(v_e_5169_);
v___x_5181_ = l_Lean_Expr_letE___override(v_declName_5174_, v_newType_5170_, v_newVal_5171_, v_newBody_5172_, v_newNondep_5173_);
return v___x_5181_;
}
else
{
size_t v___x_5182_; size_t v___x_5183_; uint8_t v___x_5184_; 
v___x_5182_ = lean_ptr_addr(v_body_5177_);
v___x_5183_ = lean_ptr_addr(v_newBody_5172_);
v___x_5184_ = lean_usize_dec_eq(v___x_5182_, v___x_5183_);
if (v___x_5184_ == 0)
{
lean_object* v___x_5185_; 
lean_inc(v_declName_5174_);
lean_dec_ref(v_e_5169_);
v___x_5185_ = l_Lean_Expr_letE___override(v_declName_5174_, v_newType_5170_, v_newVal_5171_, v_newBody_5172_, v_newNondep_5173_);
return v___x_5185_;
}
else
{
if (v_nondep_5178_ == 0)
{
if (v_newNondep_5173_ == 0)
{
lean_dec_ref(v_newBody_5172_);
lean_dec_ref(v_newVal_5171_);
lean_dec_ref(v_newType_5170_);
return v_e_5169_;
}
else
{
lean_object* v___x_5186_; 
lean_inc(v_declName_5174_);
lean_dec_ref(v_e_5169_);
v___x_5186_ = l_Lean_Expr_letE___override(v_declName_5174_, v_newType_5170_, v_newVal_5171_, v_newBody_5172_, v_newNondep_5173_);
return v___x_5186_;
}
}
else
{
if (v_newNondep_5173_ == 0)
{
lean_object* v___x_5187_; 
lean_inc(v_declName_5174_);
lean_dec_ref(v_e_5169_);
v___x_5187_ = l_Lean_Expr_letE___override(v_declName_5174_, v_newType_5170_, v_newVal_5171_, v_newBody_5172_, v_newNondep_5173_);
return v___x_5187_;
}
else
{
lean_dec_ref(v_newBody_5172_);
lean_dec_ref(v_newVal_5171_);
lean_dec_ref(v_newType_5170_);
return v_e_5169_;
}
}
}
}
}
}
else
{
lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; 
lean_dec_ref(v_newBody_5172_);
lean_dec_ref(v_newVal_5171_);
lean_dec_ref(v_newType_5170_);
lean_dec_ref(v_e_5169_);
v___x_5194_ = l_Lean_instInhabitedExpr;
v___x_5195_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5196_ = l_panic___redArg(v___x_5194_, v___x_5195_);
return v___x_5196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5197_, lean_object* v_newType_5198_, lean_object* v_newVal_5199_, lean_object* v_newBody_5200_, lean_object* v_newNondep_5201_){
_start:
{
uint8_t v_newNondep_boxed_5202_; lean_object* v_res_5203_; 
v_newNondep_boxed_5202_ = lean_unbox(v_newNondep_5201_);
v_res_5203_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5197_, v_newType_5198_, v_newVal_5199_, v_newBody_5200_, v_newNondep_boxed_5202_);
return v_res_5203_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; 
v___x_5205_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5206_ = lean_unsigned_to_nat(27u);
v___x_5207_ = lean_unsigned_to_nat(1946u);
v___x_5208_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5209_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5210_ = l_mkPanicMessageWithDecl(v___x_5209_, v___x_5208_, v___x_5207_, v___x_5206_, v___x_5205_);
return v___x_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5211_, lean_object* v_newType_5212_, lean_object* v_newVal_5213_, lean_object* v_newBody_5214_){
_start:
{
if (lean_obj_tag(v_e_5211_) == 8)
{
lean_object* v_declName_5215_; lean_object* v_type_5216_; lean_object* v_value_5217_; lean_object* v_body_5218_; uint8_t v_nondep_5219_; uint8_t v___y_5221_; size_t v___x_5227_; size_t v___x_5228_; uint8_t v___x_5229_; 
v_declName_5215_ = lean_ctor_get(v_e_5211_, 0);
v_type_5216_ = lean_ctor_get(v_e_5211_, 1);
v_value_5217_ = lean_ctor_get(v_e_5211_, 2);
v_body_5218_ = lean_ctor_get(v_e_5211_, 3);
v_nondep_5219_ = lean_ctor_get_uint8(v_e_5211_, sizeof(void*)*4 + 8);
v___x_5227_ = lean_ptr_addr(v_type_5216_);
v___x_5228_ = lean_ptr_addr(v_newType_5212_);
v___x_5229_ = lean_usize_dec_eq(v___x_5227_, v___x_5228_);
if (v___x_5229_ == 0)
{
v___y_5221_ = v___x_5229_;
goto v___jp_5220_;
}
else
{
size_t v___x_5230_; size_t v___x_5231_; uint8_t v___x_5232_; 
v___x_5230_ = lean_ptr_addr(v_value_5217_);
v___x_5231_ = lean_ptr_addr(v_newVal_5213_);
v___x_5232_ = lean_usize_dec_eq(v___x_5230_, v___x_5231_);
v___y_5221_ = v___x_5232_;
goto v___jp_5220_;
}
v___jp_5220_:
{
if (v___y_5221_ == 0)
{
lean_object* v___x_5222_; 
lean_inc(v_declName_5215_);
lean_dec_ref(v_e_5211_);
v___x_5222_ = l_Lean_Expr_letE___override(v_declName_5215_, v_newType_5212_, v_newVal_5213_, v_newBody_5214_, v_nondep_5219_);
return v___x_5222_;
}
else
{
size_t v___x_5223_; size_t v___x_5224_; uint8_t v___x_5225_; 
v___x_5223_ = lean_ptr_addr(v_body_5218_);
v___x_5224_ = lean_ptr_addr(v_newBody_5214_);
v___x_5225_ = lean_usize_dec_eq(v___x_5223_, v___x_5224_);
if (v___x_5225_ == 0)
{
lean_object* v___x_5226_; 
lean_inc(v_declName_5215_);
lean_dec_ref(v_e_5211_);
v___x_5226_ = l_Lean_Expr_letE___override(v_declName_5215_, v_newType_5212_, v_newVal_5213_, v_newBody_5214_, v_nondep_5219_);
return v___x_5226_;
}
else
{
lean_dec_ref(v_newBody_5214_);
lean_dec_ref(v_newVal_5213_);
lean_dec_ref(v_newType_5212_);
return v_e_5211_;
}
}
}
}
else
{
lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; 
lean_dec_ref(v_newBody_5214_);
lean_dec_ref(v_newVal_5213_);
lean_dec_ref(v_newType_5212_);
lean_dec_ref(v_e_5211_);
v___x_5233_ = l_Lean_instInhabitedExpr;
v___x_5234_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5235_ = l_panic___redArg(v___x_5233_, v___x_5234_);
return v___x_5235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5236_, lean_object* v_x_5237_){
_start:
{
if (lean_obj_tag(v_x_5236_) == 5)
{
lean_object* v_fn_5238_; lean_object* v_arg_5239_; lean_object* v___x_5240_; uint8_t v___y_5242_; size_t v___x_5244_; size_t v___x_5245_; uint8_t v___x_5246_; 
v_fn_5238_ = lean_ctor_get(v_x_5236_, 0);
v_arg_5239_ = lean_ctor_get(v_x_5236_, 1);
lean_inc_ref(v_fn_5238_);
v___x_5240_ = l_Lean_Expr_updateFn(v_fn_5238_, v_x_5237_);
v___x_5244_ = lean_ptr_addr(v_fn_5238_);
v___x_5245_ = lean_ptr_addr(v___x_5240_);
v___x_5246_ = lean_usize_dec_eq(v___x_5244_, v___x_5245_);
if (v___x_5246_ == 0)
{
v___y_5242_ = v___x_5246_;
goto v___jp_5241_;
}
else
{
size_t v___x_5247_; uint8_t v___x_5248_; 
v___x_5247_ = lean_ptr_addr(v_arg_5239_);
v___x_5248_ = lean_usize_dec_eq(v___x_5247_, v___x_5247_);
v___y_5242_ = v___x_5248_;
goto v___jp_5241_;
}
v___jp_5241_:
{
if (v___y_5242_ == 0)
{
lean_object* v___x_5243_; 
lean_inc_ref(v_arg_5239_);
lean_dec_ref(v_x_5236_);
v___x_5243_ = l_Lean_Expr_app___override(v___x_5240_, v_arg_5239_);
return v___x_5243_;
}
else
{
lean_dec_ref(v___x_5240_);
return v_x_5236_;
}
}
}
else
{
lean_dec_ref(v_x_5236_);
lean_inc_ref(v_x_5237_);
return v_x_5237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5249_, lean_object* v_x_5250_){
_start:
{
lean_object* v_res_5251_; 
v_res_5251_ = l_Lean_Expr_updateFn(v_x_5249_, v_x_5250_);
lean_dec_ref(v_x_5250_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5252_){
_start:
{
if (lean_obj_tag(v_e_5252_) == 6)
{
lean_object* v_binderName_5253_; lean_object* v_binderType_5254_; lean_object* v_body_5255_; uint8_t v_binderInfo_5256_; lean_object* v_b_x27_5257_; uint8_t v___y_5259_; uint8_t v___y_5264_; 
v_binderName_5253_ = lean_ctor_get(v_e_5252_, 0);
v_binderType_5254_ = lean_ctor_get(v_e_5252_, 1);
v_body_5255_ = lean_ctor_get(v_e_5252_, 2);
v_binderInfo_5256_ = lean_ctor_get_uint8(v_e_5252_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5255_);
v_b_x27_5257_ = l_Lean_Expr_eta(v_body_5255_);
if (lean_obj_tag(v_b_x27_5257_) == 5)
{
lean_object* v_arg_5274_; 
v_arg_5274_ = lean_ctor_get(v_b_x27_5257_, 1);
lean_inc_ref(v_arg_5274_);
if (lean_obj_tag(v_arg_5274_) == 0)
{
lean_object* v_fn_5275_; lean_object* v_deBruijnIndex_5276_; lean_object* v___x_5277_; uint8_t v___x_5278_; 
v_fn_5275_ = lean_ctor_get(v_b_x27_5257_, 0);
lean_inc_ref(v_fn_5275_);
v_deBruijnIndex_5276_ = lean_ctor_get(v_arg_5274_, 0);
lean_inc(v_deBruijnIndex_5276_);
lean_dec_ref(v_arg_5274_);
v___x_5277_ = lean_unsigned_to_nat(0u);
v___x_5278_ = lean_nat_dec_eq(v_deBruijnIndex_5276_, v___x_5277_);
lean_dec(v_deBruijnIndex_5276_);
if (v___x_5278_ == 0)
{
lean_dec_ref(v_fn_5275_);
goto v___jp_5268_;
}
else
{
uint8_t v___x_5279_; 
v___x_5279_ = lean_expr_has_loose_bvar(v_fn_5275_, v___x_5277_);
if (v___x_5279_ == 0)
{
lean_object* v___x_5280_; lean_object* v___x_5281_; 
lean_dec_ref(v_b_x27_5257_);
lean_dec_ref(v_e_5252_);
v___x_5280_ = lean_unsigned_to_nat(1u);
v___x_5281_ = lean_expr_lower_loose_bvars(v_fn_5275_, v___x_5280_, v___x_5280_);
lean_dec_ref(v_fn_5275_);
return v___x_5281_;
}
else
{
size_t v___x_5282_; uint8_t v___x_5283_; 
lean_dec_ref(v_fn_5275_);
v___x_5282_ = lean_ptr_addr(v_binderType_5254_);
v___x_5283_ = lean_usize_dec_eq(v___x_5282_, v___x_5282_);
if (v___x_5283_ == 0)
{
v___y_5259_ = v___x_5283_;
goto v___jp_5258_;
}
else
{
size_t v___x_5284_; size_t v___x_5285_; uint8_t v___x_5286_; 
v___x_5284_ = lean_ptr_addr(v_body_5255_);
v___x_5285_ = lean_ptr_addr(v_b_x27_5257_);
v___x_5286_ = lean_usize_dec_eq(v___x_5284_, v___x_5285_);
v___y_5259_ = v___x_5286_;
goto v___jp_5258_;
}
}
}
}
else
{
lean_dec_ref(v_arg_5274_);
goto v___jp_5268_;
}
}
else
{
goto v___jp_5268_;
}
v___jp_5258_:
{
if (v___y_5259_ == 0)
{
lean_object* v___x_5260_; 
lean_inc_ref(v_binderType_5254_);
lean_inc(v_binderName_5253_);
lean_dec_ref(v_e_5252_);
v___x_5260_ = l_Lean_Expr_lam___override(v_binderName_5253_, v_binderType_5254_, v_b_x27_5257_, v_binderInfo_5256_);
return v___x_5260_;
}
else
{
uint8_t v___x_5261_; 
v___x_5261_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5256_, v_binderInfo_5256_);
if (v___x_5261_ == 0)
{
lean_object* v___x_5262_; 
lean_inc_ref(v_binderType_5254_);
lean_inc(v_binderName_5253_);
lean_dec_ref(v_e_5252_);
v___x_5262_ = l_Lean_Expr_lam___override(v_binderName_5253_, v_binderType_5254_, v_b_x27_5257_, v_binderInfo_5256_);
return v___x_5262_;
}
else
{
lean_dec_ref(v_b_x27_5257_);
return v_e_5252_;
}
}
}
v___jp_5263_:
{
if (v___y_5264_ == 0)
{
lean_object* v___x_5265_; 
lean_inc_ref(v_binderType_5254_);
lean_inc(v_binderName_5253_);
lean_dec_ref(v_e_5252_);
v___x_5265_ = l_Lean_Expr_lam___override(v_binderName_5253_, v_binderType_5254_, v_b_x27_5257_, v_binderInfo_5256_);
return v___x_5265_;
}
else
{
uint8_t v___x_5266_; 
v___x_5266_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5256_, v_binderInfo_5256_);
if (v___x_5266_ == 0)
{
lean_object* v___x_5267_; 
lean_inc_ref(v_binderType_5254_);
lean_inc(v_binderName_5253_);
lean_dec_ref(v_e_5252_);
v___x_5267_ = l_Lean_Expr_lam___override(v_binderName_5253_, v_binderType_5254_, v_b_x27_5257_, v_binderInfo_5256_);
return v___x_5267_;
}
else
{
lean_dec_ref(v_b_x27_5257_);
return v_e_5252_;
}
}
}
v___jp_5268_:
{
size_t v___x_5269_; uint8_t v___x_5270_; 
v___x_5269_ = lean_ptr_addr(v_binderType_5254_);
v___x_5270_ = lean_usize_dec_eq(v___x_5269_, v___x_5269_);
if (v___x_5270_ == 0)
{
v___y_5264_ = v___x_5270_;
goto v___jp_5263_;
}
else
{
size_t v___x_5271_; size_t v___x_5272_; uint8_t v___x_5273_; 
v___x_5271_ = lean_ptr_addr(v_body_5255_);
v___x_5272_ = lean_ptr_addr(v_b_x27_5257_);
v___x_5273_ = lean_usize_dec_eq(v___x_5271_, v___x_5272_);
v___y_5264_ = v___x_5273_;
goto v___jp_5263_;
}
}
}
else
{
return v_e_5252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5287_, lean_object* v_optionName_5288_, lean_object* v_inst_5289_, lean_object* v_val_5290_){
_start:
{
lean_object* v_toDataValue_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; 
v_toDataValue_5291_ = lean_ctor_get(v_inst_5289_, 0);
lean_inc_ref(v_toDataValue_5291_);
lean_dec_ref(v_inst_5289_);
v___x_5292_ = lean_box(0);
v___x_5293_ = lean_apply_1(v_toDataValue_5291_, v_val_5290_);
v___x_5294_ = l_Lean_KVMap_insert(v___x_5292_, v_optionName_5288_, v___x_5293_);
v___x_5295_ = l_Lean_Expr_mdata___override(v___x_5294_, v_e_5287_);
return v___x_5295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5296_, lean_object* v_e_5297_, lean_object* v_optionName_5298_, lean_object* v_inst_5299_, lean_object* v_val_5300_){
_start:
{
lean_object* v___x_5301_; 
v___x_5301_ = l_Lean_Expr_setOption___redArg(v_e_5297_, v_optionName_5298_, v_inst_5299_, v_val_5300_);
return v___x_5301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5302_, lean_object* v_optionName_5303_, uint8_t v_val_5304_){
_start:
{
lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; 
v___x_5305_ = lean_box(0);
v___x_5306_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5306_, 0, v_val_5304_);
v___x_5307_ = l_Lean_KVMap_insert(v___x_5305_, v_optionName_5303_, v___x_5306_);
v___x_5308_ = l_Lean_Expr_mdata___override(v___x_5307_, v_e_5302_);
return v___x_5308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5309_, lean_object* v_optionName_5310_, lean_object* v_val_5311_){
_start:
{
uint8_t v_val_boxed_5312_; lean_object* v_res_5313_; 
v_val_boxed_5312_ = lean_unbox(v_val_5311_);
v_res_5313_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5309_, v_optionName_5310_, v_val_boxed_5312_);
return v_res_5313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5319_, uint8_t v_flag_5320_){
_start:
{
lean_object* v___x_5321_; lean_object* v___x_5322_; 
v___x_5321_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5322_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5319_, v___x_5321_, v_flag_5320_);
return v___x_5322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5323_, lean_object* v_flag_5324_){
_start:
{
uint8_t v_flag_boxed_5325_; lean_object* v_res_5326_; 
v_flag_boxed_5325_ = lean_unbox(v_flag_5324_);
v_res_5326_ = l_Lean_Expr_setPPExplicit(v_e_5323_, v_flag_boxed_5325_);
return v_res_5326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5331_, uint8_t v_flag_5332_){
_start:
{
lean_object* v___x_5333_; lean_object* v___x_5334_; 
v___x_5333_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5334_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5331_, v___x_5333_, v_flag_5332_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5335_, lean_object* v_flag_5336_){
_start:
{
uint8_t v_flag_boxed_5337_; lean_object* v_res_5338_; 
v_flag_boxed_5337_ = lean_unbox(v_flag_5336_);
v_res_5338_ = l_Lean_Expr_setPPUniverses(v_e_5335_, v_flag_boxed_5337_);
return v_res_5338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5343_, uint8_t v_flag_5344_){
_start:
{
lean_object* v___x_5345_; lean_object* v___x_5346_; 
v___x_5345_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5346_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5343_, v___x_5345_, v_flag_5344_);
return v___x_5346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5347_, lean_object* v_flag_5348_){
_start:
{
uint8_t v_flag_boxed_5349_; lean_object* v_res_5350_; 
v_flag_boxed_5349_ = lean_unbox(v_flag_5348_);
v_res_5350_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5347_, v_flag_boxed_5349_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5355_, uint8_t v_flag_5356_){
_start:
{
lean_object* v___x_5357_; lean_object* v___x_5358_; 
v___x_5357_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5358_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5355_, v___x_5357_, v_flag_5356_);
return v___x_5358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5359_, lean_object* v_flag_5360_){
_start:
{
uint8_t v_flag_boxed_5361_; lean_object* v_res_5362_; 
v_flag_boxed_5361_ = lean_unbox(v_flag_5360_);
v_res_5362_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5359_, v_flag_boxed_5361_);
return v_res_5362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5367_, uint8_t v_flag_5368_){
_start:
{
lean_object* v___x_5369_; lean_object* v___x_5370_; 
v___x_5369_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5370_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5367_, v___x_5369_, v_flag_5368_);
return v___x_5370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5371_, lean_object* v_flag_5372_){
_start:
{
uint8_t v_flag_boxed_5373_; lean_object* v_res_5374_; 
v_flag_boxed_5373_ = lean_unbox(v_flag_5372_);
v_res_5374_ = l_Lean_Expr_setPPNumericTypes(v_e_5371_, v_flag_boxed_5373_);
return v_res_5374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5375_, size_t v_i_5376_, lean_object* v_bs_5377_){
_start:
{
uint8_t v___x_5378_; 
v___x_5378_ = lean_usize_dec_lt(v_i_5376_, v_sz_5375_);
if (v___x_5378_ == 0)
{
return v_bs_5377_;
}
else
{
uint8_t v___x_5379_; lean_object* v_v_5380_; lean_object* v___x_5381_; lean_object* v_bs_x27_5382_; lean_object* v___x_5383_; size_t v___x_5384_; size_t v___x_5385_; lean_object* v___x_5386_; 
v___x_5379_ = 0;
v_v_5380_ = lean_array_uget(v_bs_5377_, v_i_5376_);
v___x_5381_ = lean_unsigned_to_nat(0u);
v_bs_x27_5382_ = lean_array_uset(v_bs_5377_, v_i_5376_, v___x_5381_);
v___x_5383_ = l_Lean_Expr_setPPExplicit(v_v_5380_, v___x_5379_);
v___x_5384_ = ((size_t)1ULL);
v___x_5385_ = lean_usize_add(v_i_5376_, v___x_5384_);
v___x_5386_ = lean_array_uset(v_bs_x27_5382_, v_i_5376_, v___x_5383_);
v_i_5376_ = v___x_5385_;
v_bs_5377_ = v___x_5386_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5388_, lean_object* v_i_5389_, lean_object* v_bs_5390_){
_start:
{
size_t v_sz_boxed_5391_; size_t v_i_boxed_5392_; lean_object* v_res_5393_; 
v_sz_boxed_5391_ = lean_unbox_usize(v_sz_5388_);
lean_dec(v_sz_5388_);
v_i_boxed_5392_ = lean_unbox_usize(v_i_5389_);
lean_dec(v_i_5389_);
v_res_5393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5391_, v_i_boxed_5392_, v_bs_5390_);
return v_res_5393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5394_){
_start:
{
if (lean_obj_tag(v_e_5394_) == 5)
{
lean_object* v___x_5395_; uint8_t v___x_5396_; lean_object* v_f_5397_; lean_object* v_dummy_5398_; lean_object* v_nargs_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; size_t v_sz_5404_; size_t v___x_5405_; lean_object* v_args_5406_; lean_object* v___x_5407_; uint8_t v___x_5408_; lean_object* v___x_5409_; 
v___x_5395_ = l_Lean_Expr_getAppFn(v_e_5394_);
v___x_5396_ = 0;
v_f_5397_ = l_Lean_Expr_setPPExplicit(v___x_5395_, v___x_5396_);
v_dummy_5398_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5399_ = l_Lean_Expr_getAppNumArgs(v_e_5394_);
lean_inc(v_nargs_5399_);
v___x_5400_ = lean_mk_array(v_nargs_5399_, v_dummy_5398_);
v___x_5401_ = lean_unsigned_to_nat(1u);
v___x_5402_ = lean_nat_sub(v_nargs_5399_, v___x_5401_);
lean_dec(v_nargs_5399_);
v___x_5403_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5394_, v___x_5400_, v___x_5402_);
v_sz_5404_ = lean_array_size(v___x_5403_);
v___x_5405_ = ((size_t)0ULL);
v_args_5406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5404_, v___x_5405_, v___x_5403_);
v___x_5407_ = l_Lean_mkAppN(v_f_5397_, v_args_5406_);
lean_dec_ref(v_args_5406_);
v___x_5408_ = 1;
v___x_5409_ = l_Lean_Expr_setPPExplicit(v___x_5407_, v___x_5408_);
return v___x_5409_;
}
else
{
return v_e_5394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5410_, size_t v_i_5411_, lean_object* v_bs_5412_){
_start:
{
uint8_t v___x_5413_; 
v___x_5413_ = lean_usize_dec_lt(v_i_5411_, v_sz_5410_);
if (v___x_5413_ == 0)
{
return v_bs_5412_;
}
else
{
lean_object* v_v_5414_; lean_object* v___x_5415_; lean_object* v_bs_x27_5416_; lean_object* v___y_5418_; uint8_t v___x_5423_; 
v_v_5414_ = lean_array_uget(v_bs_5412_, v_i_5411_);
v___x_5415_ = lean_unsigned_to_nat(0u);
v_bs_x27_5416_ = lean_array_uset(v_bs_5412_, v_i_5411_, v___x_5415_);
v___x_5423_ = l_Lean_Expr_hasMVar(v_v_5414_);
if (v___x_5423_ == 0)
{
lean_object* v___x_5424_; 
v___x_5424_ = l_Lean_Expr_setPPExplicit(v_v_5414_, v___x_5423_);
v___y_5418_ = v___x_5424_;
goto v___jp_5417_;
}
else
{
v___y_5418_ = v_v_5414_;
goto v___jp_5417_;
}
v___jp_5417_:
{
size_t v___x_5419_; size_t v___x_5420_; lean_object* v___x_5421_; 
v___x_5419_ = ((size_t)1ULL);
v___x_5420_ = lean_usize_add(v_i_5411_, v___x_5419_);
v___x_5421_ = lean_array_uset(v_bs_x27_5416_, v_i_5411_, v___y_5418_);
v_i_5411_ = v___x_5420_;
v_bs_5412_ = v___x_5421_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5425_, lean_object* v_i_5426_, lean_object* v_bs_5427_){
_start:
{
size_t v_sz_boxed_5428_; size_t v_i_boxed_5429_; lean_object* v_res_5430_; 
v_sz_boxed_5428_ = lean_unbox_usize(v_sz_5425_);
lean_dec(v_sz_5425_);
v_i_boxed_5429_ = lean_unbox_usize(v_i_5426_);
lean_dec(v_i_5426_);
v_res_5430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5428_, v_i_boxed_5429_, v_bs_5427_);
return v_res_5430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5431_){
_start:
{
if (lean_obj_tag(v_e_5431_) == 5)
{
lean_object* v___x_5432_; uint8_t v___x_5433_; lean_object* v_f_5434_; lean_object* v_dummy_5435_; lean_object* v_nargs_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; size_t v_sz_5441_; size_t v___x_5442_; lean_object* v_args_5443_; lean_object* v___x_5444_; uint8_t v___x_5445_; lean_object* v___x_5446_; 
v___x_5432_ = l_Lean_Expr_getAppFn(v_e_5431_);
v___x_5433_ = 0;
v_f_5434_ = l_Lean_Expr_setPPExplicit(v___x_5432_, v___x_5433_);
v_dummy_5435_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5436_ = l_Lean_Expr_getAppNumArgs(v_e_5431_);
lean_inc(v_nargs_5436_);
v___x_5437_ = lean_mk_array(v_nargs_5436_, v_dummy_5435_);
v___x_5438_ = lean_unsigned_to_nat(1u);
v___x_5439_ = lean_nat_sub(v_nargs_5436_, v___x_5438_);
lean_dec(v_nargs_5436_);
v___x_5440_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5431_, v___x_5437_, v___x_5439_);
v_sz_5441_ = lean_array_size(v___x_5440_);
v___x_5442_ = ((size_t)0ULL);
v_args_5443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5441_, v___x_5442_, v___x_5440_);
v___x_5444_ = l_Lean_mkAppN(v_f_5434_, v_args_5443_);
lean_dec_ref(v_args_5443_);
v___x_5445_ = 1;
v___x_5446_ = l_Lean_Expr_setPPExplicit(v___x_5444_, v___x_5445_);
return v___x_5446_;
}
else
{
return v_e_5431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5447_, lean_object* v_body_5448_, lean_object* v_x_5449_){
_start:
{
lean_object* v___x_5450_; 
v___x_5450_ = lean_apply_1(v_f_5447_, v_body_5448_);
return v___x_5450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5451_, lean_object* v_binderType_5452_, lean_object* v_x_5453_){
_start:
{
lean_object* v___x_5454_; 
v___x_5454_ = lean_apply_1(v_f_5451_, v_binderType_5452_);
return v___x_5454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5455_, lean_object* v_value_5456_, lean_object* v_x_5457_){
_start:
{
lean_object* v___x_5458_; 
v___x_5458_ = lean_apply_1(v_f_5455_, v_value_5456_);
return v___x_5458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5459_, lean_object* v_type_5460_, lean_object* v_x_5461_){
_start:
{
lean_object* v___x_5462_; 
v___x_5462_ = lean_apply_1(v_f_5459_, v_type_5460_);
return v___x_5462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5463_, lean_object* v_arg_5464_, lean_object* v_x_5465_){
_start:
{
lean_object* v___x_5466_; 
v___x_5466_ = lean_apply_1(v_f_5463_, v_arg_5464_);
return v___x_5466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5467_, lean_object* v_fn_5468_, lean_object* v_x_5469_){
_start:
{
lean_object* v___x_5470_; 
v___x_5470_ = lean_apply_1(v_f_5467_, v_fn_5468_);
return v___x_5470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5471_, lean_object* v_f_5472_, lean_object* v_x_5473_){
_start:
{
switch(lean_obj_tag(v_x_5473_))
{
case 7:
{
lean_object* v_toPure_5474_; lean_object* v_toSeq_5475_; lean_object* v_binderType_5476_; lean_object* v_body_5477_; lean_object* v___f_5478_; lean_object* v___f_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; 
v_toPure_5474_ = lean_ctor_get(v_inst_5471_, 1);
lean_inc(v_toPure_5474_);
v_toSeq_5475_ = lean_ctor_get(v_inst_5471_, 2);
lean_inc_n(v_toSeq_5475_, 2);
lean_dec_ref(v_inst_5471_);
v_binderType_5476_ = lean_ctor_get(v_x_5473_, 1);
v_body_5477_ = lean_ctor_get(v_x_5473_, 2);
lean_inc_ref(v_body_5477_);
lean_inc(v_f_5472_);
v___f_5478_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5478_, 0, v_f_5472_);
lean_closure_set(v___f_5478_, 1, v_body_5477_);
lean_inc_ref(v_binderType_5476_);
v___f_5479_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5479_, 0, v_f_5472_);
lean_closure_set(v___f_5479_, 1, v_binderType_5476_);
v___x_5480_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5480_, 0, v_x_5473_);
v___x_5481_ = lean_apply_2(v_toPure_5474_, lean_box(0), v___x_5480_);
v___x_5482_ = lean_apply_4(v_toSeq_5475_, lean_box(0), lean_box(0), v___x_5481_, v___f_5479_);
v___x_5483_ = lean_apply_4(v_toSeq_5475_, lean_box(0), lean_box(0), v___x_5482_, v___f_5478_);
return v___x_5483_;
}
case 6:
{
lean_object* v_toPure_5484_; lean_object* v_toSeq_5485_; lean_object* v_binderType_5486_; lean_object* v_body_5487_; lean_object* v___f_5488_; lean_object* v___f_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; 
v_toPure_5484_ = lean_ctor_get(v_inst_5471_, 1);
lean_inc(v_toPure_5484_);
v_toSeq_5485_ = lean_ctor_get(v_inst_5471_, 2);
lean_inc_n(v_toSeq_5485_, 2);
lean_dec_ref(v_inst_5471_);
v_binderType_5486_ = lean_ctor_get(v_x_5473_, 1);
v_body_5487_ = lean_ctor_get(v_x_5473_, 2);
lean_inc_ref(v_body_5487_);
lean_inc(v_f_5472_);
v___f_5488_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5488_, 0, v_f_5472_);
lean_closure_set(v___f_5488_, 1, v_body_5487_);
lean_inc_ref(v_binderType_5486_);
v___f_5489_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5489_, 0, v_f_5472_);
lean_closure_set(v___f_5489_, 1, v_binderType_5486_);
v___x_5490_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5490_, 0, v_x_5473_);
v___x_5491_ = lean_apply_2(v_toPure_5484_, lean_box(0), v___x_5490_);
v___x_5492_ = lean_apply_4(v_toSeq_5485_, lean_box(0), lean_box(0), v___x_5491_, v___f_5489_);
v___x_5493_ = lean_apply_4(v_toSeq_5485_, lean_box(0), lean_box(0), v___x_5492_, v___f_5488_);
return v___x_5493_;
}
case 10:
{
lean_object* v_toFunctor_5494_; lean_object* v_expr_5495_; lean_object* v_map_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; 
v_toFunctor_5494_ = lean_ctor_get(v_inst_5471_, 0);
lean_inc_ref(v_toFunctor_5494_);
lean_dec_ref(v_inst_5471_);
v_expr_5495_ = lean_ctor_get(v_x_5473_, 1);
lean_inc_ref(v_expr_5495_);
v_map_5496_ = lean_ctor_get(v_toFunctor_5494_, 0);
lean_inc(v_map_5496_);
lean_dec_ref(v_toFunctor_5494_);
v___x_5497_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5497_, 0, v_x_5473_);
v___x_5498_ = lean_apply_1(v_f_5472_, v_expr_5495_);
v___x_5499_ = lean_apply_4(v_map_5496_, lean_box(0), lean_box(0), v___x_5497_, v___x_5498_);
return v___x_5499_;
}
case 8:
{
lean_object* v_toPure_5500_; lean_object* v_toSeq_5501_; lean_object* v_type_5502_; lean_object* v_value_5503_; lean_object* v_body_5504_; lean_object* v___f_5505_; lean_object* v___f_5506_; lean_object* v___f_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; 
v_toPure_5500_ = lean_ctor_get(v_inst_5471_, 1);
lean_inc(v_toPure_5500_);
v_toSeq_5501_ = lean_ctor_get(v_inst_5471_, 2);
lean_inc_n(v_toSeq_5501_, 3);
lean_dec_ref(v_inst_5471_);
v_type_5502_ = lean_ctor_get(v_x_5473_, 1);
v_value_5503_ = lean_ctor_get(v_x_5473_, 2);
v_body_5504_ = lean_ctor_get(v_x_5473_, 3);
lean_inc_ref(v_body_5504_);
lean_inc_n(v_f_5472_, 2);
v___f_5505_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5505_, 0, v_f_5472_);
lean_closure_set(v___f_5505_, 1, v_body_5504_);
lean_inc_ref(v_value_5503_);
v___f_5506_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5506_, 0, v_f_5472_);
lean_closure_set(v___f_5506_, 1, v_value_5503_);
lean_inc_ref(v_type_5502_);
v___f_5507_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5507_, 0, v_f_5472_);
lean_closure_set(v___f_5507_, 1, v_type_5502_);
v___x_5508_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5508_, 0, v_x_5473_);
v___x_5509_ = lean_apply_2(v_toPure_5500_, lean_box(0), v___x_5508_);
v___x_5510_ = lean_apply_4(v_toSeq_5501_, lean_box(0), lean_box(0), v___x_5509_, v___f_5507_);
v___x_5511_ = lean_apply_4(v_toSeq_5501_, lean_box(0), lean_box(0), v___x_5510_, v___f_5506_);
v___x_5512_ = lean_apply_4(v_toSeq_5501_, lean_box(0), lean_box(0), v___x_5511_, v___f_5505_);
return v___x_5512_;
}
case 5:
{
lean_object* v_toPure_5513_; lean_object* v_toSeq_5514_; lean_object* v_fn_5515_; lean_object* v_arg_5516_; lean_object* v___f_5517_; lean_object* v___f_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; 
v_toPure_5513_ = lean_ctor_get(v_inst_5471_, 1);
lean_inc(v_toPure_5513_);
v_toSeq_5514_ = lean_ctor_get(v_inst_5471_, 2);
lean_inc_n(v_toSeq_5514_, 2);
lean_dec_ref(v_inst_5471_);
v_fn_5515_ = lean_ctor_get(v_x_5473_, 0);
v_arg_5516_ = lean_ctor_get(v_x_5473_, 1);
lean_inc_ref(v_arg_5516_);
lean_inc(v_f_5472_);
v___f_5517_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5517_, 0, v_f_5472_);
lean_closure_set(v___f_5517_, 1, v_arg_5516_);
lean_inc_ref(v_fn_5515_);
v___f_5518_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5518_, 0, v_f_5472_);
lean_closure_set(v___f_5518_, 1, v_fn_5515_);
v___x_5519_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5519_, 0, v_x_5473_);
v___x_5520_ = lean_apply_2(v_toPure_5513_, lean_box(0), v___x_5519_);
v___x_5521_ = lean_apply_4(v_toSeq_5514_, lean_box(0), lean_box(0), v___x_5520_, v___f_5518_);
v___x_5522_ = lean_apply_4(v_toSeq_5514_, lean_box(0), lean_box(0), v___x_5521_, v___f_5517_);
return v___x_5522_;
}
case 11:
{
lean_object* v_toFunctor_5523_; lean_object* v_struct_5524_; lean_object* v_map_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; 
v_toFunctor_5523_ = lean_ctor_get(v_inst_5471_, 0);
lean_inc_ref(v_toFunctor_5523_);
lean_dec_ref(v_inst_5471_);
v_struct_5524_ = lean_ctor_get(v_x_5473_, 2);
lean_inc_ref(v_struct_5524_);
v_map_5525_ = lean_ctor_get(v_toFunctor_5523_, 0);
lean_inc(v_map_5525_);
lean_dec_ref(v_toFunctor_5523_);
v___x_5526_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5526_, 0, v_x_5473_);
v___x_5527_ = lean_apply_1(v_f_5472_, v_struct_5524_);
v___x_5528_ = lean_apply_4(v_map_5525_, lean_box(0), lean_box(0), v___x_5526_, v___x_5527_);
return v___x_5528_;
}
default: 
{
lean_object* v_toPure_5529_; lean_object* v___x_5530_; 
lean_dec(v_f_5472_);
v_toPure_5529_ = lean_ctor_get(v_inst_5471_, 1);
lean_inc(v_toPure_5529_);
lean_dec_ref(v_inst_5471_);
v___x_5530_ = lean_apply_2(v_toPure_5529_, lean_box(0), v_x_5473_);
return v___x_5530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5531_, lean_object* v_inst_5532_, lean_object* v_f_5533_, lean_object* v_x_5534_){
_start:
{
lean_object* v___x_5535_; 
v___x_5535_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5532_, v_f_5533_, v_x_5534_);
return v___x_5535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5536_){
_start:
{
lean_object* v_snd_5537_; 
v_snd_5537_ = lean_ctor_get(v_self_5536_, 1);
lean_inc(v_snd_5537_);
return v_snd_5537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5538_){
_start:
{
lean_object* v_res_5539_; 
v_res_5539_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5538_);
lean_dec_ref(v_self_5538_);
return v_res_5539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5540_, lean_object* v_snd_5541_){
_start:
{
lean_object* v___x_5542_; 
v___x_5542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5542_, 0, v_e_x27_5540_);
lean_ctor_set(v___x_5542_, 1, v_snd_5541_);
return v___x_5542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5543_, lean_object* v_map_5544_, lean_object* v_e_x27_5545_, lean_object* v_a_5546_){
_start:
{
lean_object* v___f_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; 
lean_inc_ref(v_e_x27_5545_);
v___f_5547_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5547_, 0, v_e_x27_5545_);
v___x_5548_ = lean_apply_2(v_f_5543_, v_a_5546_, v_e_x27_5545_);
v___x_5549_ = lean_apply_4(v_map_5544_, lean_box(0), lean_box(0), v___f_5547_, v___x_5548_);
return v___x_5549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5551_, lean_object* v_f_5552_, lean_object* v_init_5553_, lean_object* v_e_5554_){
_start:
{
lean_object* v_toApplicative_5555_; lean_object* v_toFunctor_5556_; lean_object* v___x_5558_; uint8_t v_isShared_5559_; uint8_t v_isSharedCheck_5583_; 
v_toApplicative_5555_ = lean_ctor_get(v_inst_5551_, 0);
lean_inc_ref(v_toApplicative_5555_);
v_toFunctor_5556_ = lean_ctor_get(v_toApplicative_5555_, 0);
v_isSharedCheck_5583_ = !lean_is_exclusive(v_toApplicative_5555_);
if (v_isSharedCheck_5583_ == 0)
{
lean_object* v_unused_5584_; lean_object* v_unused_5585_; lean_object* v_unused_5586_; lean_object* v_unused_5587_; 
v_unused_5584_ = lean_ctor_get(v_toApplicative_5555_, 4);
lean_dec(v_unused_5584_);
v_unused_5585_ = lean_ctor_get(v_toApplicative_5555_, 3);
lean_dec(v_unused_5585_);
v_unused_5586_ = lean_ctor_get(v_toApplicative_5555_, 2);
lean_dec(v_unused_5586_);
v_unused_5587_ = lean_ctor_get(v_toApplicative_5555_, 1);
lean_dec(v_unused_5587_);
v___x_5558_ = v_toApplicative_5555_;
v_isShared_5559_ = v_isSharedCheck_5583_;
goto v_resetjp_5557_;
}
else
{
lean_inc(v_toFunctor_5556_);
lean_dec(v_toApplicative_5555_);
v___x_5558_ = lean_box(0);
v_isShared_5559_ = v_isSharedCheck_5583_;
goto v_resetjp_5557_;
}
v_resetjp_5557_:
{
lean_object* v_map_5560_; lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5581_; 
v_map_5560_ = lean_ctor_get(v_toFunctor_5556_, 0);
v_isSharedCheck_5581_ = !lean_is_exclusive(v_toFunctor_5556_);
if (v_isSharedCheck_5581_ == 0)
{
lean_object* v_unused_5582_; 
v_unused_5582_ = lean_ctor_get(v_toFunctor_5556_, 1);
lean_dec(v_unused_5582_);
v___x_5562_ = v_toFunctor_5556_;
v_isShared_5563_ = v_isSharedCheck_5581_;
goto v_resetjp_5561_;
}
else
{
lean_inc(v_map_5560_);
lean_dec(v_toFunctor_5556_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5581_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
lean_object* v___f_5564_; lean_object* v___f_5565_; lean_object* v___f_5566_; lean_object* v___f_5567_; lean_object* v___f_5568_; lean_object* v___f_5569_; lean_object* v___x_5570_; lean_object* v___x_5572_; 
v___f_5564_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5560_);
v___f_5565_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5565_, 0, v_f_5552_);
lean_closure_set(v___f_5565_, 1, v_map_5560_);
lean_inc_ref_n(v_inst_5551_, 5);
v___f_5566_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5566_, 0, v_inst_5551_);
v___f_5567_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5567_, 0, v_inst_5551_);
v___f_5568_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5568_, 0, v_inst_5551_);
v___f_5569_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5569_, 0, v_inst_5551_);
v___x_5570_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5570_, 0, lean_box(0));
lean_closure_set(v___x_5570_, 1, lean_box(0));
lean_closure_set(v___x_5570_, 2, v_inst_5551_);
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 1, v___f_5566_);
lean_ctor_set(v___x_5562_, 0, v___x_5570_);
v___x_5572_ = v___x_5562_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v___x_5570_);
lean_ctor_set(v_reuseFailAlloc_5580_, 1, v___f_5566_);
v___x_5572_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
lean_object* v___x_5573_; lean_object* v___x_5575_; 
v___x_5573_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5573_, 0, lean_box(0));
lean_closure_set(v___x_5573_, 1, lean_box(0));
lean_closure_set(v___x_5573_, 2, v_inst_5551_);
if (v_isShared_5559_ == 0)
{
lean_ctor_set(v___x_5558_, 4, v___f_5569_);
lean_ctor_set(v___x_5558_, 3, v___f_5568_);
lean_ctor_set(v___x_5558_, 2, v___f_5567_);
lean_ctor_set(v___x_5558_, 1, v___x_5573_);
lean_ctor_set(v___x_5558_, 0, v___x_5572_);
v___x_5575_ = v___x_5558_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v___x_5572_);
lean_ctor_set(v_reuseFailAlloc_5579_, 1, v___x_5573_);
lean_ctor_set(v_reuseFailAlloc_5579_, 2, v___f_5567_);
lean_ctor_set(v_reuseFailAlloc_5579_, 3, v___f_5568_);
lean_ctor_set(v_reuseFailAlloc_5579_, 4, v___f_5569_);
v___x_5575_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
lean_object* v___x_18__overap_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; 
v___x_18__overap_5576_ = l_Lean_Expr_traverseChildren___redArg(v___x_5575_, v___f_5565_, v_e_5554_);
v___x_5577_ = lean_apply_1(v___x_18__overap_5576_, v_init_5553_);
v___x_5578_ = lean_apply_4(v_map_5560_, lean_box(0), lean_box(0), v___f_5564_, v___x_5577_);
return v___x_5578_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5588_, lean_object* v_m_5589_, lean_object* v_inst_5590_, lean_object* v_f_5591_, lean_object* v_init_5592_, lean_object* v_e_5593_){
_start:
{
lean_object* v___x_5594_; 
v___x_5594_ = l_Lean_Expr_foldlM___redArg(v_inst_5590_, v_f_5591_, v_init_5592_, v_e_5593_);
return v___x_5594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5595_){
_start:
{
lean_object* v_d_5597_; lean_object* v_b_5598_; 
switch(lean_obj_tag(v_x_5595_))
{
case 5:
{
lean_object* v_fn_5604_; lean_object* v_arg_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; 
v_fn_5604_ = lean_ctor_get(v_x_5595_, 0);
v_arg_5605_ = lean_ctor_get(v_x_5595_, 1);
v___x_5606_ = lean_unsigned_to_nat(1u);
v___x_5607_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5604_);
v___x_5608_ = lean_nat_add(v___x_5606_, v___x_5607_);
lean_dec(v___x_5607_);
v___x_5609_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5605_);
v___x_5610_ = lean_nat_add(v___x_5608_, v___x_5609_);
lean_dec(v___x_5609_);
lean_dec(v___x_5608_);
return v___x_5610_;
}
case 6:
{
lean_object* v_binderType_5611_; lean_object* v_body_5612_; 
v_binderType_5611_ = lean_ctor_get(v_x_5595_, 1);
v_body_5612_ = lean_ctor_get(v_x_5595_, 2);
v_d_5597_ = v_binderType_5611_;
v_b_5598_ = v_body_5612_;
goto v___jp_5596_;
}
case 7:
{
lean_object* v_binderType_5613_; lean_object* v_body_5614_; 
v_binderType_5613_ = lean_ctor_get(v_x_5595_, 1);
v_body_5614_ = lean_ctor_get(v_x_5595_, 2);
v_d_5597_ = v_binderType_5613_;
v_b_5598_ = v_body_5614_;
goto v___jp_5596_;
}
case 8:
{
lean_object* v_type_5615_; lean_object* v_value_5616_; lean_object* v_body_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; 
v_type_5615_ = lean_ctor_get(v_x_5595_, 1);
v_value_5616_ = lean_ctor_get(v_x_5595_, 2);
v_body_5617_ = lean_ctor_get(v_x_5595_, 3);
v___x_5618_ = lean_unsigned_to_nat(1u);
v___x_5619_ = l_Lean_Expr_sizeWithoutSharing(v_type_5615_);
v___x_5620_ = lean_nat_add(v___x_5618_, v___x_5619_);
lean_dec(v___x_5619_);
v___x_5621_ = l_Lean_Expr_sizeWithoutSharing(v_value_5616_);
v___x_5622_ = lean_nat_add(v___x_5620_, v___x_5621_);
lean_dec(v___x_5621_);
lean_dec(v___x_5620_);
v___x_5623_ = l_Lean_Expr_sizeWithoutSharing(v_body_5617_);
v___x_5624_ = lean_nat_add(v___x_5622_, v___x_5623_);
lean_dec(v___x_5623_);
lean_dec(v___x_5622_);
return v___x_5624_;
}
case 10:
{
lean_object* v_expr_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; 
v_expr_5625_ = lean_ctor_get(v_x_5595_, 1);
v___x_5626_ = lean_unsigned_to_nat(1u);
v___x_5627_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5625_);
v___x_5628_ = lean_nat_add(v___x_5626_, v___x_5627_);
lean_dec(v___x_5627_);
return v___x_5628_;
}
case 11:
{
lean_object* v_struct_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; 
v_struct_5629_ = lean_ctor_get(v_x_5595_, 2);
v___x_5630_ = lean_unsigned_to_nat(1u);
v___x_5631_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5629_);
v___x_5632_ = lean_nat_add(v___x_5630_, v___x_5631_);
lean_dec(v___x_5631_);
return v___x_5632_;
}
default: 
{
lean_object* v___x_5633_; 
v___x_5633_ = lean_unsigned_to_nat(1u);
return v___x_5633_;
}
}
v___jp_5596_:
{
lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; 
v___x_5599_ = lean_unsigned_to_nat(1u);
v___x_5600_ = l_Lean_Expr_sizeWithoutSharing(v_d_5597_);
v___x_5601_ = lean_nat_add(v___x_5599_, v___x_5600_);
lean_dec(v___x_5600_);
v___x_5602_ = l_Lean_Expr_sizeWithoutSharing(v_b_5598_);
v___x_5603_ = lean_nat_add(v___x_5601_, v___x_5602_);
lean_dec(v___x_5602_);
lean_dec(v___x_5601_);
return v___x_5603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5634_){
_start:
{
lean_object* v_res_5635_; 
v_res_5635_ = l_Lean_Expr_sizeWithoutSharing(v_x_5634_);
lean_dec_ref(v_x_5634_);
return v_res_5635_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5638_, lean_object* v_e_5639_){
_start:
{
lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; 
v___x_5640_ = l_Lean_KVMap_empty;
v___x_5641_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5642_ = l_Lean_KVMap_insert(v___x_5640_, v_kind_5638_, v___x_5641_);
v___x_5643_ = l_Lean_Expr_mdata___override(v___x_5642_, v_e_5639_);
return v___x_5643_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5644_, lean_object* v_e_5645_){
_start:
{
if (lean_obj_tag(v_e_5645_) == 10)
{
lean_object* v_data_5646_; lean_object* v_expr_5647_; uint8_t v___y_5649_; lean_object* v___x_5652_; lean_object* v___x_5653_; uint8_t v___x_5654_; 
v_data_5646_ = lean_ctor_get(v_e_5645_, 0);
v_expr_5647_ = lean_ctor_get(v_e_5645_, 1);
v___x_5652_ = l_Lean_KVMap_size(v_data_5646_);
v___x_5653_ = lean_unsigned_to_nat(1u);
v___x_5654_ = lean_nat_dec_eq(v___x_5652_, v___x_5653_);
lean_dec(v___x_5652_);
if (v___x_5654_ == 0)
{
v___y_5649_ = v___x_5654_;
goto v___jp_5648_;
}
else
{
uint8_t v___x_5655_; uint8_t v___x_5656_; 
v___x_5655_ = 0;
v___x_5656_ = l_Lean_KVMap_getBool(v_data_5646_, v_kind_5644_, v___x_5655_);
v___y_5649_ = v___x_5656_;
goto v___jp_5648_;
}
v___jp_5648_:
{
if (v___y_5649_ == 0)
{
lean_object* v___x_5650_; 
v___x_5650_ = lean_box(0);
return v___x_5650_;
}
else
{
lean_object* v___x_5651_; 
lean_inc_ref(v_expr_5647_);
v___x_5651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5651_, 0, v_expr_5647_);
return v___x_5651_;
}
}
}
else
{
lean_object* v___x_5657_; 
v___x_5657_ = lean_box(0);
return v___x_5657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* v_kind_5658_, lean_object* v_e_5659_){
_start:
{
lean_object* v_res_5660_; 
v_res_5660_ = l_Lean_annotation_x3f(v_kind_5658_, v_e_5659_);
lean_dec_ref(v_e_5659_);
lean_dec(v_kind_5658_);
return v_res_5660_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* v_e_5664_){
_start:
{
lean_object* v___x_5665_; lean_object* v___x_5666_; 
v___x_5665_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5666_ = l_Lean_mkAnnotation(v___x_5665_, v_e_5664_);
return v___x_5666_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* v_e_5667_){
_start:
{
lean_object* v___x_5668_; lean_object* v___x_5669_; 
v___x_5668_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5669_ = l_Lean_annotation_x3f(v___x_5668_, v_e_5667_);
return v___x_5669_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* v_e_5670_){
_start:
{
lean_object* v_res_5671_; 
v_res_5671_ = l_Lean_inaccessible_x3f(v_e_5670_);
lean_dec_ref(v_e_5670_);
return v_res_5671_;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* v_p_5676_){
_start:
{
if (lean_obj_tag(v_p_5676_) == 10)
{
lean_object* v_data_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; 
v_data_5677_ = lean_ctor_get(v_p_5676_, 0);
v___x_5678_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5679_ = l_Lean_KVMap_find(v_data_5677_, v___x_5678_);
if (lean_obj_tag(v___x_5679_) == 1)
{
lean_object* v_val_5680_; lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5691_; 
v_val_5680_ = lean_ctor_get(v___x_5679_, 0);
v_isSharedCheck_5691_ = !lean_is_exclusive(v___x_5679_);
if (v_isSharedCheck_5691_ == 0)
{
v___x_5682_ = v___x_5679_;
v_isShared_5683_ = v_isSharedCheck_5691_;
goto v_resetjp_5681_;
}
else
{
lean_inc(v_val_5680_);
lean_dec(v___x_5679_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5691_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
if (lean_obj_tag(v_val_5680_) == 5)
{
lean_object* v_v_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5688_; 
v_v_5684_ = lean_ctor_get(v_val_5680_, 0);
lean_inc(v_v_5684_);
lean_dec_ref(v_val_5680_);
v___x_5685_ = l_Lean_Expr_mdataExpr_x21(v_p_5676_);
v___x_5686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5686_, 0, v_v_5684_);
lean_ctor_set(v___x_5686_, 1, v___x_5685_);
if (v_isShared_5683_ == 0)
{
lean_ctor_set(v___x_5682_, 0, v___x_5686_);
v___x_5688_ = v___x_5682_;
goto v_reusejp_5687_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v___x_5686_);
v___x_5688_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5687_;
}
v_reusejp_5687_:
{
return v___x_5688_;
}
}
else
{
lean_object* v___x_5690_; 
lean_del_object(v___x_5682_);
lean_dec(v_val_5680_);
v___x_5690_ = lean_box(0);
return v___x_5690_;
}
}
}
else
{
lean_object* v___x_5692_; 
lean_dec(v___x_5679_);
v___x_5692_ = lean_box(0);
return v___x_5692_;
}
}
else
{
lean_object* v___x_5693_; 
v___x_5693_ = lean_box(0);
return v___x_5693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* v_p_5694_){
_start:
{
lean_object* v_res_5695_; 
v_res_5695_ = l_Lean_patternWithRef_x3f(v_p_5694_);
lean_dec_ref(v_p_5694_);
return v_res_5695_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object* v_p_5696_){
_start:
{
lean_object* v___x_5697_; 
v___x_5697_ = l_Lean_patternWithRef_x3f(v_p_5696_);
if (lean_obj_tag(v___x_5697_) == 0)
{
uint8_t v___x_5698_; 
v___x_5698_ = 0;
return v___x_5698_;
}
else
{
uint8_t v___x_5699_; 
lean_dec_ref(v___x_5697_);
v___x_5699_ = 1;
return v___x_5699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* v_p_5700_){
_start:
{
uint8_t v_res_5701_; lean_object* v_r_5702_; 
v_res_5701_ = l_Lean_isPatternWithRef(v_p_5700_);
lean_dec_ref(v_p_5700_);
v_r_5702_ = lean_box(v_res_5701_);
return v_r_5702_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* v_p_5703_, lean_object* v_stx_5704_){
_start:
{
lean_object* v___x_5705_; 
v___x_5705_ = l_Lean_patternWithRef_x3f(v_p_5703_);
if (lean_obj_tag(v___x_5705_) == 0)
{
lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; 
v___x_5706_ = l_Lean_KVMap_empty;
v___x_5707_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5708_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_5708_, 0, v_stx_5704_);
v___x_5709_ = l_Lean_KVMap_insert(v___x_5706_, v___x_5707_, v___x_5708_);
v___x_5710_ = l_Lean_Expr_mdata___override(v___x_5709_, v_p_5703_);
return v___x_5710_;
}
else
{
lean_dec_ref(v___x_5705_);
lean_dec(v_stx_5704_);
return v_p_5703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* v_e_5711_){
_start:
{
lean_object* v___x_5712_; 
v___x_5712_ = l_Lean_inaccessible_x3f(v_e_5711_);
if (lean_obj_tag(v___x_5712_) == 1)
{
return v___x_5712_;
}
else
{
lean_object* v___x_5713_; 
lean_dec(v___x_5712_);
v___x_5713_ = l_Lean_patternWithRef_x3f(v_e_5711_);
if (lean_obj_tag(v___x_5713_) == 1)
{
lean_object* v_val_5714_; lean_object* v___x_5716_; uint8_t v_isShared_5717_; uint8_t v_isSharedCheck_5722_; 
v_val_5714_ = lean_ctor_get(v___x_5713_, 0);
v_isSharedCheck_5722_ = !lean_is_exclusive(v___x_5713_);
if (v_isSharedCheck_5722_ == 0)
{
v___x_5716_ = v___x_5713_;
v_isShared_5717_ = v_isSharedCheck_5722_;
goto v_resetjp_5715_;
}
else
{
lean_inc(v_val_5714_);
lean_dec(v___x_5713_);
v___x_5716_ = lean_box(0);
v_isShared_5717_ = v_isSharedCheck_5722_;
goto v_resetjp_5715_;
}
v_resetjp_5715_:
{
lean_object* v_snd_5718_; lean_object* v___x_5720_; 
v_snd_5718_ = lean_ctor_get(v_val_5714_, 1);
lean_inc(v_snd_5718_);
lean_dec(v_val_5714_);
if (v_isShared_5717_ == 0)
{
lean_ctor_set(v___x_5716_, 0, v_snd_5718_);
v___x_5720_ = v___x_5716_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5721_; 
v_reuseFailAlloc_5721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5721_, 0, v_snd_5718_);
v___x_5720_ = v_reuseFailAlloc_5721_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
return v___x_5720_;
}
}
}
else
{
lean_object* v___x_5723_; 
lean_dec(v___x_5713_);
v___x_5723_ = lean_box(0);
return v___x_5723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* v_e_5724_){
_start:
{
lean_object* v_res_5725_; 
v_res_5725_ = l_Lean_patternAnnotation_x3f(v_e_5724_);
lean_dec_ref(v_e_5724_);
return v_res_5725_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* v_e_5729_){
_start:
{
lean_object* v___x_5730_; lean_object* v___x_5731_; 
v___x_5730_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5731_ = l_Lean_mkAnnotation(v___x_5730_, v_e_5729_);
return v___x_5731_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* v_e_5735_){
_start:
{
lean_object* v___x_5736_; lean_object* v___x_5737_; 
v___x_5736_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5737_ = l_Lean_annotation_x3f(v___x_5736_, v_e_5735_);
if (lean_obj_tag(v___x_5737_) == 0)
{
return v___x_5737_;
}
else
{
lean_object* v_val_5738_; lean_object* v___x_5740_; uint8_t v_isShared_5741_; uint8_t v_isSharedCheck_5751_; 
v_val_5738_ = lean_ctor_get(v___x_5737_, 0);
v_isSharedCheck_5751_ = !lean_is_exclusive(v___x_5737_);
if (v_isSharedCheck_5751_ == 0)
{
v___x_5740_ = v___x_5737_;
v_isShared_5741_ = v_isSharedCheck_5751_;
goto v_resetjp_5739_;
}
else
{
lean_inc(v_val_5738_);
lean_dec(v___x_5737_);
v___x_5740_ = lean_box(0);
v_isShared_5741_ = v_isSharedCheck_5751_;
goto v_resetjp_5739_;
}
v_resetjp_5739_:
{
lean_object* v___x_5742_; lean_object* v___x_5743_; uint8_t v___x_5744_; 
v___x_5742_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5743_ = lean_unsigned_to_nat(3u);
v___x_5744_ = l_Lean_Expr_isAppOfArity(v_val_5738_, v___x_5742_, v___x_5743_);
if (v___x_5744_ == 0)
{
lean_object* v___x_5745_; 
lean_del_object(v___x_5740_);
lean_dec(v_val_5738_);
v___x_5745_ = lean_box(0);
return v___x_5745_;
}
else
{
lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5749_; 
v___x_5746_ = l_Lean_Expr_appFn_x21(v_val_5738_);
lean_dec(v_val_5738_);
v___x_5747_ = l_Lean_Expr_appArg_x21(v___x_5746_);
lean_dec_ref(v___x_5746_);
if (v_isShared_5741_ == 0)
{
lean_ctor_set(v___x_5740_, 0, v___x_5747_);
v___x_5749_ = v___x_5740_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v___x_5747_);
v___x_5749_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
return v___x_5749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* v_e_5752_){
_start:
{
lean_object* v_res_5753_; 
v_res_5753_ = l_Lean_isLHSGoal_x3f(v_e_5752_);
lean_dec_ref(v_e_5752_);
return v_res_5753_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* v_toPure_5754_, lean_object* v_____do__lift_5755_){
_start:
{
lean_object* v___x_5756_; 
v___x_5756_ = lean_apply_2(v_toPure_5754_, lean_box(0), v_____do__lift_5755_);
return v___x_5756_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* v_inst_5757_, lean_object* v_inst_5758_){
_start:
{
lean_object* v_toApplicative_5759_; lean_object* v_toBind_5760_; lean_object* v_toPure_5761_; lean_object* v___x_5762_; lean_object* v___f_5763_; lean_object* v___x_5764_; 
v_toApplicative_5759_ = lean_ctor_get(v_inst_5757_, 0);
v_toBind_5760_ = lean_ctor_get(v_inst_5757_, 1);
lean_inc(v_toBind_5760_);
v_toPure_5761_ = lean_ctor_get(v_toApplicative_5759_, 1);
lean_inc(v_toPure_5761_);
v___x_5762_ = l_Lean_mkFreshId___redArg(v_inst_5757_, v_inst_5758_);
v___f_5763_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5763_, 0, v_toPure_5761_);
v___x_5764_ = lean_apply_4(v_toBind_5760_, lean_box(0), lean_box(0), v___x_5762_, v___f_5763_);
return v___x_5764_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* v_m_5765_, lean_object* v_inst_5766_, lean_object* v_inst_5767_){
_start:
{
lean_object* v___x_5768_; 
v___x_5768_ = l_Lean_mkFreshFVarId___redArg(v_inst_5766_, v_inst_5767_);
return v___x_5768_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* v_inst_5769_, lean_object* v_inst_5770_){
_start:
{
lean_object* v_toApplicative_5771_; lean_object* v_toBind_5772_; lean_object* v_toPure_5773_; lean_object* v___x_5774_; lean_object* v___f_5775_; lean_object* v___x_5776_; 
v_toApplicative_5771_ = lean_ctor_get(v_inst_5769_, 0);
v_toBind_5772_ = lean_ctor_get(v_inst_5769_, 1);
lean_inc(v_toBind_5772_);
v_toPure_5773_ = lean_ctor_get(v_toApplicative_5771_, 1);
lean_inc(v_toPure_5773_);
v___x_5774_ = l_Lean_mkFreshId___redArg(v_inst_5769_, v_inst_5770_);
v___f_5775_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5775_, 0, v_toPure_5773_);
v___x_5776_ = lean_apply_4(v_toBind_5772_, lean_box(0), lean_box(0), v___x_5774_, v___f_5775_);
return v___x_5776_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* v_m_5777_, lean_object* v_inst_5778_, lean_object* v_inst_5779_){
_start:
{
lean_object* v___x_5780_; 
v___x_5780_ = l_Lean_mkFreshMVarId___redArg(v_inst_5778_, v_inst_5779_);
return v___x_5780_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* v_inst_5781_, lean_object* v_inst_5782_){
_start:
{
lean_object* v_toApplicative_5783_; lean_object* v_toBind_5784_; lean_object* v_toPure_5785_; lean_object* v___x_5786_; lean_object* v___f_5787_; lean_object* v___x_5788_; 
v_toApplicative_5783_ = lean_ctor_get(v_inst_5781_, 0);
v_toBind_5784_ = lean_ctor_get(v_inst_5781_, 1);
lean_inc(v_toBind_5784_);
v_toPure_5785_ = lean_ctor_get(v_toApplicative_5783_, 1);
lean_inc(v_toPure_5785_);
v___x_5786_ = l_Lean_mkFreshId___redArg(v_inst_5781_, v_inst_5782_);
v___f_5787_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5787_, 0, v_toPure_5785_);
v___x_5788_ = lean_apply_4(v_toBind_5784_, lean_box(0), lean_box(0), v___x_5786_, v___f_5787_);
return v___x_5788_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* v_m_5789_, lean_object* v_inst_5790_, lean_object* v_inst_5791_){
_start:
{
lean_object* v___x_5792_; 
v___x_5792_ = l_Lean_mkFreshLMVarId___redArg(v_inst_5790_, v_inst_5791_);
return v___x_5792_;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2(void){
_start:
{
lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; 
v___x_5796_ = lean_box(0);
v___x_5797_ = ((lean_object*)(l_Lean_mkNot___closed__1));
v___x_5798_ = l_Lean_Expr_const___override(v___x_5797_, v___x_5796_);
return v___x_5798_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* v_p_5799_){
_start:
{
lean_object* v___x_5800_; lean_object* v___x_5801_; 
v___x_5800_ = lean_obj_once(&l_Lean_mkNot___closed__2, &l_Lean_mkNot___closed__2_once, _init_l_Lean_mkNot___closed__2);
v___x_5801_ = l_Lean_Expr_app___override(v___x_5800_, v_p_5799_);
return v___x_5801_;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2(void){
_start:
{
lean_object* v___x_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; 
v___x_5805_ = lean_box(0);
v___x_5806_ = ((lean_object*)(l_Lean_mkOr___closed__1));
v___x_5807_ = l_Lean_Expr_const___override(v___x_5806_, v___x_5805_);
return v___x_5807_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* v_p_5808_, lean_object* v_q_5809_){
_start:
{
lean_object* v___x_5810_; lean_object* v___x_5811_; 
v___x_5810_ = lean_obj_once(&l_Lean_mkOr___closed__2, &l_Lean_mkOr___closed__2_once, _init_l_Lean_mkOr___closed__2);
v___x_5811_ = l_Lean_mkAppB(v___x_5810_, v_p_5808_, v_q_5809_);
return v___x_5811_;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2(void){
_start:
{
lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; 
v___x_5815_ = lean_box(0);
v___x_5816_ = ((lean_object*)(l_Lean_mkAnd___closed__1));
v___x_5817_ = l_Lean_Expr_const___override(v___x_5816_, v___x_5815_);
return v___x_5817_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* v_p_5818_, lean_object* v_q_5819_){
_start:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; 
v___x_5820_ = lean_obj_once(&l_Lean_mkAnd___closed__2, &l_Lean_mkAnd___closed__2_once, _init_l_Lean_mkAnd___closed__2);
v___x_5821_ = l_Lean_mkAppB(v___x_5820_, v_p_5818_, v_q_5819_);
return v___x_5821_;
}
}
static lean_object* _init_l_Lean_mkAndN___closed__0(void){
_start:
{
lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; 
v___x_5822_ = lean_box(0);
v___x_5823_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_5824_ = l_Lean_Expr_const___override(v___x_5823_, v___x_5822_);
return v___x_5824_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* v_x_5825_){
_start:
{
if (lean_obj_tag(v_x_5825_) == 0)
{
lean_object* v___x_5826_; 
v___x_5826_ = lean_obj_once(&l_Lean_mkAndN___closed__0, &l_Lean_mkAndN___closed__0_once, _init_l_Lean_mkAndN___closed__0);
return v___x_5826_;
}
else
{
lean_object* v_tail_5827_; 
v_tail_5827_ = lean_ctor_get(v_x_5825_, 1);
if (lean_obj_tag(v_tail_5827_) == 0)
{
lean_object* v_head_5828_; 
v_head_5828_ = lean_ctor_get(v_x_5825_, 0);
lean_inc(v_head_5828_);
lean_dec_ref(v_x_5825_);
return v_head_5828_;
}
else
{
lean_object* v_head_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; 
lean_inc(v_tail_5827_);
v_head_5829_ = lean_ctor_get(v_x_5825_, 0);
lean_inc(v_head_5829_);
lean_dec_ref(v_x_5825_);
v___x_5830_ = l_Lean_mkAndN(v_tail_5827_);
v___x_5831_ = l_Lean_mkAnd(v_head_5829_, v___x_5830_);
return v___x_5831_;
}
}
}
}
static lean_object* _init_l_Lean_mkEM___closed__3(void){
_start:
{
lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; 
v___x_5837_ = lean_box(0);
v___x_5838_ = ((lean_object*)(l_Lean_mkEM___closed__2));
v___x_5839_ = l_Lean_Expr_const___override(v___x_5838_, v___x_5837_);
return v___x_5839_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* v_p_5840_){
_start:
{
lean_object* v___x_5841_; lean_object* v___x_5842_; 
v___x_5841_ = lean_obj_once(&l_Lean_mkEM___closed__3, &l_Lean_mkEM___closed__3_once, _init_l_Lean_mkEM___closed__3);
v___x_5842_ = l_Lean_Expr_app___override(v___x_5841_, v_p_5840_);
return v___x_5842_;
}
}
static lean_object* _init_l_Lean_mkIff___closed__2(void){
_start:
{
lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; 
v___x_5846_ = lean_box(0);
v___x_5847_ = ((lean_object*)(l_Lean_mkIff___closed__1));
v___x_5848_ = l_Lean_Expr_const___override(v___x_5847_, v___x_5846_);
return v___x_5848_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* v_p_5849_, lean_object* v_q_5850_){
_start:
{
lean_object* v___x_5851_; lean_object* v___x_5852_; 
v___x_5851_ = lean_obj_once(&l_Lean_mkIff___closed__2, &l_Lean_mkIff___closed__2_once, _init_l_Lean_mkIff___closed__2);
v___x_5852_ = l_Lean_mkAppB(v___x_5851_, v_p_5849_, v_q_5850_);
return v___x_5852_;
}
}
static lean_object* _init_l_Lean_Nat_mkType(void){
_start:
{
lean_object* v___x_5853_; 
v___x_5853_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_5853_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; 
v___x_5857_ = lean_box(0);
v___x_5858_ = ((lean_object*)(l_Lean_Nat_mkInstAdd___closed__1));
v___x_5859_ = l_Lean_Expr_const___override(v___x_5858_, v___x_5857_);
return v___x_5859_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd(void){
_start:
{
lean_object* v___x_5860_; 
v___x_5860_ = lean_obj_once(&l_Lean_Nat_mkInstAdd___closed__2, &l_Lean_Nat_mkInstAdd___closed__2_once, _init_l_Lean_Nat_mkInstAdd___closed__2);
return v___x_5860_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__2(void){
_start:
{
lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; 
v___x_5864_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5865_ = ((lean_object*)(l_Lean_Nat_mkInstHAdd___closed__1));
v___x_5866_ = l_Lean_Expr_const___override(v___x_5865_, v___x_5864_);
return v___x_5866_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__3(void){
_start:
{
lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; 
v___x_5867_ = l_Lean_Nat_mkInstAdd;
v___x_5868_ = l_Lean_Nat_mkType;
v___x_5869_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_5870_ = l_Lean_mkAppB(v___x_5869_, v___x_5868_, v___x_5867_);
return v___x_5870_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd(void){
_start:
{
lean_object* v___x_5871_; 
v___x_5871_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__3, &l_Lean_Nat_mkInstHAdd___closed__3_once, _init_l_Lean_Nat_mkInstHAdd___closed__3);
return v___x_5871_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; 
v___x_5875_ = lean_box(0);
v___x_5876_ = ((lean_object*)(l_Lean_Nat_mkInstSub___closed__1));
v___x_5877_ = l_Lean_Expr_const___override(v___x_5876_, v___x_5875_);
return v___x_5877_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub(void){
_start:
{
lean_object* v___x_5878_; 
v___x_5878_ = lean_obj_once(&l_Lean_Nat_mkInstSub___closed__2, &l_Lean_Nat_mkInstSub___closed__2_once, _init_l_Lean_Nat_mkInstSub___closed__2);
return v___x_5878_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__2(void){
_start:
{
lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; 
v___x_5882_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5883_ = ((lean_object*)(l_Lean_Nat_mkInstHSub___closed__1));
v___x_5884_ = l_Lean_Expr_const___override(v___x_5883_, v___x_5882_);
return v___x_5884_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__3(void){
_start:
{
lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; 
v___x_5885_ = l_Lean_Nat_mkInstSub;
v___x_5886_ = l_Lean_Nat_mkType;
v___x_5887_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_5888_ = l_Lean_mkAppB(v___x_5887_, v___x_5886_, v___x_5885_);
return v___x_5888_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub(void){
_start:
{
lean_object* v___x_5889_; 
v___x_5889_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__3, &l_Lean_Nat_mkInstHSub___closed__3_once, _init_l_Lean_Nat_mkInstHSub___closed__3);
return v___x_5889_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; 
v___x_5893_ = lean_box(0);
v___x_5894_ = ((lean_object*)(l_Lean_Nat_mkInstMul___closed__1));
v___x_5895_ = l_Lean_Expr_const___override(v___x_5894_, v___x_5893_);
return v___x_5895_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul(void){
_start:
{
lean_object* v___x_5896_; 
v___x_5896_ = lean_obj_once(&l_Lean_Nat_mkInstMul___closed__2, &l_Lean_Nat_mkInstMul___closed__2_once, _init_l_Lean_Nat_mkInstMul___closed__2);
return v___x_5896_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__2(void){
_start:
{
lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; 
v___x_5900_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5901_ = ((lean_object*)(l_Lean_Nat_mkInstHMul___closed__1));
v___x_5902_ = l_Lean_Expr_const___override(v___x_5901_, v___x_5900_);
return v___x_5902_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; 
v___x_5903_ = l_Lean_Nat_mkInstMul;
v___x_5904_ = l_Lean_Nat_mkType;
v___x_5905_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_5906_ = l_Lean_mkAppB(v___x_5905_, v___x_5904_, v___x_5903_);
return v___x_5906_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul(void){
_start:
{
lean_object* v___x_5907_; 
v___x_5907_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__3, &l_Lean_Nat_mkInstHMul___closed__3_once, _init_l_Lean_Nat_mkInstHMul___closed__3);
return v___x_5907_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv___closed__2(void){
_start:
{
lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; 
v___x_5912_ = lean_box(0);
v___x_5913_ = ((lean_object*)(l_Lean_Nat_mkInstDiv___closed__1));
v___x_5914_ = l_Lean_Expr_const___override(v___x_5913_, v___x_5912_);
return v___x_5914_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv(void){
_start:
{
lean_object* v___x_5915_; 
v___x_5915_ = lean_obj_once(&l_Lean_Nat_mkInstDiv___closed__2, &l_Lean_Nat_mkInstDiv___closed__2_once, _init_l_Lean_Nat_mkInstDiv___closed__2);
return v___x_5915_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__2(void){
_start:
{
lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; 
v___x_5919_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5920_ = ((lean_object*)(l_Lean_Nat_mkInstHDiv___closed__1));
v___x_5921_ = l_Lean_Expr_const___override(v___x_5920_, v___x_5919_);
return v___x_5921_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__3(void){
_start:
{
lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; 
v___x_5922_ = l_Lean_Nat_mkInstDiv;
v___x_5923_ = l_Lean_Nat_mkType;
v___x_5924_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_5925_ = l_Lean_mkAppB(v___x_5924_, v___x_5923_, v___x_5922_);
return v___x_5925_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv(void){
_start:
{
lean_object* v___x_5926_; 
v___x_5926_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__3, &l_Lean_Nat_mkInstHDiv___closed__3_once, _init_l_Lean_Nat_mkInstHDiv___closed__3);
return v___x_5926_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod___closed__2(void){
_start:
{
lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; 
v___x_5931_ = lean_box(0);
v___x_5932_ = ((lean_object*)(l_Lean_Nat_mkInstMod___closed__1));
v___x_5933_ = l_Lean_Expr_const___override(v___x_5932_, v___x_5931_);
return v___x_5933_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod(void){
_start:
{
lean_object* v___x_5934_; 
v___x_5934_ = lean_obj_once(&l_Lean_Nat_mkInstMod___closed__2, &l_Lean_Nat_mkInstMod___closed__2_once, _init_l_Lean_Nat_mkInstMod___closed__2);
return v___x_5934_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__2(void){
_start:
{
lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; 
v___x_5938_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5939_ = ((lean_object*)(l_Lean_Nat_mkInstHMod___closed__1));
v___x_5940_ = l_Lean_Expr_const___override(v___x_5939_, v___x_5938_);
return v___x_5940_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__3(void){
_start:
{
lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; 
v___x_5941_ = l_Lean_Nat_mkInstMod;
v___x_5942_ = l_Lean_Nat_mkType;
v___x_5943_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_5944_ = l_Lean_mkAppB(v___x_5943_, v___x_5942_, v___x_5941_);
return v___x_5944_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod(void){
_start:
{
lean_object* v___x_5945_; 
v___x_5945_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__3, &l_Lean_Nat_mkInstHMod___closed__3_once, _init_l_Lean_Nat_mkInstHMod___closed__3);
return v___x_5945_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow___closed__2(void){
_start:
{
lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; 
v___x_5949_ = lean_box(0);
v___x_5950_ = ((lean_object*)(l_Lean_Nat_mkInstNatPow___closed__1));
v___x_5951_ = l_Lean_Expr_const___override(v___x_5950_, v___x_5949_);
return v___x_5951_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow(void){
_start:
{
lean_object* v___x_5952_; 
v___x_5952_ = lean_obj_once(&l_Lean_Nat_mkInstNatPow___closed__2, &l_Lean_Nat_mkInstNatPow___closed__2_once, _init_l_Lean_Nat_mkInstNatPow___closed__2);
return v___x_5952_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; 
v___x_5956_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5957_ = ((lean_object*)(l_Lean_Nat_mkInstPow___closed__1));
v___x_5958_ = l_Lean_Expr_const___override(v___x_5957_, v___x_5956_);
return v___x_5958_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__3(void){
_start:
{
lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; 
v___x_5959_ = l_Lean_Nat_mkInstNatPow;
v___x_5960_ = l_Lean_Nat_mkType;
v___x_5961_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_5962_ = l_Lean_mkAppB(v___x_5961_, v___x_5960_, v___x_5959_);
return v___x_5962_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow(void){
_start:
{
lean_object* v___x_5963_; 
v___x_5963_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__3, &l_Lean_Nat_mkInstPow___closed__3_once, _init_l_Lean_Nat_mkInstPow___closed__3);
return v___x_5963_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__3(void){
_start:
{
lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; 
v___x_5970_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__2));
v___x_5971_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__1));
v___x_5972_ = l_Lean_Expr_const___override(v___x_5971_, v___x_5970_);
return v___x_5972_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__4(void){
_start:
{
lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; 
v___x_5973_ = l_Lean_Nat_mkInstPow;
v___x_5974_ = l_Lean_Nat_mkType;
v___x_5975_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_5976_ = l_Lean_mkApp3(v___x_5975_, v___x_5974_, v___x_5974_, v___x_5973_);
return v___x_5976_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow(void){
_start:
{
lean_object* v___x_5977_; 
v___x_5977_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__4, &l_Lean_Nat_mkInstHPow___closed__4_once, _init_l_Lean_Nat_mkInstHPow___closed__4);
return v___x_5977_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; 
v___x_5981_ = lean_box(0);
v___x_5982_ = ((lean_object*)(l_Lean_Nat_mkInstLT___closed__1));
v___x_5983_ = l_Lean_Expr_const___override(v___x_5982_, v___x_5981_);
return v___x_5983_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT(void){
_start:
{
lean_object* v___x_5984_; 
v___x_5984_ = lean_obj_once(&l_Lean_Nat_mkInstLT___closed__2, &l_Lean_Nat_mkInstLT___closed__2_once, _init_l_Lean_Nat_mkInstLT___closed__2);
return v___x_5984_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; 
v___x_5988_ = lean_box(0);
v___x_5989_ = ((lean_object*)(l_Lean_Nat_mkInstLE___closed__1));
v___x_5990_ = l_Lean_Expr_const___override(v___x_5989_, v___x_5988_);
return v___x_5990_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE(void){
_start:
{
lean_object* v___x_5991_; 
v___x_5991_ = lean_obj_once(&l_Lean_Nat_mkInstLE___closed__2, &l_Lean_Nat_mkInstLE___closed__2_once, _init_l_Lean_Nat_mkInstLE___closed__2);
return v___x_5991_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3(void){
_start:
{
lean_object* v___x_5997_; lean_object* v___x_5998_; 
v___x_5997_ = lean_unsigned_to_nat(0u);
v___x_5998_ = l_Lean_Level_ofNat(v___x_5997_);
return v___x_5998_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4(void){
_start:
{
lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; 
v___x_5999_ = lean_box(0);
v___x_6000_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6001_, 0, v___x_6000_);
lean_ctor_set(v___x_6001_, 1, v___x_5999_);
return v___x_6001_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5(void){
_start:
{
lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; 
v___x_6002_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6003_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6004_, 0, v___x_6003_);
lean_ctor_set(v___x_6004_, 1, v___x_6002_);
return v___x_6004_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6(void){
_start:
{
lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; 
v___x_6005_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__5, &l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5);
v___x_6006_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6007_, 0, v___x_6006_);
lean_ctor_set(v___x_6007_, 1, v___x_6005_);
return v___x_6007_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7(void){
_start:
{
lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; 
v___x_6008_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6009_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natAddFn___closed__2));
v___x_6010_ = l_Lean_Expr_const___override(v___x_6009_, v___x_6008_);
return v___x_6010_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8(void){
_start:
{
lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; 
v___x_6011_ = l_Lean_Nat_mkInstHAdd;
v___x_6012_ = l_Lean_Nat_mkType;
v___x_6013_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6014_ = l_Lean_mkApp4(v___x_6013_, v___x_6012_, v___x_6012_, v___x_6012_, v___x_6011_);
return v___x_6014_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn(void){
_start:
{
lean_object* v___x_6015_; 
v___x_6015_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__8, &l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8);
return v___x_6015_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3(void){
_start:
{
lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; 
v___x_6021_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6022_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natSubFn___closed__2));
v___x_6023_ = l_Lean_Expr_const___override(v___x_6022_, v___x_6021_);
return v___x_6023_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4(void){
_start:
{
lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; 
v___x_6024_ = l_Lean_Nat_mkInstHSub;
v___x_6025_ = l_Lean_Nat_mkType;
v___x_6026_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6027_ = l_Lean_mkApp4(v___x_6026_, v___x_6025_, v___x_6025_, v___x_6025_, v___x_6024_);
return v___x_6027_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn(void){
_start:
{
lean_object* v___x_6028_; 
v___x_6028_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__4, &l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4);
return v___x_6028_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3(void){
_start:
{
lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; 
v___x_6034_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6035_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natMulFn___closed__2));
v___x_6036_ = l_Lean_Expr_const___override(v___x_6035_, v___x_6034_);
return v___x_6036_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4(void){
_start:
{
lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; 
v___x_6037_ = l_Lean_Nat_mkInstHMul;
v___x_6038_ = l_Lean_Nat_mkType;
v___x_6039_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6040_ = l_Lean_mkApp4(v___x_6039_, v___x_6038_, v___x_6038_, v___x_6038_, v___x_6037_);
return v___x_6040_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn(void){
_start:
{
lean_object* v___x_6041_; 
v___x_6041_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__4, &l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4);
return v___x_6041_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3(void){
_start:
{
lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; 
v___x_6047_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6048_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natPowFn___closed__2));
v___x_6049_ = l_Lean_Expr_const___override(v___x_6048_, v___x_6047_);
return v___x_6049_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4(void){
_start:
{
lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; 
v___x_6050_ = l_Lean_Nat_mkInstHPow;
v___x_6051_ = l_Lean_Nat_mkType;
v___x_6052_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6053_ = l_Lean_mkApp4(v___x_6052_, v___x_6051_, v___x_6051_, v___x_6051_, v___x_6050_);
return v___x_6053_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn(void){
_start:
{
lean_object* v___x_6054_; 
v___x_6054_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__4, &l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4);
return v___x_6054_;
}
}
static lean_object* _init_l_Lean_mkNatSucc___closed__2(void){
_start:
{
lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; 
v___x_6059_ = lean_box(0);
v___x_6060_ = ((lean_object*)(l_Lean_mkNatSucc___closed__1));
v___x_6061_ = l_Lean_Expr_const___override(v___x_6060_, v___x_6059_);
return v___x_6061_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* v_a_6062_){
_start:
{
lean_object* v___x_6063_; lean_object* v___x_6064_; 
v___x_6063_ = lean_obj_once(&l_Lean_mkNatSucc___closed__2, &l_Lean_mkNatSucc___closed__2_once, _init_l_Lean_mkNatSucc___closed__2);
v___x_6064_ = l_Lean_Expr_app___override(v___x_6063_, v_a_6062_);
return v___x_6064_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* v_a_6065_, lean_object* v_b_6066_){
_start:
{
lean_object* v___x_6067_; lean_object* v___x_6068_; 
v___x_6067_ = l___private_Lean_Expr_0__Lean_natAddFn;
v___x_6068_ = l_Lean_mkAppB(v___x_6067_, v_a_6065_, v_b_6066_);
return v___x_6068_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* v_a_6069_, lean_object* v_b_6070_){
_start:
{
lean_object* v___x_6071_; lean_object* v___x_6072_; 
v___x_6071_ = l___private_Lean_Expr_0__Lean_natSubFn;
v___x_6072_ = l_Lean_mkAppB(v___x_6071_, v_a_6069_, v_b_6070_);
return v___x_6072_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* v_a_6073_, lean_object* v_b_6074_){
_start:
{
lean_object* v___x_6075_; lean_object* v___x_6076_; 
v___x_6075_ = l___private_Lean_Expr_0__Lean_natMulFn;
v___x_6076_ = l_Lean_mkAppB(v___x_6075_, v_a_6073_, v_b_6074_);
return v___x_6076_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object* v_a_6077_, lean_object* v_b_6078_){
_start:
{
lean_object* v___x_6079_; lean_object* v___x_6080_; 
v___x_6079_ = l___private_Lean_Expr_0__Lean_natPowFn;
v___x_6080_ = l_Lean_mkAppB(v___x_6079_, v_a_6077_, v_b_6078_);
return v___x_6080_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3(void){
_start:
{
lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; 
v___x_6086_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6087_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natLEPred___closed__2));
v___x_6088_ = l_Lean_Expr_const___override(v___x_6087_, v___x_6086_);
return v___x_6088_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4(void){
_start:
{
lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; 
v___x_6089_ = l_Lean_Nat_mkInstLE;
v___x_6090_ = l_Lean_Nat_mkType;
v___x_6091_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6092_ = l_Lean_mkAppB(v___x_6091_, v___x_6090_, v___x_6089_);
return v___x_6092_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred(void){
_start:
{
lean_object* v___x_6093_; 
v___x_6093_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__4, &l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4);
return v___x_6093_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* v_a_6094_, lean_object* v_b_6095_){
_start:
{
lean_object* v___x_6096_; lean_object* v___x_6097_; 
v___x_6096_ = l___private_Lean_Expr_0__Lean_natLEPred;
v___x_6097_ = l_Lean_mkAppB(v___x_6096_, v_a_6094_, v_b_6095_);
return v___x_6097_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0(void){
_start:
{
lean_object* v___x_6098_; lean_object* v___x_6099_; 
v___x_6098_ = lean_unsigned_to_nat(1u);
v___x_6099_ = l_Lean_Level_ofNat(v___x_6098_);
return v___x_6099_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1(void){
_start:
{
lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; 
v___x_6100_ = lean_box(0);
v___x_6101_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__0, &l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0);
v___x_6102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
lean_ctor_set(v___x_6102_, 1, v___x_6100_);
return v___x_6102_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2(void){
_start:
{
lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; 
v___x_6103_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__1, &l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1);
v___x_6104_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_6105_ = l_Lean_Expr_const___override(v___x_6104_, v___x_6103_);
return v___x_6105_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3(void){
_start:
{
lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; 
v___x_6106_ = l_Lean_Nat_mkType;
v___x_6107_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6108_ = l_Lean_Expr_app___override(v___x_6107_, v___x_6106_);
return v___x_6108_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred(void){
_start:
{
lean_object* v___x_6109_; 
v___x_6109_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__3, &l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3);
return v___x_6109_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* v_a_6110_, lean_object* v_b_6111_){
_start:
{
lean_object* v___x_6112_; lean_object* v___x_6113_; 
v___x_6112_ = l___private_Lean_Expr_0__Lean_natEqPred;
v___x_6113_ = l_Lean_mkAppB(v___x_6112_, v_a_6110_, v_b_6111_);
return v___x_6113_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__0(void){
_start:
{
lean_object* v___x_6114_; lean_object* v___x_6115_; 
v___x_6114_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6115_ = l_Lean_Expr_sort___override(v___x_6114_);
return v___x_6115_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__1(void){
_start:
{
lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; 
v___x_6116_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__0, &l___private_Lean_Expr_0__Lean_propEq___closed__0_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__0);
v___x_6117_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6118_ = l_Lean_Expr_app___override(v___x_6117_, v___x_6116_);
return v___x_6118_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq(void){
_start:
{
lean_object* v___x_6119_; 
v___x_6119_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__1, &l___private_Lean_Expr_0__Lean_propEq___closed__1_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__1);
return v___x_6119_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* v_a_6120_, lean_object* v_b_6121_){
_start:
{
lean_object* v___x_6122_; lean_object* v___x_6123_; 
v___x_6122_ = l___private_Lean_Expr_0__Lean_propEq;
v___x_6123_ = l_Lean_mkAppB(v___x_6122_, v_a_6120_, v_b_6121_);
return v___x_6123_;
}
}
static lean_object* _init_l_Lean_Int_mkType___closed__2(void){
_start:
{
lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; 
v___x_6127_ = lean_box(0);
v___x_6128_ = ((lean_object*)(l_Lean_Int_mkType___closed__1));
v___x_6129_ = l_Lean_Expr_const___override(v___x_6128_, v___x_6127_);
return v___x_6129_;
}
}
static lean_object* _init_l_Lean_Int_mkType(void){
_start:
{
lean_object* v___x_6130_; 
v___x_6130_ = lean_obj_once(&l_Lean_Int_mkType___closed__2, &l_Lean_Int_mkType___closed__2_once, _init_l_Lean_Int_mkType___closed__2);
return v___x_6130_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg___closed__2(void){
_start:
{
lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; 
v___x_6135_ = lean_box(0);
v___x_6136_ = ((lean_object*)(l_Lean_Int_mkInstNeg___closed__1));
v___x_6137_ = l_Lean_Expr_const___override(v___x_6136_, v___x_6135_);
return v___x_6137_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg(void){
_start:
{
lean_object* v___x_6138_; 
v___x_6138_ = lean_obj_once(&l_Lean_Int_mkInstNeg___closed__2, &l_Lean_Int_mkInstNeg___closed__2_once, _init_l_Lean_Int_mkInstNeg___closed__2);
return v___x_6138_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; 
v___x_6143_ = lean_box(0);
v___x_6144_ = ((lean_object*)(l_Lean_Int_mkInstAdd___closed__1));
v___x_6145_ = l_Lean_Expr_const___override(v___x_6144_, v___x_6143_);
return v___x_6145_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd(void){
_start:
{
lean_object* v___x_6146_; 
v___x_6146_ = lean_obj_once(&l_Lean_Int_mkInstAdd___closed__2, &l_Lean_Int_mkInstAdd___closed__2_once, _init_l_Lean_Int_mkInstAdd___closed__2);
return v___x_6146_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd___closed__0(void){
_start:
{
lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; 
v___x_6147_ = l_Lean_Int_mkInstAdd;
v___x_6148_ = l_Lean_Int_mkType;
v___x_6149_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6150_ = l_Lean_mkAppB(v___x_6149_, v___x_6148_, v___x_6147_);
return v___x_6150_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd(void){
_start:
{
lean_object* v___x_6151_; 
v___x_6151_ = lean_obj_once(&l_Lean_Int_mkInstHAdd___closed__0, &l_Lean_Int_mkInstHAdd___closed__0_once, _init_l_Lean_Int_mkInstHAdd___closed__0);
return v___x_6151_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; 
v___x_6156_ = lean_box(0);
v___x_6157_ = ((lean_object*)(l_Lean_Int_mkInstSub___closed__1));
v___x_6158_ = l_Lean_Expr_const___override(v___x_6157_, v___x_6156_);
return v___x_6158_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub(void){
_start:
{
lean_object* v___x_6159_; 
v___x_6159_ = lean_obj_once(&l_Lean_Int_mkInstSub___closed__2, &l_Lean_Int_mkInstSub___closed__2_once, _init_l_Lean_Int_mkInstSub___closed__2);
return v___x_6159_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub___closed__0(void){
_start:
{
lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; 
v___x_6160_ = l_Lean_Int_mkInstSub;
v___x_6161_ = l_Lean_Int_mkType;
v___x_6162_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6163_ = l_Lean_mkAppB(v___x_6162_, v___x_6161_, v___x_6160_);
return v___x_6163_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub(void){
_start:
{
lean_object* v___x_6164_; 
v___x_6164_ = lean_obj_once(&l_Lean_Int_mkInstHSub___closed__0, &l_Lean_Int_mkInstHSub___closed__0_once, _init_l_Lean_Int_mkInstHSub___closed__0);
return v___x_6164_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; 
v___x_6169_ = lean_box(0);
v___x_6170_ = ((lean_object*)(l_Lean_Int_mkInstMul___closed__1));
v___x_6171_ = l_Lean_Expr_const___override(v___x_6170_, v___x_6169_);
return v___x_6171_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul(void){
_start:
{
lean_object* v___x_6172_; 
v___x_6172_ = lean_obj_once(&l_Lean_Int_mkInstMul___closed__2, &l_Lean_Int_mkInstMul___closed__2_once, _init_l_Lean_Int_mkInstMul___closed__2);
return v___x_6172_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul___closed__0(void){
_start:
{
lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; 
v___x_6173_ = l_Lean_Int_mkInstMul;
v___x_6174_ = l_Lean_Int_mkType;
v___x_6175_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6176_ = l_Lean_mkAppB(v___x_6175_, v___x_6174_, v___x_6173_);
return v___x_6176_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul(void){
_start:
{
lean_object* v___x_6177_; 
v___x_6177_ = lean_obj_once(&l_Lean_Int_mkInstHMul___closed__0, &l_Lean_Int_mkInstHMul___closed__0_once, _init_l_Lean_Int_mkInstHMul___closed__0);
return v___x_6177_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv___closed__1(void){
_start:
{
lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; 
v___x_6181_ = lean_box(0);
v___x_6182_ = ((lean_object*)(l_Lean_Int_mkInstDiv___closed__0));
v___x_6183_ = l_Lean_Expr_const___override(v___x_6182_, v___x_6181_);
return v___x_6183_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv(void){
_start:
{
lean_object* v___x_6184_; 
v___x_6184_ = lean_obj_once(&l_Lean_Int_mkInstDiv___closed__1, &l_Lean_Int_mkInstDiv___closed__1_once, _init_l_Lean_Int_mkInstDiv___closed__1);
return v___x_6184_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv___closed__0(void){
_start:
{
lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; 
v___x_6185_ = l_Lean_Int_mkInstDiv;
v___x_6186_ = l_Lean_Int_mkType;
v___x_6187_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6188_ = l_Lean_mkAppB(v___x_6187_, v___x_6186_, v___x_6185_);
return v___x_6188_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv(void){
_start:
{
lean_object* v___x_6189_; 
v___x_6189_ = lean_obj_once(&l_Lean_Int_mkInstHDiv___closed__0, &l_Lean_Int_mkInstHDiv___closed__0_once, _init_l_Lean_Int_mkInstHDiv___closed__0);
return v___x_6189_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod___closed__1(void){
_start:
{
lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; 
v___x_6193_ = lean_box(0);
v___x_6194_ = ((lean_object*)(l_Lean_Int_mkInstMod___closed__0));
v___x_6195_ = l_Lean_Expr_const___override(v___x_6194_, v___x_6193_);
return v___x_6195_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod(void){
_start:
{
lean_object* v___x_6196_; 
v___x_6196_ = lean_obj_once(&l_Lean_Int_mkInstMod___closed__1, &l_Lean_Int_mkInstMod___closed__1_once, _init_l_Lean_Int_mkInstMod___closed__1);
return v___x_6196_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod___closed__0(void){
_start:
{
lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; 
v___x_6197_ = l_Lean_Int_mkInstMod;
v___x_6198_ = l_Lean_Int_mkType;
v___x_6199_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6200_ = l_Lean_mkAppB(v___x_6199_, v___x_6198_, v___x_6197_);
return v___x_6200_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod(void){
_start:
{
lean_object* v___x_6201_; 
v___x_6201_ = lean_obj_once(&l_Lean_Int_mkInstHMod___closed__0, &l_Lean_Int_mkInstHMod___closed__0_once, _init_l_Lean_Int_mkInstHMod___closed__0);
return v___x_6201_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; 
v___x_6206_ = lean_box(0);
v___x_6207_ = ((lean_object*)(l_Lean_Int_mkInstPow___closed__1));
v___x_6208_ = l_Lean_Expr_const___override(v___x_6207_, v___x_6206_);
return v___x_6208_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow(void){
_start:
{
lean_object* v___x_6209_; 
v___x_6209_ = lean_obj_once(&l_Lean_Int_mkInstPow___closed__2, &l_Lean_Int_mkInstPow___closed__2_once, _init_l_Lean_Int_mkInstPow___closed__2);
return v___x_6209_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat___closed__0(void){
_start:
{
lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; 
v___x_6210_ = l_Lean_Int_mkInstPow;
v___x_6211_ = l_Lean_Int_mkType;
v___x_6212_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6213_ = l_Lean_mkAppB(v___x_6212_, v___x_6211_, v___x_6210_);
return v___x_6213_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat(void){
_start:
{
lean_object* v___x_6214_; 
v___x_6214_ = lean_obj_once(&l_Lean_Int_mkInstPowNat___closed__0, &l_Lean_Int_mkInstPowNat___closed__0_once, _init_l_Lean_Int_mkInstPowNat___closed__0);
return v___x_6214_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow___closed__0(void){
_start:
{
lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; 
v___x_6215_ = l_Lean_Int_mkInstPowNat;
v___x_6216_ = l_Lean_Nat_mkType;
v___x_6217_ = l_Lean_Int_mkType;
v___x_6218_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6219_ = l_Lean_mkApp3(v___x_6218_, v___x_6217_, v___x_6216_, v___x_6215_);
return v___x_6219_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow(void){
_start:
{
lean_object* v___x_6220_; 
v___x_6220_ = lean_obj_once(&l_Lean_Int_mkInstHPow___closed__0, &l_Lean_Int_mkInstHPow___closed__0_once, _init_l_Lean_Int_mkInstHPow___closed__0);
return v___x_6220_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; 
v___x_6225_ = lean_box(0);
v___x_6226_ = ((lean_object*)(l_Lean_Int_mkInstLT___closed__1));
v___x_6227_ = l_Lean_Expr_const___override(v___x_6226_, v___x_6225_);
return v___x_6227_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT(void){
_start:
{
lean_object* v___x_6228_; 
v___x_6228_ = lean_obj_once(&l_Lean_Int_mkInstLT___closed__2, &l_Lean_Int_mkInstLT___closed__2_once, _init_l_Lean_Int_mkInstLT___closed__2);
return v___x_6228_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6233_; lean_object* v___x_6234_; lean_object* v___x_6235_; 
v___x_6233_ = lean_box(0);
v___x_6234_ = ((lean_object*)(l_Lean_Int_mkInstLE___closed__1));
v___x_6235_ = l_Lean_Expr_const___override(v___x_6234_, v___x_6233_);
return v___x_6235_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE(void){
_start:
{
lean_object* v___x_6236_; 
v___x_6236_ = lean_obj_once(&l_Lean_Int_mkInstLE___closed__2, &l_Lean_Int_mkInstLE___closed__2_once, _init_l_Lean_Int_mkInstLE___closed__2);
return v___x_6236_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast___closed__2(void){
_start:
{
lean_object* v___x_6240_; lean_object* v___x_6241_; lean_object* v___x_6242_; 
v___x_6240_ = lean_box(0);
v___x_6241_ = ((lean_object*)(l_Lean_Int_mkInstNatCast___closed__1));
v___x_6242_ = l_Lean_Expr_const___override(v___x_6241_, v___x_6240_);
return v___x_6242_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast(void){
_start:
{
lean_object* v___x_6243_; 
v___x_6243_ = lean_obj_once(&l_Lean_Int_mkInstNatCast___closed__2, &l_Lean_Int_mkInstNatCast___closed__2_once, _init_l_Lean_Int_mkInstNatCast___closed__2);
return v___x_6243_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0(void){
_start:
{
lean_object* v___x_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; 
v___x_6244_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6245_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_6246_ = l_Lean_Expr_const___override(v___x_6245_, v___x_6244_);
return v___x_6246_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1(void){
_start:
{
lean_object* v___x_6247_; lean_object* v___x_6248_; lean_object* v___x_6249_; lean_object* v___x_6250_; 
v___x_6247_ = l_Lean_Int_mkInstNeg;
v___x_6248_ = l_Lean_Int_mkType;
v___x_6249_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__0, &l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0);
v___x_6250_ = l_Lean_mkAppB(v___x_6249_, v___x_6248_, v___x_6247_);
return v___x_6250_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn(void){
_start:
{
lean_object* v___x_6251_; 
v___x_6251_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__1, &l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1);
return v___x_6251_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0(void){
_start:
{
lean_object* v___x_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; 
v___x_6252_ = l_Lean_Int_mkInstHAdd;
v___x_6253_ = l_Lean_Int_mkType;
v___x_6254_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6255_ = l_Lean_mkApp4(v___x_6254_, v___x_6253_, v___x_6253_, v___x_6253_, v___x_6252_);
return v___x_6255_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn(void){
_start:
{
lean_object* v___x_6256_; 
v___x_6256_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intAddFn___closed__0, &l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0);
return v___x_6256_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0(void){
_start:
{
lean_object* v___x_6257_; lean_object* v___x_6258_; lean_object* v___x_6259_; lean_object* v___x_6260_; 
v___x_6257_ = l_Lean_Int_mkInstHSub;
v___x_6258_ = l_Lean_Int_mkType;
v___x_6259_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6260_ = l_Lean_mkApp4(v___x_6259_, v___x_6258_, v___x_6258_, v___x_6258_, v___x_6257_);
return v___x_6260_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn(void){
_start:
{
lean_object* v___x_6261_; 
v___x_6261_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intSubFn___closed__0, &l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0);
return v___x_6261_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0(void){
_start:
{
lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; 
v___x_6262_ = l_Lean_Int_mkInstHMul;
v___x_6263_ = l_Lean_Int_mkType;
v___x_6264_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6265_ = l_Lean_mkApp4(v___x_6264_, v___x_6263_, v___x_6263_, v___x_6263_, v___x_6262_);
return v___x_6265_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn(void){
_start:
{
lean_object* v___x_6266_; 
v___x_6266_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intMulFn___closed__0, &l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0);
return v___x_6266_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3(void){
_start:
{
lean_object* v___x_6272_; lean_object* v___x_6273_; lean_object* v___x_6274_; 
v___x_6272_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6273_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intDivFn___closed__2));
v___x_6274_ = l_Lean_Expr_const___override(v___x_6273_, v___x_6272_);
return v___x_6274_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4(void){
_start:
{
lean_object* v___x_6275_; lean_object* v___x_6276_; lean_object* v___x_6277_; lean_object* v___x_6278_; 
v___x_6275_ = l_Lean_Int_mkInstHDiv;
v___x_6276_ = l_Lean_Int_mkType;
v___x_6277_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__3, &l___private_Lean_Expr_0__Lean_intDivFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3);
v___x_6278_ = l_Lean_mkApp4(v___x_6277_, v___x_6276_, v___x_6276_, v___x_6276_, v___x_6275_);
return v___x_6278_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn(void){
_start:
{
lean_object* v___x_6279_; 
v___x_6279_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__4, &l___private_Lean_Expr_0__Lean_intDivFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4);
return v___x_6279_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3(void){
_start:
{
lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; 
v___x_6285_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6286_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intModFn___closed__2));
v___x_6287_ = l_Lean_Expr_const___override(v___x_6286_, v___x_6285_);
return v___x_6287_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4(void){
_start:
{
lean_object* v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; 
v___x_6288_ = l_Lean_Int_mkInstHMod;
v___x_6289_ = l_Lean_Int_mkType;
v___x_6290_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__3, &l___private_Lean_Expr_0__Lean_intModFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3);
v___x_6291_ = l_Lean_mkApp4(v___x_6290_, v___x_6289_, v___x_6289_, v___x_6289_, v___x_6288_);
return v___x_6291_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn(void){
_start:
{
lean_object* v___x_6292_; 
v___x_6292_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__4, &l___private_Lean_Expr_0__Lean_intModFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4);
return v___x_6292_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0(void){
_start:
{
lean_object* v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; 
v___x_6293_ = l_Lean_Int_mkInstHPow;
v___x_6294_ = l_Lean_Nat_mkType;
v___x_6295_ = l_Lean_Int_mkType;
v___x_6296_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6297_ = l_Lean_mkApp4(v___x_6296_, v___x_6295_, v___x_6294_, v___x_6295_, v___x_6293_);
return v___x_6297_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn(void){
_start:
{
lean_object* v___x_6298_; 
v___x_6298_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0, &l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0);
return v___x_6298_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3(void){
_start:
{
lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; 
v___x_6304_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6305_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2));
v___x_6306_ = l_Lean_Expr_const___override(v___x_6305_, v___x_6304_);
return v___x_6306_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4(void){
_start:
{
lean_object* v___x_6307_; lean_object* v___x_6308_; lean_object* v___x_6309_; lean_object* v___x_6310_; 
v___x_6307_ = l_Lean_Int_mkInstNatCast;
v___x_6308_ = l_Lean_Int_mkType;
v___x_6309_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3);
v___x_6310_ = l_Lean_mkAppB(v___x_6309_, v___x_6308_, v___x_6307_);
return v___x_6310_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn(void){
_start:
{
lean_object* v___x_6311_; 
v___x_6311_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4);
return v___x_6311_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* v_a_6312_){
_start:
{
lean_object* v___x_6313_; lean_object* v___x_6314_; 
v___x_6313_ = l___private_Lean_Expr_0__Lean_intNegFn;
v___x_6314_ = l_Lean_Expr_app___override(v___x_6313_, v_a_6312_);
return v___x_6314_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* v_a_6315_, lean_object* v_b_6316_){
_start:
{
lean_object* v___x_6317_; lean_object* v___x_6318_; 
v___x_6317_ = l___private_Lean_Expr_0__Lean_intAddFn;
v___x_6318_ = l_Lean_mkAppB(v___x_6317_, v_a_6315_, v_b_6316_);
return v___x_6318_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* v_a_6319_, lean_object* v_b_6320_){
_start:
{
lean_object* v___x_6321_; lean_object* v___x_6322_; 
v___x_6321_ = l___private_Lean_Expr_0__Lean_intSubFn;
v___x_6322_ = l_Lean_mkAppB(v___x_6321_, v_a_6319_, v_b_6320_);
return v___x_6322_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* v_a_6323_, lean_object* v_b_6324_){
_start:
{
lean_object* v___x_6325_; lean_object* v___x_6326_; 
v___x_6325_ = l___private_Lean_Expr_0__Lean_intMulFn;
v___x_6326_ = l_Lean_mkAppB(v___x_6325_, v_a_6323_, v_b_6324_);
return v___x_6326_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* v_a_6327_, lean_object* v_b_6328_){
_start:
{
lean_object* v___x_6329_; lean_object* v___x_6330_; 
v___x_6329_ = l___private_Lean_Expr_0__Lean_intDivFn;
v___x_6330_ = l_Lean_mkAppB(v___x_6329_, v_a_6327_, v_b_6328_);
return v___x_6330_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* v_a_6331_, lean_object* v_b_6332_){
_start:
{
lean_object* v___x_6333_; lean_object* v___x_6334_; 
v___x_6333_ = l___private_Lean_Expr_0__Lean_intModFn;
v___x_6334_ = l_Lean_mkAppB(v___x_6333_, v_a_6331_, v_b_6332_);
return v___x_6334_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* v_a_6335_){
_start:
{
lean_object* v___x_6336_; lean_object* v___x_6337_; 
v___x_6336_ = l___private_Lean_Expr_0__Lean_intNatCastFn;
v___x_6337_ = l_Lean_Expr_app___override(v___x_6336_, v_a_6335_);
return v___x_6337_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object* v_a_6338_, lean_object* v_b_6339_){
_start:
{
lean_object* v___x_6340_; lean_object* v___x_6341_; 
v___x_6340_ = l___private_Lean_Expr_0__Lean_intPowNatFn;
v___x_6341_ = l_Lean_mkAppB(v___x_6340_, v_a_6338_, v_b_6339_);
return v___x_6341_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0(void){
_start:
{
lean_object* v___x_6342_; lean_object* v___x_6343_; lean_object* v___x_6344_; lean_object* v___x_6345_; 
v___x_6342_ = l_Lean_Int_mkInstLE;
v___x_6343_ = l_Lean_Int_mkType;
v___x_6344_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6345_ = l_Lean_mkAppB(v___x_6344_, v___x_6343_, v___x_6342_);
return v___x_6345_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred(void){
_start:
{
lean_object* v___x_6346_; 
v___x_6346_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLEPred___closed__0, &l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0);
return v___x_6346_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* v_a_6347_, lean_object* v_b_6348_){
_start:
{
lean_object* v___x_6349_; lean_object* v___x_6350_; 
v___x_6349_ = l___private_Lean_Expr_0__Lean_intLEPred;
v___x_6350_ = l_Lean_mkAppB(v___x_6349_, v_a_6347_, v_b_6348_);
return v___x_6350_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3(void){
_start:
{
lean_object* v___x_6356_; lean_object* v___x_6357_; lean_object* v___x_6358_; 
v___x_6356_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6357_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intLTPred___closed__2));
v___x_6358_ = l_Lean_Expr_const___override(v___x_6357_, v___x_6356_);
return v___x_6358_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4(void){
_start:
{
lean_object* v___x_6359_; lean_object* v___x_6360_; lean_object* v___x_6361_; lean_object* v___x_6362_; 
v___x_6359_ = l_Lean_Int_mkInstLT;
v___x_6360_ = l_Lean_Int_mkType;
v___x_6361_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__3, &l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3);
v___x_6362_ = l_Lean_mkAppB(v___x_6361_, v___x_6360_, v___x_6359_);
return v___x_6362_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred(void){
_start:
{
lean_object* v___x_6363_; 
v___x_6363_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__4, &l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4);
return v___x_6363_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object* v_a_6364_, lean_object* v_b_6365_){
_start:
{
lean_object* v___x_6366_; lean_object* v___x_6367_; 
v___x_6366_ = l___private_Lean_Expr_0__Lean_intLTPred;
v___x_6367_ = l_Lean_mkAppB(v___x_6366_, v_a_6364_, v_b_6365_);
return v___x_6367_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0(void){
_start:
{
lean_object* v___x_6368_; lean_object* v___x_6369_; lean_object* v___x_6370_; 
v___x_6368_ = l_Lean_Int_mkType;
v___x_6369_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6370_ = l_Lean_Expr_app___override(v___x_6369_, v___x_6368_);
return v___x_6370_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred(void){
_start:
{
lean_object* v___x_6371_; 
v___x_6371_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intEqPred___closed__0, &l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0);
return v___x_6371_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* v_a_6372_, lean_object* v_b_6373_){
_start:
{
lean_object* v___x_6374_; lean_object* v___x_6375_; 
v___x_6374_ = l___private_Lean_Expr_0__Lean_intEqPred;
v___x_6375_ = l_Lean_mkAppB(v___x_6374_, v_a_6372_, v_b_6373_);
return v___x_6375_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__3(void){
_start:
{
lean_object* v___x_6381_; lean_object* v___x_6382_; lean_object* v___x_6383_; 
v___x_6381_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6382_ = ((lean_object*)(l_Lean_mkIntDvd___closed__2));
v___x_6383_ = l_Lean_Expr_const___override(v___x_6382_, v___x_6381_);
return v___x_6383_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__6(void){
_start:
{
lean_object* v___x_6388_; lean_object* v___x_6389_; lean_object* v___x_6390_; 
v___x_6388_ = lean_box(0);
v___x_6389_ = ((lean_object*)(l_Lean_mkIntDvd___closed__5));
v___x_6390_ = l_Lean_Expr_const___override(v___x_6389_, v___x_6388_);
return v___x_6390_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* v_a_6391_, lean_object* v_b_6392_){
_start:
{
lean_object* v___x_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; 
v___x_6393_ = lean_obj_once(&l_Lean_mkIntDvd___closed__3, &l_Lean_mkIntDvd___closed__3_once, _init_l_Lean_mkIntDvd___closed__3);
v___x_6394_ = l_Lean_Int_mkType;
v___x_6395_ = lean_obj_once(&l_Lean_mkIntDvd___closed__6, &l_Lean_mkIntDvd___closed__6_once, _init_l_Lean_mkIntDvd___closed__6);
v___x_6396_ = l_Lean_mkApp4(v___x_6393_, v___x_6394_, v___x_6395_, v_a_6391_, v_b_6392_);
return v___x_6396_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__2(void){
_start:
{
lean_object* v___x_6400_; lean_object* v___x_6401_; lean_object* v___x_6402_; 
v___x_6400_ = lean_box(0);
v___x_6401_ = ((lean_object*)(l_Lean_mkIntLit___closed__1));
v___x_6402_ = l_Lean_Expr_const___override(v___x_6401_, v___x_6400_);
return v___x_6402_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__3(void){
_start:
{
lean_object* v___x_6403_; lean_object* v___x_6404_; 
v___x_6403_ = lean_unsigned_to_nat(0u);
v___x_6404_ = lean_nat_to_int(v___x_6403_);
return v___x_6404_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* v_n_6405_){
_start:
{
lean_object* v___x_6406_; lean_object* v_r_6407_; lean_object* v___x_6408_; lean_object* v___x_6409_; lean_object* v___x_6410_; lean_object* v___x_6411_; lean_object* v_r_6412_; lean_object* v___x_6413_; uint8_t v___x_6414_; 
v___x_6406_ = lean_nat_abs(v_n_6405_);
v_r_6407_ = l_Lean_mkRawNatLit(v___x_6406_);
v___x_6408_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_6409_ = l_Lean_Int_mkType;
v___x_6410_ = lean_obj_once(&l_Lean_mkIntLit___closed__2, &l_Lean_mkIntLit___closed__2_once, _init_l_Lean_mkIntLit___closed__2);
lean_inc_ref(v_r_6407_);
v___x_6411_ = l_Lean_Expr_app___override(v___x_6410_, v_r_6407_);
v_r_6412_ = l_Lean_mkApp3(v___x_6408_, v___x_6409_, v_r_6407_, v___x_6411_);
v___x_6413_ = lean_obj_once(&l_Lean_mkIntLit___closed__3, &l_Lean_mkIntLit___closed__3_once, _init_l_Lean_mkIntLit___closed__3);
v___x_6414_ = lean_int_dec_lt(v_n_6405_, v___x_6413_);
if (v___x_6414_ == 0)
{
return v_r_6412_;
}
else
{
lean_object* v___x_6415_; 
v___x_6415_ = l_Lean_mkIntNeg(v_r_6412_);
return v___x_6415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* v_n_6416_){
_start:
{
lean_object* v_res_6417_; 
v_res_6417_ = l_Lean_mkIntLit(v_n_6416_);
lean_dec(v_n_6416_);
return v_res_6417_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6422_; lean_object* v___x_6423_; 
v___x_6422_ = lean_box(0);
v___x_6423_ = l_Lean_Level_succ___override(v___x_6422_);
return v___x_6423_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; 
v___x_6424_ = lean_box(0);
v___x_6425_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__2, &l_Lean_reflBoolTrue___closed__2_once, _init_l_Lean_reflBoolTrue___closed__2);
v___x_6426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6426_, 0, v___x_6425_);
lean_ctor_set(v___x_6426_, 1, v___x_6424_);
return v___x_6426_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6427_; lean_object* v___x_6428_; lean_object* v___x_6429_; 
v___x_6427_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__3, &l_Lean_reflBoolTrue___closed__3_once, _init_l_Lean_reflBoolTrue___closed__3);
v___x_6428_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__1));
v___x_6429_ = l_Lean_Expr_const___override(v___x_6428_, v___x_6427_);
return v___x_6429_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__6(void){
_start:
{
lean_object* v___x_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; 
v___x_6432_ = lean_box(0);
v___x_6433_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__5));
v___x_6434_ = l_Lean_Expr_const___override(v___x_6433_, v___x_6432_);
return v___x_6434_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__7(void){
_start:
{
lean_object* v___x_6435_; lean_object* v___x_6436_; lean_object* v___x_6437_; 
v___x_6435_ = lean_box(0);
v___x_6436_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_6437_ = l_Lean_Expr_const___override(v___x_6436_, v___x_6435_);
return v___x_6437_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__8(void){
_start:
{
lean_object* v___x_6438_; lean_object* v___x_6439_; lean_object* v___x_6440_; lean_object* v___x_6441_; 
v___x_6438_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6439_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6440_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6441_ = l_Lean_mkAppB(v___x_6440_, v___x_6439_, v___x_6438_);
return v___x_6441_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue(void){
_start:
{
lean_object* v___x_6442_; 
v___x_6442_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__8, &l_Lean_reflBoolTrue___closed__8_once, _init_l_Lean_reflBoolTrue___closed__8);
return v___x_6442_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6443_; lean_object* v___x_6444_; lean_object* v___x_6445_; 
v___x_6443_ = lean_box(0);
v___x_6444_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_6445_ = l_Lean_Expr_const___override(v___x_6444_, v___x_6443_);
return v___x_6445_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6446_; lean_object* v___x_6447_; lean_object* v___x_6448_; lean_object* v___x_6449_; 
v___x_6446_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6447_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6448_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6449_ = l_Lean_mkAppB(v___x_6448_, v___x_6447_, v___x_6446_);
return v___x_6449_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse(void){
_start:
{
lean_object* v___x_6450_; 
v___x_6450_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
return v___x_6450_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6454_; lean_object* v___x_6455_; lean_object* v___x_6456_; 
v___x_6454_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6455_ = ((lean_object*)(l_Lean_eagerReflBoolTrue___closed__1));
v___x_6456_ = l_Lean_Expr_const___override(v___x_6455_, v___x_6454_);
return v___x_6456_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; lean_object* v___x_6460_; 
v___x_6457_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6458_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6459_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6460_ = l_Lean_mkApp3(v___x_6459_, v___x_6458_, v___x_6457_, v___x_6457_);
return v___x_6460_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; lean_object* v___x_6464_; 
v___x_6461_ = l_Lean_reflBoolTrue;
v___x_6462_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__3, &l_Lean_eagerReflBoolTrue___closed__3_once, _init_l_Lean_eagerReflBoolTrue___closed__3);
v___x_6463_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6464_ = l_Lean_mkAppB(v___x_6463_, v___x_6462_, v___x_6461_);
return v___x_6464_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue(void){
_start:
{
lean_object* v___x_6465_; 
v___x_6465_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__4, &l_Lean_eagerReflBoolTrue___closed__4_once, _init_l_Lean_eagerReflBoolTrue___closed__4);
return v___x_6465_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6466_; lean_object* v___x_6467_; lean_object* v___x_6468_; lean_object* v___x_6469_; 
v___x_6466_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6467_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6468_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6469_ = l_Lean_mkApp3(v___x_6468_, v___x_6467_, v___x_6466_, v___x_6466_);
return v___x_6469_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; lean_object* v___x_6473_; 
v___x_6470_ = l_Lean_reflBoolFalse;
v___x_6471_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__0, &l_Lean_eagerReflBoolFalse___closed__0_once, _init_l_Lean_eagerReflBoolFalse___closed__0);
v___x_6472_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6473_ = l_Lean_mkAppB(v___x_6472_, v___x_6471_, v___x_6470_);
return v___x_6473_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse(void){
_start:
{
lean_object* v___x_6474_; 
v___x_6474_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__1, &l_Lean_eagerReflBoolFalse___closed__1_once, _init_l_Lean_eagerReflBoolFalse___closed__1);
return v___x_6474_;
}
}
static lean_object* _init_l_Lean_Expr_replaceFn___closed__2(void){
_start:
{
lean_object* v___x_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; 
v___x_6477_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__1));
v___x_6478_ = lean_unsigned_to_nat(9u);
v___x_6479_ = lean_unsigned_to_nat(2423u);
v___x_6480_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__0));
v___x_6481_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_6482_ = l_mkPanicMessageWithDecl(v___x_6481_, v___x_6480_, v___x_6479_, v___x_6478_, v___x_6477_);
return v___x_6482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object* v_e_6483_, lean_object* v_declName_6484_){
_start:
{
switch(lean_obj_tag(v_e_6483_))
{
case 5:
{
lean_object* v_fn_6485_; lean_object* v_arg_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; 
v_fn_6485_ = lean_ctor_get(v_e_6483_, 0);
lean_inc_ref(v_fn_6485_);
v_arg_6486_ = lean_ctor_get(v_e_6483_, 1);
lean_inc_ref(v_arg_6486_);
lean_dec_ref(v_e_6483_);
v___x_6487_ = l_Lean_Expr_replaceFn(v_fn_6485_, v_declName_6484_);
v___x_6488_ = l_Lean_Expr_app___override(v___x_6487_, v_arg_6486_);
return v___x_6488_;
}
case 4:
{
lean_object* v_us_6489_; lean_object* v___x_6490_; 
v_us_6489_ = lean_ctor_get(v_e_6483_, 1);
lean_inc(v_us_6489_);
lean_dec_ref(v_e_6483_);
v___x_6490_ = l_Lean_Expr_const___override(v_declName_6484_, v_us_6489_);
return v___x_6490_;
}
default: 
{
lean_object* v___x_6491_; lean_object* v___x_6492_; 
lean_dec(v_declName_6484_);
lean_dec_ref(v_e_6483_);
v___x_6491_ = lean_obj_once(&l_Lean_Expr_replaceFn___closed__2, &l_Lean_Expr_replaceFn___closed__2_once, _init_l_Lean_Expr_replaceFn___closed__2);
v___x_6492_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_6491_);
return v___x_6492_;
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
