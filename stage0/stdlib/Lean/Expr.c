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
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_string_hash(lean_object*);
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
lean_object* l_Std_TreeSet_instForInOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint64_t l_instInhabitedUInt64;
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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_TreeSet_instSingleton___redArg___lam__0(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_HashSet_instEmptyCollection(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_HashSet_instInhabited(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofList___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdSet;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdSet;
static const lean_closure_object l_Lean_instSingletonFVarIdFVarIdSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instSingletonFVarIdFVarIdSet___closed__0 = (const lean_object*)&l_Lean_instSingletonFVarIdFVarIdSet___closed__0_value;
static const lean_closure_object l_Lean_instSingletonFVarIdFVarIdSet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeSet_instSingleton___redArg___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instSingletonFVarIdFVarIdSet___closed__0_value)} };
static const lean_object* l_Lean_instSingletonFVarIdFVarIdSet___closed__1 = (const lean_object*)&l_Lean_instSingletonFVarIdFVarIdSet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instSingletonFVarIdFVarIdSet = (const lean_object*)&l_Lean_instSingletonFVarIdFVarIdSet___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_FVarIdSet_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_FVarIdSet_insert_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_FVarIdSet_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_FVarIdSet_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_union(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedFVarIdHashSet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedFVarIdHashSet___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdHashSet;
static lean_once_cell_t l_Lean_instEmptyCollectionFVarIdHashSet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instEmptyCollectionFVarIdHashSet___closed__0;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdSet;
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
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object*);
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
static const lean_string_object l_Lean_reflBoolTrue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_reflBoolTrue___closed__5 = (const lean_object*)&l_Lean_reflBoolTrue___closed__5_value;
static const lean_ctor_object l_Lean_reflBoolTrue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_reflBoolTrue___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_reflBoolTrue___closed__6 = (const lean_object*)&l_Lean_reflBoolTrue___closed__6_value;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__7;
static const lean_ctor_object l_Lean_reflBoolTrue___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_reflBoolTrue___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_reflBoolTrue___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_reflBoolTrue___closed__8_value_aux_0),((lean_object*)&l_Lean_instReprData__1___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_reflBoolTrue___closed__8 = (const lean_object*)&l_Lean_reflBoolTrue___closed__8_value;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__9;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__10;
LEAN_EXPORT lean_object* l_Lean_reflBoolTrue;
static const lean_ctor_object l_Lean_reflBoolFalse___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_reflBoolTrue___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_reflBoolFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_reflBoolFalse___closed__0_value_aux_0),((lean_object*)&l_Lean_instReprData__1___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_reflBoolFalse___closed__0 = (const lean_object*)&l_Lean_reflBoolFalse___closed__0_value;
static lean_once_cell_t l_Lean_reflBoolFalse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolFalse___closed__1;
static lean_once_cell_t l_Lean_reflBoolFalse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolFalse___closed__2;
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
static uint64_t _init_l_Lean_instInhabitedData__1(void){
_start:
{
uint64_t v___x_358_; 
v___x_358_ = l_instInhabitedUInt64;
return v___x_358_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_Data_hash(uint64_t v_c_359_){
_start:
{
uint32_t v___x_360_; uint64_t v___x_361_; 
v___x_360_ = lean_uint64_to_uint32(v_c_359_);
v___x_361_ = lean_uint32_to_uint64(v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object* v_c_362_){
_start:
{
uint64_t v_c_boxed_363_; uint64_t v_res_364_; lean_object* v_r_365_; 
v_c_boxed_363_ = lean_unbox_uint64(v_c_362_);
lean_dec_ref(v_c_362_);
v_res_364_ = l_Lean_Expr_Data_hash(v_c_boxed_363_);
v_r_365_ = lean_box_uint64(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t v_c_368_){
_start:
{
uint64_t v___x_369_; uint64_t v___x_370_; uint64_t v___x_371_; uint64_t v___x_372_; uint8_t v___x_373_; 
v___x_369_ = 32ULL;
v___x_370_ = lean_uint64_shift_right(v_c_368_, v___x_369_);
v___x_371_ = 255ULL;
v___x_372_ = lean_uint64_land(v___x_370_, v___x_371_);
v___x_373_ = lean_uint64_to_uint8(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object* v_c_374_){
_start:
{
uint64_t v_c_boxed_375_; uint8_t v_res_376_; lean_object* v_r_377_; 
v_c_boxed_375_ = lean_unbox_uint64(v_c_374_);
lean_dec_ref(v_c_374_);
v_res_376_ = l_Lean_Expr_Data_approxDepth(v_c_boxed_375_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t v_c_378_){
_start:
{
uint64_t v___x_379_; uint64_t v___x_380_; uint32_t v___x_381_; 
v___x_379_ = 44ULL;
v___x_380_ = lean_uint64_shift_right(v_c_378_, v___x_379_);
v___x_381_ = lean_uint64_to_uint32(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object* v_c_382_){
_start:
{
uint64_t v_c_boxed_383_; uint32_t v_res_384_; lean_object* v_r_385_; 
v_c_boxed_383_ = lean_unbox_uint64(v_c_382_);
lean_dec_ref(v_c_382_);
v_res_384_ = l_Lean_Expr_Data_looseBVarRange(v_c_boxed_383_);
v_r_385_ = lean_box_uint32(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t v_c_386_){
_start:
{
uint64_t v___x_387_; uint64_t v___x_388_; uint64_t v___x_389_; uint64_t v___x_390_; uint8_t v___x_391_; 
v___x_387_ = 40ULL;
v___x_388_ = lean_uint64_shift_right(v_c_386_, v___x_387_);
v___x_389_ = 1ULL;
v___x_390_ = lean_uint64_land(v___x_388_, v___x_389_);
v___x_391_ = lean_uint64_dec_eq(v___x_390_, v___x_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object* v_c_392_){
_start:
{
uint64_t v_c_boxed_393_; uint8_t v_res_394_; lean_object* v_r_395_; 
v_c_boxed_393_ = lean_unbox_uint64(v_c_392_);
lean_dec_ref(v_c_392_);
v_res_394_ = l_Lean_Expr_Data_hasFVar(v_c_boxed_393_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t v_c_396_){
_start:
{
uint64_t v___x_397_; uint64_t v___x_398_; uint64_t v___x_399_; uint64_t v___x_400_; uint8_t v___x_401_; 
v___x_397_ = 41ULL;
v___x_398_ = lean_uint64_shift_right(v_c_396_, v___x_397_);
v___x_399_ = 1ULL;
v___x_400_ = lean_uint64_land(v___x_398_, v___x_399_);
v___x_401_ = lean_uint64_dec_eq(v___x_400_, v___x_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object* v_c_402_){
_start:
{
uint64_t v_c_boxed_403_; uint8_t v_res_404_; lean_object* v_r_405_; 
v_c_boxed_403_ = lean_unbox_uint64(v_c_402_);
lean_dec_ref(v_c_402_);
v_res_404_ = l_Lean_Expr_Data_hasExprMVar(v_c_boxed_403_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t v_c_406_){
_start:
{
uint64_t v___x_407_; uint64_t v___x_408_; uint64_t v___x_409_; uint64_t v___x_410_; uint8_t v___x_411_; 
v___x_407_ = 42ULL;
v___x_408_ = lean_uint64_shift_right(v_c_406_, v___x_407_);
v___x_409_ = 1ULL;
v___x_410_ = lean_uint64_land(v___x_408_, v___x_409_);
v___x_411_ = lean_uint64_dec_eq(v___x_410_, v___x_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object* v_c_412_){
_start:
{
uint64_t v_c_boxed_413_; uint8_t v_res_414_; lean_object* v_r_415_; 
v_c_boxed_413_ = lean_unbox_uint64(v_c_412_);
lean_dec_ref(v_c_412_);
v_res_414_ = l_Lean_Expr_Data_hasLevelMVar(v_c_boxed_413_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t v_c_416_){
_start:
{
uint64_t v___x_417_; uint64_t v___x_418_; uint64_t v___x_419_; uint64_t v___x_420_; uint8_t v___x_421_; 
v___x_417_ = 43ULL;
v___x_418_ = lean_uint64_shift_right(v_c_416_, v___x_417_);
v___x_419_ = 1ULL;
v___x_420_ = lean_uint64_land(v___x_418_, v___x_419_);
v___x_421_ = lean_uint64_dec_eq(v___x_420_, v___x_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object* v_c_422_){
_start:
{
uint64_t v_c_boxed_423_; uint8_t v_res_424_; lean_object* v_r_425_; 
v_c_boxed_423_ = lean_unbox_uint64(v_c_422_);
lean_dec_ref(v_c_422_);
v_res_424_ = l_Lean_Expr_Data_hasLevelParam(v_c_boxed_423_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_427_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_428_; uint64_t v_res_429_; lean_object* v_r_430_; 
v_a_00___x40___internal___hyg_1__boxed_428_ = lean_unbox(v_a_00___x40___internal___hyg_427_);
v_res_429_ = lean_uint8_to_uint64(v_a_00___x40___internal___hyg_1__boxed_428_);
v_r_430_ = lean_box_uint64(v_res_429_);
return v_r_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object* v_h_438_, lean_object* v_looseBVarRange_439_, lean_object* v_approxDepth_440_, lean_object* v_hasFVar_441_, lean_object* v_hasExprMVar_442_, lean_object* v_hasLevelMVar_443_, lean_object* v_hasLevelParam_444_){
_start:
{
uint64_t v_h_boxed_445_; uint32_t v_approxDepth_boxed_446_; uint8_t v_hasFVar_boxed_447_; uint8_t v_hasExprMVar_boxed_448_; uint8_t v_hasLevelMVar_boxed_449_; uint8_t v_hasLevelParam_boxed_450_; uint64_t v_res_451_; lean_object* v_r_452_; 
v_h_boxed_445_ = lean_unbox_uint64(v_h_438_);
lean_dec_ref(v_h_438_);
v_approxDepth_boxed_446_ = lean_unbox_uint32(v_approxDepth_440_);
lean_dec(v_approxDepth_440_);
v_hasFVar_boxed_447_ = lean_unbox(v_hasFVar_441_);
v_hasExprMVar_boxed_448_ = lean_unbox(v_hasExprMVar_442_);
v_hasLevelMVar_boxed_449_ = lean_unbox(v_hasLevelMVar_443_);
v_hasLevelParam_boxed_450_ = lean_unbox(v_hasLevelParam_444_);
v_res_451_ = lean_expr_mk_data(v_h_boxed_445_, v_looseBVarRange_439_, v_approxDepth_boxed_446_, v_hasFVar_boxed_447_, v_hasExprMVar_boxed_448_, v_hasLevelMVar_boxed_449_, v_hasLevelParam_boxed_450_);
v_r_452_ = lean_box_uint64(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object* v_fData_455_, lean_object* v_aData_456_){
_start:
{
uint64_t v_fData_boxed_457_; uint64_t v_aData_boxed_458_; uint64_t v_res_459_; lean_object* v_r_460_; 
v_fData_boxed_457_ = lean_unbox_uint64(v_fData_455_);
lean_dec_ref(v_fData_455_);
v_aData_boxed_458_ = lean_unbox_uint64(v_aData_456_);
lean_dec_ref(v_aData_456_);
v_res_459_ = lean_expr_mk_app_data(v_fData_boxed_457_, v_aData_boxed_458_);
v_r_460_ = lean_box_uint64(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint64_t v_h_461_, lean_object* v_looseBVarRange_462_, uint32_t v_approxDepth_463_, uint8_t v_hasFVar_464_, uint8_t v_hasExprMVar_465_, uint8_t v_hasLevelMVar_466_, uint8_t v_hasLevelParam_467_){
_start:
{
uint64_t v___x_468_; 
v___x_468_ = lean_expr_mk_data(v_h_461_, v_looseBVarRange_462_, v_approxDepth_463_, v_hasFVar_464_, v_hasExprMVar_465_, v_hasLevelMVar_466_, v_hasLevelParam_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object* v_h_469_, lean_object* v_looseBVarRange_470_, lean_object* v_approxDepth_471_, lean_object* v_hasFVar_472_, lean_object* v_hasExprMVar_473_, lean_object* v_hasLevelMVar_474_, lean_object* v_hasLevelParam_475_){
_start:
{
uint64_t v_h_boxed_476_; uint32_t v_approxDepth_boxed_477_; uint8_t v_hasFVar_boxed_478_; uint8_t v_hasExprMVar_boxed_479_; uint8_t v_hasLevelMVar_boxed_480_; uint8_t v_hasLevelParam_boxed_481_; uint64_t v_res_482_; lean_object* v_r_483_; 
v_h_boxed_476_ = lean_unbox_uint64(v_h_469_);
lean_dec_ref(v_h_469_);
v_approxDepth_boxed_477_ = lean_unbox_uint32(v_approxDepth_471_);
lean_dec(v_approxDepth_471_);
v_hasFVar_boxed_478_ = lean_unbox(v_hasFVar_472_);
v_hasExprMVar_boxed_479_ = lean_unbox(v_hasExprMVar_473_);
v_hasLevelMVar_boxed_480_ = lean_unbox(v_hasLevelMVar_474_);
v_hasLevelParam_boxed_481_ = lean_unbox(v_hasLevelParam_475_);
v_res_482_ = l_Lean_Expr_mkDataForBinder(v_h_boxed_476_, v_looseBVarRange_470_, v_approxDepth_boxed_477_, v_hasFVar_boxed_478_, v_hasExprMVar_boxed_479_, v_hasLevelMVar_boxed_480_, v_hasLevelParam_boxed_481_);
v_r_483_ = lean_box_uint64(v_res_482_);
return v_r_483_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint64_t v_h_484_, lean_object* v_looseBVarRange_485_, uint32_t v_approxDepth_486_, uint8_t v_hasFVar_487_, uint8_t v_hasExprMVar_488_, uint8_t v_hasLevelMVar_489_, uint8_t v_hasLevelParam_490_){
_start:
{
uint64_t v___x_491_; 
v___x_491_ = lean_expr_mk_data(v_h_484_, v_looseBVarRange_485_, v_approxDepth_486_, v_hasFVar_487_, v_hasExprMVar_488_, v_hasLevelMVar_489_, v_hasLevelParam_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object* v_h_492_, lean_object* v_looseBVarRange_493_, lean_object* v_approxDepth_494_, lean_object* v_hasFVar_495_, lean_object* v_hasExprMVar_496_, lean_object* v_hasLevelMVar_497_, lean_object* v_hasLevelParam_498_){
_start:
{
uint64_t v_h_boxed_499_; uint32_t v_approxDepth_boxed_500_; uint8_t v_hasFVar_boxed_501_; uint8_t v_hasExprMVar_boxed_502_; uint8_t v_hasLevelMVar_boxed_503_; uint8_t v_hasLevelParam_boxed_504_; uint64_t v_res_505_; lean_object* v_r_506_; 
v_h_boxed_499_ = lean_unbox_uint64(v_h_492_);
lean_dec_ref(v_h_492_);
v_approxDepth_boxed_500_ = lean_unbox_uint32(v_approxDepth_494_);
lean_dec(v_approxDepth_494_);
v_hasFVar_boxed_501_ = lean_unbox(v_hasFVar_495_);
v_hasExprMVar_boxed_502_ = lean_unbox(v_hasExprMVar_496_);
v_hasLevelMVar_boxed_503_ = lean_unbox(v_hasLevelMVar_497_);
v_hasLevelParam_boxed_504_ = lean_unbox(v_hasLevelParam_498_);
v_res_505_ = l_Lean_Expr_mkDataForLet(v_h_boxed_499_, v_looseBVarRange_493_, v_approxDepth_boxed_500_, v_hasFVar_boxed_501_, v_hasExprMVar_boxed_502_, v_hasLevelMVar_boxed_503_, v_hasLevelParam_boxed_504_);
v_r_506_ = lean_box_uint64(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0(uint64_t v_v_516_, lean_object* v_prec_517_){
_start:
{
lean_object* v_r_519_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v_r_529_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v_r_542_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v_r_555_; lean_object* v_r_562_; lean_object* v___x_573_; uint64_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v_r_577_; uint32_t v___x_578_; uint32_t v___x_579_; uint8_t v___x_580_; 
v___x_573_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__7));
v___x_574_ = l_Lean_Expr_Data_hash(v_v_516_);
v___x_575_ = lean_uint64_to_nat(v___x_574_);
v___x_576_ = l_Nat_reprFast(v___x_575_);
v_r_577_ = lean_string_append(v___x_573_, v___x_576_);
lean_dec_ref(v___x_576_);
v___x_578_ = l_Lean_Expr_Data_looseBVarRange(v_v_516_);
v___x_579_ = 0;
v___x_580_ = lean_uint32_dec_eq(v___x_578_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v_r_587_; 
v___x_581_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__8));
v___x_582_ = lean_string_append(v_r_577_, v___x_581_);
v___x_583_ = lean_uint32_to_nat(v___x_578_);
v___x_584_ = l_Nat_reprFast(v___x_583_);
v___x_585_ = lean_string_append(v___x_582_, v___x_584_);
lean_dec_ref(v___x_584_);
v___x_586_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_587_ = lean_string_append(v___x_585_, v___x_586_);
v_r_562_ = v_r_587_;
goto v___jp_561_;
}
else
{
v_r_562_ = v_r_577_;
goto v___jp_561_;
}
v___jp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_520_, 0, v_r_519_);
v___x_521_ = l_Repr_addAppParen(v___x_520_, v_prec_517_);
return v___x_521_;
}
v___jp_522_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_r_527_; 
v___x_525_ = lean_string_append(v___y_523_, v___y_524_);
lean_dec_ref(v___y_524_);
v___x_526_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_527_ = lean_string_append(v___x_525_, v___x_526_);
v_r_519_ = v_r_527_;
goto v___jp_518_;
}
v___jp_528_:
{
uint8_t v___x_530_; 
v___x_530_ = l_Lean_Expr_Data_hasLevelMVar(v_v_516_);
if (v___x_530_ == 0)
{
v_r_519_ = v_r_529_;
goto v___jp_518_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
v___x_532_ = lean_string_append(v_r_529_, v___x_531_);
if (v___x_530_ == 0)
{
lean_object* v___x_533_; 
v___x_533_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_523_ = v___x_532_;
v___y_524_ = v___x_533_;
goto v___jp_522_;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_523_ = v___x_532_;
v___y_524_ = v___x_534_;
goto v___jp_522_;
}
}
}
v___jp_535_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_r_540_; 
v___x_538_ = lean_string_append(v___y_536_, v___y_537_);
lean_dec_ref(v___y_537_);
v___x_539_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_540_ = lean_string_append(v___x_538_, v___x_539_);
v_r_529_ = v_r_540_;
goto v___jp_528_;
}
v___jp_541_:
{
uint8_t v___x_543_; 
v___x_543_ = l_Lean_Expr_Data_hasExprMVar(v_v_516_);
if (v___x_543_ == 0)
{
v_r_529_ = v_r_542_;
goto v___jp_528_;
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__4));
v___x_545_ = lean_string_append(v_r_542_, v___x_544_);
if (v___x_543_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_536_ = v___x_545_;
v___y_537_ = v___x_546_;
goto v___jp_535_;
}
else
{
lean_object* v___x_547_; 
v___x_547_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_536_ = v___x_545_;
v___y_537_ = v___x_547_;
goto v___jp_535_;
}
}
}
v___jp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v_r_553_; 
v___x_551_ = lean_string_append(v___y_549_, v___y_550_);
lean_dec_ref(v___y_550_);
v___x_552_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_553_ = lean_string_append(v___x_551_, v___x_552_);
v_r_542_ = v_r_553_;
goto v___jp_541_;
}
v___jp_554_:
{
uint8_t v___x_556_; 
v___x_556_ = l_Lean_Expr_Data_hasFVar(v_v_516_);
if (v___x_556_ == 0)
{
v_r_542_ = v_r_555_;
goto v___jp_541_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__5));
v___x_558_ = lean_string_append(v_r_555_, v___x_557_);
if (v___x_556_ == 0)
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_549_ = v___x_558_;
v___y_550_ = v___x_559_;
goto v___jp_548_;
}
else
{
lean_object* v___x_560_; 
v___x_560_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_549_ = v___x_558_;
v___y_550_ = v___x_560_;
goto v___jp_548_;
}
}
}
v___jp_561_:
{
uint8_t v___x_563_; uint8_t v___x_564_; uint8_t v___x_565_; 
v___x_563_ = l_Lean_Expr_Data_approxDepth(v_v_516_);
v___x_564_ = 0;
v___x_565_ = lean_uint8_dec_eq(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v_r_572_; 
v___x_566_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__6));
v___x_567_ = lean_string_append(v_r_562_, v___x_566_);
v___x_568_ = lean_uint8_to_nat(v___x_563_);
v___x_569_ = l_Nat_reprFast(v___x_568_);
v___x_570_ = lean_string_append(v___x_567_, v___x_569_);
lean_dec_ref(v___x_569_);
v___x_571_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_572_ = lean_string_append(v___x_570_, v___x_571_);
v_r_555_ = v_r_572_;
goto v___jp_554_;
}
else
{
v_r_555_ = v_r_562_;
goto v___jp_554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0___boxed(lean_object* v_v_588_, lean_object* v_prec_589_){
_start:
{
uint64_t v_v_boxed_590_; lean_object* v_res_591_; 
v_v_boxed_590_ = lean_unbox_uint64(v_v_588_);
lean_dec_ref(v_v_588_);
v_res_591_ = l_Lean_instReprData__1___lam__0(v_v_boxed_590_, v_prec_589_);
lean_dec(v_prec_589_);
return v_res_591_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId_default(void){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = lean_box(0);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId(void){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_box(0);
return v___x_595_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqFVarId_beq(lean_object* v_x_596_, lean_object* v_x_597_){
_start:
{
uint8_t v___x_598_; 
v___x_598_ = lean_name_eq(v_x_596_, v_x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
uint8_t v_res_601_; lean_object* v_r_602_; 
v_res_601_ = l_Lean_instBEqFVarId_beq(v_x_599_, v_x_600_);
lean_dec(v_x_600_);
lean_dec(v_x_599_);
v_r_602_ = lean_box(v_res_601_);
return v_r_602_;
}
}
static uint64_t _init_l_Lean_instHashableFVarId_hash___closed__0(void){
_start:
{
lean_object* v___x_605_; uint64_t v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(1723u);
v___x_606_ = lean_uint64_of_nat(v___x_605_);
return v___x_606_;
}
}
static uint64_t _init_l_Lean_instHashableFVarId_hash___closed__1(void){
_start:
{
uint64_t v___x_607_; uint64_t v___x_608_; uint64_t v___x_609_; 
v___x_607_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
v___x_608_ = 0ULL;
v___x_609_ = lean_uint64_mix_hash(v___x_608_, v___x_607_);
return v___x_609_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableFVarId_hash(lean_object* v_x_610_){
_start:
{
uint64_t v___x_611_; 
v___x_611_ = 0ULL;
if (lean_obj_tag(v_x_610_) == 0)
{
uint64_t v___x_612_; 
v___x_612_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__1, &l_Lean_instHashableFVarId_hash___closed__1_once, _init_l_Lean_instHashableFVarId_hash___closed__1);
return v___x_612_;
}
else
{
uint64_t v_hash_613_; uint64_t v___x_614_; 
v_hash_613_ = lean_ctor_get_uint64(v_x_610_, sizeof(void*)*2);
v___x_614_ = lean_uint64_mix_hash(v___x_611_, v_hash_613_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object* v_x_615_){
_start:
{
uint64_t v_res_616_; lean_object* v_r_617_; 
v_res_616_ = l_Lean_instHashableFVarId_hash(v_x_615_);
lean_dec(v_x_615_);
v_r_617_ = lean_box_uint64(v_res_616_);
return v_r_617_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet(void){
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
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___redArg(lean_object* v_inst_628_){
_start:
{
lean_object* v___f_629_; 
v___f_629_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_629_, 0, v_inst_628_);
return v___f_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad(lean_object* v_m_630_, lean_object* v_inst_631_){
_start:
{
lean_object* v___f_632_; 
v___f_632_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_632_, 0, v_inst_631_);
return v___f_632_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_FVarIdSet_insert_spec__0___redArg(lean_object* v_k_633_, lean_object* v_t_634_){
_start:
{
if (lean_obj_tag(v_t_634_) == 0)
{
lean_object* v_k_635_; lean_object* v_l_636_; lean_object* v_r_637_; uint8_t v___x_638_; 
v_k_635_ = lean_ctor_get(v_t_634_, 1);
v_l_636_ = lean_ctor_get(v_t_634_, 3);
v_r_637_ = lean_ctor_get(v_t_634_, 4);
v___x_638_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_633_, v_k_635_);
switch(v___x_638_)
{
case 0:
{
v_t_634_ = v_l_636_;
goto _start;
}
case 1:
{
uint8_t v___x_640_; 
v___x_640_ = 1;
return v___x_640_;
}
default: 
{
v_t_634_ = v_r_637_;
goto _start;
}
}
}
else
{
uint8_t v___x_642_; 
v___x_642_ = 0;
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_FVarIdSet_insert_spec__0___redArg___boxed(lean_object* v_k_643_, lean_object* v_t_644_){
_start:
{
uint8_t v_res_645_; lean_object* v_r_646_; 
v_res_645_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_FVarIdSet_insert_spec__0___redArg(v_k_643_, v_t_644_);
lean_dec(v_t_644_);
lean_dec(v_k_643_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(lean_object* v_k_647_, lean_object* v_v_648_, lean_object* v_t_649_){
_start:
{
if (lean_obj_tag(v_t_649_) == 0)
{
lean_object* v_size_650_; lean_object* v_k_651_; lean_object* v_v_652_; lean_object* v_l_653_; lean_object* v_r_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_934_; 
v_size_650_ = lean_ctor_get(v_t_649_, 0);
v_k_651_ = lean_ctor_get(v_t_649_, 1);
v_v_652_ = lean_ctor_get(v_t_649_, 2);
v_l_653_ = lean_ctor_get(v_t_649_, 3);
v_r_654_ = lean_ctor_get(v_t_649_, 4);
v_isSharedCheck_934_ = !lean_is_exclusive(v_t_649_);
if (v_isSharedCheck_934_ == 0)
{
v___x_656_ = v_t_649_;
v_isShared_657_ = v_isSharedCheck_934_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_r_654_);
lean_inc(v_l_653_);
lean_inc(v_v_652_);
lean_inc(v_k_651_);
lean_inc(v_size_650_);
lean_dec(v_t_649_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_934_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
uint8_t v___x_658_; 
v___x_658_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_647_, v_k_651_);
switch(v___x_658_)
{
case 0:
{
lean_object* v_impl_659_; lean_object* v___x_660_; 
lean_dec(v_size_650_);
v_impl_659_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_k_647_, v_v_648_, v_l_653_);
v___x_660_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_654_) == 0)
{
lean_object* v_size_661_; lean_object* v_size_662_; lean_object* v_k_663_; lean_object* v_v_664_; lean_object* v_l_665_; lean_object* v_r_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_size_661_ = lean_ctor_get(v_r_654_, 0);
v_size_662_ = lean_ctor_get(v_impl_659_, 0);
lean_inc(v_size_662_);
v_k_663_ = lean_ctor_get(v_impl_659_, 1);
lean_inc(v_k_663_);
v_v_664_ = lean_ctor_get(v_impl_659_, 2);
lean_inc(v_v_664_);
v_l_665_ = lean_ctor_get(v_impl_659_, 3);
lean_inc(v_l_665_);
v_r_666_ = lean_ctor_get(v_impl_659_, 4);
lean_inc(v_r_666_);
v___x_667_ = lean_unsigned_to_nat(3u);
v___x_668_ = lean_nat_mul(v___x_667_, v_size_661_);
v___x_669_ = lean_nat_dec_lt(v___x_668_, v_size_662_);
lean_dec(v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_673_; 
lean_dec(v_r_666_);
lean_dec(v_l_665_);
lean_dec(v_v_664_);
lean_dec(v_k_663_);
v___x_670_ = lean_nat_add(v___x_660_, v_size_662_);
lean_dec(v_size_662_);
v___x_671_ = lean_nat_add(v___x_670_, v_size_661_);
lean_dec(v___x_670_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 3, v_impl_659_);
lean_ctor_set(v___x_656_, 0, v___x_671_);
v___x_673_ = v___x_656_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_k_651_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_v_652_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_impl_659_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v_r_654_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
else
{
lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_740_; 
v_isSharedCheck_740_ = !lean_is_exclusive(v_impl_659_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; lean_object* v_unused_742_; lean_object* v_unused_743_; lean_object* v_unused_744_; lean_object* v_unused_745_; 
v_unused_741_ = lean_ctor_get(v_impl_659_, 4);
lean_dec(v_unused_741_);
v_unused_742_ = lean_ctor_get(v_impl_659_, 3);
lean_dec(v_unused_742_);
v_unused_743_ = lean_ctor_get(v_impl_659_, 2);
lean_dec(v_unused_743_);
v_unused_744_ = lean_ctor_get(v_impl_659_, 1);
lean_dec(v_unused_744_);
v_unused_745_ = lean_ctor_get(v_impl_659_, 0);
lean_dec(v_unused_745_);
v___x_676_ = v_impl_659_;
v_isShared_677_ = v_isSharedCheck_740_;
goto v_resetjp_675_;
}
else
{
lean_dec(v_impl_659_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_740_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v_size_678_; lean_object* v_size_679_; lean_object* v_k_680_; lean_object* v_v_681_; lean_object* v_l_682_; lean_object* v_r_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_size_678_ = lean_ctor_get(v_l_665_, 0);
v_size_679_ = lean_ctor_get(v_r_666_, 0);
v_k_680_ = lean_ctor_get(v_r_666_, 1);
v_v_681_ = lean_ctor_get(v_r_666_, 2);
v_l_682_ = lean_ctor_get(v_r_666_, 3);
v_r_683_ = lean_ctor_get(v_r_666_, 4);
v___x_684_ = lean_unsigned_to_nat(2u);
v___x_685_ = lean_nat_mul(v___x_684_, v_size_678_);
v___x_686_ = lean_nat_dec_lt(v_size_679_, v___x_685_);
lean_dec(v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_715_; 
lean_inc(v_r_683_);
lean_inc(v_l_682_);
lean_inc(v_v_681_);
lean_inc(v_k_680_);
v_isSharedCheck_715_ = !lean_is_exclusive(v_r_666_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; lean_object* v_unused_717_; lean_object* v_unused_718_; lean_object* v_unused_719_; lean_object* v_unused_720_; 
v_unused_716_ = lean_ctor_get(v_r_666_, 4);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v_r_666_, 3);
lean_dec(v_unused_717_);
v_unused_718_ = lean_ctor_get(v_r_666_, 2);
lean_dec(v_unused_718_);
v_unused_719_ = lean_ctor_get(v_r_666_, 1);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_r_666_, 0);
lean_dec(v_unused_720_);
v___x_688_ = v_r_666_;
v_isShared_689_ = v_isSharedCheck_715_;
goto v_resetjp_687_;
}
else
{
lean_dec(v_r_666_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_715_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___x_703_; lean_object* v___y_705_; 
v___x_690_ = lean_nat_add(v___x_660_, v_size_662_);
lean_dec(v_size_662_);
v___x_691_ = lean_nat_add(v___x_690_, v_size_661_);
lean_dec(v___x_690_);
v___x_703_ = lean_nat_add(v___x_660_, v_size_678_);
if (lean_obj_tag(v_l_682_) == 0)
{
lean_object* v_size_713_; 
v_size_713_ = lean_ctor_get(v_l_682_, 0);
lean_inc(v_size_713_);
v___y_705_ = v_size_713_;
goto v___jp_704_;
}
else
{
lean_object* v___x_714_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___y_705_ = v___x_714_;
goto v___jp_704_;
}
v___jp_692_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = lean_nat_add(v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec(v___y_694_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 4, v_r_654_);
lean_ctor_set(v___x_688_, 3, v_r_683_);
lean_ctor_set(v___x_688_, 2, v_v_652_);
lean_ctor_set(v___x_688_, 1, v_k_651_);
lean_ctor_set(v___x_688_, 0, v___x_696_);
v___x_698_ = v___x_688_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_k_651_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_v_652_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_r_683_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_r_654_);
v___x_698_ = v_reuseFailAlloc_702_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_700_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 4, v___x_698_);
lean_ctor_set(v___x_676_, 3, v___y_693_);
lean_ctor_set(v___x_676_, 2, v_v_681_);
lean_ctor_set(v___x_676_, 1, v_k_680_);
lean_ctor_set(v___x_676_, 0, v___x_691_);
v___x_700_ = v___x_676_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_k_680_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_v_681_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v___y_693_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
v___jp_704_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_706_ = lean_nat_add(v___x_703_, v___y_705_);
lean_dec(v___y_705_);
lean_dec(v___x_703_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v_l_682_);
lean_ctor_set(v___x_656_, 3, v_l_665_);
lean_ctor_set(v___x_656_, 2, v_v_664_);
lean_ctor_set(v___x_656_, 1, v_k_663_);
lean_ctor_set(v___x_656_, 0, v___x_706_);
v___x_708_ = v___x_656_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_k_663_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v_v_664_);
lean_ctor_set(v_reuseFailAlloc_712_, 3, v_l_665_);
lean_ctor_set(v_reuseFailAlloc_712_, 4, v_l_682_);
v___x_708_ = v_reuseFailAlloc_712_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; 
v___x_709_ = lean_nat_add(v___x_660_, v_size_661_);
if (lean_obj_tag(v_r_683_) == 0)
{
lean_object* v_size_710_; 
v_size_710_ = lean_ctor_get(v_r_683_, 0);
lean_inc(v_size_710_);
v___y_693_ = v___x_708_;
v___y_694_ = v___x_709_;
v___y_695_ = v_size_710_;
goto v___jp_692_;
}
else
{
lean_object* v___x_711_; 
v___x_711_ = lean_unsigned_to_nat(0u);
v___y_693_ = v___x_708_;
v___y_694_ = v___x_709_;
v___y_695_ = v___x_711_;
goto v___jp_692_;
}
}
}
}
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
lean_del_object(v___x_656_);
v___x_721_ = lean_nat_add(v___x_660_, v_size_662_);
lean_dec(v_size_662_);
v___x_722_ = lean_nat_add(v___x_721_, v_size_661_);
lean_dec(v___x_721_);
v___x_723_ = lean_nat_add(v___x_660_, v_size_661_);
v___x_724_ = lean_nat_add(v___x_723_, v_size_679_);
lean_dec(v___x_723_);
lean_inc_ref(v_r_654_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 4, v_r_654_);
lean_ctor_set(v___x_676_, 3, v_r_666_);
lean_ctor_set(v___x_676_, 2, v_v_652_);
lean_ctor_set(v___x_676_, 1, v_k_651_);
lean_ctor_set(v___x_676_, 0, v___x_724_);
v___x_726_ = v___x_676_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_k_651_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v_v_652_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_r_666_);
lean_ctor_set(v_reuseFailAlloc_739_, 4, v_r_654_);
v___x_726_ = v_reuseFailAlloc_739_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
v_isSharedCheck_733_ = !lean_is_exclusive(v_r_654_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; lean_object* v_unused_737_; lean_object* v_unused_738_; 
v_unused_734_ = lean_ctor_get(v_r_654_, 4);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_r_654_, 3);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_r_654_, 2);
lean_dec(v_unused_736_);
v_unused_737_ = lean_ctor_get(v_r_654_, 1);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v_r_654_, 0);
lean_dec(v_unused_738_);
v___x_728_ = v_r_654_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_dec(v_r_654_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v___x_726_);
lean_ctor_set(v___x_728_, 3, v_l_665_);
lean_ctor_set(v___x_728_, 2, v_v_664_);
lean_ctor_set(v___x_728_, 1, v_k_663_);
lean_ctor_set(v___x_728_, 0, v___x_722_);
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_k_663_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_v_664_);
lean_ctor_set(v_reuseFailAlloc_732_, 3, v_l_665_);
lean_ctor_set(v_reuseFailAlloc_732_, 4, v___x_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_746_; 
v_l_746_ = lean_ctor_get(v_impl_659_, 3);
lean_inc(v_l_746_);
if (lean_obj_tag(v_l_746_) == 0)
{
lean_object* v_r_747_; lean_object* v_k_748_; lean_object* v_v_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_760_; 
v_r_747_ = lean_ctor_get(v_impl_659_, 4);
v_k_748_ = lean_ctor_get(v_impl_659_, 1);
v_v_749_ = lean_ctor_get(v_impl_659_, 2);
v_isSharedCheck_760_ = !lean_is_exclusive(v_impl_659_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; lean_object* v_unused_762_; 
v_unused_761_ = lean_ctor_get(v_impl_659_, 3);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_impl_659_, 0);
lean_dec(v_unused_762_);
v___x_751_ = v_impl_659_;
v_isShared_752_ = v_isSharedCheck_760_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_r_747_);
lean_inc(v_v_749_);
lean_inc(v_k_748_);
lean_dec(v_impl_659_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_760_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_753_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_747_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 3, v_r_747_);
lean_ctor_set(v___x_751_, 2, v_v_652_);
lean_ctor_set(v___x_751_, 1, v_k_651_);
lean_ctor_set(v___x_751_, 0, v___x_660_);
v___x_755_ = v___x_751_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_k_651_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_v_652_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_r_747_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_r_747_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_757_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v___x_755_);
lean_ctor_set(v___x_656_, 3, v_l_746_);
lean_ctor_set(v___x_656_, 2, v_v_749_);
lean_ctor_set(v___x_656_, 1, v_k_748_);
lean_ctor_set(v___x_656_, 0, v___x_753_);
v___x_757_ = v___x_656_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_k_748_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_v_749_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_l_746_);
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
else
{
lean_object* v_r_763_; 
v_r_763_ = lean_ctor_get(v_impl_659_, 4);
lean_inc(v_r_763_);
if (lean_obj_tag(v_r_763_) == 0)
{
lean_object* v_k_764_; lean_object* v_v_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_788_; 
v_k_764_ = lean_ctor_get(v_impl_659_, 1);
v_v_765_ = lean_ctor_get(v_impl_659_, 2);
v_isSharedCheck_788_ = !lean_is_exclusive(v_impl_659_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; lean_object* v_unused_790_; lean_object* v_unused_791_; 
v_unused_789_ = lean_ctor_get(v_impl_659_, 4);
lean_dec(v_unused_789_);
v_unused_790_ = lean_ctor_get(v_impl_659_, 3);
lean_dec(v_unused_790_);
v_unused_791_ = lean_ctor_get(v_impl_659_, 0);
lean_dec(v_unused_791_);
v___x_767_ = v_impl_659_;
v_isShared_768_ = v_isSharedCheck_788_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_v_765_);
lean_inc(v_k_764_);
lean_dec(v_impl_659_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_788_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_k_769_; lean_object* v_v_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_784_; 
v_k_769_ = lean_ctor_get(v_r_763_, 1);
v_v_770_ = lean_ctor_get(v_r_763_, 2);
v_isSharedCheck_784_ = !lean_is_exclusive(v_r_763_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; lean_object* v_unused_786_; lean_object* v_unused_787_; 
v_unused_785_ = lean_ctor_get(v_r_763_, 4);
lean_dec(v_unused_785_);
v_unused_786_ = lean_ctor_get(v_r_763_, 3);
lean_dec(v_unused_786_);
v_unused_787_ = lean_ctor_get(v_r_763_, 0);
lean_dec(v_unused_787_);
v___x_772_ = v_r_763_;
v_isShared_773_ = v_isSharedCheck_784_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_v_770_);
lean_inc(v_k_769_);
lean_dec(v_r_763_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_784_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = lean_unsigned_to_nat(3u);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v_l_746_);
lean_ctor_set(v___x_772_, 3, v_l_746_);
lean_ctor_set(v___x_772_, 2, v_v_765_);
lean_ctor_set(v___x_772_, 1, v_k_764_);
lean_ctor_set(v___x_772_, 0, v___x_660_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_k_764_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_v_765_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v_l_746_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v_l_746_);
v___x_776_ = v_reuseFailAlloc_783_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_778_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 4, v_l_746_);
lean_ctor_set(v___x_767_, 2, v_v_652_);
lean_ctor_set(v___x_767_, 1, v_k_651_);
lean_ctor_set(v___x_767_, 0, v___x_660_);
v___x_778_ = v___x_767_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_k_651_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_v_652_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_l_746_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v_l_746_);
v___x_778_ = v_reuseFailAlloc_782_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v___x_778_);
lean_ctor_set(v___x_656_, 3, v___x_776_);
lean_ctor_set(v___x_656_, 2, v_v_770_);
lean_ctor_set(v___x_656_, 1, v_k_769_);
lean_ctor_set(v___x_656_, 0, v___x_774_);
v___x_780_ = v___x_656_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_k_769_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_v_770_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
}
else
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = lean_unsigned_to_nat(2u);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v_r_763_);
lean_ctor_set(v___x_656_, 3, v_impl_659_);
lean_ctor_set(v___x_656_, 0, v___x_792_);
v___x_794_ = v___x_656_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_k_651_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_v_652_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v_impl_659_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_r_763_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
case 1:
{
lean_object* v___x_797_; 
lean_dec(v_v_652_);
lean_dec(v_k_651_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 2, v_v_648_);
lean_ctor_set(v___x_656_, 1, v_k_647_);
v___x_797_ = v___x_656_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_size_650_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v_l_653_);
lean_ctor_set(v_reuseFailAlloc_798_, 4, v_r_654_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
default: 
{
lean_object* v_impl_799_; lean_object* v___x_800_; 
lean_dec(v_size_650_);
v_impl_799_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_k_647_, v_v_648_, v_r_654_);
v___x_800_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_653_) == 0)
{
lean_object* v_size_801_; lean_object* v_size_802_; lean_object* v_k_803_; lean_object* v_v_804_; lean_object* v_l_805_; lean_object* v_r_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_size_801_ = lean_ctor_get(v_l_653_, 0);
v_size_802_ = lean_ctor_get(v_impl_799_, 0);
lean_inc(v_size_802_);
v_k_803_ = lean_ctor_get(v_impl_799_, 1);
lean_inc(v_k_803_);
v_v_804_ = lean_ctor_get(v_impl_799_, 2);
lean_inc(v_v_804_);
v_l_805_ = lean_ctor_get(v_impl_799_, 3);
lean_inc(v_l_805_);
v_r_806_ = lean_ctor_get(v_impl_799_, 4);
lean_inc(v_r_806_);
v___x_807_ = lean_unsigned_to_nat(3u);
v___x_808_ = lean_nat_mul(v___x_807_, v_size_801_);
v___x_809_ = lean_nat_dec_lt(v___x_808_, v_size_802_);
lean_dec(v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
lean_dec(v_r_806_);
lean_dec(v_l_805_);
lean_dec(v_v_804_);
lean_dec(v_k_803_);
v___x_810_ = lean_nat_add(v___x_800_, v_size_801_);
v___x_811_ = lean_nat_add(v___x_810_, v_size_802_);
lean_dec(v_size_802_);
lean_dec(v___x_810_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v_impl_799_);
lean_ctor_set(v___x_656_, 0, v___x_811_);
v___x_813_ = v___x_656_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_k_651_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_v_652_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_l_653_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v_impl_799_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
else
{
lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_878_; 
v_isSharedCheck_878_ = !lean_is_exclusive(v_impl_799_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; lean_object* v_unused_880_; lean_object* v_unused_881_; lean_object* v_unused_882_; lean_object* v_unused_883_; 
v_unused_879_ = lean_ctor_get(v_impl_799_, 4);
lean_dec(v_unused_879_);
v_unused_880_ = lean_ctor_get(v_impl_799_, 3);
lean_dec(v_unused_880_);
v_unused_881_ = lean_ctor_get(v_impl_799_, 2);
lean_dec(v_unused_881_);
v_unused_882_ = lean_ctor_get(v_impl_799_, 1);
lean_dec(v_unused_882_);
v_unused_883_ = lean_ctor_get(v_impl_799_, 0);
lean_dec(v_unused_883_);
v___x_816_ = v_impl_799_;
v_isShared_817_ = v_isSharedCheck_878_;
goto v_resetjp_815_;
}
else
{
lean_dec(v_impl_799_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_878_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_size_818_; lean_object* v_k_819_; lean_object* v_v_820_; lean_object* v_l_821_; lean_object* v_r_822_; lean_object* v_size_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_size_818_ = lean_ctor_get(v_l_805_, 0);
v_k_819_ = lean_ctor_get(v_l_805_, 1);
v_v_820_ = lean_ctor_get(v_l_805_, 2);
v_l_821_ = lean_ctor_get(v_l_805_, 3);
v_r_822_ = lean_ctor_get(v_l_805_, 4);
v_size_823_ = lean_ctor_get(v_r_806_, 0);
v___x_824_ = lean_unsigned_to_nat(2u);
v___x_825_ = lean_nat_mul(v___x_824_, v_size_823_);
v___x_826_ = lean_nat_dec_lt(v_size_818_, v___x_825_);
lean_dec(v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_854_; 
lean_inc(v_r_822_);
lean_inc(v_l_821_);
lean_inc(v_v_820_);
lean_inc(v_k_819_);
v_isSharedCheck_854_ = !lean_is_exclusive(v_l_805_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; lean_object* v_unused_856_; lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; 
v_unused_855_ = lean_ctor_get(v_l_805_, 4);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v_l_805_, 3);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_l_805_, 2);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_l_805_, 1);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_l_805_, 0);
lean_dec(v_unused_859_);
v___x_828_ = v_l_805_;
v_isShared_829_ = v_isSharedCheck_854_;
goto v_resetjp_827_;
}
else
{
lean_dec(v_l_805_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_854_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_844_; 
v___x_830_ = lean_nat_add(v___x_800_, v_size_801_);
v___x_831_ = lean_nat_add(v___x_830_, v_size_802_);
lean_dec(v_size_802_);
if (lean_obj_tag(v_l_821_) == 0)
{
lean_object* v_size_852_; 
v_size_852_ = lean_ctor_get(v_l_821_, 0);
lean_inc(v_size_852_);
v___y_844_ = v_size_852_;
goto v___jp_843_;
}
else
{
lean_object* v___x_853_; 
v___x_853_ = lean_unsigned_to_nat(0u);
v___y_844_ = v___x_853_;
goto v___jp_843_;
}
v___jp_832_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_nat_add(v___y_833_, v___y_835_);
lean_dec(v___y_835_);
lean_dec(v___y_833_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 4, v_r_806_);
lean_ctor_set(v___x_828_, 3, v_r_822_);
lean_ctor_set(v___x_828_, 2, v_v_804_);
lean_ctor_set(v___x_828_, 1, v_k_803_);
lean_ctor_set(v___x_828_, 0, v___x_836_);
v___x_838_ = v___x_828_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_k_803_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_v_804_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_r_822_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_r_806_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_840_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 4, v___x_838_);
lean_ctor_set(v___x_816_, 3, v___y_834_);
lean_ctor_set(v___x_816_, 2, v_v_820_);
lean_ctor_set(v___x_816_, 1, v_k_819_);
lean_ctor_set(v___x_816_, 0, v___x_831_);
v___x_840_ = v___x_816_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_841_, 3, v___y_834_);
lean_ctor_set(v_reuseFailAlloc_841_, 4, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
v___jp_843_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_nat_add(v___x_830_, v___y_844_);
lean_dec(v___y_844_);
lean_dec(v___x_830_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v_l_821_);
lean_ctor_set(v___x_656_, 0, v___x_845_);
v___x_847_ = v___x_656_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_k_651_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_v_652_);
lean_ctor_set(v_reuseFailAlloc_851_, 3, v_l_653_);
lean_ctor_set(v_reuseFailAlloc_851_, 4, v_l_821_);
v___x_847_ = v_reuseFailAlloc_851_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; 
v___x_848_ = lean_nat_add(v___x_800_, v_size_823_);
if (lean_obj_tag(v_r_822_) == 0)
{
lean_object* v_size_849_; 
v_size_849_ = lean_ctor_get(v_r_822_, 0);
lean_inc(v_size_849_);
v___y_833_ = v___x_848_;
v___y_834_ = v___x_847_;
v___y_835_ = v_size_849_;
goto v___jp_832_;
}
else
{
lean_object* v___x_850_; 
v___x_850_ = lean_unsigned_to_nat(0u);
v___y_833_ = v___x_848_;
v___y_834_ = v___x_847_;
v___y_835_ = v___x_850_;
goto v___jp_832_;
}
}
}
}
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
lean_del_object(v___x_656_);
v___x_860_ = lean_nat_add(v___x_800_, v_size_801_);
v___x_861_ = lean_nat_add(v___x_860_, v_size_802_);
lean_dec(v_size_802_);
v___x_862_ = lean_nat_add(v___x_860_, v_size_818_);
lean_dec(v___x_860_);
lean_inc_ref(v_l_653_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 4, v_l_805_);
lean_ctor_set(v___x_816_, 3, v_l_653_);
lean_ctor_set(v___x_816_, 2, v_v_652_);
lean_ctor_set(v___x_816_, 1, v_k_651_);
lean_ctor_set(v___x_816_, 0, v___x_862_);
v___x_864_ = v___x_816_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_k_651_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_v_652_);
lean_ctor_set(v_reuseFailAlloc_877_, 3, v_l_653_);
lean_ctor_set(v_reuseFailAlloc_877_, 4, v_l_805_);
v___x_864_ = v_reuseFailAlloc_877_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_isSharedCheck_871_ = !lean_is_exclusive(v_l_653_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; lean_object* v_unused_873_; lean_object* v_unused_874_; lean_object* v_unused_875_; lean_object* v_unused_876_; 
v_unused_872_ = lean_ctor_get(v_l_653_, 4);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_l_653_, 3);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_l_653_, 2);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_l_653_, 1);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_l_653_, 0);
lean_dec(v_unused_876_);
v___x_866_ = v_l_653_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_dec(v_l_653_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v_r_806_);
lean_ctor_set(v___x_866_, 3, v___x_864_);
lean_ctor_set(v___x_866_, 2, v_v_804_);
lean_ctor_set(v___x_866_, 1, v_k_803_);
lean_ctor_set(v___x_866_, 0, v___x_861_);
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_k_803_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_v_804_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v_r_806_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_884_; 
v_l_884_ = lean_ctor_get(v_impl_799_, 3);
lean_inc(v_l_884_);
if (lean_obj_tag(v_l_884_) == 0)
{
lean_object* v_r_885_; lean_object* v_k_886_; lean_object* v_v_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_910_; 
v_r_885_ = lean_ctor_get(v_impl_799_, 4);
v_k_886_ = lean_ctor_get(v_impl_799_, 1);
v_v_887_ = lean_ctor_get(v_impl_799_, 2);
v_isSharedCheck_910_ = !lean_is_exclusive(v_impl_799_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; lean_object* v_unused_912_; 
v_unused_911_ = lean_ctor_get(v_impl_799_, 3);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_impl_799_, 0);
lean_dec(v_unused_912_);
v___x_889_ = v_impl_799_;
v_isShared_890_ = v_isSharedCheck_910_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_r_885_);
lean_inc(v_v_887_);
lean_inc(v_k_886_);
lean_dec(v_impl_799_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_910_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_k_891_; lean_object* v_v_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_906_; 
v_k_891_ = lean_ctor_get(v_l_884_, 1);
v_v_892_ = lean_ctor_get(v_l_884_, 2);
v_isSharedCheck_906_ = !lean_is_exclusive(v_l_884_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; lean_object* v_unused_908_; lean_object* v_unused_909_; 
v_unused_907_ = lean_ctor_get(v_l_884_, 4);
lean_dec(v_unused_907_);
v_unused_908_ = lean_ctor_get(v_l_884_, 3);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_l_884_, 0);
lean_dec(v_unused_909_);
v___x_894_ = v_l_884_;
v_isShared_895_ = v_isSharedCheck_906_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_v_892_);
lean_inc(v_k_891_);
lean_dec(v_l_884_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_906_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_885_, 2);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 4, v_r_885_);
lean_ctor_set(v___x_894_, 3, v_r_885_);
lean_ctor_set(v___x_894_, 2, v_v_652_);
lean_ctor_set(v___x_894_, 1, v_k_651_);
lean_ctor_set(v___x_894_, 0, v___x_800_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_651_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_v_652_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_r_885_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v_r_885_);
v___x_898_ = v_reuseFailAlloc_905_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
lean_inc(v_r_885_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 3, v_r_885_);
lean_ctor_set(v___x_889_, 0, v___x_800_);
v___x_900_ = v___x_889_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v_r_885_);
lean_ctor_set(v_reuseFailAlloc_904_, 4, v_r_885_);
v___x_900_ = v_reuseFailAlloc_904_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_902_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v___x_900_);
lean_ctor_set(v___x_656_, 3, v___x_898_);
lean_ctor_set(v___x_656_, 2, v_v_892_);
lean_ctor_set(v___x_656_, 1, v_k_891_);
lean_ctor_set(v___x_656_, 0, v___x_896_);
v___x_902_ = v___x_656_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_k_891_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_v_892_);
lean_ctor_set(v_reuseFailAlloc_903_, 3, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_903_, 4, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
else
{
lean_object* v_r_913_; 
v_r_913_ = lean_ctor_get(v_impl_799_, 4);
lean_inc(v_r_913_);
if (lean_obj_tag(v_r_913_) == 0)
{
lean_object* v_k_914_; lean_object* v_v_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_926_; 
v_k_914_ = lean_ctor_get(v_impl_799_, 1);
v_v_915_ = lean_ctor_get(v_impl_799_, 2);
v_isSharedCheck_926_ = !lean_is_exclusive(v_impl_799_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; lean_object* v_unused_928_; lean_object* v_unused_929_; 
v_unused_927_ = lean_ctor_get(v_impl_799_, 4);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_impl_799_, 3);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_impl_799_, 0);
lean_dec(v_unused_929_);
v___x_917_ = v_impl_799_;
v_isShared_918_ = v_isSharedCheck_926_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_v_915_);
lean_inc(v_k_914_);
lean_dec(v_impl_799_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_926_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = lean_unsigned_to_nat(3u);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 4, v_l_884_);
lean_ctor_set(v___x_917_, 2, v_v_652_);
lean_ctor_set(v___x_917_, 1, v_k_651_);
lean_ctor_set(v___x_917_, 0, v___x_800_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_k_651_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_v_652_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v_l_884_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v_l_884_);
v___x_921_ = v_reuseFailAlloc_925_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_923_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v_r_913_);
lean_ctor_set(v___x_656_, 3, v___x_921_);
lean_ctor_set(v___x_656_, 2, v_v_915_);
lean_ctor_set(v___x_656_, 1, v_k_914_);
lean_ctor_set(v___x_656_, 0, v___x_919_);
v___x_923_ = v___x_656_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_k_914_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v_v_915_);
lean_ctor_set(v_reuseFailAlloc_924_, 3, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_924_, 4, v_r_913_);
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
else
{
lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_930_ = lean_unsigned_to_nat(2u);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v_impl_799_);
lean_ctor_set(v___x_656_, 3, v_r_913_);
lean_ctor_set(v___x_656_, 0, v___x_930_);
v___x_932_ = v___x_656_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_k_651_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_v_652_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v_r_913_);
lean_ctor_set(v_reuseFailAlloc_933_, 4, v_impl_799_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
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
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_unsigned_to_nat(1u);
v___x_936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v_k_647_);
lean_ctor_set(v___x_936_, 2, v_v_648_);
lean_ctor_set(v___x_936_, 3, v_t_649_);
lean_ctor_set(v___x_936_, 4, v_t_649_);
return v___x_936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object* v_s_937_, lean_object* v_fvarId_938_){
_start:
{
uint8_t v___x_939_; 
v___x_939_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_FVarIdSet_insert_spec__0___redArg(v_fvarId_938_, v_s_937_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_box(0);
v___x_941_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_938_, v___x_940_, v_s_937_);
return v___x_941_;
}
else
{
lean_dec(v_fvarId_938_);
return v_s_937_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_FVarIdSet_insert_spec__0(lean_object* v_00_u03b2_942_, lean_object* v_k_943_, lean_object* v_t_944_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_FVarIdSet_insert_spec__0___redArg(v_k_943_, v_t_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_FVarIdSet_insert_spec__0___boxed(lean_object* v_00_u03b2_946_, lean_object* v_k_947_, lean_object* v_t_948_){
_start:
{
uint8_t v_res_949_; lean_object* v_r_950_; 
v_res_949_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_FVarIdSet_insert_spec__0(v_00_u03b2_946_, v_k_947_, v_t_948_);
lean_dec(v_t_948_);
lean_dec(v_k_947_);
v_r_950_ = lean_box(v_res_949_);
return v_r_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1(lean_object* v_00_u03b2_951_, lean_object* v_k_952_, lean_object* v_v_953_, lean_object* v_t_954_, lean_object* v_hl_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_k_952_, v_v_953_, v_t_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(lean_object* v_init_957_, lean_object* v_x_958_){
_start:
{
if (lean_obj_tag(v_x_958_) == 0)
{
lean_object* v_k_959_; lean_object* v_l_960_; lean_object* v_r_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_k_959_ = lean_ctor_get(v_x_958_, 1);
lean_inc(v_k_959_);
v_l_960_ = lean_ctor_get(v_x_958_, 3);
lean_inc(v_l_960_);
v_r_961_ = lean_ctor_get(v_x_958_, 4);
lean_inc(v_r_961_);
lean_dec_ref(v_x_958_);
v___x_962_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_957_, v_l_960_);
v___x_963_ = l_Lean_FVarIdSet_insert(v___x_962_, v_k_959_);
v_init_957_ = v___x_963_;
v_x_958_ = v_r_961_;
goto _start;
}
else
{
return v_init_957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_union(lean_object* v_vs_u2081_965_, lean_object* v_vs_u2082_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_vs_u2082_966_, v_vs_u2081_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0(lean_object* v_init_968_, lean_object* v_t_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_968_, v_t_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList(lean_object* v_l_971_){
_start:
{
lean_object* v___f_972_; lean_object* v___x_973_; 
v___f_972_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___closed__0));
v___x_973_ = l_Std_TreeSet_ofList___redArg(v_l_971_, v___f_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object* v_l_974_){
_start:
{
lean_object* v___f_975_; lean_object* v___x_976_; 
v___f_975_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___closed__0));
v___x_976_ = l_Std_TreeSet_ofArray___redArg(v_l_974_, v___f_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object* v_l_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_FVarIdSet_ofArray(v_l_977_);
lean_dec_ref(v_l_977_);
return v_res_978_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___closed__0(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = ((lean_object*)(l_Lean_instHashableFVarId___closed__0));
v___x_980_ = ((lean_object*)(l_Lean_instBEqFVarId___closed__0));
v___x_981_ = l_Std_HashSet_instInhabited(lean_box(0), v___x_980_, v___x_979_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet(void){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___closed__0, &l_Lean_instInhabitedFVarIdHashSet___closed__0_once, _init_l_Lean_instInhabitedFVarIdHashSet___closed__0);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet___closed__0(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = ((lean_object*)(l_Lean_instHashableFVarId___closed__0));
v___x_984_ = ((lean_object*)(l_Lean_instBEqFVarId___closed__0));
v___x_985_ = l_Std_HashSet_instEmptyCollection(lean_box(0), v___x_984_, v___x_983_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet(void){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = lean_obj_once(&l_Lean_instEmptyCollectionFVarIdHashSet___closed__0, &l_Lean_instEmptyCollectionFVarIdHashSet___closed__0_once, _init_l_Lean_instEmptyCollectionFVarIdHashSet___closed__0);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object* v_s_987_, lean_object* v_fvarId_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_988_, v_a_989_, v_s_987_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object* v_00_u03b1_991_, lean_object* v_s_992_, lean_object* v_fvarId_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_993_, v_a_994_, v_s_992_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* v_00_u03b1_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = lean_box(1);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* v_00_u03b1_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = lean_box(1);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId_default(void){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_box(0);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId(void){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_box(0);
return v___x_1001_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMVarId_beq(lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_name_eq(v_x_1002_, v_x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object* v_x_1005_, lean_object* v_x_1006_){
_start:
{
uint8_t v_res_1007_; lean_object* v_r_1008_; 
v_res_1007_ = l_Lean_instBEqMVarId_beq(v_x_1005_, v_x_1006_);
lean_dec(v_x_1006_);
lean_dec(v_x_1005_);
v_r_1008_ = lean_box(v_res_1007_);
return v_r_1008_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableMVarId_hash(lean_object* v_x_1011_){
_start:
{
uint64_t v___x_1012_; 
v___x_1012_ = 0ULL;
if (lean_obj_tag(v_x_1011_) == 0)
{
uint64_t v___x_1013_; 
v___x_1013_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__1, &l_Lean_instHashableFVarId_hash___closed__1_once, _init_l_Lean_instHashableFVarId_hash___closed__1);
return v___x_1013_;
}
else
{
uint64_t v_hash_1014_; uint64_t v___x_1015_; 
v_hash_1014_ = lean_ctor_get_uint64(v_x_1011_, sizeof(void*)*2);
v___x_1015_ = lean_uint64_mix_hash(v___x_1012_, v_hash_1014_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object* v_x_1016_){
_start:
{
uint64_t v_res_1017_; lean_object* v_r_1018_; 
v_res_1017_ = l_Lean_instHashableMVarId_hash(v_x_1016_);
lean_dec(v_x_1016_);
v_r_1018_ = lean_box_uint64(v_res_1017_);
return v_r_1018_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet(void){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_box(1);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet(void){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_box(1);
return v___x_1023_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object* v_k_1024_, lean_object* v_t_1025_){
_start:
{
if (lean_obj_tag(v_t_1025_) == 0)
{
lean_object* v_k_1026_; lean_object* v_l_1027_; lean_object* v_r_1028_; uint8_t v___x_1029_; 
v_k_1026_ = lean_ctor_get(v_t_1025_, 1);
v_l_1027_ = lean_ctor_get(v_t_1025_, 3);
v_r_1028_ = lean_ctor_get(v_t_1025_, 4);
v___x_1029_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1024_, v_k_1026_);
switch(v___x_1029_)
{
case 0:
{
v_t_1025_ = v_l_1027_;
goto _start;
}
case 1:
{
uint8_t v___x_1031_; 
v___x_1031_ = 1;
return v___x_1031_;
}
default: 
{
v_t_1025_ = v_r_1028_;
goto _start;
}
}
}
else
{
uint8_t v___x_1033_; 
v___x_1033_ = 0;
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object* v_k_1034_, lean_object* v_t_1035_){
_start:
{
uint8_t v_res_1036_; lean_object* v_r_1037_; 
v_res_1036_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1034_, v_t_1035_);
lean_dec(v_t_1035_);
lean_dec(v_k_1034_);
v_r_1037_ = lean_box(v_res_1036_);
return v_r_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object* v_k_1038_, lean_object* v_v_1039_, lean_object* v_t_1040_){
_start:
{
if (lean_obj_tag(v_t_1040_) == 0)
{
lean_object* v_size_1041_; lean_object* v_k_1042_; lean_object* v_v_1043_; lean_object* v_l_1044_; lean_object* v_r_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1325_; 
v_size_1041_ = lean_ctor_get(v_t_1040_, 0);
v_k_1042_ = lean_ctor_get(v_t_1040_, 1);
v_v_1043_ = lean_ctor_get(v_t_1040_, 2);
v_l_1044_ = lean_ctor_get(v_t_1040_, 3);
v_r_1045_ = lean_ctor_get(v_t_1040_, 4);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_t_1040_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1047_ = v_t_1040_;
v_isShared_1048_ = v_isSharedCheck_1325_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_r_1045_);
lean_inc(v_l_1044_);
lean_inc(v_v_1043_);
lean_inc(v_k_1042_);
lean_inc(v_size_1041_);
lean_dec(v_t_1040_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1325_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
uint8_t v___x_1049_; 
v___x_1049_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1038_, v_k_1042_);
switch(v___x_1049_)
{
case 0:
{
lean_object* v_impl_1050_; lean_object* v___x_1051_; 
lean_dec(v_size_1041_);
v_impl_1050_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1038_, v_v_1039_, v_l_1044_);
v___x_1051_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1045_) == 0)
{
lean_object* v_size_1052_; lean_object* v_size_1053_; lean_object* v_k_1054_; lean_object* v_v_1055_; lean_object* v_l_1056_; lean_object* v_r_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v_size_1052_ = lean_ctor_get(v_r_1045_, 0);
v_size_1053_ = lean_ctor_get(v_impl_1050_, 0);
lean_inc(v_size_1053_);
v_k_1054_ = lean_ctor_get(v_impl_1050_, 1);
lean_inc(v_k_1054_);
v_v_1055_ = lean_ctor_get(v_impl_1050_, 2);
lean_inc(v_v_1055_);
v_l_1056_ = lean_ctor_get(v_impl_1050_, 3);
lean_inc(v_l_1056_);
v_r_1057_ = lean_ctor_get(v_impl_1050_, 4);
lean_inc(v_r_1057_);
v___x_1058_ = lean_unsigned_to_nat(3u);
v___x_1059_ = lean_nat_mul(v___x_1058_, v_size_1052_);
v___x_1060_ = lean_nat_dec_lt(v___x_1059_, v_size_1053_);
lean_dec(v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
lean_dec(v_r_1057_);
lean_dec(v_l_1056_);
lean_dec(v_v_1055_);
lean_dec(v_k_1054_);
v___x_1061_ = lean_nat_add(v___x_1051_, v_size_1053_);
lean_dec(v_size_1053_);
v___x_1062_ = lean_nat_add(v___x_1061_, v_size_1052_);
lean_dec(v___x_1061_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 3, v_impl_1050_);
lean_ctor_set(v___x_1047_, 0, v___x_1062_);
v___x_1064_ = v___x_1047_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v_impl_1050_);
lean_ctor_set(v_reuseFailAlloc_1065_, 4, v_r_1045_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
else
{
lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1131_; 
v_isSharedCheck_1131_ = !lean_is_exclusive(v_impl_1050_);
if (v_isSharedCheck_1131_ == 0)
{
lean_object* v_unused_1132_; lean_object* v_unused_1133_; lean_object* v_unused_1134_; lean_object* v_unused_1135_; lean_object* v_unused_1136_; 
v_unused_1132_ = lean_ctor_get(v_impl_1050_, 4);
lean_dec(v_unused_1132_);
v_unused_1133_ = lean_ctor_get(v_impl_1050_, 3);
lean_dec(v_unused_1133_);
v_unused_1134_ = lean_ctor_get(v_impl_1050_, 2);
lean_dec(v_unused_1134_);
v_unused_1135_ = lean_ctor_get(v_impl_1050_, 1);
lean_dec(v_unused_1135_);
v_unused_1136_ = lean_ctor_get(v_impl_1050_, 0);
lean_dec(v_unused_1136_);
v___x_1067_ = v_impl_1050_;
v_isShared_1068_ = v_isSharedCheck_1131_;
goto v_resetjp_1066_;
}
else
{
lean_dec(v_impl_1050_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1131_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_size_1069_; lean_object* v_size_1070_; lean_object* v_k_1071_; lean_object* v_v_1072_; lean_object* v_l_1073_; lean_object* v_r_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v_size_1069_ = lean_ctor_get(v_l_1056_, 0);
v_size_1070_ = lean_ctor_get(v_r_1057_, 0);
v_k_1071_ = lean_ctor_get(v_r_1057_, 1);
v_v_1072_ = lean_ctor_get(v_r_1057_, 2);
v_l_1073_ = lean_ctor_get(v_r_1057_, 3);
v_r_1074_ = lean_ctor_get(v_r_1057_, 4);
v___x_1075_ = lean_unsigned_to_nat(2u);
v___x_1076_ = lean_nat_mul(v___x_1075_, v_size_1069_);
v___x_1077_ = lean_nat_dec_lt(v_size_1070_, v___x_1076_);
lean_dec(v___x_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1106_; 
lean_inc(v_r_1074_);
lean_inc(v_l_1073_);
lean_inc(v_v_1072_);
lean_inc(v_k_1071_);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_r_1057_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; lean_object* v_unused_1108_; lean_object* v_unused_1109_; lean_object* v_unused_1110_; lean_object* v_unused_1111_; 
v_unused_1107_ = lean_ctor_get(v_r_1057_, 4);
lean_dec(v_unused_1107_);
v_unused_1108_ = lean_ctor_get(v_r_1057_, 3);
lean_dec(v_unused_1108_);
v_unused_1109_ = lean_ctor_get(v_r_1057_, 2);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v_r_1057_, 1);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_r_1057_, 0);
lean_dec(v_unused_1111_);
v___x_1079_ = v_r_1057_;
v_isShared_1080_ = v_isSharedCheck_1106_;
goto v_resetjp_1078_;
}
else
{
lean_dec(v_r_1057_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1106_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___x_1094_; lean_object* v___y_1096_; 
v___x_1081_ = lean_nat_add(v___x_1051_, v_size_1053_);
lean_dec(v_size_1053_);
v___x_1082_ = lean_nat_add(v___x_1081_, v_size_1052_);
lean_dec(v___x_1081_);
v___x_1094_ = lean_nat_add(v___x_1051_, v_size_1069_);
if (lean_obj_tag(v_l_1073_) == 0)
{
lean_object* v_size_1104_; 
v_size_1104_ = lean_ctor_get(v_l_1073_, 0);
lean_inc(v_size_1104_);
v___y_1096_ = v_size_1104_;
goto v___jp_1095_;
}
else
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_unsigned_to_nat(0u);
v___y_1096_ = v___x_1105_;
goto v___jp_1095_;
}
v___jp_1083_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = lean_nat_add(v___y_1084_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec(v___y_1084_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 4, v_r_1045_);
lean_ctor_set(v___x_1079_, 3, v_r_1074_);
lean_ctor_set(v___x_1079_, 2, v_v_1043_);
lean_ctor_set(v___x_1079_, 1, v_k_1042_);
lean_ctor_set(v___x_1079_, 0, v___x_1087_);
v___x_1089_ = v___x_1079_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1093_, 3, v_r_1074_);
lean_ctor_set(v_reuseFailAlloc_1093_, 4, v_r_1045_);
v___x_1089_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1091_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 4, v___x_1089_);
lean_ctor_set(v___x_1067_, 3, v___y_1085_);
lean_ctor_set(v___x_1067_, 2, v_v_1072_);
lean_ctor_set(v___x_1067_, 1, v_k_1071_);
lean_ctor_set(v___x_1067_, 0, v___x_1082_);
v___x_1091_ = v___x_1067_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_k_1071_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_v_1072_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v___y_1085_);
lean_ctor_set(v_reuseFailAlloc_1092_, 4, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
v___jp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = lean_nat_add(v___x_1094_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec(v___x_1094_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v_l_1073_);
lean_ctor_set(v___x_1047_, 3, v_l_1056_);
lean_ctor_set(v___x_1047_, 2, v_v_1055_);
lean_ctor_set(v___x_1047_, 1, v_k_1054_);
lean_ctor_set(v___x_1047_, 0, v___x_1097_);
v___x_1099_ = v___x_1047_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_k_1054_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v_v_1055_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v_l_1056_);
lean_ctor_set(v_reuseFailAlloc_1103_, 4, v_l_1073_);
v___x_1099_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_nat_add(v___x_1051_, v_size_1052_);
if (lean_obj_tag(v_r_1074_) == 0)
{
lean_object* v_size_1101_; 
v_size_1101_ = lean_ctor_get(v_r_1074_, 0);
lean_inc(v_size_1101_);
v___y_1084_ = v___x_1100_;
v___y_1085_ = v___x_1099_;
v___y_1086_ = v_size_1101_;
goto v___jp_1083_;
}
else
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_unsigned_to_nat(0u);
v___y_1084_ = v___x_1100_;
v___y_1085_ = v___x_1099_;
v___y_1086_ = v___x_1102_;
goto v___jp_1083_;
}
}
}
}
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
lean_del_object(v___x_1047_);
v___x_1112_ = lean_nat_add(v___x_1051_, v_size_1053_);
lean_dec(v_size_1053_);
v___x_1113_ = lean_nat_add(v___x_1112_, v_size_1052_);
lean_dec(v___x_1112_);
v___x_1114_ = lean_nat_add(v___x_1051_, v_size_1052_);
v___x_1115_ = lean_nat_add(v___x_1114_, v_size_1070_);
lean_dec(v___x_1114_);
lean_inc_ref(v_r_1045_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 4, v_r_1045_);
lean_ctor_set(v___x_1067_, 3, v_r_1057_);
lean_ctor_set(v___x_1067_, 2, v_v_1043_);
lean_ctor_set(v___x_1067_, 1, v_k_1042_);
lean_ctor_set(v___x_1067_, 0, v___x_1115_);
v___x_1117_ = v___x_1067_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1130_, 3, v_r_1057_);
lean_ctor_set(v_reuseFailAlloc_1130_, 4, v_r_1045_);
v___x_1117_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
v_isSharedCheck_1124_ = !lean_is_exclusive(v_r_1045_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; lean_object* v_unused_1126_; lean_object* v_unused_1127_; lean_object* v_unused_1128_; lean_object* v_unused_1129_; 
v_unused_1125_ = lean_ctor_get(v_r_1045_, 4);
lean_dec(v_unused_1125_);
v_unused_1126_ = lean_ctor_get(v_r_1045_, 3);
lean_dec(v_unused_1126_);
v_unused_1127_ = lean_ctor_get(v_r_1045_, 2);
lean_dec(v_unused_1127_);
v_unused_1128_ = lean_ctor_get(v_r_1045_, 1);
lean_dec(v_unused_1128_);
v_unused_1129_ = lean_ctor_get(v_r_1045_, 0);
lean_dec(v_unused_1129_);
v___x_1119_ = v_r_1045_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_dec(v_r_1045_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 4, v___x_1117_);
lean_ctor_set(v___x_1119_, 3, v_l_1056_);
lean_ctor_set(v___x_1119_, 2, v_v_1055_);
lean_ctor_set(v___x_1119_, 1, v_k_1054_);
lean_ctor_set(v___x_1119_, 0, v___x_1113_);
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_k_1054_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_v_1055_);
lean_ctor_set(v_reuseFailAlloc_1123_, 3, v_l_1056_);
lean_ctor_set(v_reuseFailAlloc_1123_, 4, v___x_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1137_; 
v_l_1137_ = lean_ctor_get(v_impl_1050_, 3);
lean_inc(v_l_1137_);
if (lean_obj_tag(v_l_1137_) == 0)
{
lean_object* v_r_1138_; lean_object* v_k_1139_; lean_object* v_v_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1151_; 
v_r_1138_ = lean_ctor_get(v_impl_1050_, 4);
v_k_1139_ = lean_ctor_get(v_impl_1050_, 1);
v_v_1140_ = lean_ctor_get(v_impl_1050_, 2);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_impl_1050_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; lean_object* v_unused_1153_; 
v_unused_1152_ = lean_ctor_get(v_impl_1050_, 3);
lean_dec(v_unused_1152_);
v_unused_1153_ = lean_ctor_get(v_impl_1050_, 0);
lean_dec(v_unused_1153_);
v___x_1142_ = v_impl_1050_;
v_isShared_1143_ = v_isSharedCheck_1151_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_r_1138_);
lean_inc(v_v_1140_);
lean_inc(v_k_1139_);
lean_dec(v_impl_1050_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1151_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1144_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1138_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 3, v_r_1138_);
lean_ctor_set(v___x_1142_, 2, v_v_1043_);
lean_ctor_set(v___x_1142_, 1, v_k_1042_);
lean_ctor_set(v___x_1142_, 0, v___x_1051_);
v___x_1146_ = v___x_1142_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1150_, 3, v_r_1138_);
lean_ctor_set(v_reuseFailAlloc_1150_, 4, v_r_1138_);
v___x_1146_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v___x_1146_);
lean_ctor_set(v___x_1047_, 3, v_l_1137_);
lean_ctor_set(v___x_1047_, 2, v_v_1140_);
lean_ctor_set(v___x_1047_, 1, v_k_1139_);
lean_ctor_set(v___x_1047_, 0, v___x_1144_);
v___x_1148_ = v___x_1047_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_k_1139_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_v_1140_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_l_1137_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
else
{
lean_object* v_r_1154_; 
v_r_1154_ = lean_ctor_get(v_impl_1050_, 4);
lean_inc(v_r_1154_);
if (lean_obj_tag(v_r_1154_) == 0)
{
lean_object* v_k_1155_; lean_object* v_v_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1179_; 
v_k_1155_ = lean_ctor_get(v_impl_1050_, 1);
v_v_1156_ = lean_ctor_get(v_impl_1050_, 2);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_impl_1050_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; lean_object* v_unused_1181_; lean_object* v_unused_1182_; 
v_unused_1180_ = lean_ctor_get(v_impl_1050_, 4);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_impl_1050_, 3);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_impl_1050_, 0);
lean_dec(v_unused_1182_);
v___x_1158_ = v_impl_1050_;
v_isShared_1159_ = v_isSharedCheck_1179_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_v_1156_);
lean_inc(v_k_1155_);
lean_dec(v_impl_1050_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1179_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_k_1160_; lean_object* v_v_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1175_; 
v_k_1160_ = lean_ctor_get(v_r_1154_, 1);
v_v_1161_ = lean_ctor_get(v_r_1154_, 2);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_r_1154_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; lean_object* v_unused_1177_; lean_object* v_unused_1178_; 
v_unused_1176_ = lean_ctor_get(v_r_1154_, 4);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_r_1154_, 3);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_r_1154_, 0);
lean_dec(v_unused_1178_);
v___x_1163_ = v_r_1154_;
v_isShared_1164_ = v_isSharedCheck_1175_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_v_1161_);
lean_inc(v_k_1160_);
lean_dec(v_r_1154_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1175_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1165_ = lean_unsigned_to_nat(3u);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 4, v_l_1137_);
lean_ctor_set(v___x_1163_, 3, v_l_1137_);
lean_ctor_set(v___x_1163_, 2, v_v_1156_);
lean_ctor_set(v___x_1163_, 1, v_k_1155_);
lean_ctor_set(v___x_1163_, 0, v___x_1051_);
v___x_1167_ = v___x_1163_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_k_1155_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v_v_1156_);
lean_ctor_set(v_reuseFailAlloc_1174_, 3, v_l_1137_);
lean_ctor_set(v_reuseFailAlloc_1174_, 4, v_l_1137_);
v___x_1167_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1169_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v_l_1137_);
lean_ctor_set(v___x_1158_, 2, v_v_1043_);
lean_ctor_set(v___x_1158_, 1, v_k_1042_);
lean_ctor_set(v___x_1158_, 0, v___x_1051_);
v___x_1169_ = v___x_1158_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v_l_1137_);
lean_ctor_set(v_reuseFailAlloc_1173_, 4, v_l_1137_);
v___x_1169_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1171_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v___x_1169_);
lean_ctor_set(v___x_1047_, 3, v___x_1167_);
lean_ctor_set(v___x_1047_, 2, v_v_1161_);
lean_ctor_set(v___x_1047_, 1, v_k_1160_);
lean_ctor_set(v___x_1047_, 0, v___x_1165_);
v___x_1171_ = v___x_1047_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_k_1160_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_v_1161_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1172_, 4, v___x_1169_);
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
else
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_unsigned_to_nat(2u);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v_r_1154_);
lean_ctor_set(v___x_1047_, 3, v_impl_1050_);
lean_ctor_set(v___x_1047_, 0, v___x_1183_);
v___x_1185_ = v___x_1047_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v_impl_1050_);
lean_ctor_set(v_reuseFailAlloc_1186_, 4, v_r_1154_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1188_; 
lean_dec(v_v_1043_);
lean_dec(v_k_1042_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 2, v_v_1039_);
lean_ctor_set(v___x_1047_, 1, v_k_1038_);
v___x_1188_ = v___x_1047_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_size_1041_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_k_1038_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_v_1039_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v_l_1044_);
lean_ctor_set(v_reuseFailAlloc_1189_, 4, v_r_1045_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
default: 
{
lean_object* v_impl_1190_; lean_object* v___x_1191_; 
lean_dec(v_size_1041_);
v_impl_1190_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1038_, v_v_1039_, v_r_1045_);
v___x_1191_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1044_) == 0)
{
lean_object* v_size_1192_; lean_object* v_size_1193_; lean_object* v_k_1194_; lean_object* v_v_1195_; lean_object* v_l_1196_; lean_object* v_r_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v_size_1192_ = lean_ctor_get(v_l_1044_, 0);
v_size_1193_ = lean_ctor_get(v_impl_1190_, 0);
lean_inc(v_size_1193_);
v_k_1194_ = lean_ctor_get(v_impl_1190_, 1);
lean_inc(v_k_1194_);
v_v_1195_ = lean_ctor_get(v_impl_1190_, 2);
lean_inc(v_v_1195_);
v_l_1196_ = lean_ctor_get(v_impl_1190_, 3);
lean_inc(v_l_1196_);
v_r_1197_ = lean_ctor_get(v_impl_1190_, 4);
lean_inc(v_r_1197_);
v___x_1198_ = lean_unsigned_to_nat(3u);
v___x_1199_ = lean_nat_mul(v___x_1198_, v_size_1192_);
v___x_1200_ = lean_nat_dec_lt(v___x_1199_, v_size_1193_);
lean_dec(v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
lean_dec(v_r_1197_);
lean_dec(v_l_1196_);
lean_dec(v_v_1195_);
lean_dec(v_k_1194_);
v___x_1201_ = lean_nat_add(v___x_1191_, v_size_1192_);
v___x_1202_ = lean_nat_add(v___x_1201_, v_size_1193_);
lean_dec(v_size_1193_);
lean_dec(v___x_1201_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v_impl_1190_);
lean_ctor_set(v___x_1047_, 0, v___x_1202_);
v___x_1204_ = v___x_1047_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_l_1044_);
lean_ctor_set(v_reuseFailAlloc_1205_, 4, v_impl_1190_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
else
{
lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1269_; 
v_isSharedCheck_1269_ = !lean_is_exclusive(v_impl_1190_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; lean_object* v_unused_1271_; lean_object* v_unused_1272_; lean_object* v_unused_1273_; lean_object* v_unused_1274_; 
v_unused_1270_ = lean_ctor_get(v_impl_1190_, 4);
lean_dec(v_unused_1270_);
v_unused_1271_ = lean_ctor_get(v_impl_1190_, 3);
lean_dec(v_unused_1271_);
v_unused_1272_ = lean_ctor_get(v_impl_1190_, 2);
lean_dec(v_unused_1272_);
v_unused_1273_ = lean_ctor_get(v_impl_1190_, 1);
lean_dec(v_unused_1273_);
v_unused_1274_ = lean_ctor_get(v_impl_1190_, 0);
lean_dec(v_unused_1274_);
v___x_1207_ = v_impl_1190_;
v_isShared_1208_ = v_isSharedCheck_1269_;
goto v_resetjp_1206_;
}
else
{
lean_dec(v_impl_1190_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1269_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v_size_1209_; lean_object* v_k_1210_; lean_object* v_v_1211_; lean_object* v_l_1212_; lean_object* v_r_1213_; lean_object* v_size_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_size_1209_ = lean_ctor_get(v_l_1196_, 0);
v_k_1210_ = lean_ctor_get(v_l_1196_, 1);
v_v_1211_ = lean_ctor_get(v_l_1196_, 2);
v_l_1212_ = lean_ctor_get(v_l_1196_, 3);
v_r_1213_ = lean_ctor_get(v_l_1196_, 4);
v_size_1214_ = lean_ctor_get(v_r_1197_, 0);
v___x_1215_ = lean_unsigned_to_nat(2u);
v___x_1216_ = lean_nat_mul(v___x_1215_, v_size_1214_);
v___x_1217_ = lean_nat_dec_lt(v_size_1209_, v___x_1216_);
lean_dec(v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1245_; 
lean_inc(v_r_1213_);
lean_inc(v_l_1212_);
lean_inc(v_v_1211_);
lean_inc(v_k_1210_);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_l_1196_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; lean_object* v_unused_1247_; lean_object* v_unused_1248_; lean_object* v_unused_1249_; lean_object* v_unused_1250_; 
v_unused_1246_ = lean_ctor_get(v_l_1196_, 4);
lean_dec(v_unused_1246_);
v_unused_1247_ = lean_ctor_get(v_l_1196_, 3);
lean_dec(v_unused_1247_);
v_unused_1248_ = lean_ctor_get(v_l_1196_, 2);
lean_dec(v_unused_1248_);
v_unused_1249_ = lean_ctor_get(v_l_1196_, 1);
lean_dec(v_unused_1249_);
v_unused_1250_ = lean_ctor_get(v_l_1196_, 0);
lean_dec(v_unused_1250_);
v___x_1219_ = v_l_1196_;
v_isShared_1220_ = v_isSharedCheck_1245_;
goto v_resetjp_1218_;
}
else
{
lean_dec(v_l_1196_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1245_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1235_; 
v___x_1221_ = lean_nat_add(v___x_1191_, v_size_1192_);
v___x_1222_ = lean_nat_add(v___x_1221_, v_size_1193_);
lean_dec(v_size_1193_);
if (lean_obj_tag(v_l_1212_) == 0)
{
lean_object* v_size_1243_; 
v_size_1243_ = lean_ctor_get(v_l_1212_, 0);
lean_inc(v_size_1243_);
v___y_1235_ = v_size_1243_;
goto v___jp_1234_;
}
else
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_unsigned_to_nat(0u);
v___y_1235_ = v___x_1244_;
goto v___jp_1234_;
}
v___jp_1223_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = lean_nat_add(v___y_1224_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec(v___y_1224_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 4, v_r_1197_);
lean_ctor_set(v___x_1219_, 3, v_r_1213_);
lean_ctor_set(v___x_1219_, 2, v_v_1195_);
lean_ctor_set(v___x_1219_, 1, v_k_1194_);
lean_ctor_set(v___x_1219_, 0, v___x_1227_);
v___x_1229_ = v___x_1219_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_k_1194_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_v_1195_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v_r_1213_);
lean_ctor_set(v_reuseFailAlloc_1233_, 4, v_r_1197_);
v___x_1229_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1231_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v___x_1229_);
lean_ctor_set(v___x_1207_, 3, v___y_1225_);
lean_ctor_set(v___x_1207_, 2, v_v_1211_);
lean_ctor_set(v___x_1207_, 1, v_k_1210_);
lean_ctor_set(v___x_1207_, 0, v___x_1222_);
v___x_1231_ = v___x_1207_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_k_1210_);
lean_ctor_set(v_reuseFailAlloc_1232_, 2, v_v_1211_);
lean_ctor_set(v_reuseFailAlloc_1232_, 3, v___y_1225_);
lean_ctor_set(v_reuseFailAlloc_1232_, 4, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
v___jp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1236_ = lean_nat_add(v___x_1221_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec(v___x_1221_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v_l_1212_);
lean_ctor_set(v___x_1047_, 0, v___x_1236_);
v___x_1238_ = v___x_1047_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_l_1044_);
lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_l_1212_);
v___x_1238_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_nat_add(v___x_1191_, v_size_1214_);
if (lean_obj_tag(v_r_1213_) == 0)
{
lean_object* v_size_1240_; 
v_size_1240_ = lean_ctor_get(v_r_1213_, 0);
lean_inc(v_size_1240_);
v___y_1224_ = v___x_1239_;
v___y_1225_ = v___x_1238_;
v___y_1226_ = v_size_1240_;
goto v___jp_1223_;
}
else
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_unsigned_to_nat(0u);
v___y_1224_ = v___x_1239_;
v___y_1225_ = v___x_1238_;
v___y_1226_ = v___x_1241_;
goto v___jp_1223_;
}
}
}
}
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
lean_del_object(v___x_1047_);
v___x_1251_ = lean_nat_add(v___x_1191_, v_size_1192_);
v___x_1252_ = lean_nat_add(v___x_1251_, v_size_1193_);
lean_dec(v_size_1193_);
v___x_1253_ = lean_nat_add(v___x_1251_, v_size_1209_);
lean_dec(v___x_1251_);
lean_inc_ref(v_l_1044_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v_l_1196_);
lean_ctor_set(v___x_1207_, 3, v_l_1044_);
lean_ctor_set(v___x_1207_, 2, v_v_1043_);
lean_ctor_set(v___x_1207_, 1, v_k_1042_);
lean_ctor_set(v___x_1207_, 0, v___x_1253_);
v___x_1255_ = v___x_1207_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v_l_1044_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v_l_1196_);
v___x_1255_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
v_isSharedCheck_1262_ = !lean_is_exclusive(v_l_1044_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; lean_object* v_unused_1264_; lean_object* v_unused_1265_; lean_object* v_unused_1266_; lean_object* v_unused_1267_; 
v_unused_1263_ = lean_ctor_get(v_l_1044_, 4);
lean_dec(v_unused_1263_);
v_unused_1264_ = lean_ctor_get(v_l_1044_, 3);
lean_dec(v_unused_1264_);
v_unused_1265_ = lean_ctor_get(v_l_1044_, 2);
lean_dec(v_unused_1265_);
v_unused_1266_ = lean_ctor_get(v_l_1044_, 1);
lean_dec(v_unused_1266_);
v_unused_1267_ = lean_ctor_get(v_l_1044_, 0);
lean_dec(v_unused_1267_);
v___x_1257_ = v_l_1044_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_dec(v_l_1044_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 4, v_r_1197_);
lean_ctor_set(v___x_1257_, 3, v___x_1255_);
lean_ctor_set(v___x_1257_, 2, v_v_1195_);
lean_ctor_set(v___x_1257_, 1, v_k_1194_);
lean_ctor_set(v___x_1257_, 0, v___x_1252_);
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_k_1194_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_v_1195_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_r_1197_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1275_; 
v_l_1275_ = lean_ctor_get(v_impl_1190_, 3);
lean_inc(v_l_1275_);
if (lean_obj_tag(v_l_1275_) == 0)
{
lean_object* v_r_1276_; lean_object* v_k_1277_; lean_object* v_v_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1301_; 
v_r_1276_ = lean_ctor_get(v_impl_1190_, 4);
v_k_1277_ = lean_ctor_get(v_impl_1190_, 1);
v_v_1278_ = lean_ctor_get(v_impl_1190_, 2);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_impl_1190_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; lean_object* v_unused_1303_; 
v_unused_1302_ = lean_ctor_get(v_impl_1190_, 3);
lean_dec(v_unused_1302_);
v_unused_1303_ = lean_ctor_get(v_impl_1190_, 0);
lean_dec(v_unused_1303_);
v___x_1280_ = v_impl_1190_;
v_isShared_1281_ = v_isSharedCheck_1301_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_r_1276_);
lean_inc(v_v_1278_);
lean_inc(v_k_1277_);
lean_dec(v_impl_1190_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1301_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v_k_1282_; lean_object* v_v_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1297_; 
v_k_1282_ = lean_ctor_get(v_l_1275_, 1);
v_v_1283_ = lean_ctor_get(v_l_1275_, 2);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_l_1275_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; lean_object* v_unused_1299_; lean_object* v_unused_1300_; 
v_unused_1298_ = lean_ctor_get(v_l_1275_, 4);
lean_dec(v_unused_1298_);
v_unused_1299_ = lean_ctor_get(v_l_1275_, 3);
lean_dec(v_unused_1299_);
v_unused_1300_ = lean_ctor_get(v_l_1275_, 0);
lean_dec(v_unused_1300_);
v___x_1285_ = v_l_1275_;
v_isShared_1286_ = v_isSharedCheck_1297_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_v_1283_);
lean_inc(v_k_1282_);
lean_dec(v_l_1275_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1297_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1276_, 2);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v_r_1276_);
lean_ctor_set(v___x_1285_, 3, v_r_1276_);
lean_ctor_set(v___x_1285_, 2, v_v_1043_);
lean_ctor_set(v___x_1285_, 1, v_k_1042_);
lean_ctor_set(v___x_1285_, 0, v___x_1191_);
v___x_1289_ = v___x_1285_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v_r_1276_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v_r_1276_);
v___x_1289_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1291_; 
lean_inc(v_r_1276_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 3, v_r_1276_);
lean_ctor_set(v___x_1280_, 0, v___x_1191_);
v___x_1291_ = v___x_1280_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_k_1277_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_v_1278_);
lean_ctor_set(v_reuseFailAlloc_1295_, 3, v_r_1276_);
lean_ctor_set(v_reuseFailAlloc_1295_, 4, v_r_1276_);
v___x_1291_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1293_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v___x_1291_);
lean_ctor_set(v___x_1047_, 3, v___x_1289_);
lean_ctor_set(v___x_1047_, 2, v_v_1283_);
lean_ctor_set(v___x_1047_, 1, v_k_1282_);
lean_ctor_set(v___x_1047_, 0, v___x_1287_);
v___x_1293_ = v___x_1047_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1294_, 3, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1294_, 4, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
}
else
{
lean_object* v_r_1304_; 
v_r_1304_ = lean_ctor_get(v_impl_1190_, 4);
lean_inc(v_r_1304_);
if (lean_obj_tag(v_r_1304_) == 0)
{
lean_object* v_k_1305_; lean_object* v_v_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1317_; 
v_k_1305_ = lean_ctor_get(v_impl_1190_, 1);
v_v_1306_ = lean_ctor_get(v_impl_1190_, 2);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_impl_1190_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; lean_object* v_unused_1319_; lean_object* v_unused_1320_; 
v_unused_1318_ = lean_ctor_get(v_impl_1190_, 4);
lean_dec(v_unused_1318_);
v_unused_1319_ = lean_ctor_get(v_impl_1190_, 3);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_impl_1190_, 0);
lean_dec(v_unused_1320_);
v___x_1308_ = v_impl_1190_;
v_isShared_1309_ = v_isSharedCheck_1317_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_v_1306_);
lean_inc(v_k_1305_);
lean_dec(v_impl_1190_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1317_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1310_ = lean_unsigned_to_nat(3u);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 4, v_l_1275_);
lean_ctor_set(v___x_1308_, 2, v_v_1043_);
lean_ctor_set(v___x_1308_, 1, v_k_1042_);
lean_ctor_set(v___x_1308_, 0, v___x_1191_);
v___x_1312_ = v___x_1308_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1316_, 3, v_l_1275_);
lean_ctor_set(v_reuseFailAlloc_1316_, 4, v_l_1275_);
v___x_1312_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1314_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v_r_1304_);
lean_ctor_set(v___x_1047_, 3, v___x_1312_);
lean_ctor_set(v___x_1047_, 2, v_v_1306_);
lean_ctor_set(v___x_1047_, 1, v_k_1305_);
lean_ctor_set(v___x_1047_, 0, v___x_1310_);
v___x_1314_ = v___x_1047_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_k_1305_);
lean_ctor_set(v_reuseFailAlloc_1315_, 2, v_v_1306_);
lean_ctor_set(v_reuseFailAlloc_1315_, 3, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1315_, 4, v_r_1304_);
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
else
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = lean_unsigned_to_nat(2u);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v_impl_1190_);
lean_ctor_set(v___x_1047_, 3, v_r_1304_);
lean_ctor_set(v___x_1047_, 0, v___x_1321_);
v___x_1323_ = v___x_1047_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1324_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1324_, 3, v_r_1304_);
lean_ctor_set(v_reuseFailAlloc_1324_, 4, v_impl_1190_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
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
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_unsigned_to_nat(1u);
v___x_1327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
lean_ctor_set(v___x_1327_, 1, v_k_1038_);
lean_ctor_set(v___x_1327_, 2, v_v_1039_);
lean_ctor_set(v___x_1327_, 3, v_t_1040_);
lean_ctor_set(v___x_1327_, 4, v_t_1040_);
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object* v_s_1328_, lean_object* v_mvarId_1329_){
_start:
{
uint8_t v___x_1330_; 
v___x_1330_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_mvarId_1329_, v_s_1328_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_box(0);
v___x_1332_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1329_, v___x_1331_, v_s_1328_);
return v___x_1332_;
}
else
{
lean_dec(v_mvarId_1329_);
return v_s_1328_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object* v_00_u03b2_1333_, lean_object* v_k_1334_, lean_object* v_t_1335_){
_start:
{
uint8_t v___x_1336_; 
v___x_1336_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1334_, v_t_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object* v_00_u03b2_1337_, lean_object* v_k_1338_, lean_object* v_t_1339_){
_start:
{
uint8_t v_res_1340_; lean_object* v_r_1341_; 
v_res_1340_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(v_00_u03b2_1337_, v_k_1338_, v_t_1339_);
lean_dec(v_t_1339_);
lean_dec(v_k_1338_);
v_r_1341_ = lean_box(v_res_1340_);
return v_r_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object* v_00_u03b2_1342_, lean_object* v_k_1343_, lean_object* v_v_1344_, lean_object* v_t_1345_, lean_object* v_hl_1346_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1343_, v_v_1344_, v_t_1345_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object* v_l_1348_){
_start:
{
lean_object* v___f_1349_; lean_object* v___x_1350_; 
v___f_1349_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___closed__0));
v___x_1350_ = l_Std_TreeSet_ofList___redArg(v_l_1348_, v___f_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object* v_l_1351_){
_start:
{
lean_object* v___f_1352_; lean_object* v___x_1353_; 
v___f_1352_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___closed__0));
v___x_1353_ = l_Std_TreeSet_ofArray___redArg(v_l_1351_, v___f_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object* v_l_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_MVarIdSet_ofArray(v_l_1354_);
lean_dec_ref(v_l_1354_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object* v_inst_1356_){
_start:
{
lean_object* v___f_1357_; 
v___f_1357_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1357_, 0, v_inst_1356_);
return v___f_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object* v_m_1358_, lean_object* v_inst_1359_){
_start:
{
lean_object* v___f_1360_; 
v___f_1360_ = lean_alloc_closure((void*)(l_Std_TreeSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1360_, 0, v_inst_1359_);
return v___f_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object* v_s_1361_, lean_object* v_mvarId_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1362_, v_a_1363_, v_s_1361_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object* v_00_u03b1_1365_, lean_object* v_s_1366_, lean_object* v_mvarId_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1367_, v_a_1368_, v_s_1366_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* v_00_u03b1_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_box(1);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object* v_inst_1372_){
_start:
{
lean_object* v___f_1373_; 
v___f_1373_ = lean_alloc_closure((void*)(l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1373_, 0, v_inst_1372_);
return v___f_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object* v_m_1374_, lean_object* v_00_u03b1_1375_, lean_object* v_inst_1376_){
_start:
{
lean_object* v___f_1377_; 
v___f_1377_ = lean_alloc_closure((void*)(l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1377_, 0, v_inst_1376_);
return v___f_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* v_00_u03b1_1378_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_box(1);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx(lean_object* v_x_1380_){
_start:
{
switch(lean_obj_tag(v_x_1380_))
{
case 0:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
return v___x_1381_;
}
case 1:
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_unsigned_to_nat(1u);
return v___x_1382_;
}
case 2:
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_unsigned_to_nat(2u);
return v___x_1383_;
}
case 3:
{
lean_object* v___x_1384_; 
v___x_1384_ = lean_unsigned_to_nat(3u);
return v___x_1384_;
}
case 4:
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_unsigned_to_nat(4u);
return v___x_1385_;
}
case 5:
{
lean_object* v___x_1386_; 
v___x_1386_ = lean_unsigned_to_nat(5u);
return v___x_1386_;
}
case 6:
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_unsigned_to_nat(6u);
return v___x_1387_;
}
case 7:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_unsigned_to_nat(7u);
return v___x_1388_;
}
case 8:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_unsigned_to_nat(8u);
return v___x_1389_;
}
case 9:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_unsigned_to_nat(9u);
return v___x_1390_;
}
case 10:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_unsigned_to_nat(10u);
return v___x_1391_;
}
default: 
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_unsigned_to_nat(11u);
return v___x_1392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___boxed(lean_object* v_x_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Expr_ctorIdx(v_x_1393_);
lean_dec_ref(v_x_1393_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object* v_t_1395_, lean_object* v_k_1396_){
_start:
{
switch(lean_obj_tag(v_t_1395_))
{
case 4:
{
lean_object* v_declName_1397_; lean_object* v_us_1398_; lean_object* v___x_1399_; 
v_declName_1397_ = lean_ctor_get(v_t_1395_, 0);
lean_inc(v_declName_1397_);
v_us_1398_ = lean_ctor_get(v_t_1395_, 1);
lean_inc(v_us_1398_);
lean_dec_ref(v_t_1395_);
v___x_1399_ = lean_apply_2(v_k_1396_, v_declName_1397_, v_us_1398_);
return v___x_1399_;
}
case 5:
{
lean_object* v_fn_1400_; lean_object* v_arg_1401_; lean_object* v___x_1402_; 
v_fn_1400_ = lean_ctor_get(v_t_1395_, 0);
lean_inc_ref(v_fn_1400_);
v_arg_1401_ = lean_ctor_get(v_t_1395_, 1);
lean_inc_ref(v_arg_1401_);
lean_dec_ref(v_t_1395_);
v___x_1402_ = lean_apply_2(v_k_1396_, v_fn_1400_, v_arg_1401_);
return v___x_1402_;
}
case 6:
{
lean_object* v_binderName_1403_; lean_object* v_binderType_1404_; lean_object* v_body_1405_; uint8_t v_binderInfo_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_binderName_1403_ = lean_ctor_get(v_t_1395_, 0);
lean_inc(v_binderName_1403_);
v_binderType_1404_ = lean_ctor_get(v_t_1395_, 1);
lean_inc_ref(v_binderType_1404_);
v_body_1405_ = lean_ctor_get(v_t_1395_, 2);
lean_inc_ref(v_body_1405_);
v_binderInfo_1406_ = lean_ctor_get_uint8(v_t_1395_, sizeof(void*)*3);
lean_dec_ref(v_t_1395_);
v___x_1407_ = lean_box(v_binderInfo_1406_);
v___x_1408_ = lean_apply_4(v_k_1396_, v_binderName_1403_, v_binderType_1404_, v_body_1405_, v___x_1407_);
return v___x_1408_;
}
case 7:
{
lean_object* v_binderName_1409_; lean_object* v_binderType_1410_; lean_object* v_body_1411_; uint8_t v_binderInfo_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_binderName_1409_ = lean_ctor_get(v_t_1395_, 0);
lean_inc(v_binderName_1409_);
v_binderType_1410_ = lean_ctor_get(v_t_1395_, 1);
lean_inc_ref(v_binderType_1410_);
v_body_1411_ = lean_ctor_get(v_t_1395_, 2);
lean_inc_ref(v_body_1411_);
v_binderInfo_1412_ = lean_ctor_get_uint8(v_t_1395_, sizeof(void*)*3);
lean_dec_ref(v_t_1395_);
v___x_1413_ = lean_box(v_binderInfo_1412_);
v___x_1414_ = lean_apply_4(v_k_1396_, v_binderName_1409_, v_binderType_1410_, v_body_1411_, v___x_1413_);
return v___x_1414_;
}
case 8:
{
lean_object* v_declName_1415_; lean_object* v_type_1416_; lean_object* v_value_1417_; lean_object* v_body_1418_; uint8_t v_nondep_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_declName_1415_ = lean_ctor_get(v_t_1395_, 0);
lean_inc(v_declName_1415_);
v_type_1416_ = lean_ctor_get(v_t_1395_, 1);
lean_inc_ref(v_type_1416_);
v_value_1417_ = lean_ctor_get(v_t_1395_, 2);
lean_inc_ref(v_value_1417_);
v_body_1418_ = lean_ctor_get(v_t_1395_, 3);
lean_inc_ref(v_body_1418_);
v_nondep_1419_ = lean_ctor_get_uint8(v_t_1395_, sizeof(void*)*4);
lean_dec_ref(v_t_1395_);
v___x_1420_ = lean_box(v_nondep_1419_);
v___x_1421_ = lean_apply_5(v_k_1396_, v_declName_1415_, v_type_1416_, v_value_1417_, v_body_1418_, v___x_1420_);
return v___x_1421_;
}
case 9:
{
lean_object* v_a_1422_; lean_object* v___x_1423_; 
v_a_1422_ = lean_ctor_get(v_t_1395_, 0);
lean_inc_ref(v_a_1422_);
lean_dec_ref(v_t_1395_);
v___x_1423_ = lean_apply_1(v_k_1396_, v_a_1422_);
return v___x_1423_;
}
case 10:
{
lean_object* v_data_1424_; lean_object* v_expr_1425_; lean_object* v___x_1426_; 
v_data_1424_ = lean_ctor_get(v_t_1395_, 0);
lean_inc(v_data_1424_);
v_expr_1425_ = lean_ctor_get(v_t_1395_, 1);
lean_inc_ref(v_expr_1425_);
lean_dec_ref(v_t_1395_);
v___x_1426_ = lean_apply_2(v_k_1396_, v_data_1424_, v_expr_1425_);
return v___x_1426_;
}
case 11:
{
lean_object* v_typeName_1427_; lean_object* v_idx_1428_; lean_object* v_struct_1429_; lean_object* v___x_1430_; 
v_typeName_1427_ = lean_ctor_get(v_t_1395_, 0);
lean_inc(v_typeName_1427_);
v_idx_1428_ = lean_ctor_get(v_t_1395_, 1);
lean_inc(v_idx_1428_);
v_struct_1429_ = lean_ctor_get(v_t_1395_, 2);
lean_inc_ref(v_struct_1429_);
lean_dec_ref(v_t_1395_);
v___x_1430_ = lean_apply_3(v_k_1396_, v_typeName_1427_, v_idx_1428_, v_struct_1429_);
return v___x_1430_;
}
default: 
{
lean_object* v_deBruijnIndex_1431_; lean_object* v___x_1432_; 
v_deBruijnIndex_1431_ = lean_ctor_get(v_t_1395_, 0);
lean_inc(v_deBruijnIndex_1431_);
lean_dec_ref(v_t_1395_);
v___x_1432_ = lean_apply_1(v_k_1396_, v_deBruijnIndex_1431_);
return v___x_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object* v_motive_1433_, lean_object* v_ctorIdx_1434_, lean_object* v_t_1435_, lean_object* v_h_1436_, lean_object* v_k_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Expr_ctorElim___redArg(v_t_1435_, v_k_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object* v_motive_1439_, lean_object* v_ctorIdx_1440_, lean_object* v_t_1441_, lean_object* v_h_1442_, lean_object* v_k_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_Expr_ctorElim(v_motive_1439_, v_ctorIdx_1440_, v_t_1441_, v_h_1442_, v_k_1443_);
lean_dec(v_ctorIdx_1440_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object* v_t_1445_, lean_object* v_bvar_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_Expr_ctorElim___redArg(v_t_1445_, v_bvar_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object* v_motive_1448_, lean_object* v_t_1449_, lean_object* v_h_1450_, lean_object* v_bvar_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_Expr_ctorElim___redArg(v_t_1449_, v_bvar_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object* v_t_1453_, lean_object* v_fvar_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_Expr_ctorElim___redArg(v_t_1453_, v_fvar_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object* v_motive_1456_, lean_object* v_t_1457_, lean_object* v_h_1458_, lean_object* v_fvar_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_Expr_ctorElim___redArg(v_t_1457_, v_fvar_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object* v_t_1461_, lean_object* v_mvar_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_Expr_ctorElim___redArg(v_t_1461_, v_mvar_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object* v_motive_1464_, lean_object* v_t_1465_, lean_object* v_h_1466_, lean_object* v_mvar_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_Expr_ctorElim___redArg(v_t_1465_, v_mvar_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object* v_t_1469_, lean_object* v_sort_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_Expr_ctorElim___redArg(v_t_1469_, v_sort_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object* v_motive_1472_, lean_object* v_t_1473_, lean_object* v_h_1474_, lean_object* v_sort_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_Expr_ctorElim___redArg(v_t_1473_, v_sort_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object* v_t_1477_, lean_object* v_const_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Expr_ctorElim___redArg(v_t_1477_, v_const_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object* v_motive_1480_, lean_object* v_t_1481_, lean_object* v_h_1482_, lean_object* v_const_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_Expr_ctorElim___redArg(v_t_1481_, v_const_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object* v_t_1485_, lean_object* v_app_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_Expr_ctorElim___redArg(v_t_1485_, v_app_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object* v_motive_1488_, lean_object* v_t_1489_, lean_object* v_h_1490_, lean_object* v_app_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_Expr_ctorElim___redArg(v_t_1489_, v_app_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object* v_t_1493_, lean_object* v_lam_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_Expr_ctorElim___redArg(v_t_1493_, v_lam_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object* v_motive_1496_, lean_object* v_t_1497_, lean_object* v_h_1498_, lean_object* v_lam_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_Expr_ctorElim___redArg(v_t_1497_, v_lam_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object* v_t_1501_, lean_object* v_forallE_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_Expr_ctorElim___redArg(v_t_1501_, v_forallE_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object* v_motive_1504_, lean_object* v_t_1505_, lean_object* v_h_1506_, lean_object* v_forallE_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_Expr_ctorElim___redArg(v_t_1505_, v_forallE_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object* v_t_1509_, lean_object* v_letE_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_Expr_ctorElim___redArg(v_t_1509_, v_letE_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object* v_motive_1512_, lean_object* v_t_1513_, lean_object* v_h_1514_, lean_object* v_letE_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_Expr_ctorElim___redArg(v_t_1513_, v_letE_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object* v_t_1517_, lean_object* v_lit_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_Expr_ctorElim___redArg(v_t_1517_, v_lit_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object* v_motive_1520_, lean_object* v_t_1521_, lean_object* v_h_1522_, lean_object* v_lit_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_Expr_ctorElim___redArg(v_t_1521_, v_lit_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object* v_t_1525_, lean_object* v_mdata_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_Expr_ctorElim___redArg(v_t_1525_, v_mdata_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object* v_motive_1528_, lean_object* v_t_1529_, lean_object* v_h_1530_, lean_object* v_mdata_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_Expr_ctorElim___redArg(v_t_1529_, v_mdata_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object* v_t_1533_, lean_object* v_proj_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_Expr_ctorElim___redArg(v_t_1533_, v_proj_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object* v_motive_1536_, lean_object* v_t_1537_, lean_object* v_h_1538_, lean_object* v_proj_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_Expr_ctorElim___redArg(v_t_1537_, v_proj_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* v_a_00___x40___internal___hyg_1542_){
_start:
{
uint64_t v_res_1543_; lean_object* v_r_1544_; 
v_res_1543_ = lean_expr_data(v_a_00___x40___internal___hyg_1542_);
lean_dec_ref(v_a_00___x40___internal___hyg_1542_);
v_r_1544_ = lean_box_uint64(v_res_1543_);
return v_r_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object* v_t_1545_, lean_object* v_bvar_1546_, lean_object* v_fvar_1547_, lean_object* v_mvar_1548_, lean_object* v_sort_1549_, lean_object* v_const_1550_, lean_object* v_app_1551_, lean_object* v_lam_1552_, lean_object* v_forallE_1553_, lean_object* v_letE_1554_, lean_object* v_lit_1555_, lean_object* v_mdata_1556_, lean_object* v_proj_1557_){
_start:
{
switch(lean_obj_tag(v_t_1545_))
{
case 0:
{
lean_object* v_deBruijnIndex_1558_; lean_object* v___x_1559_; 
lean_dec(v_proj_1557_);
lean_dec(v_mdata_1556_);
lean_dec(v_lit_1555_);
lean_dec(v_letE_1554_);
lean_dec(v_forallE_1553_);
lean_dec(v_lam_1552_);
lean_dec(v_app_1551_);
lean_dec(v_const_1550_);
lean_dec(v_sort_1549_);
lean_dec(v_mvar_1548_);
lean_dec(v_fvar_1547_);
v_deBruijnIndex_1558_ = lean_ctor_get(v_t_1545_, 0);
lean_inc(v_deBruijnIndex_1558_);
lean_dec_ref(v_t_1545_);
v___x_1559_ = lean_apply_1(v_bvar_1546_, v_deBruijnIndex_1558_);
return v___x_1559_;
}
case 1:
{
lean_object* v_fvarId_1560_; lean_object* v___x_1561_; 
lean_dec(v_proj_1557_);
lean_dec(v_mdata_1556_);
lean_dec(v_lit_1555_);
lean_dec(v_letE_1554_);
lean_dec(v_forallE_1553_);
lean_dec(v_lam_1552_);
lean_dec(v_app_1551_);
lean_dec(v_const_1550_);
lean_dec(v_sort_1549_);
lean_dec(v_mvar_1548_);
lean_dec(v_bvar_1546_);
v_fvarId_1560_ = lean_ctor_get(v_t_1545_, 0);
lean_inc(v_fvarId_1560_);
lean_dec_ref(v_t_1545_);
v___x_1561_ = lean_apply_1(v_fvar_1547_, v_fvarId_1560_);
return v___x_1561_;
}
case 2:
{
lean_object* v_mvarId_1562_; lean_object* v___x_1563_; 
lean_dec(v_proj_1557_);
lean_dec(v_mdata_1556_);
lean_dec(v_lit_1555_);
lean_dec(v_letE_1554_);
lean_dec(v_forallE_1553_);
lean_dec(v_lam_1552_);
lean_dec(v_app_1551_);
lean_dec(v_const_1550_);
lean_dec(v_sort_1549_);
lean_dec(v_fvar_1547_);
lean_dec(v_bvar_1546_);
v_mvarId_1562_ = lean_ctor_get(v_t_1545_, 0);
lean_inc(v_mvarId_1562_);
lean_dec_ref(v_t_1545_);
v___x_1563_ = lean_apply_1(v_mvar_1548_, v_mvarId_1562_);
return v___x_1563_;
}
case 3:
{
lean_object* v_u_1564_; lean_object* v___x_1565_; 
lean_dec(v_proj_1557_);
lean_dec(v_mdata_1556_);
lean_dec(v_lit_1555_);
lean_dec(v_letE_1554_);
lean_dec(v_forallE_1553_);
lean_dec(v_lam_1552_);
lean_dec(v_app_1551_);
lean_dec(v_const_1550_);
lean_dec(v_mvar_1548_);
lean_dec(v_fvar_1547_);
lean_dec(v_bvar_1546_);
v_u_1564_ = lean_ctor_get(v_t_1545_, 0);
lean_inc(v_u_1564_);
lean_dec_ref(v_t_1545_);
v___x_1565_ = lean_apply_1(v_sort_1549_, v_u_1564_);
return v___x_1565_;
}
case 4:
{
lean_object* v_declName_1566_; lean_object* v_us_1567_; lean_object* v___x_1568_; 
lean_dec(v_proj_1557_);
lean_dec(v_mdata_1556_);
lean_dec(v_lit_1555_);
lean_dec(v_letE_1554_);
lean_dec(v_forallE_1553_);
lean_dec(v_lam_1552_);
lean_dec(v_app_1551_);
lean_dec(v_sort_1549_);
lean_dec(v_mvar_1548_);
lean_dec(v_fvar_1547_);
lean_dec(v_bvar_1546_);
v_declName_1566_ = lean_ctor_get(v_t_1545_, 0);
lean_inc(v_declName_1566_);
v_us_1567_ = lean_ctor_get(v_t_1545_, 1);
lean_inc(v_us_1567_);
lean_dec_ref(v_t_1545_);
v___x_1568_ = lean_apply_2(v_const_1550_, v_declName_1566_, v_us_1567_);
return v___x_1568_;
}
case 5:
{
lean_object* v_fn_1569_; lean_object* v_arg_1570_; lean_object* v___x_1571_; 
lean_dec(v_proj_1557_);
lean_dec(v_mdata_1556_);
lean_dec(v_lit_1555_);
lean_dec(v_letE_1554_);
lean_dec(v_forallE_1553_);
lean_dec(v_lam_1552_);
lean_dec(v_const_1550_);
lean_dec(v_sort_1549_);
lean_dec(v_mvar_1548_);
lean_dec(v_fvar_1547_);
lean_dec(v_bvar_1546_);
v_fn_1569_ = lean_ctor_get(v_t_1545_, 0);
lean_inc_ref(v_fn_1569_);
v_arg_1570_ = lean_ctor_get(v_t_1545_, 1);
lean_inc_ref(v_arg_1570_);
lean_dec_ref(v_t_1545_);
v___x_1571_ = lean_apply_2(v_app_1551_, v_fn_1569_, v_arg_1570_);
return v___x_1571_;
}
case 6:
{
lean_object* v_binderName_1572_; lean_object* v_binderType_1573_; lean_object* v_body_1574_; uint8_t v_binderInfo_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_dec(v_proj_1557_);
lean_dec(v_mdata_1556_);
lean_dec(v_lit_1555_);
lean_dec(v_letE_1554_);
lean_dec(v_forallE_1553_);
lean_dec(v_app_1551_);
lean_dec(v_const_1550_);
lean_dec(v_sort_1549_);
lean_dec(v_mvar_1548_);
lean_dec(v_fvar_1547_);
lean_dec(v_bvar_1546_);
v_binderName_1572_ = lean_ctor_get(v_t_1545_, 0);
lean_inc(v_binderName_1572_);
v_binderType_1573_ = lean_ctor_get(v_t_1545_, 1);
lean_inc_ref(v_binderType_1573_);
v_body_1574_ = lean_ctor_get(v_t_1545_, 2);
lean_inc_ref(v_body_1574_);
v_binderInfo_1575_ = lean_ctor_get_uint8(v_t_1545_, sizeof(void*)*3 + 8);
lean_dec_ref(v_t_1545_);
v___x_1576_ = lean_box(v_binderInfo_1575_);
v___x_1577_ = lean_apply_4(v_lam_1552_, v_binderName_1572_, v_binderType_1573_, v_body_1574_, v___x_1576_);
return v___x_1577_;
}
case 7:
{
lean_object* v_binderName_1578_; lean_object* v_binderType_1579_; lean_object* v_body_1580_; uint8_t v_binderInfo_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec(v_proj_1557_);
lean_dec(v_mdata_1556_);
lean_dec(v_lit_1555_);
lean_dec(v_letE_1554_);
lean_dec(v_lam_1552_);
lean_dec(v_app_1551_);
lean_dec(v_const_1550_);
lean_dec(v_sort_1549_);
lean_dec(v_mvar_1548_);
lean_dec(v_fvar_1547_);
lean_dec(v_bvar_1546_);
v_binderName_1578_ = lean_ctor_get(v_t_1545_, 0);
lean_inc(v_binderName_1578_);
v_binderType_1579_ = lean_ctor_get(v_t_1545_, 1);
lean_inc_ref(v_binderType_1579_);
v_body_1580_ = lean_ctor_get(v_t_1545_, 2);
lean_inc_ref(v_body_1580_);
v_binderInfo_1581_ = lean_ctor_get_uint8(v_t_1545_, sizeof(void*)*3 + 8);
lean_dec_ref(v_t_1545_);
v___x_1582_ = lean_box(v_binderInfo_1581_);
v___x_1583_ = lean_apply_4(v_forallE_1553_, v_binderName_1578_, v_binderType_1579_, v_body_1580_, v___x_1582_);
return v___x_1583_;
}
case 8:
{
lean_object* v_declName_1584_; lean_object* v_type_1585_; lean_object* v_value_1586_; lean_object* v_body_1587_; uint8_t v_nondep_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec(v_proj_1557_);
lean_dec(v_mdata_1556_);
lean_dec(v_lit_1555_);
lean_dec(v_forallE_1553_);
lean_dec(v_lam_1552_);
lean_dec(v_app_1551_);
lean_dec(v_const_1550_);
lean_dec(v_sort_1549_);
lean_dec(v_mvar_1548_);
lean_dec(v_fvar_1547_);
lean_dec(v_bvar_1546_);
v_declName_1584_ = lean_ctor_get(v_t_1545_, 0);
lean_inc(v_declName_1584_);
v_type_1585_ = lean_ctor_get(v_t_1545_, 1);
lean_inc_ref(v_type_1585_);
v_value_1586_ = lean_ctor_get(v_t_1545_, 2);
lean_inc_ref(v_value_1586_);
v_body_1587_ = lean_ctor_get(v_t_1545_, 3);
lean_inc_ref(v_body_1587_);
v_nondep_1588_ = lean_ctor_get_uint8(v_t_1545_, sizeof(void*)*4 + 8);
lean_dec_ref(v_t_1545_);
v___x_1589_ = lean_box(v_nondep_1588_);
v___x_1590_ = lean_apply_5(v_letE_1554_, v_declName_1584_, v_type_1585_, v_value_1586_, v_body_1587_, v___x_1589_);
return v___x_1590_;
}
case 9:
{
lean_object* v_a_1591_; lean_object* v___x_1592_; 
lean_dec(v_proj_1557_);
lean_dec(v_mdata_1556_);
lean_dec(v_letE_1554_);
lean_dec(v_forallE_1553_);
lean_dec(v_lam_1552_);
lean_dec(v_app_1551_);
lean_dec(v_const_1550_);
lean_dec(v_sort_1549_);
lean_dec(v_mvar_1548_);
lean_dec(v_fvar_1547_);
lean_dec(v_bvar_1546_);
v_a_1591_ = lean_ctor_get(v_t_1545_, 0);
lean_inc_ref(v_a_1591_);
lean_dec_ref(v_t_1545_);
v___x_1592_ = lean_apply_1(v_lit_1555_, v_a_1591_);
return v___x_1592_;
}
case 10:
{
lean_object* v_data_1593_; lean_object* v_expr_1594_; lean_object* v___x_1595_; 
lean_dec(v_proj_1557_);
lean_dec(v_lit_1555_);
lean_dec(v_letE_1554_);
lean_dec(v_forallE_1553_);
lean_dec(v_lam_1552_);
lean_dec(v_app_1551_);
lean_dec(v_const_1550_);
lean_dec(v_sort_1549_);
lean_dec(v_mvar_1548_);
lean_dec(v_fvar_1547_);
lean_dec(v_bvar_1546_);
v_data_1593_ = lean_ctor_get(v_t_1545_, 0);
lean_inc(v_data_1593_);
v_expr_1594_ = lean_ctor_get(v_t_1545_, 1);
lean_inc_ref(v_expr_1594_);
lean_dec_ref(v_t_1545_);
v___x_1595_ = lean_apply_2(v_mdata_1556_, v_data_1593_, v_expr_1594_);
return v___x_1595_;
}
default: 
{
lean_object* v_typeName_1596_; lean_object* v_idx_1597_; lean_object* v_struct_1598_; lean_object* v___x_1599_; 
lean_dec(v_mdata_1556_);
lean_dec(v_lit_1555_);
lean_dec(v_letE_1554_);
lean_dec(v_forallE_1553_);
lean_dec(v_lam_1552_);
lean_dec(v_app_1551_);
lean_dec(v_const_1550_);
lean_dec(v_sort_1549_);
lean_dec(v_mvar_1548_);
lean_dec(v_fvar_1547_);
lean_dec(v_bvar_1546_);
v_typeName_1596_ = lean_ctor_get(v_t_1545_, 0);
lean_inc(v_typeName_1596_);
v_idx_1597_ = lean_ctor_get(v_t_1545_, 1);
lean_inc(v_idx_1597_);
v_struct_1598_ = lean_ctor_get(v_t_1545_, 2);
lean_inc_ref(v_struct_1598_);
lean_dec_ref(v_t_1545_);
v___x_1599_ = lean_apply_3(v_proj_1557_, v_typeName_1596_, v_idx_1597_, v_struct_1598_);
return v___x_1599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* v_motive_1600_, lean_object* v_t_1601_, lean_object* v_bvar_1602_, lean_object* v_fvar_1603_, lean_object* v_mvar_1604_, lean_object* v_sort_1605_, lean_object* v_const_1606_, lean_object* v_app_1607_, lean_object* v_lam_1608_, lean_object* v_forallE_1609_, lean_object* v_letE_1610_, lean_object* v_lit_1611_, lean_object* v_mdata_1612_, lean_object* v_proj_1613_){
_start:
{
switch(lean_obj_tag(v_t_1601_))
{
case 0:
{
lean_object* v_deBruijnIndex_1614_; lean_object* v___x_1615_; 
lean_dec(v_proj_1613_);
lean_dec(v_mdata_1612_);
lean_dec(v_lit_1611_);
lean_dec(v_letE_1610_);
lean_dec(v_forallE_1609_);
lean_dec(v_lam_1608_);
lean_dec(v_app_1607_);
lean_dec(v_const_1606_);
lean_dec(v_sort_1605_);
lean_dec(v_mvar_1604_);
lean_dec(v_fvar_1603_);
v_deBruijnIndex_1614_ = lean_ctor_get(v_t_1601_, 0);
lean_inc(v_deBruijnIndex_1614_);
lean_dec_ref(v_t_1601_);
v___x_1615_ = lean_apply_1(v_bvar_1602_, v_deBruijnIndex_1614_);
return v___x_1615_;
}
case 1:
{
lean_object* v_fvarId_1616_; lean_object* v___x_1617_; 
lean_dec(v_proj_1613_);
lean_dec(v_mdata_1612_);
lean_dec(v_lit_1611_);
lean_dec(v_letE_1610_);
lean_dec(v_forallE_1609_);
lean_dec(v_lam_1608_);
lean_dec(v_app_1607_);
lean_dec(v_const_1606_);
lean_dec(v_sort_1605_);
lean_dec(v_mvar_1604_);
lean_dec(v_bvar_1602_);
v_fvarId_1616_ = lean_ctor_get(v_t_1601_, 0);
lean_inc(v_fvarId_1616_);
lean_dec_ref(v_t_1601_);
v___x_1617_ = lean_apply_1(v_fvar_1603_, v_fvarId_1616_);
return v___x_1617_;
}
case 2:
{
lean_object* v_mvarId_1618_; lean_object* v___x_1619_; 
lean_dec(v_proj_1613_);
lean_dec(v_mdata_1612_);
lean_dec(v_lit_1611_);
lean_dec(v_letE_1610_);
lean_dec(v_forallE_1609_);
lean_dec(v_lam_1608_);
lean_dec(v_app_1607_);
lean_dec(v_const_1606_);
lean_dec(v_sort_1605_);
lean_dec(v_fvar_1603_);
lean_dec(v_bvar_1602_);
v_mvarId_1618_ = lean_ctor_get(v_t_1601_, 0);
lean_inc(v_mvarId_1618_);
lean_dec_ref(v_t_1601_);
v___x_1619_ = lean_apply_1(v_mvar_1604_, v_mvarId_1618_);
return v___x_1619_;
}
case 3:
{
lean_object* v_u_1620_; lean_object* v___x_1621_; 
lean_dec(v_proj_1613_);
lean_dec(v_mdata_1612_);
lean_dec(v_lit_1611_);
lean_dec(v_letE_1610_);
lean_dec(v_forallE_1609_);
lean_dec(v_lam_1608_);
lean_dec(v_app_1607_);
lean_dec(v_const_1606_);
lean_dec(v_mvar_1604_);
lean_dec(v_fvar_1603_);
lean_dec(v_bvar_1602_);
v_u_1620_ = lean_ctor_get(v_t_1601_, 0);
lean_inc(v_u_1620_);
lean_dec_ref(v_t_1601_);
v___x_1621_ = lean_apply_1(v_sort_1605_, v_u_1620_);
return v___x_1621_;
}
case 4:
{
lean_object* v_declName_1622_; lean_object* v_us_1623_; lean_object* v___x_1624_; 
lean_dec(v_proj_1613_);
lean_dec(v_mdata_1612_);
lean_dec(v_lit_1611_);
lean_dec(v_letE_1610_);
lean_dec(v_forallE_1609_);
lean_dec(v_lam_1608_);
lean_dec(v_app_1607_);
lean_dec(v_sort_1605_);
lean_dec(v_mvar_1604_);
lean_dec(v_fvar_1603_);
lean_dec(v_bvar_1602_);
v_declName_1622_ = lean_ctor_get(v_t_1601_, 0);
lean_inc(v_declName_1622_);
v_us_1623_ = lean_ctor_get(v_t_1601_, 1);
lean_inc(v_us_1623_);
lean_dec_ref(v_t_1601_);
v___x_1624_ = lean_apply_2(v_const_1606_, v_declName_1622_, v_us_1623_);
return v___x_1624_;
}
case 5:
{
lean_object* v_fn_1625_; lean_object* v_arg_1626_; lean_object* v___x_1627_; 
lean_dec(v_proj_1613_);
lean_dec(v_mdata_1612_);
lean_dec(v_lit_1611_);
lean_dec(v_letE_1610_);
lean_dec(v_forallE_1609_);
lean_dec(v_lam_1608_);
lean_dec(v_const_1606_);
lean_dec(v_sort_1605_);
lean_dec(v_mvar_1604_);
lean_dec(v_fvar_1603_);
lean_dec(v_bvar_1602_);
v_fn_1625_ = lean_ctor_get(v_t_1601_, 0);
lean_inc_ref(v_fn_1625_);
v_arg_1626_ = lean_ctor_get(v_t_1601_, 1);
lean_inc_ref(v_arg_1626_);
lean_dec_ref(v_t_1601_);
v___x_1627_ = lean_apply_2(v_app_1607_, v_fn_1625_, v_arg_1626_);
return v___x_1627_;
}
case 6:
{
lean_object* v_binderName_1628_; lean_object* v_binderType_1629_; lean_object* v_body_1630_; uint8_t v_binderInfo_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec(v_proj_1613_);
lean_dec(v_mdata_1612_);
lean_dec(v_lit_1611_);
lean_dec(v_letE_1610_);
lean_dec(v_forallE_1609_);
lean_dec(v_app_1607_);
lean_dec(v_const_1606_);
lean_dec(v_sort_1605_);
lean_dec(v_mvar_1604_);
lean_dec(v_fvar_1603_);
lean_dec(v_bvar_1602_);
v_binderName_1628_ = lean_ctor_get(v_t_1601_, 0);
lean_inc(v_binderName_1628_);
v_binderType_1629_ = lean_ctor_get(v_t_1601_, 1);
lean_inc_ref(v_binderType_1629_);
v_body_1630_ = lean_ctor_get(v_t_1601_, 2);
lean_inc_ref(v_body_1630_);
v_binderInfo_1631_ = lean_ctor_get_uint8(v_t_1601_, sizeof(void*)*3 + 8);
lean_dec_ref(v_t_1601_);
v___x_1632_ = lean_box(v_binderInfo_1631_);
v___x_1633_ = lean_apply_4(v_lam_1608_, v_binderName_1628_, v_binderType_1629_, v_body_1630_, v___x_1632_);
return v___x_1633_;
}
case 7:
{
lean_object* v_binderName_1634_; lean_object* v_binderType_1635_; lean_object* v_body_1636_; uint8_t v_binderInfo_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec(v_proj_1613_);
lean_dec(v_mdata_1612_);
lean_dec(v_lit_1611_);
lean_dec(v_letE_1610_);
lean_dec(v_lam_1608_);
lean_dec(v_app_1607_);
lean_dec(v_const_1606_);
lean_dec(v_sort_1605_);
lean_dec(v_mvar_1604_);
lean_dec(v_fvar_1603_);
lean_dec(v_bvar_1602_);
v_binderName_1634_ = lean_ctor_get(v_t_1601_, 0);
lean_inc(v_binderName_1634_);
v_binderType_1635_ = lean_ctor_get(v_t_1601_, 1);
lean_inc_ref(v_binderType_1635_);
v_body_1636_ = lean_ctor_get(v_t_1601_, 2);
lean_inc_ref(v_body_1636_);
v_binderInfo_1637_ = lean_ctor_get_uint8(v_t_1601_, sizeof(void*)*3 + 8);
lean_dec_ref(v_t_1601_);
v___x_1638_ = lean_box(v_binderInfo_1637_);
v___x_1639_ = lean_apply_4(v_forallE_1609_, v_binderName_1634_, v_binderType_1635_, v_body_1636_, v___x_1638_);
return v___x_1639_;
}
case 8:
{
lean_object* v_declName_1640_; lean_object* v_type_1641_; lean_object* v_value_1642_; lean_object* v_body_1643_; uint8_t v_nondep_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v_proj_1613_);
lean_dec(v_mdata_1612_);
lean_dec(v_lit_1611_);
lean_dec(v_forallE_1609_);
lean_dec(v_lam_1608_);
lean_dec(v_app_1607_);
lean_dec(v_const_1606_);
lean_dec(v_sort_1605_);
lean_dec(v_mvar_1604_);
lean_dec(v_fvar_1603_);
lean_dec(v_bvar_1602_);
v_declName_1640_ = lean_ctor_get(v_t_1601_, 0);
lean_inc(v_declName_1640_);
v_type_1641_ = lean_ctor_get(v_t_1601_, 1);
lean_inc_ref(v_type_1641_);
v_value_1642_ = lean_ctor_get(v_t_1601_, 2);
lean_inc_ref(v_value_1642_);
v_body_1643_ = lean_ctor_get(v_t_1601_, 3);
lean_inc_ref(v_body_1643_);
v_nondep_1644_ = lean_ctor_get_uint8(v_t_1601_, sizeof(void*)*4 + 8);
lean_dec_ref(v_t_1601_);
v___x_1645_ = lean_box(v_nondep_1644_);
v___x_1646_ = lean_apply_5(v_letE_1610_, v_declName_1640_, v_type_1641_, v_value_1642_, v_body_1643_, v___x_1645_);
return v___x_1646_;
}
case 9:
{
lean_object* v_a_1647_; lean_object* v___x_1648_; 
lean_dec(v_proj_1613_);
lean_dec(v_mdata_1612_);
lean_dec(v_letE_1610_);
lean_dec(v_forallE_1609_);
lean_dec(v_lam_1608_);
lean_dec(v_app_1607_);
lean_dec(v_const_1606_);
lean_dec(v_sort_1605_);
lean_dec(v_mvar_1604_);
lean_dec(v_fvar_1603_);
lean_dec(v_bvar_1602_);
v_a_1647_ = lean_ctor_get(v_t_1601_, 0);
lean_inc_ref(v_a_1647_);
lean_dec_ref(v_t_1601_);
v___x_1648_ = lean_apply_1(v_lit_1611_, v_a_1647_);
return v___x_1648_;
}
case 10:
{
lean_object* v_data_1649_; lean_object* v_expr_1650_; lean_object* v___x_1651_; 
lean_dec(v_proj_1613_);
lean_dec(v_lit_1611_);
lean_dec(v_letE_1610_);
lean_dec(v_forallE_1609_);
lean_dec(v_lam_1608_);
lean_dec(v_app_1607_);
lean_dec(v_const_1606_);
lean_dec(v_sort_1605_);
lean_dec(v_mvar_1604_);
lean_dec(v_fvar_1603_);
lean_dec(v_bvar_1602_);
v_data_1649_ = lean_ctor_get(v_t_1601_, 0);
lean_inc(v_data_1649_);
v_expr_1650_ = lean_ctor_get(v_t_1601_, 1);
lean_inc_ref(v_expr_1650_);
lean_dec_ref(v_t_1601_);
v___x_1651_ = lean_apply_2(v_mdata_1612_, v_data_1649_, v_expr_1650_);
return v___x_1651_;
}
default: 
{
lean_object* v_typeName_1652_; lean_object* v_idx_1653_; lean_object* v_struct_1654_; lean_object* v___x_1655_; 
lean_dec(v_mdata_1612_);
lean_dec(v_lit_1611_);
lean_dec(v_letE_1610_);
lean_dec(v_forallE_1609_);
lean_dec(v_lam_1608_);
lean_dec(v_app_1607_);
lean_dec(v_const_1606_);
lean_dec(v_sort_1605_);
lean_dec(v_mvar_1604_);
lean_dec(v_fvar_1603_);
lean_dec(v_bvar_1602_);
v_typeName_1652_ = lean_ctor_get(v_t_1601_, 0);
lean_inc(v_typeName_1652_);
v_idx_1653_ = lean_ctor_get(v_t_1601_, 1);
lean_inc(v_idx_1653_);
v_struct_1654_ = lean_ctor_get(v_t_1601_, 2);
lean_inc_ref(v_struct_1654_);
lean_dec_ref(v_t_1601_);
v___x_1655_ = lean_apply_3(v_proj_1613_, v_typeName_1652_, v_idx_1653_, v_struct_1654_);
return v___x_1655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* v_deBruijnIndex_1656_){
_start:
{
uint64_t v___x_1657_; uint64_t v___x_1658_; uint64_t v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; uint32_t v___x_1662_; uint8_t v___x_1663_; uint64_t v___x_1664_; lean_object* v___x_1665_; 
v___x_1657_ = 7ULL;
v___x_1658_ = lean_uint64_of_nat(v_deBruijnIndex_1656_);
v___x_1659_ = lean_uint64_mix_hash(v___x_1657_, v___x_1658_);
v___x_1660_ = lean_unsigned_to_nat(1u);
v___x_1661_ = lean_nat_add(v_deBruijnIndex_1656_, v___x_1660_);
v___x_1662_ = 0;
v___x_1663_ = 0;
v___x_1664_ = lean_expr_mk_data(v___x_1659_, v___x_1661_, v___x_1662_, v___x_1663_, v___x_1663_, v___x_1663_, v___x_1663_);
v___x_1665_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1665_, 0, v_deBruijnIndex_1656_);
lean_ctor_set_uint64(v___x_1665_, sizeof(void*)*1, v___x_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* v_fvarId_1666_){
_start:
{
uint64_t v___x_1667_; uint64_t v___x_1668_; uint64_t v___x_1669_; lean_object* v___x_1670_; uint32_t v___x_1671_; uint8_t v___x_1672_; uint8_t v___x_1673_; uint64_t v___x_1674_; lean_object* v___x_1675_; 
v___x_1667_ = 13ULL;
v___x_1668_ = l_Lean_instHashableFVarId_hash(v_fvarId_1666_);
v___x_1669_ = lean_uint64_mix_hash(v___x_1667_, v___x_1668_);
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = 0;
v___x_1672_ = 1;
v___x_1673_ = 0;
v___x_1674_ = lean_expr_mk_data(v___x_1669_, v___x_1670_, v___x_1671_, v___x_1672_, v___x_1673_, v___x_1673_, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_1675_, 0, v_fvarId_1666_);
lean_ctor_set_uint64(v___x_1675_, sizeof(void*)*1, v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* v_mvarId_1676_){
_start:
{
uint64_t v___x_1677_; uint64_t v___x_1678_; uint64_t v___x_1679_; lean_object* v___x_1680_; uint32_t v___x_1681_; uint8_t v___x_1682_; uint8_t v___x_1683_; uint64_t v___x_1684_; lean_object* v___x_1685_; 
v___x_1677_ = 17ULL;
v___x_1678_ = l_Lean_instHashableMVarId_hash(v_mvarId_1676_);
v___x_1679_ = lean_uint64_mix_hash(v___x_1677_, v___x_1678_);
v___x_1680_ = lean_unsigned_to_nat(0u);
v___x_1681_ = 0;
v___x_1682_ = 0;
v___x_1683_ = 1;
v___x_1684_ = lean_expr_mk_data(v___x_1679_, v___x_1680_, v___x_1681_, v___x_1682_, v___x_1683_, v___x_1682_, v___x_1682_);
v___x_1685_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_1685_, 0, v_mvarId_1676_);
lean_ctor_set_uint64(v___x_1685_, sizeof(void*)*1, v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* v_u_1686_){
_start:
{
uint64_t v___x_1687_; uint64_t v___x_1688_; uint64_t v___x_1689_; lean_object* v___x_1690_; uint32_t v___x_1691_; uint8_t v___x_1692_; uint8_t v___x_1693_; uint8_t v___x_1694_; uint64_t v___x_1695_; lean_object* v___x_1696_; 
v___x_1687_ = 11ULL;
v___x_1688_ = l_Lean_Level_hash(v_u_1686_);
v___x_1689_ = lean_uint64_mix_hash(v___x_1687_, v___x_1688_);
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = 0;
v___x_1692_ = 0;
v___x_1693_ = l_Lean_Level_hasMVar(v_u_1686_);
v___x_1694_ = l_Lean_Level_hasParam(v_u_1686_);
v___x_1695_ = lean_expr_mk_data(v___x_1689_, v___x_1690_, v___x_1691_, v___x_1692_, v___x_1692_, v___x_1693_, v___x_1694_);
v___x_1696_ = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(v___x_1696_, 0, v_u_1686_);
lean_ctor_set_uint64(v___x_1696_, sizeof(void*)*1, v___x_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* v_fn_1697_, lean_object* v_arg_1698_){
_start:
{
uint64_t v___x_1699_; uint64_t v___x_1700_; uint64_t v___x_1701_; lean_object* v___x_1702_; 
v___x_1699_ = lean_expr_data(v_fn_1697_);
v___x_1700_ = lean_expr_data(v_arg_1698_);
v___x_1701_ = lean_expr_mk_app_data(v___x_1699_, v___x_1700_);
v___x_1702_ = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(v___x_1702_, 0, v_fn_1697_);
lean_ctor_set(v___x_1702_, 1, v_arg_1698_);
lean_ctor_set_uint64(v___x_1702_, sizeof(void*)*2, v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object* v_binderName_1703_, lean_object* v_binderType_1704_, lean_object* v_body_1705_, uint8_t v_binderInfo_1706_){
_start:
{
lean_object* v___y_1708_; uint8_t v___y_1709_; uint32_t v___y_1710_; uint8_t v___y_1711_; uint64_t v___y_1712_; uint8_t v___y_1713_; uint8_t v___y_1714_; uint64_t v___x_1717_; uint8_t v___x_1718_; uint32_t v___x_1719_; uint64_t v___x_1720_; lean_object* v___y_1722_; uint32_t v___y_1723_; uint8_t v___y_1724_; uint8_t v___y_1725_; uint64_t v___y_1726_; uint8_t v___y_1727_; lean_object* v___y_1731_; uint32_t v___y_1732_; uint8_t v___y_1733_; uint64_t v___y_1734_; uint8_t v___y_1735_; lean_object* v___y_1739_; uint32_t v___y_1740_; uint64_t v___y_1741_; uint8_t v___y_1742_; uint32_t v___y_1746_; uint64_t v___y_1747_; lean_object* v___y_1748_; uint32_t v___y_1752_; uint8_t v___x_1767_; uint32_t v___x_1768_; uint8_t v___x_1769_; 
v___x_1717_ = lean_expr_data(v_binderType_1704_);
v___x_1718_ = l_Lean_Expr_Data_approxDepth(v___x_1717_);
v___x_1719_ = lean_uint8_to_uint32(v___x_1718_);
v___x_1720_ = lean_expr_data(v_body_1705_);
v___x_1767_ = l_Lean_Expr_Data_approxDepth(v___x_1720_);
v___x_1768_ = lean_uint8_to_uint32(v___x_1767_);
v___x_1769_ = lean_uint32_dec_le(v___x_1719_, v___x_1768_);
if (v___x_1769_ == 0)
{
v___y_1752_ = v___x_1719_;
goto v___jp_1751_;
}
else
{
v___y_1752_ = v___x_1768_;
goto v___jp_1751_;
}
v___jp_1707_:
{
uint64_t v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_expr_mk_data(v___y_1712_, v___y_1708_, v___y_1710_, v___y_1711_, v___y_1709_, v___y_1713_, v___y_1714_);
v___x_1716_ = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(v___x_1716_, 0, v_binderName_1703_);
lean_ctor_set(v___x_1716_, 1, v_binderType_1704_);
lean_ctor_set(v___x_1716_, 2, v_body_1705_);
lean_ctor_set_uint64(v___x_1716_, sizeof(void*)*3, v___x_1715_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*3 + 8, v_binderInfo_1706_);
return v___x_1716_;
}
v___jp_1721_:
{
uint8_t v___x_1728_; 
v___x_1728_ = l_Lean_Expr_Data_hasLevelParam(v___x_1717_);
if (v___x_1728_ == 0)
{
uint8_t v___x_1729_; 
v___x_1729_ = l_Lean_Expr_Data_hasLevelParam(v___x_1720_);
v___y_1708_ = v___y_1722_;
v___y_1709_ = v___y_1724_;
v___y_1710_ = v___y_1723_;
v___y_1711_ = v___y_1725_;
v___y_1712_ = v___y_1726_;
v___y_1713_ = v___y_1727_;
v___y_1714_ = v___x_1729_;
goto v___jp_1707_;
}
else
{
v___y_1708_ = v___y_1722_;
v___y_1709_ = v___y_1724_;
v___y_1710_ = v___y_1723_;
v___y_1711_ = v___y_1725_;
v___y_1712_ = v___y_1726_;
v___y_1713_ = v___y_1727_;
v___y_1714_ = v___x_1728_;
goto v___jp_1707_;
}
}
v___jp_1730_:
{
uint8_t v___x_1736_; 
v___x_1736_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1717_);
if (v___x_1736_ == 0)
{
uint8_t v___x_1737_; 
v___x_1737_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1720_);
v___y_1722_ = v___y_1731_;
v___y_1723_ = v___y_1732_;
v___y_1724_ = v___y_1735_;
v___y_1725_ = v___y_1733_;
v___y_1726_ = v___y_1734_;
v___y_1727_ = v___x_1737_;
goto v___jp_1721_;
}
else
{
v___y_1722_ = v___y_1731_;
v___y_1723_ = v___y_1732_;
v___y_1724_ = v___y_1735_;
v___y_1725_ = v___y_1733_;
v___y_1726_ = v___y_1734_;
v___y_1727_ = v___x_1736_;
goto v___jp_1721_;
}
}
v___jp_1738_:
{
uint8_t v___x_1743_; 
v___x_1743_ = l_Lean_Expr_Data_hasExprMVar(v___x_1717_);
if (v___x_1743_ == 0)
{
uint8_t v___x_1744_; 
v___x_1744_ = l_Lean_Expr_Data_hasExprMVar(v___x_1720_);
v___y_1731_ = v___y_1739_;
v___y_1732_ = v___y_1740_;
v___y_1733_ = v___y_1742_;
v___y_1734_ = v___y_1741_;
v___y_1735_ = v___x_1744_;
goto v___jp_1730_;
}
else
{
v___y_1731_ = v___y_1739_;
v___y_1732_ = v___y_1740_;
v___y_1733_ = v___y_1742_;
v___y_1734_ = v___y_1741_;
v___y_1735_ = v___x_1743_;
goto v___jp_1730_;
}
}
v___jp_1745_:
{
uint8_t v___x_1749_; 
v___x_1749_ = l_Lean_Expr_Data_hasFVar(v___x_1717_);
if (v___x_1749_ == 0)
{
uint8_t v___x_1750_; 
v___x_1750_ = l_Lean_Expr_Data_hasFVar(v___x_1720_);
v___y_1739_ = v___y_1748_;
v___y_1740_ = v___y_1746_;
v___y_1741_ = v___y_1747_;
v___y_1742_ = v___x_1750_;
goto v___jp_1738_;
}
else
{
v___y_1739_ = v___y_1748_;
v___y_1740_ = v___y_1746_;
v___y_1741_ = v___y_1747_;
v___y_1742_ = v___x_1749_;
goto v___jp_1738_;
}
}
v___jp_1751_:
{
lean_object* v___x_1753_; uint32_t v___x_1754_; uint32_t v___x_1755_; uint64_t v___x_1756_; uint64_t v___x_1757_; uint64_t v___x_1758_; uint64_t v___x_1759_; uint64_t v___x_1760_; uint32_t v___x_1761_; lean_object* v___x_1762_; uint32_t v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1753_ = lean_unsigned_to_nat(1u);
v___x_1754_ = 1;
v___x_1755_ = lean_uint32_add(v___y_1752_, v___x_1754_);
v___x_1756_ = lean_uint32_to_uint64(v___x_1755_);
v___x_1757_ = l_Lean_Expr_Data_hash(v___x_1717_);
v___x_1758_ = l_Lean_Expr_Data_hash(v___x_1720_);
v___x_1759_ = lean_uint64_mix_hash(v___x_1757_, v___x_1758_);
v___x_1760_ = lean_uint64_mix_hash(v___x_1756_, v___x_1759_);
v___x_1761_ = l_Lean_Expr_Data_looseBVarRange(v___x_1717_);
v___x_1762_ = lean_uint32_to_nat(v___x_1761_);
v___x_1763_ = l_Lean_Expr_Data_looseBVarRange(v___x_1720_);
v___x_1764_ = lean_uint32_to_nat(v___x_1763_);
v___x_1765_ = lean_nat_sub(v___x_1764_, v___x_1753_);
lean_dec(v___x_1764_);
v___x_1766_ = lean_nat_dec_le(v___x_1762_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_dec(v___x_1765_);
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1760_;
v___y_1748_ = v___x_1762_;
goto v___jp_1745_;
}
else
{
lean_dec(v___x_1762_);
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1760_;
v___y_1748_ = v___x_1765_;
goto v___jp_1745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* v_binderName_1770_, lean_object* v_binderType_1771_, lean_object* v_body_1772_, lean_object* v_binderInfo_1773_){
_start:
{
uint8_t v_binderInfo_boxed_1774_; lean_object* v_res_1775_; 
v_binderInfo_boxed_1774_ = lean_unbox(v_binderInfo_1773_);
v_res_1775_ = l_Lean_Expr_lam___override(v_binderName_1770_, v_binderType_1771_, v_body_1772_, v_binderInfo_boxed_1774_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object* v_binderName_1776_, lean_object* v_binderType_1777_, lean_object* v_body_1778_, uint8_t v_binderInfo_1779_){
_start:
{
lean_object* v___y_1781_; uint8_t v___y_1782_; uint64_t v___y_1783_; uint8_t v___y_1784_; uint8_t v___y_1785_; uint32_t v___y_1786_; uint8_t v___y_1787_; uint64_t v___x_1790_; uint8_t v___x_1791_; uint32_t v___x_1792_; uint64_t v___x_1793_; lean_object* v___y_1795_; uint8_t v___y_1796_; uint64_t v___y_1797_; uint8_t v___y_1798_; uint32_t v___y_1799_; uint8_t v___y_1800_; lean_object* v___y_1804_; uint8_t v___y_1805_; uint64_t v___y_1806_; uint32_t v___y_1807_; uint8_t v___y_1808_; lean_object* v___y_1812_; uint64_t v___y_1813_; uint32_t v___y_1814_; uint8_t v___y_1815_; uint64_t v___y_1819_; uint32_t v___y_1820_; lean_object* v___y_1821_; uint32_t v___y_1825_; uint8_t v___x_1840_; uint32_t v___x_1841_; uint8_t v___x_1842_; 
v___x_1790_ = lean_expr_data(v_binderType_1777_);
v___x_1791_ = l_Lean_Expr_Data_approxDepth(v___x_1790_);
v___x_1792_ = lean_uint8_to_uint32(v___x_1791_);
v___x_1793_ = lean_expr_data(v_body_1778_);
v___x_1840_ = l_Lean_Expr_Data_approxDepth(v___x_1793_);
v___x_1841_ = lean_uint8_to_uint32(v___x_1840_);
v___x_1842_ = lean_uint32_dec_le(v___x_1792_, v___x_1841_);
if (v___x_1842_ == 0)
{
v___y_1825_ = v___x_1792_;
goto v___jp_1824_;
}
else
{
v___y_1825_ = v___x_1841_;
goto v___jp_1824_;
}
v___jp_1780_:
{
uint64_t v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_expr_mk_data(v___y_1783_, v___y_1781_, v___y_1786_, v___y_1782_, v___y_1784_, v___y_1785_, v___y_1787_);
v___x_1789_ = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(v___x_1789_, 0, v_binderName_1776_);
lean_ctor_set(v___x_1789_, 1, v_binderType_1777_);
lean_ctor_set(v___x_1789_, 2, v_body_1778_);
lean_ctor_set_uint64(v___x_1789_, sizeof(void*)*3, v___x_1788_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*3 + 8, v_binderInfo_1779_);
return v___x_1789_;
}
v___jp_1794_:
{
uint8_t v___x_1801_; 
v___x_1801_ = l_Lean_Expr_Data_hasLevelParam(v___x_1790_);
if (v___x_1801_ == 0)
{
uint8_t v___x_1802_; 
v___x_1802_ = l_Lean_Expr_Data_hasLevelParam(v___x_1793_);
v___y_1781_ = v___y_1795_;
v___y_1782_ = v___y_1796_;
v___y_1783_ = v___y_1797_;
v___y_1784_ = v___y_1798_;
v___y_1785_ = v___y_1800_;
v___y_1786_ = v___y_1799_;
v___y_1787_ = v___x_1802_;
goto v___jp_1780_;
}
else
{
v___y_1781_ = v___y_1795_;
v___y_1782_ = v___y_1796_;
v___y_1783_ = v___y_1797_;
v___y_1784_ = v___y_1798_;
v___y_1785_ = v___y_1800_;
v___y_1786_ = v___y_1799_;
v___y_1787_ = v___x_1801_;
goto v___jp_1780_;
}
}
v___jp_1803_:
{
uint8_t v___x_1809_; 
v___x_1809_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1790_);
if (v___x_1809_ == 0)
{
uint8_t v___x_1810_; 
v___x_1810_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1793_);
v___y_1795_ = v___y_1804_;
v___y_1796_ = v___y_1805_;
v___y_1797_ = v___y_1806_;
v___y_1798_ = v___y_1808_;
v___y_1799_ = v___y_1807_;
v___y_1800_ = v___x_1810_;
goto v___jp_1794_;
}
else
{
v___y_1795_ = v___y_1804_;
v___y_1796_ = v___y_1805_;
v___y_1797_ = v___y_1806_;
v___y_1798_ = v___y_1808_;
v___y_1799_ = v___y_1807_;
v___y_1800_ = v___x_1809_;
goto v___jp_1794_;
}
}
v___jp_1811_:
{
uint8_t v___x_1816_; 
v___x_1816_ = l_Lean_Expr_Data_hasExprMVar(v___x_1790_);
if (v___x_1816_ == 0)
{
uint8_t v___x_1817_; 
v___x_1817_ = l_Lean_Expr_Data_hasExprMVar(v___x_1793_);
v___y_1804_ = v___y_1812_;
v___y_1805_ = v___y_1815_;
v___y_1806_ = v___y_1813_;
v___y_1807_ = v___y_1814_;
v___y_1808_ = v___x_1817_;
goto v___jp_1803_;
}
else
{
v___y_1804_ = v___y_1812_;
v___y_1805_ = v___y_1815_;
v___y_1806_ = v___y_1813_;
v___y_1807_ = v___y_1814_;
v___y_1808_ = v___x_1816_;
goto v___jp_1803_;
}
}
v___jp_1818_:
{
uint8_t v___x_1822_; 
v___x_1822_ = l_Lean_Expr_Data_hasFVar(v___x_1790_);
if (v___x_1822_ == 0)
{
uint8_t v___x_1823_; 
v___x_1823_ = l_Lean_Expr_Data_hasFVar(v___x_1793_);
v___y_1812_ = v___y_1821_;
v___y_1813_ = v___y_1819_;
v___y_1814_ = v___y_1820_;
v___y_1815_ = v___x_1823_;
goto v___jp_1811_;
}
else
{
v___y_1812_ = v___y_1821_;
v___y_1813_ = v___y_1819_;
v___y_1814_ = v___y_1820_;
v___y_1815_ = v___x_1822_;
goto v___jp_1811_;
}
}
v___jp_1824_:
{
lean_object* v___x_1826_; uint32_t v___x_1827_; uint32_t v___x_1828_; uint64_t v___x_1829_; uint64_t v___x_1830_; uint64_t v___x_1831_; uint64_t v___x_1832_; uint64_t v___x_1833_; uint32_t v___x_1834_; lean_object* v___x_1835_; uint32_t v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1826_ = lean_unsigned_to_nat(1u);
v___x_1827_ = 1;
v___x_1828_ = lean_uint32_add(v___y_1825_, v___x_1827_);
v___x_1829_ = lean_uint32_to_uint64(v___x_1828_);
v___x_1830_ = l_Lean_Expr_Data_hash(v___x_1790_);
v___x_1831_ = l_Lean_Expr_Data_hash(v___x_1793_);
v___x_1832_ = lean_uint64_mix_hash(v___x_1830_, v___x_1831_);
v___x_1833_ = lean_uint64_mix_hash(v___x_1829_, v___x_1832_);
v___x_1834_ = l_Lean_Expr_Data_looseBVarRange(v___x_1790_);
v___x_1835_ = lean_uint32_to_nat(v___x_1834_);
v___x_1836_ = l_Lean_Expr_Data_looseBVarRange(v___x_1793_);
v___x_1837_ = lean_uint32_to_nat(v___x_1836_);
v___x_1838_ = lean_nat_sub(v___x_1837_, v___x_1826_);
lean_dec(v___x_1837_);
v___x_1839_ = lean_nat_dec_le(v___x_1835_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_dec(v___x_1838_);
v___y_1819_ = v___x_1833_;
v___y_1820_ = v___x_1828_;
v___y_1821_ = v___x_1835_;
goto v___jp_1818_;
}
else
{
lean_dec(v___x_1835_);
v___y_1819_ = v___x_1833_;
v___y_1820_ = v___x_1828_;
v___y_1821_ = v___x_1838_;
goto v___jp_1818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* v_binderName_1843_, lean_object* v_binderType_1844_, lean_object* v_body_1845_, lean_object* v_binderInfo_1846_){
_start:
{
uint8_t v_binderInfo_boxed_1847_; lean_object* v_res_1848_; 
v_binderInfo_boxed_1847_ = lean_unbox(v_binderInfo_1846_);
v_res_1848_ = l_Lean_Expr_forallE___override(v_binderName_1843_, v_binderType_1844_, v_body_1845_, v_binderInfo_boxed_1847_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object* v_declName_1849_, lean_object* v_type_1850_, lean_object* v_value_1851_, lean_object* v_body_1852_, uint8_t v_nondep_1853_){
_start:
{
uint8_t v___y_1855_; uint64_t v___y_1856_; uint32_t v___y_1857_; uint8_t v___y_1858_; uint8_t v___y_1859_; lean_object* v___y_1860_; uint8_t v___y_1861_; uint64_t v___y_1865_; uint8_t v___y_1866_; uint32_t v___y_1867_; uint8_t v___y_1868_; uint8_t v___y_1869_; lean_object* v___y_1870_; uint64_t v___y_1871_; uint8_t v___y_1872_; uint64_t v___x_1874_; uint8_t v___x_1875_; uint32_t v___x_1876_; uint64_t v___x_1877_; uint64_t v___y_1879_; uint8_t v___y_1880_; uint32_t v___y_1881_; uint8_t v___y_1882_; lean_object* v___y_1883_; uint64_t v___y_1884_; uint8_t v___y_1885_; uint8_t v___y_1889_; uint64_t v___y_1890_; uint32_t v___y_1891_; uint8_t v___y_1892_; lean_object* v___y_1893_; uint64_t v___y_1894_; uint8_t v___y_1895_; uint8_t v___y_1898_; uint64_t v___y_1899_; uint32_t v___y_1900_; lean_object* v___y_1901_; uint64_t v___y_1902_; uint8_t v___y_1903_; uint64_t v___y_1907_; uint8_t v___y_1908_; uint32_t v___y_1909_; lean_object* v___y_1910_; uint64_t v___y_1911_; uint8_t v___y_1912_; uint64_t v___y_1915_; uint32_t v___y_1916_; lean_object* v___y_1917_; uint64_t v___y_1918_; uint8_t v___y_1919_; uint64_t v___y_1923_; uint32_t v___y_1924_; lean_object* v___y_1925_; uint64_t v___y_1926_; uint8_t v___y_1927_; uint64_t v___y_1930_; uint32_t v___y_1931_; uint64_t v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1937_; uint64_t v___y_1938_; uint32_t v___y_1939_; uint64_t v___y_1940_; lean_object* v___y_1941_; uint64_t v___y_1947_; uint32_t v___y_1948_; uint32_t v___y_1965_; uint8_t v___x_1970_; uint32_t v___x_1971_; uint8_t v___x_1972_; 
v___x_1874_ = lean_expr_data(v_type_1850_);
v___x_1875_ = l_Lean_Expr_Data_approxDepth(v___x_1874_);
v___x_1876_ = lean_uint8_to_uint32(v___x_1875_);
v___x_1877_ = lean_expr_data(v_value_1851_);
v___x_1970_ = l_Lean_Expr_Data_approxDepth(v___x_1877_);
v___x_1971_ = lean_uint8_to_uint32(v___x_1970_);
v___x_1972_ = lean_uint32_dec_le(v___x_1876_, v___x_1971_);
if (v___x_1972_ == 0)
{
v___y_1965_ = v___x_1876_;
goto v___jp_1964_;
}
else
{
v___y_1965_ = v___x_1971_;
goto v___jp_1964_;
}
v___jp_1854_:
{
uint64_t v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_expr_mk_data(v___y_1856_, v___y_1860_, v___y_1857_, v___y_1855_, v___y_1859_, v___y_1858_, v___y_1861_);
v___x_1863_ = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(v___x_1863_, 0, v_declName_1849_);
lean_ctor_set(v___x_1863_, 1, v_type_1850_);
lean_ctor_set(v___x_1863_, 2, v_value_1851_);
lean_ctor_set(v___x_1863_, 3, v_body_1852_);
lean_ctor_set_uint64(v___x_1863_, sizeof(void*)*4, v___x_1862_);
lean_ctor_set_uint8(v___x_1863_, sizeof(void*)*4 + 8, v_nondep_1853_);
return v___x_1863_;
}
v___jp_1864_:
{
if (v___y_1872_ == 0)
{
uint8_t v___x_1873_; 
v___x_1873_ = l_Lean_Expr_Data_hasLevelParam(v___y_1871_);
v___y_1855_ = v___y_1866_;
v___y_1856_ = v___y_1865_;
v___y_1857_ = v___y_1867_;
v___y_1858_ = v___y_1868_;
v___y_1859_ = v___y_1869_;
v___y_1860_ = v___y_1870_;
v___y_1861_ = v___x_1873_;
goto v___jp_1854_;
}
else
{
v___y_1855_ = v___y_1866_;
v___y_1856_ = v___y_1865_;
v___y_1857_ = v___y_1867_;
v___y_1858_ = v___y_1868_;
v___y_1859_ = v___y_1869_;
v___y_1860_ = v___y_1870_;
v___y_1861_ = v___y_1872_;
goto v___jp_1854_;
}
}
v___jp_1878_:
{
uint8_t v___x_1886_; 
v___x_1886_ = l_Lean_Expr_Data_hasLevelParam(v___x_1874_);
if (v___x_1886_ == 0)
{
uint8_t v___x_1887_; 
v___x_1887_ = l_Lean_Expr_Data_hasLevelParam(v___x_1877_);
v___y_1865_ = v___y_1879_;
v___y_1866_ = v___y_1880_;
v___y_1867_ = v___y_1881_;
v___y_1868_ = v___y_1885_;
v___y_1869_ = v___y_1882_;
v___y_1870_ = v___y_1883_;
v___y_1871_ = v___y_1884_;
v___y_1872_ = v___x_1887_;
goto v___jp_1864_;
}
else
{
v___y_1865_ = v___y_1879_;
v___y_1866_ = v___y_1880_;
v___y_1867_ = v___y_1881_;
v___y_1868_ = v___y_1885_;
v___y_1869_ = v___y_1882_;
v___y_1870_ = v___y_1883_;
v___y_1871_ = v___y_1884_;
v___y_1872_ = v___x_1886_;
goto v___jp_1864_;
}
}
v___jp_1888_:
{
if (v___y_1895_ == 0)
{
uint8_t v___x_1896_; 
v___x_1896_ = l_Lean_Expr_Data_hasLevelMVar(v___y_1894_);
v___y_1879_ = v___y_1890_;
v___y_1880_ = v___y_1889_;
v___y_1881_ = v___y_1891_;
v___y_1882_ = v___y_1892_;
v___y_1883_ = v___y_1893_;
v___y_1884_ = v___y_1894_;
v___y_1885_ = v___x_1896_;
goto v___jp_1878_;
}
else
{
v___y_1879_ = v___y_1890_;
v___y_1880_ = v___y_1889_;
v___y_1881_ = v___y_1891_;
v___y_1882_ = v___y_1892_;
v___y_1883_ = v___y_1893_;
v___y_1884_ = v___y_1894_;
v___y_1885_ = v___y_1895_;
goto v___jp_1878_;
}
}
v___jp_1897_:
{
uint8_t v___x_1904_; 
v___x_1904_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1874_);
if (v___x_1904_ == 0)
{
uint8_t v___x_1905_; 
v___x_1905_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1877_);
v___y_1889_ = v___y_1898_;
v___y_1890_ = v___y_1899_;
v___y_1891_ = v___y_1900_;
v___y_1892_ = v___y_1903_;
v___y_1893_ = v___y_1901_;
v___y_1894_ = v___y_1902_;
v___y_1895_ = v___x_1905_;
goto v___jp_1888_;
}
else
{
v___y_1889_ = v___y_1898_;
v___y_1890_ = v___y_1899_;
v___y_1891_ = v___y_1900_;
v___y_1892_ = v___y_1903_;
v___y_1893_ = v___y_1901_;
v___y_1894_ = v___y_1902_;
v___y_1895_ = v___x_1904_;
goto v___jp_1888_;
}
}
v___jp_1906_:
{
if (v___y_1912_ == 0)
{
uint8_t v___x_1913_; 
v___x_1913_ = l_Lean_Expr_Data_hasExprMVar(v___y_1911_);
v___y_1898_ = v___y_1908_;
v___y_1899_ = v___y_1907_;
v___y_1900_ = v___y_1909_;
v___y_1901_ = v___y_1910_;
v___y_1902_ = v___y_1911_;
v___y_1903_ = v___x_1913_;
goto v___jp_1897_;
}
else
{
v___y_1898_ = v___y_1908_;
v___y_1899_ = v___y_1907_;
v___y_1900_ = v___y_1909_;
v___y_1901_ = v___y_1910_;
v___y_1902_ = v___y_1911_;
v___y_1903_ = v___y_1912_;
goto v___jp_1897_;
}
}
v___jp_1914_:
{
uint8_t v___x_1920_; 
v___x_1920_ = l_Lean_Expr_Data_hasExprMVar(v___x_1874_);
if (v___x_1920_ == 0)
{
uint8_t v___x_1921_; 
v___x_1921_ = l_Lean_Expr_Data_hasExprMVar(v___x_1877_);
v___y_1907_ = v___y_1915_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1916_;
v___y_1910_ = v___y_1917_;
v___y_1911_ = v___y_1918_;
v___y_1912_ = v___x_1921_;
goto v___jp_1906_;
}
else
{
v___y_1907_ = v___y_1915_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1916_;
v___y_1910_ = v___y_1917_;
v___y_1911_ = v___y_1918_;
v___y_1912_ = v___x_1920_;
goto v___jp_1906_;
}
}
v___jp_1922_:
{
if (v___y_1927_ == 0)
{
uint8_t v___x_1928_; 
v___x_1928_ = l_Lean_Expr_Data_hasFVar(v___y_1926_);
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
v___y_1919_ = v___y_1927_;
goto v___jp_1914_;
}
}
v___jp_1929_:
{
uint8_t v___x_1934_; 
v___x_1934_ = l_Lean_Expr_Data_hasFVar(v___x_1874_);
if (v___x_1934_ == 0)
{
uint8_t v___x_1935_; 
v___x_1935_ = l_Lean_Expr_Data_hasFVar(v___x_1877_);
v___y_1923_ = v___y_1930_;
v___y_1924_ = v___y_1931_;
v___y_1925_ = v___y_1933_;
v___y_1926_ = v___y_1932_;
v___y_1927_ = v___x_1935_;
goto v___jp_1922_;
}
else
{
v___y_1923_ = v___y_1930_;
v___y_1924_ = v___y_1931_;
v___y_1925_ = v___y_1933_;
v___y_1926_ = v___y_1932_;
v___y_1927_ = v___x_1934_;
goto v___jp_1922_;
}
}
v___jp_1936_:
{
uint32_t v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1942_ = l_Lean_Expr_Data_looseBVarRange(v___y_1940_);
v___x_1943_ = lean_uint32_to_nat(v___x_1942_);
v___x_1944_ = lean_nat_sub(v___x_1943_, v___y_1937_);
lean_dec(v___x_1943_);
v___x_1945_ = lean_nat_dec_le(v___y_1941_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_dec(v___x_1944_);
v___y_1930_ = v___y_1938_;
v___y_1931_ = v___y_1939_;
v___y_1932_ = v___y_1940_;
v___y_1933_ = v___y_1941_;
goto v___jp_1929_;
}
else
{
lean_dec(v___y_1941_);
v___y_1930_ = v___y_1938_;
v___y_1931_ = v___y_1939_;
v___y_1932_ = v___y_1940_;
v___y_1933_ = v___x_1944_;
goto v___jp_1929_;
}
}
v___jp_1946_:
{
lean_object* v___x_1949_; uint32_t v___x_1950_; uint32_t v___x_1951_; uint64_t v___x_1952_; uint64_t v___x_1953_; uint64_t v___x_1954_; uint64_t v___x_1955_; uint64_t v___x_1956_; uint64_t v___x_1957_; uint64_t v___x_1958_; uint32_t v___x_1959_; lean_object* v___x_1960_; uint32_t v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1949_ = lean_unsigned_to_nat(1u);
v___x_1950_ = 1;
v___x_1951_ = lean_uint32_add(v___y_1948_, v___x_1950_);
v___x_1952_ = lean_uint32_to_uint64(v___x_1951_);
v___x_1953_ = l_Lean_Expr_Data_hash(v___x_1874_);
v___x_1954_ = l_Lean_Expr_Data_hash(v___x_1877_);
v___x_1955_ = l_Lean_Expr_Data_hash(v___y_1947_);
v___x_1956_ = lean_uint64_mix_hash(v___x_1954_, v___x_1955_);
v___x_1957_ = lean_uint64_mix_hash(v___x_1953_, v___x_1956_);
v___x_1958_ = lean_uint64_mix_hash(v___x_1952_, v___x_1957_);
v___x_1959_ = l_Lean_Expr_Data_looseBVarRange(v___x_1874_);
v___x_1960_ = lean_uint32_to_nat(v___x_1959_);
v___x_1961_ = l_Lean_Expr_Data_looseBVarRange(v___x_1877_);
v___x_1962_ = lean_uint32_to_nat(v___x_1961_);
v___x_1963_ = lean_nat_dec_le(v___x_1960_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_dec(v___x_1962_);
v___y_1937_ = v___x_1949_;
v___y_1938_ = v___x_1958_;
v___y_1939_ = v___x_1951_;
v___y_1940_ = v___y_1947_;
v___y_1941_ = v___x_1960_;
goto v___jp_1936_;
}
else
{
lean_dec(v___x_1960_);
v___y_1937_ = v___x_1949_;
v___y_1938_ = v___x_1958_;
v___y_1939_ = v___x_1951_;
v___y_1940_ = v___y_1947_;
v___y_1941_ = v___x_1962_;
goto v___jp_1936_;
}
}
v___jp_1964_:
{
uint64_t v___x_1966_; uint8_t v___x_1967_; uint32_t v___x_1968_; uint8_t v___x_1969_; 
v___x_1966_ = lean_expr_data(v_body_1852_);
v___x_1967_ = l_Lean_Expr_Data_approxDepth(v___x_1966_);
v___x_1968_ = lean_uint8_to_uint32(v___x_1967_);
v___x_1969_ = lean_uint32_dec_le(v___y_1965_, v___x_1968_);
if (v___x_1969_ == 0)
{
v___y_1947_ = v___x_1966_;
v___y_1948_ = v___y_1965_;
goto v___jp_1946_;
}
else
{
v___y_1947_ = v___x_1966_;
v___y_1948_ = v___x_1968_;
goto v___jp_1946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* v_declName_1973_, lean_object* v_type_1974_, lean_object* v_value_1975_, lean_object* v_body_1976_, lean_object* v_nondep_1977_){
_start:
{
uint8_t v_nondep_boxed_1978_; lean_object* v_res_1979_; 
v_nondep_boxed_1978_ = lean_unbox(v_nondep_1977_);
v_res_1979_ = l_Lean_Expr_letE___override(v_declName_1973_, v_type_1974_, v_value_1975_, v_body_1976_, v_nondep_boxed_1978_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* v_a_1980_){
_start:
{
uint64_t v___x_1981_; uint64_t v___x_1982_; uint64_t v___x_1983_; lean_object* v___x_1984_; uint32_t v___x_1985_; uint8_t v___x_1986_; uint64_t v___x_1987_; lean_object* v___x_1988_; 
v___x_1981_ = 3ULL;
v___x_1982_ = l_Lean_Literal_hash(v_a_1980_);
v___x_1983_ = lean_uint64_mix_hash(v___x_1981_, v___x_1982_);
v___x_1984_ = lean_unsigned_to_nat(0u);
v___x_1985_ = 0;
v___x_1986_ = 0;
v___x_1987_ = lean_expr_mk_data(v___x_1983_, v___x_1984_, v___x_1985_, v___x_1986_, v___x_1986_, v___x_1986_, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(v___x_1988_, 0, v_a_1980_);
lean_ctor_set_uint64(v___x_1988_, sizeof(void*)*1, v___x_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* v_data_1989_, lean_object* v_expr_1990_){
_start:
{
uint64_t v___x_1991_; uint8_t v___x_1992_; uint32_t v___x_1993_; uint32_t v___x_1994_; uint32_t v___x_1995_; uint64_t v___x_1996_; uint64_t v___x_1997_; uint64_t v___x_1998_; uint32_t v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; uint8_t v___x_2002_; uint8_t v___x_2003_; uint8_t v___x_2004_; uint64_t v___x_2005_; lean_object* v___x_2006_; 
v___x_1991_ = lean_expr_data(v_expr_1990_);
v___x_1992_ = l_Lean_Expr_Data_approxDepth(v___x_1991_);
v___x_1993_ = lean_uint8_to_uint32(v___x_1992_);
v___x_1994_ = 1;
v___x_1995_ = lean_uint32_add(v___x_1993_, v___x_1994_);
v___x_1996_ = lean_uint32_to_uint64(v___x_1995_);
v___x_1997_ = l_Lean_Expr_Data_hash(v___x_1991_);
v___x_1998_ = lean_uint64_mix_hash(v___x_1996_, v___x_1997_);
v___x_1999_ = l_Lean_Expr_Data_looseBVarRange(v___x_1991_);
v___x_2000_ = lean_uint32_to_nat(v___x_1999_);
v___x_2001_ = l_Lean_Expr_Data_hasFVar(v___x_1991_);
v___x_2002_ = l_Lean_Expr_Data_hasExprMVar(v___x_1991_);
v___x_2003_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1991_);
v___x_2004_ = l_Lean_Expr_Data_hasLevelParam(v___x_1991_);
v___x_2005_ = lean_expr_mk_data(v___x_1998_, v___x_2000_, v___x_1995_, v___x_2001_, v___x_2002_, v___x_2003_, v___x_2004_);
v___x_2006_ = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(v___x_2006_, 0, v_data_1989_);
lean_ctor_set(v___x_2006_, 1, v_expr_1990_);
lean_ctor_set_uint64(v___x_2006_, sizeof(void*)*2, v___x_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* v_typeName_2007_, lean_object* v_idx_2008_, lean_object* v_struct_2009_){
_start:
{
uint64_t v___x_2010_; uint8_t v___x_2011_; uint32_t v___x_2012_; uint32_t v___x_2013_; uint32_t v___x_2014_; uint64_t v___x_2015_; uint64_t v___y_2017_; 
v___x_2010_ = lean_expr_data(v_struct_2009_);
v___x_2011_ = l_Lean_Expr_Data_approxDepth(v___x_2010_);
v___x_2012_ = lean_uint8_to_uint32(v___x_2011_);
v___x_2013_ = 1;
v___x_2014_ = lean_uint32_add(v___x_2012_, v___x_2013_);
v___x_2015_ = lean_uint32_to_uint64(v___x_2014_);
if (lean_obj_tag(v_typeName_2007_) == 0)
{
uint64_t v___x_2031_; 
v___x_2031_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
v___y_2017_ = v___x_2031_;
goto v___jp_2016_;
}
else
{
uint64_t v_hash_2032_; 
v_hash_2032_ = lean_ctor_get_uint64(v_typeName_2007_, sizeof(void*)*2);
v___y_2017_ = v_hash_2032_;
goto v___jp_2016_;
}
v___jp_2016_:
{
uint64_t v___x_2018_; uint64_t v___x_2019_; uint64_t v___x_2020_; uint64_t v___x_2021_; uint64_t v___x_2022_; uint32_t v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; uint8_t v___x_2026_; uint8_t v___x_2027_; uint8_t v___x_2028_; uint64_t v___x_2029_; lean_object* v___x_2030_; 
v___x_2018_ = lean_uint64_of_nat(v_idx_2008_);
v___x_2019_ = l_Lean_Expr_Data_hash(v___x_2010_);
v___x_2020_ = lean_uint64_mix_hash(v___x_2018_, v___x_2019_);
v___x_2021_ = lean_uint64_mix_hash(v___y_2017_, v___x_2020_);
v___x_2022_ = lean_uint64_mix_hash(v___x_2015_, v___x_2021_);
v___x_2023_ = l_Lean_Expr_Data_looseBVarRange(v___x_2010_);
v___x_2024_ = lean_uint32_to_nat(v___x_2023_);
v___x_2025_ = l_Lean_Expr_Data_hasFVar(v___x_2010_);
v___x_2026_ = l_Lean_Expr_Data_hasExprMVar(v___x_2010_);
v___x_2027_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2010_);
v___x_2028_ = l_Lean_Expr_Data_hasLevelParam(v___x_2010_);
v___x_2029_ = lean_expr_mk_data(v___x_2022_, v___x_2024_, v___x_2014_, v___x_2025_, v___x_2026_, v___x_2027_, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(v___x_2030_, 0, v_typeName_2007_);
lean_ctor_set(v___x_2030_, 1, v_idx_2008_);
lean_ctor_set(v___x_2030_, 2, v_struct_2009_);
lean_ctor_set_uint64(v___x_2030_, sizeof(void*)*3, v___x_2029_);
return v___x_2030_;
}
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t v_x_2033_, lean_object* v_x_2034_){
_start:
{
if (lean_obj_tag(v_x_2034_) == 0)
{
return v_x_2033_;
}
else
{
lean_object* v_head_2035_; lean_object* v_tail_2036_; uint64_t v___x_2037_; uint64_t v___x_2038_; 
v_head_2035_ = lean_ctor_get(v_x_2034_, 0);
v_tail_2036_ = lean_ctor_get(v_x_2034_, 1);
v___x_2037_ = l_Lean_Level_hash(v_head_2035_);
v___x_2038_ = lean_uint64_mix_hash(v_x_2033_, v___x_2037_);
v_x_2033_ = v___x_2038_;
v_x_2034_ = v_tail_2036_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object* v_x_2040_, lean_object* v_x_2041_){
_start:
{
uint64_t v_x_1680__boxed_2042_; uint64_t v_res_2043_; lean_object* v_r_2044_; 
v_x_1680__boxed_2042_ = lean_unbox_uint64(v_x_2040_);
lean_dec_ref(v_x_2040_);
v_res_2043_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_1680__boxed_2042_, v_x_2041_);
lean_dec(v_x_2041_);
v_r_2044_ = lean_box_uint64(v_res_2043_);
return v_r_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* v_declName_2047_, lean_object* v_us_2048_){
_start:
{
uint64_t v___x_2049_; uint64_t v___y_2051_; 
v___x_2049_ = 5ULL;
if (lean_obj_tag(v_declName_2047_) == 0)
{
uint64_t v___x_2065_; 
v___x_2065_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
v___y_2051_ = v___x_2065_;
goto v___jp_2050_;
}
else
{
uint64_t v_hash_2066_; 
v_hash_2066_ = lean_ctor_get_uint64(v_declName_2047_, sizeof(void*)*2);
v___y_2051_ = v_hash_2066_;
goto v___jp_2050_;
}
v___jp_2050_:
{
uint64_t v___x_2052_; uint64_t v___x_2053_; uint64_t v___x_2054_; uint64_t v___x_2055_; lean_object* v___x_2056_; uint32_t v___x_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; uint64_t v___x_2063_; lean_object* v___x_2064_; 
v___x_2052_ = 7ULL;
v___x_2053_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v___x_2052_, v_us_2048_);
v___x_2054_ = lean_uint64_mix_hash(v___y_2051_, v___x_2053_);
v___x_2055_ = lean_uint64_mix_hash(v___x_2049_, v___x_2054_);
v___x_2056_ = lean_unsigned_to_nat(0u);
v___x_2057_ = 0;
v___x_2058_ = 0;
v___x_2059_ = ((lean_object*)(l_Lean_Expr_const___override___closed__0));
lean_inc(v_us_2048_);
v___x_2060_ = l_List_any___redArg(v_us_2048_, v___x_2059_);
v___x_2061_ = ((lean_object*)(l_Lean_Expr_const___override___closed__1));
lean_inc(v_us_2048_);
v___x_2062_ = l_List_any___redArg(v_us_2048_, v___x_2061_);
v___x_2063_ = lean_expr_mk_data(v___x_2055_, v___x_2056_, v___x_2057_, v___x_2058_, v___x_2058_, v___x_2060_, v___x_2062_);
v___x_2064_ = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(v___x_2064_, 0, v_declName_2047_);
lean_ctor_set(v___x_2064_, 1, v_us_2048_);
lean_ctor_set_uint64(v___x_2064_, sizeof(void*)*2, v___x_2063_);
return v___x_2064_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object* v___y_2067_){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_unsigned_to_nat(0u);
v___x_2069_ = l_Lean_instReprLevel_repr(v___y_2067_, v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_){
_start:
{
if (lean_obj_tag(v_x_2072_) == 0)
{
lean_dec(v_x_2070_);
return v_x_2071_;
}
else
{
lean_object* v_head_2073_; lean_object* v_tail_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2085_; 
v_head_2073_ = lean_ctor_get(v_x_2072_, 0);
v_tail_2074_ = lean_ctor_get(v_x_2072_, 1);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_x_2072_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2076_ = v_x_2072_;
v_isShared_2077_ = v_isSharedCheck_2085_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_tail_2074_);
lean_inc(v_head_2073_);
lean_dec(v_x_2072_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2085_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
lean_inc(v_x_2070_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set_tag(v___x_2076_, 5);
lean_ctor_set(v___x_2076_, 1, v_x_2070_);
lean_ctor_set(v___x_2076_, 0, v_x_2071_);
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_x_2071_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_x_2070_);
v___x_2079_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = l_Lean_instReprLevel_repr(v_head_2073_, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2079_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v_x_2071_ = v___x_2082_;
v_x_2072_ = v_tail_2074_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object* v_x_2086_, lean_object* v_x_2087_, lean_object* v_x_2088_){
_start:
{
if (lean_obj_tag(v_x_2088_) == 0)
{
lean_dec(v_x_2086_);
return v_x_2087_;
}
else
{
lean_object* v_head_2089_; lean_object* v_tail_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2101_; 
v_head_2089_ = lean_ctor_get(v_x_2088_, 0);
v_tail_2090_ = lean_ctor_get(v_x_2088_, 1);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_x_2088_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2092_ = v_x_2088_;
v_isShared_2093_ = v_isSharedCheck_2101_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_tail_2090_);
lean_inc(v_head_2089_);
lean_dec(v_x_2088_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2101_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
lean_inc(v_x_2086_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 5);
lean_ctor_set(v___x_2092_, 1, v_x_2086_);
lean_ctor_set(v___x_2092_, 0, v_x_2087_);
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_x_2087_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_x_2086_);
v___x_2095_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2096_ = lean_unsigned_to_nat(0u);
v___x_2097_ = l_Lean_instReprLevel_repr(v_head_2089_, v___x_2096_);
v___x_2098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2095_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(v_x_2086_, v___x_2098_, v_tail_2090_);
return v___x_2099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object* v_x_2102_, lean_object* v_x_2103_){
_start:
{
if (lean_obj_tag(v_x_2102_) == 0)
{
lean_object* v___x_2104_; 
lean_dec(v_x_2103_);
v___x_2104_ = lean_box(0);
return v___x_2104_;
}
else
{
lean_object* v_tail_2105_; 
v_tail_2105_ = lean_ctor_get(v_x_2102_, 1);
if (lean_obj_tag(v_tail_2105_) == 0)
{
lean_object* v_head_2106_; lean_object* v___x_2107_; 
lean_dec(v_x_2103_);
v_head_2106_ = lean_ctor_get(v_x_2102_, 0);
lean_inc(v_head_2106_);
lean_dec_ref(v_x_2102_);
v___x_2107_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2106_);
return v___x_2107_;
}
else
{
lean_object* v_head_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_inc(v_tail_2105_);
v_head_2108_ = lean_ctor_get(v_x_2102_, 0);
lean_inc(v_head_2108_);
lean_dec_ref(v_x_2102_);
v___x_2109_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2108_);
v___x_2110_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(v_x_2103_, v___x_2109_, v_tail_2105_);
return v___x_2110_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2));
v___x_2123_ = lean_string_length(v___x_2122_);
return v___x_2123_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7);
v___x_2125_ = lean_nat_to_int(v___x_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object* v_a_2130_){
_start:
{
if (lean_obj_tag(v_a_2130_) == 0)
{
lean_object* v___x_2131_; 
v___x_2131_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1));
return v___x_2131_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; 
v___x_2132_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5));
v___x_2133_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(v_a_2130_, v___x_2132_);
v___x_2134_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8);
v___x_2135_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9));
v___x_2136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v___x_2133_);
v___x_2137_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10));
v___x_2138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2136_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2134_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = 0;
v___x_2141_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*1, v___x_2140_);
return v___x_2141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object* v_x_2214_, lean_object* v_prec_2215_){
_start:
{
switch(lean_obj_tag(v_x_2214_))
{
case 0:
{
lean_object* v_deBruijnIndex_2216_; lean_object* v___y_2218_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v_deBruijnIndex_2216_ = lean_ctor_get(v_x_2214_, 0);
lean_inc(v_deBruijnIndex_2216_);
lean_dec_ref(v_x_2214_);
v___x_2227_ = lean_unsigned_to_nat(1024u);
v___x_2228_ = lean_nat_dec_le(v___x_2227_, v_prec_2215_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2218_ = v___x_2229_;
goto v___jp_2217_;
}
else
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2218_ = v___x_2230_;
goto v___jp_2217_;
}
v___jp_2217_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2219_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__2));
v___x_2220_ = l_Nat_reprFast(v_deBruijnIndex_2216_);
v___x_2221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
v___x_2222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2219_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___y_2218_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = 0;
v___x_2225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2225_, 0, v___x_2223_);
lean_ctor_set_uint8(v___x_2225_, sizeof(void*)*1, v___x_2224_);
v___x_2226_ = l_Repr_addAppParen(v___x_2225_, v_prec_2215_);
return v___x_2226_;
}
}
case 1:
{
lean_object* v_fvarId_2231_; lean_object* v___y_2233_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v_fvarId_2231_ = lean_ctor_get(v_x_2214_, 0);
lean_inc(v_fvarId_2231_);
lean_dec_ref(v_x_2214_);
v___x_2242_ = lean_unsigned_to_nat(1024u);
v___x_2243_ = lean_nat_dec_le(v___x_2242_, v_prec_2215_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; 
v___x_2244_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2233_ = v___x_2244_;
goto v___jp_2232_;
}
else
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2233_ = v___x_2245_;
goto v___jp_2232_;
}
v___jp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2234_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__5));
v___x_2235_ = lean_unsigned_to_nat(1024u);
v___x_2236_ = l_Lean_Name_reprPrec(v_fvarId_2231_, v___x_2235_);
v___x_2237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2234_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___y_2233_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = 0;
v___x_2240_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2240_, 0, v___x_2238_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*1, v___x_2239_);
v___x_2241_ = l_Repr_addAppParen(v___x_2240_, v_prec_2215_);
return v___x_2241_;
}
}
case 2:
{
lean_object* v_mvarId_2246_; lean_object* v___y_2248_; lean_object* v___x_2257_; uint8_t v___x_2258_; 
v_mvarId_2246_ = lean_ctor_get(v_x_2214_, 0);
lean_inc(v_mvarId_2246_);
lean_dec_ref(v_x_2214_);
v___x_2257_ = lean_unsigned_to_nat(1024u);
v___x_2258_ = lean_nat_dec_le(v___x_2257_, v_prec_2215_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2248_ = v___x_2259_;
goto v___jp_2247_;
}
else
{
lean_object* v___x_2260_; 
v___x_2260_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2248_ = v___x_2260_;
goto v___jp_2247_;
}
v___jp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2249_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__8));
v___x_2250_ = lean_unsigned_to_nat(1024u);
v___x_2251_ = l_Lean_Name_reprPrec(v_mvarId_2246_, v___x_2250_);
v___x_2252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2249_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___y_2248_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = 0;
v___x_2255_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set_uint8(v___x_2255_, sizeof(void*)*1, v___x_2254_);
v___x_2256_ = l_Repr_addAppParen(v___x_2255_, v_prec_2215_);
return v___x_2256_;
}
}
case 3:
{
lean_object* v_u_2261_; lean_object* v___y_2263_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v_u_2261_ = lean_ctor_get(v_x_2214_, 0);
lean_inc(v_u_2261_);
lean_dec_ref(v_x_2214_);
v___x_2272_ = lean_unsigned_to_nat(1024u);
v___x_2273_ = lean_nat_dec_le(v___x_2272_, v_prec_2215_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; 
v___x_2274_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2263_ = v___x_2274_;
goto v___jp_2262_;
}
else
{
lean_object* v___x_2275_; 
v___x_2275_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2263_ = v___x_2275_;
goto v___jp_2262_;
}
v___jp_2262_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2264_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__11));
v___x_2265_ = lean_unsigned_to_nat(1024u);
v___x_2266_ = l_Lean_instReprLevel_repr(v_u_2261_, v___x_2265_);
v___x_2267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2264_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
v___x_2268_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___y_2263_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v___x_2269_ = 0;
v___x_2270_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set_uint8(v___x_2270_, sizeof(void*)*1, v___x_2269_);
v___x_2271_ = l_Repr_addAppParen(v___x_2270_, v_prec_2215_);
return v___x_2271_;
}
}
case 4:
{
lean_object* v_declName_2276_; lean_object* v_us_2277_; lean_object* v___y_2279_; lean_object* v___x_2292_; uint8_t v___x_2293_; 
v_declName_2276_ = lean_ctor_get(v_x_2214_, 0);
lean_inc(v_declName_2276_);
v_us_2277_ = lean_ctor_get(v_x_2214_, 1);
lean_inc(v_us_2277_);
lean_dec_ref(v_x_2214_);
v___x_2292_ = lean_unsigned_to_nat(1024u);
v___x_2293_ = lean_nat_dec_le(v___x_2292_, v_prec_2215_);
if (v___x_2293_ == 0)
{
lean_object* v___x_2294_; 
v___x_2294_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2279_ = v___x_2294_;
goto v___jp_2278_;
}
else
{
lean_object* v___x_2295_; 
v___x_2295_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2279_ = v___x_2295_;
goto v___jp_2278_;
}
v___jp_2278_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2280_ = lean_box(1);
v___x_2281_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__14));
v___x_2282_ = lean_unsigned_to_nat(1024u);
v___x_2283_ = l_Lean_Name_reprPrec(v_declName_2276_, v___x_2282_);
v___x_2284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2281_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
lean_ctor_set(v___x_2285_, 1, v___x_2280_);
v___x_2286_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_us_2277_);
v___x_2287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___y_2279_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = 0;
v___x_2290_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set_uint8(v___x_2290_, sizeof(void*)*1, v___x_2289_);
v___x_2291_ = l_Repr_addAppParen(v___x_2290_, v_prec_2215_);
return v___x_2291_;
}
}
case 5:
{
lean_object* v_fn_2296_; lean_object* v_arg_2297_; lean_object* v___x_2298_; lean_object* v___y_2300_; uint8_t v___x_2312_; 
v_fn_2296_ = lean_ctor_get(v_x_2214_, 0);
lean_inc_ref(v_fn_2296_);
v_arg_2297_ = lean_ctor_get(v_x_2214_, 1);
lean_inc_ref(v_arg_2297_);
lean_dec_ref(v_x_2214_);
v___x_2298_ = lean_unsigned_to_nat(1024u);
v___x_2312_ = lean_nat_dec_le(v___x_2298_, v_prec_2215_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; 
v___x_2313_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2300_ = v___x_2313_;
goto v___jp_2299_;
}
else
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2300_ = v___x_2314_;
goto v___jp_2299_;
}
v___jp_2299_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2301_ = lean_box(1);
v___x_2302_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__17));
v___x_2303_ = l_Lean_instReprExpr_repr(v_fn_2296_, v___x_2298_);
v___x_2304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2302_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
lean_ctor_set(v___x_2305_, 1, v___x_2301_);
v___x_2306_ = l_Lean_instReprExpr_repr(v_arg_2297_, v___x_2298_);
v___x_2307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___y_2300_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
v___x_2309_ = 0;
v___x_2310_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*1, v___x_2309_);
v___x_2311_ = l_Repr_addAppParen(v___x_2310_, v_prec_2215_);
return v___x_2311_;
}
}
case 6:
{
lean_object* v_binderName_2315_; lean_object* v_binderType_2316_; lean_object* v_body_2317_; uint8_t v_binderInfo_2318_; lean_object* v___x_2319_; lean_object* v___y_2321_; uint8_t v___x_2339_; 
v_binderName_2315_ = lean_ctor_get(v_x_2214_, 0);
lean_inc(v_binderName_2315_);
v_binderType_2316_ = lean_ctor_get(v_x_2214_, 1);
lean_inc_ref(v_binderType_2316_);
v_body_2317_ = lean_ctor_get(v_x_2214_, 2);
lean_inc_ref(v_body_2317_);
v_binderInfo_2318_ = lean_ctor_get_uint8(v_x_2214_, sizeof(void*)*3 + 8);
lean_dec_ref(v_x_2214_);
v___x_2319_ = lean_unsigned_to_nat(1024u);
v___x_2339_ = lean_nat_dec_le(v___x_2319_, v_prec_2215_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2321_ = v___x_2340_;
goto v___jp_2320_;
}
else
{
lean_object* v___x_2341_; 
v___x_2341_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2321_ = v___x_2341_;
goto v___jp_2320_;
}
v___jp_2320_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2322_ = lean_box(1);
v___x_2323_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__20));
v___x_2324_ = l_Lean_Name_reprPrec(v_binderName_2315_, v___x_2319_);
v___x_2325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2323_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
v___x_2326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
lean_ctor_set(v___x_2326_, 1, v___x_2322_);
v___x_2327_ = l_Lean_instReprExpr_repr(v_binderType_2316_, v___x_2319_);
v___x_2328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2326_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v___x_2322_);
v___x_2330_ = l_Lean_instReprExpr_repr(v_body_2317_, v___x_2319_);
v___x_2331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set(v___x_2332_, 1, v___x_2322_);
v___x_2333_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2318_, v___x_2319_);
v___x_2334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___y_2321_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = 0;
v___x_2337_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2337_, 0, v___x_2335_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*1, v___x_2336_);
v___x_2338_ = l_Repr_addAppParen(v___x_2337_, v_prec_2215_);
return v___x_2338_;
}
}
case 7:
{
lean_object* v_binderName_2342_; lean_object* v_binderType_2343_; lean_object* v_body_2344_; uint8_t v_binderInfo_2345_; lean_object* v___x_2346_; lean_object* v___y_2348_; uint8_t v___x_2366_; 
v_binderName_2342_ = lean_ctor_get(v_x_2214_, 0);
lean_inc(v_binderName_2342_);
v_binderType_2343_ = lean_ctor_get(v_x_2214_, 1);
lean_inc_ref(v_binderType_2343_);
v_body_2344_ = lean_ctor_get(v_x_2214_, 2);
lean_inc_ref(v_body_2344_);
v_binderInfo_2345_ = lean_ctor_get_uint8(v_x_2214_, sizeof(void*)*3 + 8);
lean_dec_ref(v_x_2214_);
v___x_2346_ = lean_unsigned_to_nat(1024u);
v___x_2366_ = lean_nat_dec_le(v___x_2346_, v_prec_2215_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; 
v___x_2367_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2348_ = v___x_2367_;
goto v___jp_2347_;
}
else
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2348_ = v___x_2368_;
goto v___jp_2347_;
}
v___jp_2347_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2349_ = lean_box(1);
v___x_2350_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__23));
v___x_2351_ = l_Lean_Name_reprPrec(v_binderName_2342_, v___x_2346_);
v___x_2352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2350_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
lean_ctor_set(v___x_2353_, 1, v___x_2349_);
v___x_2354_ = l_Lean_instReprExpr_repr(v_binderType_2343_, v___x_2346_);
v___x_2355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2353_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v___x_2356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
lean_ctor_set(v___x_2356_, 1, v___x_2349_);
v___x_2357_ = l_Lean_instReprExpr_repr(v_body_2344_, v___x_2346_);
v___x_2358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set(v___x_2359_, 1, v___x_2349_);
v___x_2360_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2345_, v___x_2346_);
v___x_2361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___y_2348_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
v___x_2363_ = 0;
v___x_2364_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2364_, 0, v___x_2362_);
lean_ctor_set_uint8(v___x_2364_, sizeof(void*)*1, v___x_2363_);
v___x_2365_ = l_Repr_addAppParen(v___x_2364_, v_prec_2215_);
return v___x_2365_;
}
}
case 8:
{
lean_object* v_declName_2369_; lean_object* v_type_2370_; lean_object* v_value_2371_; lean_object* v_body_2372_; uint8_t v_nondep_2373_; lean_object* v___x_2374_; lean_object* v___y_2376_; uint8_t v___x_2397_; 
v_declName_2369_ = lean_ctor_get(v_x_2214_, 0);
lean_inc(v_declName_2369_);
v_type_2370_ = lean_ctor_get(v_x_2214_, 1);
lean_inc_ref(v_type_2370_);
v_value_2371_ = lean_ctor_get(v_x_2214_, 2);
lean_inc_ref(v_value_2371_);
v_body_2372_ = lean_ctor_get(v_x_2214_, 3);
lean_inc_ref(v_body_2372_);
v_nondep_2373_ = lean_ctor_get_uint8(v_x_2214_, sizeof(void*)*4 + 8);
lean_dec_ref(v_x_2214_);
v___x_2374_ = lean_unsigned_to_nat(1024u);
v___x_2397_ = lean_nat_dec_le(v___x_2374_, v_prec_2215_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2376_ = v___x_2398_;
goto v___jp_2375_;
}
else
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2376_ = v___x_2399_;
goto v___jp_2375_;
}
v___jp_2375_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2377_ = lean_box(1);
v___x_2378_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__26));
v___x_2379_ = l_Lean_Name_reprPrec(v_declName_2369_, v___x_2374_);
v___x_2380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2378_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
lean_ctor_set(v___x_2381_, 1, v___x_2377_);
v___x_2382_ = l_Lean_instReprExpr_repr(v_type_2370_, v___x_2374_);
v___x_2383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
lean_ctor_set(v___x_2384_, 1, v___x_2377_);
v___x_2385_ = l_Lean_instReprExpr_repr(v_value_2371_, v___x_2374_);
v___x_2386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
lean_ctor_set(v___x_2387_, 1, v___x_2377_);
v___x_2388_ = l_Lean_instReprExpr_repr(v_body_2372_, v___x_2374_);
v___x_2389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2387_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
lean_ctor_set(v___x_2390_, 1, v___x_2377_);
v___x_2391_ = l_Bool_repr___redArg(v_nondep_2373_);
v___x_2392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2390_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___y_2376_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = 0;
v___x_2395_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2395_, 0, v___x_2393_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*1, v___x_2394_);
v___x_2396_ = l_Repr_addAppParen(v___x_2395_, v_prec_2215_);
return v___x_2396_;
}
}
case 9:
{
lean_object* v_a_2400_; lean_object* v___y_2402_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v_a_2400_ = lean_ctor_get(v_x_2214_, 0);
lean_inc_ref(v_a_2400_);
lean_dec_ref(v_x_2214_);
v___x_2411_ = lean_unsigned_to_nat(1024u);
v___x_2412_ = lean_nat_dec_le(v___x_2411_, v_prec_2215_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2402_ = v___x_2413_;
goto v___jp_2401_;
}
else
{
lean_object* v___x_2414_; 
v___x_2414_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2402_ = v___x_2414_;
goto v___jp_2401_;
}
v___jp_2401_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2403_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__29));
v___x_2404_ = lean_unsigned_to_nat(1024u);
v___x_2405_ = l_Lean_instReprLiteral_repr(v_a_2400_, v___x_2404_);
v___x_2406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2403_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___y_2402_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = 0;
v___x_2409_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set_uint8(v___x_2409_, sizeof(void*)*1, v___x_2408_);
v___x_2410_ = l_Repr_addAppParen(v___x_2409_, v_prec_2215_);
return v___x_2410_;
}
}
case 10:
{
lean_object* v_data_2415_; lean_object* v_expr_2416_; lean_object* v___x_2417_; lean_object* v___y_2419_; uint8_t v___x_2431_; 
v_data_2415_ = lean_ctor_get(v_x_2214_, 0);
lean_inc(v_data_2415_);
v_expr_2416_ = lean_ctor_get(v_x_2214_, 1);
lean_inc_ref(v_expr_2416_);
lean_dec_ref(v_x_2214_);
v___x_2417_ = lean_unsigned_to_nat(1024u);
v___x_2431_ = lean_nat_dec_le(v___x_2417_, v_prec_2215_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; 
v___x_2432_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2419_ = v___x_2432_;
goto v___jp_2418_;
}
else
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2419_ = v___x_2433_;
goto v___jp_2418_;
}
v___jp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2420_ = lean_box(1);
v___x_2421_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__32));
v___x_2422_ = l_Lean_instReprKVMap_repr___redArg(v_data_2415_);
v___x_2423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
lean_ctor_set(v___x_2424_, 1, v___x_2420_);
v___x_2425_ = l_Lean_instReprExpr_repr(v_expr_2416_, v___x_2417_);
v___x_2426_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2424_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
v___x_2427_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___y_2419_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = 0;
v___x_2429_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set_uint8(v___x_2429_, sizeof(void*)*1, v___x_2428_);
v___x_2430_ = l_Repr_addAppParen(v___x_2429_, v_prec_2215_);
return v___x_2430_;
}
}
default: 
{
lean_object* v_typeName_2434_; lean_object* v_idx_2435_; lean_object* v_struct_2436_; lean_object* v___x_2437_; lean_object* v___y_2439_; uint8_t v___x_2455_; 
v_typeName_2434_ = lean_ctor_get(v_x_2214_, 0);
lean_inc(v_typeName_2434_);
v_idx_2435_ = lean_ctor_get(v_x_2214_, 1);
lean_inc(v_idx_2435_);
v_struct_2436_ = lean_ctor_get(v_x_2214_, 2);
lean_inc_ref(v_struct_2436_);
lean_dec_ref(v_x_2214_);
v___x_2437_ = lean_unsigned_to_nat(1024u);
v___x_2455_ = lean_nat_dec_le(v___x_2437_, v_prec_2215_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2439_ = v___x_2456_;
goto v___jp_2438_;
}
else
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2439_ = v___x_2457_;
goto v___jp_2438_;
}
v___jp_2438_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2440_ = lean_box(1);
v___x_2441_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__35));
v___x_2442_ = l_Lean_Name_reprPrec(v_typeName_2434_, v___x_2437_);
v___x_2443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v___x_2444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set(v___x_2444_, 1, v___x_2440_);
v___x_2445_ = l_Nat_reprFast(v_idx_2435_);
v___x_2446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
v___x_2447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2444_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
v___x_2448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v___x_2440_);
v___x_2449_ = l_Lean_instReprExpr_repr(v_struct_2436_, v___x_2437_);
v___x_2450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___y_2439_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = 0;
v___x_2453_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2453_, 0, v___x_2451_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*1, v___x_2452_);
v___x_2454_ = l_Repr_addAppParen(v___x_2453_, v_prec_2215_);
return v___x_2454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object* v_x_2458_, lean_object* v_prec_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_instReprExpr_repr(v_x_2458_, v_prec_2459_);
lean_dec(v_prec_2459_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object* v_a_2461_){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_nat_to_int(v_a_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object* v_a_2463_, lean_object* v_n_2464_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_a_2463_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object* v_a_2466_, lean_object* v_n_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0(v_a_2466_, v_n_2467_);
lean_dec(v_n_2467_);
return v_res_2468_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__2(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = lean_box(0);
v___x_2475_ = ((lean_object*)(l_Lean_instInhabitedExpr___closed__1));
v___x_2476_ = l_Lean_Expr_const___override(v___x_2475_, v___x_2474_);
return v___x_2476_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr(void){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* v_x_2490_){
_start:
{
switch(lean_obj_tag(v_x_2490_))
{
case 0:
{
lean_object* v___x_2491_; 
v___x_2491_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__0));
return v___x_2491_;
}
case 1:
{
lean_object* v___x_2492_; 
v___x_2492_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__1));
return v___x_2492_;
}
case 2:
{
lean_object* v___x_2493_; 
v___x_2493_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__2));
return v___x_2493_;
}
case 3:
{
lean_object* v___x_2494_; 
v___x_2494_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__3));
return v___x_2494_;
}
case 4:
{
lean_object* v___x_2495_; 
v___x_2495_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__4));
return v___x_2495_;
}
case 5:
{
lean_object* v___x_2496_; 
v___x_2496_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__5));
return v___x_2496_;
}
case 6:
{
lean_object* v___x_2497_; 
v___x_2497_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__6));
return v___x_2497_;
}
case 7:
{
lean_object* v___x_2498_; 
v___x_2498_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__7));
return v___x_2498_;
}
case 8:
{
lean_object* v___x_2499_; 
v___x_2499_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__8));
return v___x_2499_;
}
case 9:
{
lean_object* v___x_2500_; 
v___x_2500_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__9));
return v___x_2500_;
}
case 10:
{
lean_object* v___x_2501_; 
v___x_2501_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__10));
return v___x_2501_;
}
default: 
{
lean_object* v___x_2502_; 
v___x_2502_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__11));
return v___x_2502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* v_x_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_Expr_ctorName(v_x_2503_);
lean_dec_ref(v_x_2503_);
return v_res_2504_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object* v_e_2505_){
_start:
{
uint64_t v___x_2506_; uint64_t v___x_2507_; 
v___x_2506_ = lean_expr_data(v_e_2505_);
v___x_2507_ = l_Lean_Expr_Data_hash(v___x_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* v_e_2508_){
_start:
{
uint64_t v_res_2509_; lean_object* v_r_2510_; 
v_res_2509_ = l_Lean_Expr_hash(v_e_2508_);
lean_dec_ref(v_e_2508_);
v_r_2510_ = lean_box_uint64(v_res_2509_);
return v_r_2510_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object* v_e_2513_){
_start:
{
uint64_t v___x_2514_; uint8_t v___x_2515_; 
v___x_2514_ = lean_expr_data(v_e_2513_);
v___x_2515_ = l_Lean_Expr_Data_hasFVar(v___x_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* v_e_2516_){
_start:
{
uint8_t v_res_2517_; lean_object* v_r_2518_; 
v_res_2517_ = l_Lean_Expr_hasFVar(v_e_2516_);
lean_dec_ref(v_e_2516_);
v_r_2518_ = lean_box(v_res_2517_);
return v_r_2518_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object* v_e_2519_){
_start:
{
uint64_t v___x_2520_; uint8_t v___x_2521_; 
v___x_2520_ = lean_expr_data(v_e_2519_);
v___x_2521_ = l_Lean_Expr_Data_hasExprMVar(v___x_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* v_e_2522_){
_start:
{
uint8_t v_res_2523_; lean_object* v_r_2524_; 
v_res_2523_ = l_Lean_Expr_hasExprMVar(v_e_2522_);
lean_dec_ref(v_e_2522_);
v_r_2524_ = lean_box(v_res_2523_);
return v_r_2524_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object* v_e_2525_){
_start:
{
uint64_t v___x_2526_; uint8_t v___x_2527_; 
v___x_2526_ = lean_expr_data(v_e_2525_);
v___x_2527_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2526_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* v_e_2528_){
_start:
{
uint8_t v_res_2529_; lean_object* v_r_2530_; 
v_res_2529_ = l_Lean_Expr_hasLevelMVar(v_e_2528_);
lean_dec_ref(v_e_2528_);
v_r_2530_ = lean_box(v_res_2529_);
return v_r_2530_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object* v_e_2531_){
_start:
{
uint64_t v_d_2532_; uint8_t v___x_2533_; 
v_d_2532_ = lean_expr_data(v_e_2531_);
v___x_2533_ = l_Lean_Expr_Data_hasExprMVar(v_d_2532_);
if (v___x_2533_ == 0)
{
uint8_t v___x_2534_; 
v___x_2534_ = l_Lean_Expr_Data_hasLevelMVar(v_d_2532_);
return v___x_2534_;
}
else
{
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* v_e_2535_){
_start:
{
uint8_t v_res_2536_; lean_object* v_r_2537_; 
v_res_2536_ = l_Lean_Expr_hasMVar(v_e_2535_);
lean_dec_ref(v_e_2535_);
v_r_2537_ = lean_box(v_res_2536_);
return v_r_2537_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object* v_e_2538_){
_start:
{
uint64_t v___x_2539_; uint8_t v___x_2540_; 
v___x_2539_ = lean_expr_data(v_e_2538_);
v___x_2540_ = l_Lean_Expr_Data_hasLevelParam(v___x_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* v_e_2541_){
_start:
{
uint8_t v_res_2542_; lean_object* v_r_2543_; 
v_res_2542_ = l_Lean_Expr_hasLevelParam(v_e_2541_);
lean_dec_ref(v_e_2541_);
v_r_2543_ = lean_box(v_res_2542_);
return v_r_2543_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object* v_e_2544_){
_start:
{
uint64_t v___x_2545_; uint8_t v___x_2546_; uint32_t v___x_2547_; 
v___x_2545_ = lean_expr_data(v_e_2544_);
v___x_2546_ = l_Lean_Expr_Data_approxDepth(v___x_2545_);
v___x_2547_ = lean_uint8_to_uint32(v___x_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* v_e_2548_){
_start:
{
uint32_t v_res_2549_; lean_object* v_r_2550_; 
v_res_2549_ = l_Lean_Expr_approxDepth(v_e_2548_);
lean_dec_ref(v_e_2548_);
v_r_2550_ = lean_box_uint32(v_res_2549_);
return v_r_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* v_e_2551_){
_start:
{
uint64_t v___x_2552_; uint32_t v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = lean_expr_data(v_e_2551_);
v___x_2553_ = l_Lean_Expr_Data_looseBVarRange(v___x_2552_);
v___x_2554_ = lean_uint32_to_nat(v___x_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* v_e_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_Expr_looseBVarRange(v_e_2555_);
lean_dec_ref(v_e_2555_);
return v_res_2556_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object* v_e_2557_){
_start:
{
switch(lean_obj_tag(v_e_2557_))
{
case 7:
{
uint8_t v_binderInfo_2558_; 
v_binderInfo_2558_ = lean_ctor_get_uint8(v_e_2557_, sizeof(void*)*3 + 8);
return v_binderInfo_2558_;
}
case 6:
{
uint8_t v_binderInfo_2559_; 
v_binderInfo_2559_ = lean_ctor_get_uint8(v_e_2557_, sizeof(void*)*3 + 8);
return v_binderInfo_2559_;
}
default: 
{
uint8_t v___x_2560_; 
v___x_2560_ = 0;
return v___x_2560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* v_e_2561_){
_start:
{
uint8_t v_res_2562_; lean_object* v_r_2563_; 
v_res_2562_ = l_Lean_Expr_binderInfo(v_e_2561_);
lean_dec_ref(v_e_2561_);
v_r_2563_ = lean_box(v_res_2562_);
return v_r_2563_;
}
}
LEAN_EXPORT uint64_t lean_expr_hash(lean_object* v_a_2564_){
_start:
{
uint64_t v___x_2565_; 
v___x_2565_ = l_Lean_Expr_hash(v_a_2564_);
lean_dec_ref(v_a_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* v_a_2566_){
_start:
{
uint64_t v_res_2567_; lean_object* v_r_2568_; 
v_res_2567_ = lean_expr_hash(v_a_2566_);
v_r_2568_ = lean_box_uint64(v_res_2567_);
return v_r_2568_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object* v_e_2569_){
_start:
{
uint8_t v___x_2570_; 
v___x_2570_ = l_Lean_Expr_hasFVar(v_e_2569_);
lean_dec_ref(v_e_2569_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* v_e_2571_){
_start:
{
uint8_t v_res_2572_; lean_object* v_r_2573_; 
v_res_2572_ = lean_expr_has_fvar(v_e_2571_);
v_r_2573_ = lean_box(v_res_2572_);
return v_r_2573_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object* v_e_2574_){
_start:
{
uint8_t v___x_2575_; 
v___x_2575_ = l_Lean_Expr_hasExprMVar(v_e_2574_);
lean_dec_ref(v_e_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* v_e_2576_){
_start:
{
uint8_t v_res_2577_; lean_object* v_r_2578_; 
v_res_2577_ = lean_expr_has_expr_mvar(v_e_2576_);
v_r_2578_ = lean_box(v_res_2577_);
return v_r_2578_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object* v_e_2579_){
_start:
{
uint8_t v___x_2580_; 
v___x_2580_ = l_Lean_Expr_hasLevelMVar(v_e_2579_);
lean_dec_ref(v_e_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* v_e_2581_){
_start:
{
uint8_t v_res_2582_; lean_object* v_r_2583_; 
v_res_2582_ = lean_expr_has_level_mvar(v_e_2581_);
v_r_2583_ = lean_box(v_res_2582_);
return v_r_2583_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_mvar(lean_object* v_e_2584_){
_start:
{
uint8_t v___x_2585_; 
v___x_2585_ = l_Lean_Expr_hasMVar(v_e_2584_);
lean_dec_ref(v_e_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVarEx___boxed(lean_object* v_e_2586_){
_start:
{
uint8_t v_res_2587_; lean_object* v_r_2588_; 
v_res_2587_ = lean_expr_has_mvar(v_e_2586_);
v_r_2588_ = lean_box(v_res_2587_);
return v_r_2588_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* v_e_2589_){
_start:
{
uint8_t v___x_2590_; 
v___x_2590_ = l_Lean_Expr_hasLevelParam(v_e_2589_);
lean_dec_ref(v_e_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* v_e_2591_){
_start:
{
uint8_t v_res_2592_; lean_object* v_r_2593_; 
v_res_2592_ = lean_expr_has_level_param(v_e_2591_);
v_r_2593_ = lean_box(v_res_2592_);
return v_r_2593_;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* v_e_2594_){
_start:
{
uint64_t v___x_2595_; uint32_t v___x_2596_; 
v___x_2595_ = lean_expr_data(v_e_2594_);
lean_dec_ref(v_e_2594_);
v___x_2596_ = l_Lean_Expr_Data_looseBVarRange(v___x_2595_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* v_e_2597_){
_start:
{
uint32_t v_res_2598_; lean_object* v_r_2599_; 
v_res_2598_ = lean_expr_loose_bvar_range(v_e_2597_);
v_r_2599_ = lean_box_uint32(v_res_2598_);
return v_r_2599_;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* v_e_2600_){
_start:
{
uint8_t v___x_2601_; 
v___x_2601_ = l_Lean_Expr_binderInfo(v_e_2600_);
lean_dec_ref(v_e_2600_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* v_e_2602_){
_start:
{
uint8_t v_res_2603_; lean_object* v_r_2604_; 
v_res_2603_ = lean_expr_binder_info(v_e_2602_);
v_r_2604_ = lean_box(v_res_2603_);
return v_r_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* v_declName_2605_, lean_object* v_us_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_Expr_const___override(v_declName_2605_, v_us_2606_);
return v___x_2607_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_box(0);
v___x_2612_ = ((lean_object*)(l_Lean_Literal_type___closed__1));
v___x_2613_ = l_Lean_Expr_const___override(v___x_2612_, v___x_2611_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = lean_box(0);
v___x_2618_ = ((lean_object*)(l_Lean_Literal_type___closed__4));
v___x_2619_ = l_Lean_Expr_const___override(v___x_2618_, v___x_2617_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* v_x_2620_){
_start:
{
if (lean_obj_tag(v_x_2620_) == 0)
{
lean_object* v___x_2621_; 
v___x_2621_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_2621_;
}
else
{
lean_object* v___x_2622_; 
v___x_2622_ = lean_obj_once(&l_Lean_Literal_type___closed__5, &l_Lean_Literal_type___closed__5_once, _init_l_Lean_Literal_type___closed__5);
return v___x_2622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* v_x_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_Literal_type(v_x_2623_);
lean_dec_ref(v_x_2623_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* v_a_2625_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_Literal_type(v_a_2625_);
lean_dec_ref(v_a_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* v_idx_2627_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Lean_Expr_bvar___override(v_idx_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* v_u_2629_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_Expr_sort___override(v_u_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* v_fvarId_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_Expr_fvar___override(v_fvarId_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* v_mvarId_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_Expr_mvar___override(v_mvarId_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* v_m_2635_, lean_object* v_e_2636_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lean_Expr_mdata___override(v_m_2635_, v_e_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* v_structName_2638_, lean_object* v_idx_2639_, lean_object* v_struct_2640_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_Expr_proj___override(v_structName_2638_, v_idx_2639_, v_struct_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* v_f_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_Expr_app___override(v_f_2642_, v_a_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* v_x_2645_, uint8_t v_bi_2646_, lean_object* v_t_2647_, lean_object* v_b_2648_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lean_Expr_lam___override(v_x_2645_, v_t_2647_, v_b_2648_, v_bi_2646_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* v_x_2650_, lean_object* v_bi_2651_, lean_object* v_t_2652_, lean_object* v_b_2653_){
_start:
{
uint8_t v_bi_boxed_2654_; lean_object* v_res_2655_; 
v_bi_boxed_2654_ = lean_unbox(v_bi_2651_);
v_res_2655_ = l_Lean_mkLambda(v_x_2650_, v_bi_boxed_2654_, v_t_2652_, v_b_2653_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* v_x_2656_, uint8_t v_bi_2657_, lean_object* v_t_2658_, lean_object* v_b_2659_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_Expr_forallE___override(v_x_2656_, v_t_2658_, v_b_2659_, v_bi_2657_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* v_x_2661_, lean_object* v_bi_2662_, lean_object* v_t_2663_, lean_object* v_b_2664_){
_start:
{
uint8_t v_bi_boxed_2665_; lean_object* v_res_2666_; 
v_bi_boxed_2665_ = lean_unbox(v_bi_2662_);
v_res_2666_ = l_Lean_mkForall(v_x_2661_, v_bi_boxed_2665_, v_t_2663_, v_b_2664_);
return v_res_2666_;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__2(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = lean_box(0);
v___x_2671_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2672_ = l_Lean_Expr_const___override(v___x_2671_, v___x_2670_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* v_type_2673_){
_start:
{
lean_object* v___x_2674_; uint8_t v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2674_ = lean_box(0);
v___x_2675_ = 0;
v___x_2676_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__2, &l_Lean_mkSimpleThunkType___closed__2_once, _init_l_Lean_mkSimpleThunkType___closed__2);
v___x_2677_ = l_Lean_Expr_forallE___override(v___x_2674_, v___x_2676_, v_type_2673_, v___x_2675_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* v_type_2681_){
_start:
{
lean_object* v___x_2682_; uint8_t v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2682_ = ((lean_object*)(l_Lean_mkSimpleThunk___closed__1));
v___x_2683_ = 0;
v___x_2684_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__2, &l_Lean_mkSimpleThunkType___closed__2_once, _init_l_Lean_mkSimpleThunkType___closed__2);
v___x_2685_ = l_Lean_Expr_lam___override(v___x_2682_, v___x_2684_, v_type_2681_, v___x_2683_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* v_x_2686_, lean_object* v_t_2687_, lean_object* v_v_2688_, lean_object* v_b_2689_, uint8_t v_nondep_2690_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_Expr_letE___override(v_x_2686_, v_t_2687_, v_v_2688_, v_b_2689_, v_nondep_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* v_x_2692_, lean_object* v_t_2693_, lean_object* v_v_2694_, lean_object* v_b_2695_, lean_object* v_nondep_2696_){
_start:
{
uint8_t v_nondep_boxed_2697_; lean_object* v_res_2698_; 
v_nondep_boxed_2697_ = lean_unbox(v_nondep_2696_);
v_res_2698_ = l_Lean_mkLet(v_x_2692_, v_t_2693_, v_v_2694_, v_b_2695_, v_nondep_boxed_2697_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object* v_x_2699_, lean_object* v_t_2700_, lean_object* v_v_2701_, lean_object* v_b_2702_){
_start:
{
uint8_t v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = 1;
v___x_2704_ = l_Lean_Expr_letE___override(v_x_2699_, v_t_2700_, v_v_2701_, v_b_2702_, v___x_2703_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* v_f_2705_, lean_object* v_a_2706_, lean_object* v_b_2707_){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = l_Lean_Expr_app___override(v_f_2705_, v_a_2706_);
v___x_2709_ = l_Lean_Expr_app___override(v___x_2708_, v_b_2707_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* v_f_2710_, lean_object* v_a_2711_, lean_object* v_b_2712_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_mkAppB(v_f_2710_, v_a_2711_, v_b_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* v_f_2714_, lean_object* v_a_2715_, lean_object* v_b_2716_, lean_object* v_c_2717_){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = l_Lean_mkAppB(v_f_2714_, v_a_2715_, v_b_2716_);
v___x_2719_ = l_Lean_Expr_app___override(v___x_2718_, v_c_2717_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* v_f_2720_, lean_object* v_a_2721_, lean_object* v_b_2722_, lean_object* v_c_2723_, lean_object* v_d_2724_){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = l_Lean_mkAppB(v_f_2720_, v_a_2721_, v_b_2722_);
v___x_2726_ = l_Lean_mkAppB(v___x_2725_, v_c_2723_, v_d_2724_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* v_f_2727_, lean_object* v_a_2728_, lean_object* v_b_2729_, lean_object* v_c_2730_, lean_object* v_d_2731_, lean_object* v_e_2732_){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = l_Lean_mkApp4(v_f_2727_, v_a_2728_, v_b_2729_, v_c_2730_, v_d_2731_);
v___x_2734_ = l_Lean_Expr_app___override(v___x_2733_, v_e_2732_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* v_f_2735_, lean_object* v_a_2736_, lean_object* v_b_2737_, lean_object* v_c_2738_, lean_object* v_d_2739_, lean_object* v_e_u2081_2740_, lean_object* v_e_u2082_2741_){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = l_Lean_mkApp4(v_f_2735_, v_a_2736_, v_b_2737_, v_c_2738_, v_d_2739_);
v___x_2743_ = l_Lean_mkAppB(v___x_2742_, v_e_u2081_2740_, v_e_u2082_2741_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* v_f_2744_, lean_object* v_a_2745_, lean_object* v_b_2746_, lean_object* v_c_2747_, lean_object* v_d_2748_, lean_object* v_e_u2081_2749_, lean_object* v_e_u2082_2750_, lean_object* v_e_u2083_2751_){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = l_Lean_mkApp4(v_f_2744_, v_a_2745_, v_b_2746_, v_c_2747_, v_d_2748_);
v___x_2753_ = l_Lean_mkApp3(v___x_2752_, v_e_u2081_2749_, v_e_u2082_2750_, v_e_u2083_2751_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* v_f_2754_, lean_object* v_a_2755_, lean_object* v_b_2756_, lean_object* v_c_2757_, lean_object* v_d_2758_, lean_object* v_e_u2081_2759_, lean_object* v_e_u2082_2760_, lean_object* v_e_u2083_2761_, lean_object* v_e_u2084_2762_){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = l_Lean_mkApp4(v_f_2754_, v_a_2755_, v_b_2756_, v_c_2757_, v_d_2758_);
v___x_2764_ = l_Lean_mkApp4(v___x_2763_, v_e_u2081_2759_, v_e_u2082_2760_, v_e_u2083_2761_, v_e_u2084_2762_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* v_f_2765_, lean_object* v_a_2766_, lean_object* v_b_2767_, lean_object* v_c_2768_, lean_object* v_d_2769_, lean_object* v_e_u2081_2770_, lean_object* v_e_u2082_2771_, lean_object* v_e_u2083_2772_, lean_object* v_e_u2084_2773_, lean_object* v_e_u2085_2774_){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2775_ = l_Lean_mkApp4(v_f_2765_, v_a_2766_, v_b_2767_, v_c_2768_, v_d_2769_);
v___x_2776_ = l_Lean_mkApp5(v___x_2775_, v_e_u2081_2770_, v_e_u2082_2771_, v_e_u2083_2772_, v_e_u2084_2773_, v_e_u2085_2774_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* v_f_2777_, lean_object* v_a_2778_, lean_object* v_b_2779_, lean_object* v_c_2780_, lean_object* v_d_2781_, lean_object* v_e_u2081_2782_, lean_object* v_e_u2082_2783_, lean_object* v_e_u2083_2784_, lean_object* v_e_u2084_2785_, lean_object* v_e_u2085_2786_, lean_object* v_e_u2086_2787_){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = l_Lean_mkApp4(v_f_2777_, v_a_2778_, v_b_2779_, v_c_2780_, v_d_2781_);
v___x_2789_ = l_Lean_mkApp6(v___x_2788_, v_e_u2081_2782_, v_e_u2082_2783_, v_e_u2083_2784_, v_e_u2084_2785_, v_e_u2085_2786_, v_e_u2086_2787_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* v_l_2790_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_Expr_lit___override(v_l_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* v_n_2792_){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v_n_2792_);
v___x_2794_ = l_Lean_Expr_lit___override(v___x_2793_);
return v___x_2794_;
}
}
static lean_object* _init_l_Lean_mkInstOfNatNat___closed__2(void){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2798_ = lean_box(0);
v___x_2799_ = ((lean_object*)(l_Lean_mkInstOfNatNat___closed__1));
v___x_2800_ = l_Lean_Expr_const___override(v___x_2799_, v___x_2798_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object* v_n_2801_){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = lean_obj_once(&l_Lean_mkInstOfNatNat___closed__2, &l_Lean_mkInstOfNatNat___closed__2_once, _init_l_Lean_mkInstOfNatNat___closed__2);
v___x_2803_ = l_Lean_Expr_app___override(v___x_2802_, v_n_2801_);
return v___x_2803_;
}
}
static lean_object* _init_l_Lean_mkNatLitCore___closed__4(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2812_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_2813_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_2814_ = l_Lean_Expr_const___override(v___x_2813_, v___x_2812_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object* v_n_2815_){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2816_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_2817_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
lean_inc_ref(v_n_2815_);
v___x_2818_ = l_Lean_mkInstOfNatNat(v_n_2815_);
v___x_2819_ = l_Lean_mkApp3(v___x_2816_, v___x_2817_, v_n_2815_, v___x_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* v_n_2820_){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2821_ = l_Lean_mkRawNatLit(v_n_2820_);
v___x_2822_ = l_Lean_mkNatLitCore(v___x_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* v_s_2823_){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2824_, 0, v_s_2823_);
v___x_2825_ = l_Lean_Expr_lit___override(v___x_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* v_idx_2826_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_Expr_bvar___override(v_idx_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* v_fvarId_2828_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_Expr_fvar___override(v_fvarId_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object* v_mvarId_2830_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Lean_Expr_mvar___override(v_mvarId_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_2832_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_Expr_sort___override(v_u_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_2834_, lean_object* v_lvls_2835_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Lean_Expr_const___override(v_c_2834_, v_lvls_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_Expr_app___override(v_f_2837_, v_a_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* v_n_2840_, lean_object* v_d_2841_, lean_object* v_b_2842_, uint8_t v_bi_2843_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Lean_Expr_lam___override(v_n_2840_, v_d_2841_, v_b_2842_, v_bi_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_2845_, lean_object* v_d_2846_, lean_object* v_b_2847_, lean_object* v_bi_2848_){
_start:
{
uint8_t v_bi_boxed_2849_; lean_object* v_res_2850_; 
v_bi_boxed_2849_ = lean_unbox(v_bi_2848_);
v_res_2850_ = lean_expr_mk_lambda(v_n_2845_, v_d_2846_, v_b_2847_, v_bi_boxed_2849_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* v_n_2851_, lean_object* v_d_2852_, lean_object* v_b_2853_, uint8_t v_bi_2854_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_Expr_forallE___override(v_n_2851_, v_d_2852_, v_b_2853_, v_bi_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_2856_, lean_object* v_d_2857_, lean_object* v_b_2858_, lean_object* v_bi_2859_){
_start:
{
uint8_t v_bi_boxed_2860_; lean_object* v_res_2861_; 
v_bi_boxed_2860_ = lean_unbox(v_bi_2859_);
v_res_2861_ = lean_expr_mk_forall(v_n_2856_, v_d_2857_, v_b_2858_, v_bi_boxed_2860_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* v_n_2862_, lean_object* v_t_2863_, lean_object* v_v_2864_, lean_object* v_b_2865_, uint8_t v_nondep_2866_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_Expr_letE___override(v_n_2862_, v_t_2863_, v_v_2864_, v_b_2865_, v_nondep_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_2868_, lean_object* v_t_2869_, lean_object* v_v_2870_, lean_object* v_b_2871_, lean_object* v_nondep_2872_){
_start:
{
uint8_t v_nondep_boxed_2873_; lean_object* v_res_2874_; 
v_nondep_boxed_2873_ = lean_unbox(v_nondep_2872_);
v_res_2874_ = lean_expr_mk_let(v_n_2868_, v_t_2869_, v_v_2870_, v_b_2871_, v_nondep_boxed_2873_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_2875_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_Expr_lit___override(v_l_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_2877_, lean_object* v_e_2878_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_Expr_mdata___override(v_m_2877_, v_e_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_2880_, lean_object* v_idx_2881_, lean_object* v_struct_2882_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_Expr_proj___override(v_structName_2880_, v_idx_2881_, v_struct_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_2884_, size_t v_i_2885_, size_t v_stop_2886_, lean_object* v_b_2887_){
_start:
{
uint8_t v___x_2888_; 
v___x_2888_ = lean_usize_dec_eq(v_i_2885_, v_stop_2886_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2890_; size_t v___x_2891_; size_t v___x_2892_; 
v___x_2889_ = lean_array_uget_borrowed(v_as_2884_, v_i_2885_);
lean_inc(v___x_2889_);
v___x_2890_ = l_Lean_Expr_app___override(v_b_2887_, v___x_2889_);
v___x_2891_ = ((size_t)1ULL);
v___x_2892_ = lean_usize_add(v_i_2885_, v___x_2891_);
v_i_2885_ = v___x_2892_;
v_b_2887_ = v___x_2890_;
goto _start;
}
else
{
return v_b_2887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_2894_, lean_object* v_i_2895_, lean_object* v_stop_2896_, lean_object* v_b_2897_){
_start:
{
size_t v_i_boxed_2898_; size_t v_stop_boxed_2899_; lean_object* v_res_2900_; 
v_i_boxed_2898_ = lean_unbox_usize(v_i_2895_);
lean_dec(v_i_2895_);
v_stop_boxed_2899_ = lean_unbox_usize(v_stop_2896_);
lean_dec(v_stop_2896_);
v_res_2900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_2894_, v_i_boxed_2898_, v_stop_boxed_2899_, v_b_2897_);
lean_dec_ref(v_as_2894_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_2901_, lean_object* v_args_2902_){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v___x_2903_ = lean_unsigned_to_nat(0u);
v___x_2904_ = lean_array_get_size(v_args_2902_);
v___x_2905_ = lean_nat_dec_lt(v___x_2903_, v___x_2904_);
if (v___x_2905_ == 0)
{
return v_f_2901_;
}
else
{
uint8_t v___x_2906_; 
v___x_2906_ = lean_nat_dec_le(v___x_2904_, v___x_2904_);
if (v___x_2906_ == 0)
{
if (v___x_2905_ == 0)
{
return v_f_2901_;
}
else
{
size_t v___x_2907_; size_t v___x_2908_; lean_object* v___x_2909_; 
v___x_2907_ = ((size_t)0ULL);
v___x_2908_ = lean_usize_of_nat(v___x_2904_);
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_2902_, v___x_2907_, v___x_2908_, v_f_2901_);
return v___x_2909_;
}
}
else
{
size_t v___x_2910_; size_t v___x_2911_; lean_object* v___x_2912_; 
v___x_2910_ = ((size_t)0ULL);
v___x_2911_ = lean_usize_of_nat(v___x_2904_);
v___x_2912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_2902_, v___x_2910_, v___x_2911_, v_f_2901_);
return v___x_2912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_2913_, lean_object* v_args_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Lean_mkAppN(v_f_2913_, v_args_2914_);
lean_dec_ref(v_args_2914_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_2916_, lean_object* v_args_2917_, lean_object* v_i_2918_, lean_object* v_e_2919_){
_start:
{
uint8_t v___x_2920_; 
v___x_2920_ = lean_nat_dec_lt(v_i_2918_, v_n_2916_);
if (v___x_2920_ == 0)
{
lean_dec(v_i_2918_);
return v_e_2919_;
}
else
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2921_ = lean_unsigned_to_nat(1u);
v___x_2922_ = lean_nat_add(v_i_2918_, v___x_2921_);
v___x_2923_ = l_Lean_instInhabitedExpr;
v___x_2924_ = lean_array_get_borrowed(v___x_2923_, v_args_2917_, v_i_2918_);
lean_dec(v_i_2918_);
lean_inc(v___x_2924_);
v___x_2925_ = l_Lean_Expr_app___override(v_e_2919_, v___x_2924_);
v_i_2918_ = v___x_2922_;
v_e_2919_ = v___x_2925_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_2927_, lean_object* v_args_2928_, lean_object* v_i_2929_, lean_object* v_e_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_2927_, v_args_2928_, v_i_2929_, v_e_2930_);
lean_dec_ref(v_args_2928_);
lean_dec(v_n_2927_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_2932_, lean_object* v_i_2933_, lean_object* v_j_2934_, lean_object* v_args_2935_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_2934_, v_args_2935_, v_i_2933_, v_f_2932_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_2937_, lean_object* v_i_2938_, lean_object* v_j_2939_, lean_object* v_args_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_mkAppRange(v_f_2937_, v_i_2938_, v_j_2939_, v_args_2940_);
lean_dec_ref(v_args_2940_);
lean_dec(v_j_2939_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_2942_, size_t v_i_2943_, size_t v_stop_2944_, lean_object* v_b_2945_){
_start:
{
uint8_t v___x_2946_; 
v___x_2946_ = lean_usize_dec_eq(v_i_2943_, v_stop_2944_);
if (v___x_2946_ == 0)
{
size_t v___x_2947_; size_t v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2947_ = ((size_t)1ULL);
v___x_2948_ = lean_usize_sub(v_i_2943_, v___x_2947_);
v___x_2949_ = lean_array_uget_borrowed(v_as_2942_, v___x_2948_);
lean_inc(v___x_2949_);
v___x_2950_ = l_Lean_Expr_app___override(v_b_2945_, v___x_2949_);
v_i_2943_ = v___x_2948_;
v_b_2945_ = v___x_2950_;
goto _start;
}
else
{
return v_b_2945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_2952_, lean_object* v_i_2953_, lean_object* v_stop_2954_, lean_object* v_b_2955_){
_start:
{
size_t v_i_boxed_2956_; size_t v_stop_boxed_2957_; lean_object* v_res_2958_; 
v_i_boxed_2956_ = lean_unbox_usize(v_i_2953_);
lean_dec(v_i_2953_);
v_stop_boxed_2957_ = lean_unbox_usize(v_stop_2954_);
lean_dec(v_stop_2954_);
v_res_2958_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_2952_, v_i_boxed_2956_, v_stop_boxed_2957_, v_b_2955_);
lean_dec_ref(v_as_2952_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_2959_, lean_object* v_revArgs_2960_){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2961_ = lean_array_get_size(v_revArgs_2960_);
v___x_2962_ = lean_unsigned_to_nat(0u);
v___x_2963_ = lean_nat_dec_lt(v___x_2962_, v___x_2961_);
if (v___x_2963_ == 0)
{
return v_fn_2959_;
}
else
{
size_t v___x_2964_; size_t v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = lean_usize_of_nat(v___x_2961_);
v___x_2965_ = ((size_t)0ULL);
v___x_2966_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_2960_, v___x_2964_, v___x_2965_, v_fn_2959_);
return v___x_2966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_2967_, lean_object* v_revArgs_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_mkAppRev(v_fn_2967_, v_revArgs_2968_);
lean_dec_ref(v_revArgs_2968_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = lean_expr_dbg_to_string(v_e_2971_);
lean_dec_ref(v_e_2971_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_2975_, lean_object* v_b_2976_){
_start:
{
uint8_t v_res_2977_; lean_object* v_r_2978_; 
v_res_2977_ = lean_expr_quick_lt(v_a_2975_, v_b_2976_);
lean_dec_ref(v_b_2976_);
lean_dec_ref(v_a_2975_);
v_r_2978_ = lean_box(v_res_2977_);
return v_r_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_2981_, lean_object* v_b_2982_){
_start:
{
uint8_t v_res_2983_; lean_object* v_r_2984_; 
v_res_2983_ = lean_expr_lt(v_a_2981_, v_b_2982_);
lean_dec_ref(v_b_2982_);
lean_dec_ref(v_a_2981_);
v_r_2984_ = lean_box(v_res_2983_);
return v_r_2984_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* v_a_2985_, lean_object* v_b_2986_){
_start:
{
uint8_t v___x_2987_; 
v___x_2987_ = lean_expr_quick_lt(v_a_2985_, v_b_2986_);
if (v___x_2987_ == 0)
{
uint8_t v___x_2988_; 
v___x_2988_ = lean_expr_quick_lt(v_b_2986_, v_a_2985_);
if (v___x_2988_ == 0)
{
uint8_t v___x_2989_; 
v___x_2989_ = 1;
return v___x_2989_;
}
else
{
uint8_t v___x_2990_; 
v___x_2990_ = 2;
return v___x_2990_;
}
}
else
{
uint8_t v___x_2991_; 
v___x_2991_ = 0;
return v___x_2991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_2992_, lean_object* v_b_2993_){
_start:
{
uint8_t v_res_2994_; lean_object* v_r_2995_; 
v_res_2994_ = l_Lean_Expr_quickComp(v_a_2992_, v_b_2993_);
lean_dec_ref(v_b_2993_);
lean_dec_ref(v_a_2992_);
v_r_2995_ = lean_box(v_res_2994_);
return v_r_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_2998_, lean_object* v_b_2999_){
_start:
{
uint8_t v_res_3000_; lean_object* v_r_3001_; 
v_res_3000_ = lean_expr_eqv(v_a_2998_, v_b_2999_);
lean_dec_ref(v_b_2999_);
lean_dec_ref(v_a_2998_);
v_r_3001_ = lean_box(v_res_3000_);
return v_r_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3006_, lean_object* v_b_3007_){
_start:
{
uint8_t v_res_3008_; lean_object* v_r_3009_; 
v_res_3008_ = lean_expr_equal(v_a_3006_, v_b_3007_);
lean_dec_ref(v_b_3007_);
lean_dec_ref(v_a_3006_);
v_r_3009_ = lean_box(v_res_3008_);
return v_r_3009_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* v_x_3010_){
_start:
{
if (lean_obj_tag(v_x_3010_) == 3)
{
uint8_t v___x_3011_; 
v___x_3011_ = 1;
return v___x_3011_;
}
else
{
uint8_t v___x_3012_; 
v___x_3012_ = 0;
return v___x_3012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3013_){
_start:
{
uint8_t v_res_3014_; lean_object* v_r_3015_; 
v_res_3014_ = l_Lean_Expr_isSort(v_x_3013_);
lean_dec_ref(v_x_3013_);
v_r_3015_ = lean_box(v_res_3014_);
return v_r_3015_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* v_x_3016_){
_start:
{
if (lean_obj_tag(v_x_3016_) == 3)
{
lean_object* v_u_3017_; 
v_u_3017_ = lean_ctor_get(v_x_3016_, 0);
if (lean_obj_tag(v_u_3017_) == 1)
{
uint8_t v___x_3018_; 
v___x_3018_ = 1;
return v___x_3018_;
}
else
{
uint8_t v___x_3019_; 
v___x_3019_ = 0;
return v___x_3019_;
}
}
else
{
uint8_t v___x_3020_; 
v___x_3020_ = 0;
return v___x_3020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3021_){
_start:
{
uint8_t v_res_3022_; lean_object* v_r_3023_; 
v_res_3022_ = l_Lean_Expr_isType(v_x_3021_);
lean_dec_ref(v_x_3021_);
v_r_3023_ = lean_box(v_res_3022_);
return v_r_3023_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* v_x_3024_){
_start:
{
if (lean_obj_tag(v_x_3024_) == 3)
{
lean_object* v_u_3025_; 
v_u_3025_ = lean_ctor_get(v_x_3024_, 0);
if (lean_obj_tag(v_u_3025_) == 1)
{
lean_object* v_a_3026_; 
v_a_3026_ = lean_ctor_get(v_u_3025_, 0);
if (lean_obj_tag(v_a_3026_) == 0)
{
uint8_t v___x_3027_; 
v___x_3027_ = 1;
return v___x_3027_;
}
else
{
uint8_t v___x_3028_; 
v___x_3028_ = 0;
return v___x_3028_;
}
}
else
{
uint8_t v___x_3029_; 
v___x_3029_ = 0;
return v___x_3029_;
}
}
else
{
uint8_t v___x_3030_; 
v___x_3030_ = 0;
return v___x_3030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3031_){
_start:
{
uint8_t v_res_3032_; lean_object* v_r_3033_; 
v_res_3032_ = l_Lean_Expr_isType0(v_x_3031_);
lean_dec_ref(v_x_3031_);
v_r_3033_ = lean_box(v_res_3032_);
return v_r_3033_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* v_x_3034_){
_start:
{
if (lean_obj_tag(v_x_3034_) == 3)
{
lean_object* v_u_3035_; 
v_u_3035_ = lean_ctor_get(v_x_3034_, 0);
if (lean_obj_tag(v_u_3035_) == 0)
{
uint8_t v___x_3036_; 
v___x_3036_ = 1;
return v___x_3036_;
}
else
{
uint8_t v___x_3037_; 
v___x_3037_ = 0;
return v___x_3037_;
}
}
else
{
uint8_t v___x_3038_; 
v___x_3038_ = 0;
return v___x_3038_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3039_){
_start:
{
uint8_t v_res_3040_; lean_object* v_r_3041_; 
v_res_3040_ = l_Lean_Expr_isProp(v_x_3039_);
lean_dec_ref(v_x_3039_);
v_r_3041_ = lean_box(v_res_3040_);
return v_r_3041_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3042_){
_start:
{
if (lean_obj_tag(v_x_3042_) == 0)
{
uint8_t v___x_3043_; 
v___x_3043_ = 1;
return v___x_3043_;
}
else
{
uint8_t v___x_3044_; 
v___x_3044_ = 0;
return v___x_3044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3045_){
_start:
{
uint8_t v_res_3046_; lean_object* v_r_3047_; 
v_res_3046_ = l_Lean_Expr_isBVar(v_x_3045_);
lean_dec_ref(v_x_3045_);
v_r_3047_ = lean_box(v_res_3046_);
return v_r_3047_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3048_){
_start:
{
if (lean_obj_tag(v_x_3048_) == 2)
{
uint8_t v___x_3049_; 
v___x_3049_ = 1;
return v___x_3049_;
}
else
{
uint8_t v___x_3050_; 
v___x_3050_ = 0;
return v___x_3050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3051_){
_start:
{
uint8_t v_res_3052_; lean_object* v_r_3053_; 
v_res_3052_ = l_Lean_Expr_isMVar(v_x_3051_);
lean_dec_ref(v_x_3051_);
v_r_3053_ = lean_box(v_res_3052_);
return v_r_3053_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3054_){
_start:
{
if (lean_obj_tag(v_x_3054_) == 1)
{
uint8_t v___x_3055_; 
v___x_3055_ = 1;
return v___x_3055_;
}
else
{
uint8_t v___x_3056_; 
v___x_3056_ = 0;
return v___x_3056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3057_){
_start:
{
uint8_t v_res_3058_; lean_object* v_r_3059_; 
v_res_3058_ = l_Lean_Expr_isFVar(v_x_3057_);
lean_dec_ref(v_x_3057_);
v_r_3059_ = lean_box(v_res_3058_);
return v_r_3059_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* v_x_3060_){
_start:
{
if (lean_obj_tag(v_x_3060_) == 5)
{
uint8_t v___x_3061_; 
v___x_3061_ = 1;
return v___x_3061_;
}
else
{
uint8_t v___x_3062_; 
v___x_3062_ = 0;
return v___x_3062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3063_){
_start:
{
uint8_t v_res_3064_; lean_object* v_r_3065_; 
v_res_3064_ = l_Lean_Expr_isApp(v_x_3063_);
lean_dec_ref(v_x_3063_);
v_r_3065_ = lean_box(v_res_3064_);
return v_r_3065_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* v_x_3066_){
_start:
{
if (lean_obj_tag(v_x_3066_) == 11)
{
uint8_t v___x_3067_; 
v___x_3067_ = 1;
return v___x_3067_;
}
else
{
uint8_t v___x_3068_; 
v___x_3068_ = 0;
return v___x_3068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3069_){
_start:
{
uint8_t v_res_3070_; lean_object* v_r_3071_; 
v_res_3070_ = l_Lean_Expr_isProj(v_x_3069_);
lean_dec_ref(v_x_3069_);
v_r_3071_ = lean_box(v_res_3070_);
return v_r_3071_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* v_x_3072_){
_start:
{
if (lean_obj_tag(v_x_3072_) == 4)
{
uint8_t v___x_3073_; 
v___x_3073_ = 1;
return v___x_3073_;
}
else
{
uint8_t v___x_3074_; 
v___x_3074_ = 0;
return v___x_3074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3075_){
_start:
{
uint8_t v_res_3076_; lean_object* v_r_3077_; 
v_res_3076_ = l_Lean_Expr_isConst(v_x_3075_);
lean_dec_ref(v_x_3075_);
v_r_3077_ = lean_box(v_res_3076_);
return v_r_3077_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3078_, lean_object* v_x_3079_){
_start:
{
if (lean_obj_tag(v_x_3078_) == 4)
{
lean_object* v_declName_3080_; uint8_t v___x_3081_; 
v_declName_3080_ = lean_ctor_get(v_x_3078_, 0);
v___x_3081_ = lean_name_eq(v_declName_3080_, v_x_3079_);
return v___x_3081_;
}
else
{
uint8_t v___x_3082_; 
v___x_3082_ = 0;
return v___x_3082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3083_, lean_object* v_x_3084_){
_start:
{
uint8_t v_res_3085_; lean_object* v_r_3086_; 
v_res_3085_ = l_Lean_Expr_isConstOf(v_x_3083_, v_x_3084_);
lean_dec(v_x_3084_);
lean_dec_ref(v_x_3083_);
v_r_3086_ = lean_box(v_res_3085_);
return v_r_3086_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3087_, lean_object* v_x_3088_){
_start:
{
if (lean_obj_tag(v_x_3087_) == 1)
{
lean_object* v_fvarId_3089_; uint8_t v___x_3090_; 
v_fvarId_3089_ = lean_ctor_get(v_x_3087_, 0);
v___x_3090_ = lean_name_eq(v_fvarId_3089_, v_x_3088_);
return v___x_3090_;
}
else
{
uint8_t v___x_3091_; 
v___x_3091_ = 0;
return v___x_3091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3092_, lean_object* v_x_3093_){
_start:
{
uint8_t v_res_3094_; lean_object* v_r_3095_; 
v_res_3094_ = l_Lean_Expr_isFVarOf(v_x_3092_, v_x_3093_);
lean_dec(v_x_3093_);
lean_dec_ref(v_x_3092_);
v_r_3095_ = lean_box(v_res_3094_);
return v_r_3095_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* v_x_3096_){
_start:
{
if (lean_obj_tag(v_x_3096_) == 7)
{
uint8_t v___x_3097_; 
v___x_3097_ = 1;
return v___x_3097_;
}
else
{
uint8_t v___x_3098_; 
v___x_3098_ = 0;
return v___x_3098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3099_){
_start:
{
uint8_t v_res_3100_; lean_object* v_r_3101_; 
v_res_3100_ = l_Lean_Expr_isForall(v_x_3099_);
lean_dec_ref(v_x_3099_);
v_r_3101_ = lean_box(v_res_3100_);
return v_r_3101_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3102_){
_start:
{
if (lean_obj_tag(v_x_3102_) == 6)
{
uint8_t v___x_3103_; 
v___x_3103_ = 1;
return v___x_3103_;
}
else
{
uint8_t v___x_3104_; 
v___x_3104_ = 0;
return v___x_3104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3105_){
_start:
{
uint8_t v_res_3106_; lean_object* v_r_3107_; 
v_res_3106_ = l_Lean_Expr_isLambda(v_x_3105_);
lean_dec_ref(v_x_3105_);
v_r_3107_ = lean_box(v_res_3106_);
return v_r_3107_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3108_){
_start:
{
switch(lean_obj_tag(v_x_3108_))
{
case 6:
{
uint8_t v___x_3109_; 
v___x_3109_ = 1;
return v___x_3109_;
}
case 7:
{
uint8_t v___x_3110_; 
v___x_3110_ = 1;
return v___x_3110_;
}
default: 
{
uint8_t v___x_3111_; 
v___x_3111_ = 0;
return v___x_3111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3112_){
_start:
{
uint8_t v_res_3113_; lean_object* v_r_3114_; 
v_res_3113_ = l_Lean_Expr_isBinding(v_x_3112_);
lean_dec_ref(v_x_3112_);
v_r_3114_ = lean_box(v_res_3113_);
return v_r_3114_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* v_x_3115_){
_start:
{
if (lean_obj_tag(v_x_3115_) == 8)
{
uint8_t v___x_3116_; 
v___x_3116_ = 1;
return v___x_3116_;
}
else
{
uint8_t v___x_3117_; 
v___x_3117_ = 0;
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3118_){
_start:
{
uint8_t v_res_3119_; lean_object* v_r_3120_; 
v_res_3119_ = l_Lean_Expr_isLet(v_x_3118_);
lean_dec_ref(v_x_3118_);
v_r_3120_ = lean_box(v_res_3119_);
return v_r_3120_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object* v_x_3121_){
_start:
{
if (lean_obj_tag(v_x_3121_) == 8)
{
uint8_t v_nondep_3122_; 
v_nondep_3122_ = lean_ctor_get_uint8(v_x_3121_, sizeof(void*)*4 + 8);
return v_nondep_3122_;
}
else
{
uint8_t v___x_3123_; 
v___x_3123_ = 0;
return v___x_3123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3124_){
_start:
{
uint8_t v_res_3125_; lean_object* v_r_3126_; 
v_res_3125_ = l_Lean_Expr_isHave(v_x_3124_);
lean_dec_ref(v_x_3124_);
v_r_3126_ = lean_box(v_res_3125_);
return v_r_3126_;
}
}
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object* v_a_3127_){
_start:
{
uint8_t v___x_3128_; 
v___x_3128_ = l_Lean_Expr_isHave(v_a_3127_);
lean_dec_ref(v_a_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3129_){
_start:
{
uint8_t v_res_3130_; lean_object* v_r_3131_; 
v_res_3130_ = lean_expr_is_have(v_a_3129_);
v_r_3131_ = lean_box(v_res_3130_);
return v_r_3131_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* v_x_3132_){
_start:
{
if (lean_obj_tag(v_x_3132_) == 10)
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3135_){
_start:
{
uint8_t v_res_3136_; lean_object* v_r_3137_; 
v_res_3136_ = l_Lean_Expr_isMData(v_x_3135_);
lean_dec_ref(v_x_3135_);
v_r_3137_ = lean_box(v_res_3136_);
return v_r_3137_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* v_x_3138_){
_start:
{
if (lean_obj_tag(v_x_3138_) == 9)
{
uint8_t v___x_3139_; 
v___x_3139_ = 1;
return v___x_3139_;
}
else
{
uint8_t v___x_3140_; 
v___x_3140_ = 0;
return v___x_3140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3141_){
_start:
{
uint8_t v_res_3142_; lean_object* v_r_3143_; 
v_res_3142_ = l_Lean_Expr_isLit(v_x_3141_);
lean_dec_ref(v_x_3141_);
v_r_3143_ = lean_box(v_res_3142_);
return v_r_3143_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3144_){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = l_Lean_instInhabitedExpr;
v___x_3146_ = lean_panic_fn(v___x_3145_, v_msg_3144_);
return v___x_3146_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3150_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3151_ = lean_unsigned_to_nat(15u);
v___x_3152_ = lean_unsigned_to_nat(922u);
v___x_3153_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3154_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3155_ = l_mkPanicMessageWithDecl(v___x_3154_, v___x_3153_, v___x_3152_, v___x_3151_, v___x_3150_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3156_){
_start:
{
if (lean_obj_tag(v_x_3156_) == 5)
{
lean_object* v_fn_3157_; 
v_fn_3157_ = lean_ctor_get(v_x_3156_, 0);
lean_inc_ref(v_fn_3157_);
return v_fn_3157_;
}
else
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3159_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3158_);
return v___x_3159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_Expr_appFn_x21(v_x_3160_);
lean_dec_ref(v_x_3160_);
return v_res_3161_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3163_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3164_ = lean_unsigned_to_nat(15u);
v___x_3165_ = lean_unsigned_to_nat(926u);
v___x_3166_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3167_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3168_ = l_mkPanicMessageWithDecl(v___x_3167_, v___x_3166_, v___x_3165_, v___x_3164_, v___x_3163_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3169_){
_start:
{
if (lean_obj_tag(v_x_3169_) == 5)
{
lean_object* v_arg_3170_; 
v_arg_3170_ = lean_ctor_get(v_x_3169_, 1);
lean_inc_ref(v_arg_3170_);
return v_arg_3170_;
}
else
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3172_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3171_);
return v___x_3172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Lean_Expr_appArg_x21(v_x_3173_);
lean_dec_ref(v_x_3173_);
return v_res_3174_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3176_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3177_ = lean_unsigned_to_nat(17u);
v___x_3178_ = lean_unsigned_to_nat(931u);
v___x_3179_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3180_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3181_ = l_mkPanicMessageWithDecl(v___x_3180_, v___x_3179_, v___x_3178_, v___x_3177_, v___x_3176_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3182_){
_start:
{
switch(lean_obj_tag(v_x_3182_))
{
case 10:
{
lean_object* v_expr_3183_; 
v_expr_3183_ = lean_ctor_get(v_x_3182_, 1);
v_x_3182_ = v_expr_3183_;
goto _start;
}
case 5:
{
lean_object* v_fn_3185_; 
v_fn_3185_ = lean_ctor_get(v_x_3182_, 0);
lean_inc_ref(v_fn_3185_);
return v_fn_3185_;
}
default: 
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3187_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3186_);
return v___x_3187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Lean_Expr_appFn_x21_x27(v_x_3188_);
lean_dec_ref(v_x_3188_);
return v_res_3189_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3191_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3192_ = lean_unsigned_to_nat(17u);
v___x_3193_ = lean_unsigned_to_nat(936u);
v___x_3194_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3195_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3196_ = l_mkPanicMessageWithDecl(v___x_3195_, v___x_3194_, v___x_3193_, v___x_3192_, v___x_3191_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3197_){
_start:
{
switch(lean_obj_tag(v_x_3197_))
{
case 10:
{
lean_object* v_expr_3198_; 
v_expr_3198_ = lean_ctor_get(v_x_3197_, 1);
v_x_3197_ = v_expr_3198_;
goto _start;
}
case 5:
{
lean_object* v_arg_3200_; 
v_arg_3200_ = lean_ctor_get(v_x_3197_, 1);
lean_inc_ref(v_arg_3200_);
return v_arg_3200_;
}
default: 
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3202_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3201_);
return v___x_3202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Lean_Expr_appArg_x21_x27(v_x_3203_);
lean_dec_ref(v_x_3203_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3205_){
_start:
{
lean_object* v_arg_3206_; 
v_arg_3206_ = lean_ctor_get(v_e_3205_, 1);
lean_inc_ref(v_arg_3206_);
return v_arg_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_Expr_appArg___redArg(v_e_3207_);
lean_dec_ref(v_e_3207_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3209_, lean_object* v_h_3210_){
_start:
{
lean_object* v_arg_3211_; 
v_arg_3211_ = lean_ctor_get(v_e_3209_, 1);
lean_inc_ref(v_arg_3211_);
return v_arg_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3212_, lean_object* v_h_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_Expr_appArg(v_e_3212_, v_h_3213_);
lean_dec_ref(v_e_3212_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3215_){
_start:
{
lean_object* v_fn_3216_; 
v_fn_3216_ = lean_ctor_get(v_e_3215_, 0);
lean_inc_ref(v_fn_3216_);
return v_fn_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_Expr_appFn___redArg(v_e_3217_);
lean_dec_ref(v_e_3217_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3219_, lean_object* v_h_3220_){
_start:
{
lean_object* v_fn_3221_; 
v_fn_3221_ = lean_ctor_get(v_e_3219_, 0);
lean_inc_ref(v_fn_3221_);
return v_fn_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3222_, lean_object* v_h_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Lean_Expr_appFn(v_e_3222_, v_h_3223_);
lean_dec_ref(v_e_3222_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3225_){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_box(0);
v___x_3227_ = lean_panic_fn(v___x_3226_, v_msg_3225_);
return v___x_3227_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3230_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3231_ = lean_unsigned_to_nat(14u);
v___x_3232_ = lean_unsigned_to_nat(948u);
v___x_3233_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3234_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3235_ = l_mkPanicMessageWithDecl(v___x_3234_, v___x_3233_, v___x_3232_, v___x_3231_, v___x_3230_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3236_){
_start:
{
if (lean_obj_tag(v_x_3236_) == 3)
{
lean_object* v_u_3237_; 
v_u_3237_ = lean_ctor_get(v_x_3236_, 0);
lean_inc(v_u_3237_);
return v_u_3237_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3239_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3238_);
return v___x_3239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_Expr_sortLevel_x21(v_x_3240_);
lean_dec_ref(v_x_3240_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3242_){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3244_ = lean_panic_fn(v___x_3243_, v_msg_3242_);
return v___x_3244_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3247_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3248_ = lean_unsigned_to_nat(13u);
v___x_3249_ = lean_unsigned_to_nat(952u);
v___x_3250_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3251_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3252_ = l_mkPanicMessageWithDecl(v___x_3251_, v___x_3250_, v___x_3249_, v___x_3248_, v___x_3247_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3253_){
_start:
{
if (lean_obj_tag(v_x_3253_) == 9)
{
lean_object* v_a_3254_; 
v_a_3254_ = lean_ctor_get(v_x_3253_, 0);
lean_inc_ref(v_a_3254_);
return v_a_3254_;
}
else
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3256_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3255_);
return v___x_3256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_Expr_litValue_x21(v_x_3257_);
lean_dec_ref(v_x_3257_);
return v_res_3258_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3259_){
_start:
{
if (lean_obj_tag(v_x_3259_) == 9)
{
lean_object* v_a_3260_; 
v_a_3260_ = lean_ctor_get(v_x_3259_, 0);
if (lean_obj_tag(v_a_3260_) == 0)
{
uint8_t v___x_3261_; 
v___x_3261_ = 1;
return v___x_3261_;
}
else
{
uint8_t v___x_3262_; 
v___x_3262_ = 0;
return v___x_3262_;
}
}
else
{
uint8_t v___x_3263_; 
v___x_3263_ = 0;
return v___x_3263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3264_){
_start:
{
uint8_t v_res_3265_; lean_object* v_r_3266_; 
v_res_3265_ = l_Lean_Expr_isRawNatLit(v_x_3264_);
lean_dec_ref(v_x_3264_);
v_r_3266_ = lean_box(v_res_3265_);
return v_r_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3267_){
_start:
{
if (lean_obj_tag(v_x_3267_) == 9)
{
lean_object* v_a_3268_; 
v_a_3268_ = lean_ctor_get(v_x_3267_, 0);
lean_inc_ref(v_a_3268_);
lean_dec_ref(v_x_3267_);
if (lean_obj_tag(v_a_3268_) == 0)
{
lean_object* v_val_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
v_val_3269_ = lean_ctor_get(v_a_3268_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v_a_3268_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v_a_3268_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_val_3269_);
lean_dec(v_a_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
lean_ctor_set_tag(v___x_3271_, 1);
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_val_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
else
{
lean_object* v___x_3277_; 
lean_dec_ref(v_a_3268_);
v___x_3277_ = lean_box(0);
return v___x_3277_;
}
}
else
{
lean_object* v___x_3278_; 
lean_dec_ref(v_x_3267_);
v___x_3278_ = lean_box(0);
return v___x_3278_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3279_){
_start:
{
if (lean_obj_tag(v_x_3279_) == 9)
{
lean_object* v_a_3280_; 
v_a_3280_ = lean_ctor_get(v_x_3279_, 0);
if (lean_obj_tag(v_a_3280_) == 1)
{
uint8_t v___x_3281_; 
v___x_3281_ = 1;
return v___x_3281_;
}
else
{
uint8_t v___x_3282_; 
v___x_3282_ = 0;
return v___x_3282_;
}
}
else
{
uint8_t v___x_3283_; 
v___x_3283_ = 0;
return v___x_3283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3284_){
_start:
{
uint8_t v_res_3285_; lean_object* v_r_3286_; 
v_res_3285_ = l_Lean_Expr_isStringLit(v_x_3284_);
lean_dec_ref(v_x_3284_);
v_r_3286_ = lean_box(v_res_3285_);
return v_r_3286_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3291_){
_start:
{
if (lean_obj_tag(v_x_3291_) == 5)
{
lean_object* v_fn_3292_; 
v_fn_3292_ = lean_ctor_get(v_x_3291_, 0);
if (lean_obj_tag(v_fn_3292_) == 4)
{
lean_object* v_arg_3293_; lean_object* v_declName_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
v_arg_3293_ = lean_ctor_get(v_x_3291_, 1);
v_declName_3294_ = lean_ctor_get(v_fn_3292_, 0);
v___x_3295_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3296_ = lean_name_eq(v_declName_3294_, v___x_3295_);
if (v___x_3296_ == 0)
{
return v___x_3296_;
}
else
{
uint8_t v___x_3297_; 
v___x_3297_ = l_Lean_Expr_isRawNatLit(v_arg_3293_);
return v___x_3297_;
}
}
else
{
uint8_t v___x_3298_; 
v___x_3298_ = 0;
return v___x_3298_;
}
}
else
{
uint8_t v___x_3299_; 
v___x_3299_ = 0;
return v___x_3299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3300_){
_start:
{
uint8_t v_res_3301_; lean_object* v_r_3302_; 
v_res_3301_ = l_Lean_Expr_isCharLit(v_x_3300_);
lean_dec_ref(v_x_3300_);
v_r_3302_ = lean_box(v_res_3301_);
return v_r_3302_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3303_){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_panic_fn(v___x_3304_, v_msg_3303_);
return v___x_3305_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3308_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3309_ = lean_unsigned_to_nat(17u);
v___x_3310_ = lean_unsigned_to_nat(976u);
v___x_3311_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3312_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3313_ = l_mkPanicMessageWithDecl(v___x_3312_, v___x_3311_, v___x_3310_, v___x_3309_, v___x_3308_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3314_){
_start:
{
if (lean_obj_tag(v_x_3314_) == 4)
{
lean_object* v_declName_3315_; 
v_declName_3315_ = lean_ctor_get(v_x_3314_, 0);
lean_inc(v_declName_3315_);
return v_declName_3315_;
}
else
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3317_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3316_);
return v___x_3317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_Expr_constName_x21(v_x_3318_);
lean_dec_ref(v_x_3318_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3320_){
_start:
{
if (lean_obj_tag(v_x_3320_) == 4)
{
lean_object* v_declName_3321_; lean_object* v___x_3322_; 
v_declName_3321_ = lean_ctor_get(v_x_3320_, 0);
lean_inc(v_declName_3321_);
v___x_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3322_, 0, v_declName_3321_);
return v___x_3322_;
}
else
{
lean_object* v___x_3323_; 
v___x_3323_ = lean_box(0);
return v___x_3323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Lean_Expr_constName_x3f(v_x_3324_);
lean_dec_ref(v_x_3324_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3326_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Lean_Expr_constName_x3f(v_e_3326_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v___x_3328_; 
v___x_3328_ = lean_box(0);
return v___x_3328_;
}
else
{
lean_object* v_val_3329_; 
v_val_3329_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_val_3329_);
lean_dec_ref(v___x_3327_);
return v_val_3329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_Expr_constName(v_e_3330_);
lean_dec_ref(v_e_3330_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3332_){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = lean_box(0);
v___x_3334_ = lean_panic_fn(v___x_3333_, v_msg_3332_);
return v___x_3334_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3336_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3337_ = lean_unsigned_to_nat(18u);
v___x_3338_ = lean_unsigned_to_nat(996u);
v___x_3339_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3340_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3341_ = l_mkPanicMessageWithDecl(v___x_3340_, v___x_3339_, v___x_3338_, v___x_3337_, v___x_3336_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3342_){
_start:
{
if (lean_obj_tag(v_x_3342_) == 4)
{
lean_object* v_us_3343_; 
v_us_3343_ = lean_ctor_get(v_x_3342_, 1);
lean_inc(v_us_3343_);
return v_us_3343_;
}
else
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3345_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3344_);
return v___x_3345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_Expr_constLevels_x21(v_x_3346_);
lean_dec_ref(v_x_3346_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3348_){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = lean_unsigned_to_nat(0u);
v___x_3350_ = lean_panic_fn(v___x_3349_, v_msg_3348_);
return v___x_3350_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3353_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3354_ = lean_unsigned_to_nat(16u);
v___x_3355_ = lean_unsigned_to_nat(1000u);
v___x_3356_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3357_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3358_ = l_mkPanicMessageWithDecl(v___x_3357_, v___x_3356_, v___x_3355_, v___x_3354_, v___x_3353_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3359_){
_start:
{
if (lean_obj_tag(v_x_3359_) == 0)
{
lean_object* v_deBruijnIndex_3360_; 
v_deBruijnIndex_3360_ = lean_ctor_get(v_x_3359_, 0);
lean_inc(v_deBruijnIndex_3360_);
return v_deBruijnIndex_3360_;
}
else
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3362_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3361_);
return v___x_3362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Expr_bvarIdx_x21(v_x_3363_);
lean_dec_ref(v_x_3363_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3365_){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = lean_box(0);
v___x_3367_ = lean_panic_fn(v___x_3366_, v_msg_3365_);
return v___x_3367_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3370_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3371_ = lean_unsigned_to_nat(14u);
v___x_3372_ = lean_unsigned_to_nat(1004u);
v___x_3373_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3374_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3375_ = l_mkPanicMessageWithDecl(v___x_3374_, v___x_3373_, v___x_3372_, v___x_3371_, v___x_3370_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3376_){
_start:
{
if (lean_obj_tag(v_x_3376_) == 1)
{
lean_object* v_fvarId_3377_; 
v_fvarId_3377_ = lean_ctor_get(v_x_3376_, 0);
lean_inc(v_fvarId_3377_);
return v_fvarId_3377_;
}
else
{
lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3378_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3379_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3378_);
return v___x_3379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_Expr_fvarId_x21(v_x_3380_);
lean_dec_ref(v_x_3380_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3382_){
_start:
{
if (lean_obj_tag(v_x_3382_) == 1)
{
lean_object* v_fvarId_3383_; lean_object* v___x_3384_; 
v_fvarId_3383_ = lean_ctor_get(v_x_3382_, 0);
lean_inc(v_fvarId_3383_);
v___x_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_fvarId_3383_);
return v___x_3384_;
}
else
{
lean_object* v___x_3385_; 
v___x_3385_ = lean_box(0);
return v___x_3385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_Expr_fvarId_x3f(v_x_3386_);
lean_dec_ref(v_x_3386_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3388_){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = lean_box(0);
v___x_3390_ = lean_panic_fn(v___x_3389_, v_msg_3388_);
return v___x_3390_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3393_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3394_ = lean_unsigned_to_nat(14u);
v___x_3395_ = lean_unsigned_to_nat(1012u);
v___x_3396_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3397_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3398_ = l_mkPanicMessageWithDecl(v___x_3397_, v___x_3396_, v___x_3395_, v___x_3394_, v___x_3393_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3399_){
_start:
{
if (lean_obj_tag(v_x_3399_) == 2)
{
lean_object* v_mvarId_3400_; 
v_mvarId_3400_ = lean_ctor_get(v_x_3399_, 0);
lean_inc(v_mvarId_3400_);
return v_mvarId_3400_;
}
else
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3402_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3401_);
return v___x_3402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_Lean_Expr_mvarId_x21(v_x_3403_);
lean_dec_ref(v_x_3403_);
return v_res_3404_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3407_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3408_ = lean_unsigned_to_nat(23u);
v___x_3409_ = lean_unsigned_to_nat(1017u);
v___x_3410_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3411_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3412_ = l_mkPanicMessageWithDecl(v___x_3411_, v___x_3410_, v___x_3409_, v___x_3408_, v___x_3407_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3413_){
_start:
{
switch(lean_obj_tag(v_x_3413_))
{
case 7:
{
lean_object* v_binderName_3414_; 
v_binderName_3414_ = lean_ctor_get(v_x_3413_, 0);
lean_inc(v_binderName_3414_);
return v_binderName_3414_;
}
case 6:
{
lean_object* v_binderName_3415_; 
v_binderName_3415_ = lean_ctor_get(v_x_3413_, 0);
lean_inc(v_binderName_3415_);
return v_binderName_3415_;
}
default: 
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3417_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3416_);
return v___x_3417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_Expr_bindingName_x21(v_x_3418_);
lean_dec_ref(v_x_3418_);
return v_res_3419_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3421_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3422_ = lean_unsigned_to_nat(23u);
v___x_3423_ = lean_unsigned_to_nat(1022u);
v___x_3424_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3425_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3426_ = l_mkPanicMessageWithDecl(v___x_3425_, v___x_3424_, v___x_3423_, v___x_3422_, v___x_3421_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3427_){
_start:
{
switch(lean_obj_tag(v_x_3427_))
{
case 7:
{
lean_object* v_binderType_3428_; 
v_binderType_3428_ = lean_ctor_get(v_x_3427_, 1);
lean_inc_ref(v_binderType_3428_);
return v_binderType_3428_;
}
case 6:
{
lean_object* v_binderType_3429_; 
v_binderType_3429_ = lean_ctor_get(v_x_3427_, 1);
lean_inc_ref(v_binderType_3429_);
return v_binderType_3429_;
}
default: 
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3431_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3430_);
return v___x_3431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Expr_bindingDomain_x21(v_x_3432_);
lean_dec_ref(v_x_3432_);
return v_res_3433_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3435_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3436_ = lean_unsigned_to_nat(23u);
v___x_3437_ = lean_unsigned_to_nat(1027u);
v___x_3438_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3439_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3440_ = l_mkPanicMessageWithDecl(v___x_3439_, v___x_3438_, v___x_3437_, v___x_3436_, v___x_3435_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3441_){
_start:
{
switch(lean_obj_tag(v_x_3441_))
{
case 7:
{
lean_object* v_body_3442_; 
v_body_3442_ = lean_ctor_get(v_x_3441_, 2);
lean_inc_ref(v_body_3442_);
return v_body_3442_;
}
case 6:
{
lean_object* v_body_3443_; 
v_body_3443_ = lean_ctor_get(v_x_3441_, 2);
lean_inc_ref(v_body_3443_);
return v_body_3443_;
}
default: 
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3445_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3444_);
return v___x_3445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Lean_Expr_bindingBody_x21(v_x_3446_);
lean_dec_ref(v_x_3446_);
return v_res_3447_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3448_){
_start:
{
uint8_t v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; 
v___x_3449_ = 0;
v___x_3450_ = lean_box(v___x_3449_);
v___x_3451_ = lean_panic_fn(v___x_3450_, v_msg_3448_);
v___x_3452_ = lean_unbox(v___x_3451_);
lean_dec(v___x_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3453_){
_start:
{
uint8_t v_res_3454_; lean_object* v_r_3455_; 
v_res_3454_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3453_);
v_r_3455_ = lean_box(v_res_3454_);
return v_r_3455_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3457_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3458_ = lean_unsigned_to_nat(24u);
v___x_3459_ = lean_unsigned_to_nat(1032u);
v___x_3460_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3461_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3462_ = l_mkPanicMessageWithDecl(v___x_3461_, v___x_3460_, v___x_3459_, v___x_3458_, v___x_3457_);
return v___x_3462_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3463_){
_start:
{
switch(lean_obj_tag(v_x_3463_))
{
case 7:
{
uint8_t v_binderInfo_3464_; 
v_binderInfo_3464_ = lean_ctor_get_uint8(v_x_3463_, sizeof(void*)*3 + 8);
return v_binderInfo_3464_;
}
case 6:
{
uint8_t v_binderInfo_3465_; 
v_binderInfo_3465_ = lean_ctor_get_uint8(v_x_3463_, sizeof(void*)*3 + 8);
return v_binderInfo_3465_;
}
default: 
{
lean_object* v___x_3466_; uint8_t v___x_3467_; 
v___x_3466_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3467_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3466_);
return v___x_3467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3468_){
_start:
{
uint8_t v_res_3469_; lean_object* v_r_3470_; 
v_res_3469_ = l_Lean_Expr_bindingInfo_x21(v_x_3468_);
lean_dec_ref(v_x_3468_);
v_r_3470_ = lean_box(v_res_3469_);
return v_r_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3471_){
_start:
{
lean_object* v_binderName_3472_; 
v_binderName_3472_ = lean_ctor_get(v_x_3471_, 0);
lean_inc(v_binderName_3472_);
return v_binderName_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Lean_Expr_forallName___redArg(v_x_3473_);
lean_dec_ref(v_x_3473_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3475_, lean_object* v_x_3476_){
_start:
{
lean_object* v_binderName_3477_; 
v_binderName_3477_ = lean_ctor_get(v_x_3475_, 0);
lean_inc(v_binderName_3477_);
return v_binderName_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3478_, lean_object* v_x_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_Expr_forallName(v_x_3478_, v_x_3479_);
lean_dec_ref(v_x_3478_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3481_){
_start:
{
lean_object* v_binderType_3482_; 
v_binderType_3482_ = lean_ctor_get(v_x_3481_, 1);
lean_inc_ref(v_binderType_3482_);
return v_binderType_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_Expr_forallDomain___redArg(v_x_3483_);
lean_dec_ref(v_x_3483_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3485_, lean_object* v_x_3486_){
_start:
{
lean_object* v_binderType_3487_; 
v_binderType_3487_ = lean_ctor_get(v_x_3485_, 1);
lean_inc_ref(v_binderType_3487_);
return v_binderType_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3488_, lean_object* v_x_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_Expr_forallDomain(v_x_3488_, v_x_3489_);
lean_dec_ref(v_x_3488_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3491_){
_start:
{
lean_object* v_body_3492_; 
v_body_3492_ = lean_ctor_get(v_x_3491_, 2);
lean_inc_ref(v_body_3492_);
return v_body_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_Expr_forallBody___redArg(v_x_3493_);
lean_dec_ref(v_x_3493_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3495_, lean_object* v_x_3496_){
_start:
{
lean_object* v_body_3497_; 
v_body_3497_ = lean_ctor_get(v_x_3495_, 2);
lean_inc_ref(v_body_3497_);
return v_body_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3498_, lean_object* v_x_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_Expr_forallBody(v_x_3498_, v_x_3499_);
lean_dec_ref(v_x_3498_);
return v_res_3500_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3501_){
_start:
{
uint8_t v_binderInfo_3502_; 
v_binderInfo_3502_ = lean_ctor_get_uint8(v_x_3501_, sizeof(void*)*3 + 8);
return v_binderInfo_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3503_){
_start:
{
uint8_t v_res_3504_; lean_object* v_r_3505_; 
v_res_3504_ = l_Lean_Expr_forallInfo___redArg(v_x_3503_);
lean_dec_ref(v_x_3503_);
v_r_3505_ = lean_box(v_res_3504_);
return v_r_3505_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3506_, lean_object* v_x_3507_){
_start:
{
uint8_t v_binderInfo_3508_; 
v_binderInfo_3508_ = lean_ctor_get_uint8(v_x_3506_, sizeof(void*)*3 + 8);
return v_binderInfo_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3509_, lean_object* v_x_3510_){
_start:
{
uint8_t v_res_3511_; lean_object* v_r_3512_; 
v_res_3511_ = l_Lean_Expr_forallInfo(v_x_3509_, v_x_3510_);
lean_dec_ref(v_x_3509_);
v_r_3512_ = lean_box(v_res_3511_);
return v_r_3512_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3515_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3516_ = lean_unsigned_to_nat(17u);
v___x_3517_ = lean_unsigned_to_nat(1048u);
v___x_3518_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3519_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3520_ = l_mkPanicMessageWithDecl(v___x_3519_, v___x_3518_, v___x_3517_, v___x_3516_, v___x_3515_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3521_){
_start:
{
if (lean_obj_tag(v_x_3521_) == 8)
{
lean_object* v_declName_3522_; 
v_declName_3522_ = lean_ctor_get(v_x_3521_, 0);
lean_inc(v_declName_3522_);
return v_declName_3522_;
}
else
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3523_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3524_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3523_);
return v___x_3524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Lean_Expr_letName_x21(v_x_3525_);
lean_dec_ref(v_x_3525_);
return v_res_3526_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3528_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3529_ = lean_unsigned_to_nat(19u);
v___x_3530_ = lean_unsigned_to_nat(1052u);
v___x_3531_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3532_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3533_ = l_mkPanicMessageWithDecl(v___x_3532_, v___x_3531_, v___x_3530_, v___x_3529_, v___x_3528_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3534_){
_start:
{
if (lean_obj_tag(v_x_3534_) == 8)
{
lean_object* v_type_3535_; 
v_type_3535_ = lean_ctor_get(v_x_3534_, 1);
lean_inc_ref(v_type_3535_);
return v_type_3535_;
}
else
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3536_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3537_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3536_);
return v___x_3537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_Lean_Expr_letType_x21(v_x_3538_);
lean_dec_ref(v_x_3538_);
return v_res_3539_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3541_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3542_ = lean_unsigned_to_nat(21u);
v___x_3543_ = lean_unsigned_to_nat(1056u);
v___x_3544_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3545_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3546_ = l_mkPanicMessageWithDecl(v___x_3545_, v___x_3544_, v___x_3543_, v___x_3542_, v___x_3541_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3547_){
_start:
{
if (lean_obj_tag(v_x_3547_) == 8)
{
lean_object* v_value_3548_; 
v_value_3548_ = lean_ctor_get(v_x_3547_, 2);
lean_inc_ref(v_value_3548_);
return v_value_3548_;
}
else
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3550_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3549_);
return v___x_3550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l_Lean_Expr_letValue_x21(v_x_3551_);
lean_dec_ref(v_x_3551_);
return v_res_3552_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3554_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3555_ = lean_unsigned_to_nat(23u);
v___x_3556_ = lean_unsigned_to_nat(1060u);
v___x_3557_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3558_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3559_ = l_mkPanicMessageWithDecl(v___x_3558_, v___x_3557_, v___x_3556_, v___x_3555_, v___x_3554_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3560_){
_start:
{
if (lean_obj_tag(v_x_3560_) == 8)
{
lean_object* v_body_3561_; 
v_body_3561_ = lean_ctor_get(v_x_3560_, 3);
lean_inc_ref(v_body_3561_);
return v_body_3561_;
}
else
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3563_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3562_);
return v___x_3563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Lean_Expr_letBody_x21(v_x_3564_);
lean_dec_ref(v_x_3564_);
return v_res_3565_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3566_){
_start:
{
uint8_t v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; uint8_t v___x_3570_; 
v___x_3567_ = 0;
v___x_3568_ = lean_box(v___x_3567_);
v___x_3569_ = lean_panic_fn(v___x_3568_, v_msg_3566_);
v___x_3570_ = lean_unbox(v___x_3569_);
lean_dec(v___x_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3571_){
_start:
{
uint8_t v_res_3572_; lean_object* v_r_3573_; 
v_res_3572_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3571_);
v_r_3573_ = lean_box(v_res_3572_);
return v_r_3573_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3575_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3576_ = lean_unsigned_to_nat(27u);
v___x_3577_ = lean_unsigned_to_nat(1064u);
v___x_3578_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3579_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3580_ = l_mkPanicMessageWithDecl(v___x_3579_, v___x_3578_, v___x_3577_, v___x_3576_, v___x_3575_);
return v___x_3580_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3581_){
_start:
{
if (lean_obj_tag(v_x_3581_) == 8)
{
uint8_t v_nondep_3582_; 
v_nondep_3582_ = lean_ctor_get_uint8(v_x_3581_, sizeof(void*)*4 + 8);
return v_nondep_3582_;
}
else
{
lean_object* v___x_3583_; uint8_t v___x_3584_; 
v___x_3583_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3584_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3583_);
return v___x_3584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3585_){
_start:
{
uint8_t v_res_3586_; lean_object* v_r_3587_; 
v_res_3586_ = l_Lean_Expr_letNondep_x21(v_x_3585_);
lean_dec_ref(v_x_3585_);
v_r_3587_ = lean_box(v_res_3586_);
return v_r_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3588_){
_start:
{
if (lean_obj_tag(v_x_3588_) == 10)
{
lean_object* v_expr_3589_; 
v_expr_3589_ = lean_ctor_get(v_x_3588_, 1);
v_x_3588_ = v_expr_3589_;
goto _start;
}
else
{
lean_inc_ref(v_x_3588_);
return v_x_3588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_Expr_consumeMData(v_x_3591_);
lean_dec_ref(v_x_3591_);
return v_res_3592_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3595_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3596_ = lean_unsigned_to_nat(17u);
v___x_3597_ = lean_unsigned_to_nat(1072u);
v___x_3598_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3599_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3600_ = l_mkPanicMessageWithDecl(v___x_3599_, v___x_3598_, v___x_3597_, v___x_3596_, v___x_3595_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3601_){
_start:
{
if (lean_obj_tag(v_x_3601_) == 10)
{
lean_object* v_expr_3602_; 
v_expr_3602_ = lean_ctor_get(v_x_3601_, 1);
lean_inc_ref(v_expr_3602_);
return v_expr_3602_;
}
else
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3603_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3604_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3603_);
return v___x_3604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Lean_Expr_mdataExpr_x21(v_x_3605_);
lean_dec_ref(v_x_3605_);
return v_res_3606_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3609_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3610_ = lean_unsigned_to_nat(18u);
v___x_3611_ = lean_unsigned_to_nat(1076u);
v___x_3612_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3613_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3614_ = l_mkPanicMessageWithDecl(v___x_3613_, v___x_3612_, v___x_3611_, v___x_3610_, v___x_3609_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3615_){
_start:
{
if (lean_obj_tag(v_x_3615_) == 11)
{
lean_object* v_struct_3616_; 
v_struct_3616_ = lean_ctor_get(v_x_3615_, 2);
lean_inc_ref(v_struct_3616_);
return v_struct_3616_;
}
else
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3618_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3617_);
return v___x_3618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_Expr_projExpr_x21(v_x_3619_);
lean_dec_ref(v_x_3619_);
return v_res_3620_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3622_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3623_ = lean_unsigned_to_nat(18u);
v___x_3624_ = lean_unsigned_to_nat(1080u);
v___x_3625_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3626_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3627_ = l_mkPanicMessageWithDecl(v___x_3626_, v___x_3625_, v___x_3624_, v___x_3623_, v___x_3622_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3628_){
_start:
{
if (lean_obj_tag(v_x_3628_) == 11)
{
lean_object* v_idx_3629_; 
v_idx_3629_ = lean_ctor_get(v_x_3628_, 1);
lean_inc(v_idx_3629_);
return v_idx_3629_;
}
else
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3631_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3630_);
return v___x_3631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Lean_Expr_projIdx_x21(v_x_3632_);
lean_dec_ref(v_x_3632_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3634_){
_start:
{
if (lean_obj_tag(v_x_3634_) == 7)
{
lean_object* v_body_3635_; 
v_body_3635_ = lean_ctor_get(v_x_3634_, 2);
v_x_3634_ = v_body_3635_;
goto _start;
}
else
{
lean_inc_ref(v_x_3634_);
return v_x_3634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Lean_Expr_getForallBody(v_x_3637_);
lean_dec_ref(v_x_3637_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3639_, lean_object* v_x_3640_){
_start:
{
lean_object* v_zero_3641_; uint8_t v_isZero_3642_; 
v_zero_3641_ = lean_unsigned_to_nat(0u);
v_isZero_3642_ = lean_nat_dec_eq(v_x_3639_, v_zero_3641_);
if (v_isZero_3642_ == 1)
{
lean_dec(v_x_3639_);
lean_inc_ref(v_x_3640_);
return v_x_3640_;
}
else
{
if (lean_obj_tag(v_x_3640_) == 7)
{
lean_object* v_body_3643_; lean_object* v_one_3644_; lean_object* v_n_3645_; 
v_body_3643_ = lean_ctor_get(v_x_3640_, 2);
v_one_3644_ = lean_unsigned_to_nat(1u);
v_n_3645_ = lean_nat_sub(v_x_3639_, v_one_3644_);
lean_dec(v_x_3639_);
v_x_3639_ = v_n_3645_;
v_x_3640_ = v_body_3643_;
goto _start;
}
else
{
lean_dec(v_x_3639_);
lean_inc_ref(v_x_3640_);
return v_x_3640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3647_, lean_object* v_x_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3647_, v_x_3648_);
lean_dec_ref(v_x_3648_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3650_){
_start:
{
if (lean_obj_tag(v_x_3650_) == 7)
{
lean_object* v_binderName_3651_; lean_object* v_body_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v_binderName_3651_ = lean_ctor_get(v_x_3650_, 0);
v_body_3652_ = lean_ctor_get(v_x_3650_, 2);
v___x_3653_ = l_Lean_Expr_getForallBinderNames(v_body_3652_);
lean_inc(v_binderName_3651_);
v___x_3654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3654_, 0, v_binderName_3651_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
return v___x_3654_;
}
else
{
lean_object* v___x_3655_; 
v___x_3655_ = lean_box(0);
return v___x_3655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l_Lean_Expr_getForallBinderNames(v_x_3656_);
lean_dec_ref(v_x_3656_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3658_){
_start:
{
switch(lean_obj_tag(v_x_3658_))
{
case 10:
{
lean_object* v_expr_3659_; 
v_expr_3659_ = lean_ctor_get(v_x_3658_, 1);
v_x_3658_ = v_expr_3659_;
goto _start;
}
case 7:
{
lean_object* v_body_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v_body_3661_ = lean_ctor_get(v_x_3658_, 2);
v___x_3662_ = l_Lean_Expr_getNumHeadForalls(v_body_3661_);
v___x_3663_ = lean_unsigned_to_nat(1u);
v___x_3664_ = lean_nat_add(v___x_3662_, v___x_3663_);
lean_dec(v___x_3662_);
return v___x_3664_;
}
default: 
{
lean_object* v___x_3665_; 
v___x_3665_ = lean_unsigned_to_nat(0u);
return v___x_3665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_Expr_getNumHeadForalls(v_x_3666_);
lean_dec_ref(v_x_3666_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3668_){
_start:
{
if (lean_obj_tag(v_x_3668_) == 5)
{
lean_object* v_fn_3669_; 
v_fn_3669_ = lean_ctor_get(v_x_3668_, 0);
v_x_3668_ = v_fn_3669_;
goto _start;
}
else
{
lean_inc_ref(v_x_3668_);
return v_x_3668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_Expr_getAppFn(v_x_3671_);
lean_dec_ref(v_x_3671_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3673_){
_start:
{
switch(lean_obj_tag(v_x_3673_))
{
case 5:
{
lean_object* v_fn_3674_; 
v_fn_3674_ = lean_ctor_get(v_x_3673_, 0);
v_x_3673_ = v_fn_3674_;
goto _start;
}
case 10:
{
lean_object* v_expr_3676_; 
v_expr_3676_ = lean_ctor_get(v_x_3673_, 1);
v_x_3673_ = v_expr_3676_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3673_);
return v_x_3673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l_Lean_Expr_getAppFn_x27(v_x_3678_);
lean_dec_ref(v_x_3678_);
return v_res_3679_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3680_, lean_object* v_n_3681_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_Expr_getAppFn(v_e_3680_);
if (lean_obj_tag(v___x_3682_) == 4)
{
lean_object* v_declName_3683_; uint8_t v___x_3684_; 
v_declName_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_declName_3683_);
lean_dec_ref(v___x_3682_);
v___x_3684_ = lean_name_eq(v_declName_3683_, v_n_3681_);
lean_dec(v_declName_3683_);
return v___x_3684_;
}
else
{
uint8_t v___x_3685_; 
lean_dec_ref(v___x_3682_);
v___x_3685_ = 0;
return v___x_3685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3686_, lean_object* v_n_3687_){
_start:
{
uint8_t v_res_3688_; lean_object* v_r_3689_; 
v_res_3688_ = l_Lean_Expr_isAppOf(v_e_3686_, v_n_3687_);
lean_dec(v_n_3687_);
lean_dec_ref(v_e_3686_);
v_r_3689_ = lean_box(v_res_3688_);
return v_r_3689_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3690_, lean_object* v_x_3691_, lean_object* v_x_3692_){
_start:
{
switch(lean_obj_tag(v_x_3690_))
{
case 4:
{
lean_object* v_declName_3693_; lean_object* v___x_3694_; uint8_t v___x_3695_; 
v_declName_3693_ = lean_ctor_get(v_x_3690_, 0);
v___x_3694_ = lean_unsigned_to_nat(0u);
v___x_3695_ = lean_nat_dec_eq(v_x_3692_, v___x_3694_);
lean_dec(v_x_3692_);
if (v___x_3695_ == 0)
{
return v___x_3695_;
}
else
{
uint8_t v___x_3696_; 
v___x_3696_ = lean_name_eq(v_declName_3693_, v_x_3691_);
return v___x_3696_;
}
}
case 5:
{
lean_object* v_fn_3697_; lean_object* v_zero_3698_; uint8_t v_isZero_3699_; 
v_fn_3697_ = lean_ctor_get(v_x_3690_, 0);
v_zero_3698_ = lean_unsigned_to_nat(0u);
v_isZero_3699_ = lean_nat_dec_eq(v_x_3692_, v_zero_3698_);
if (v_isZero_3699_ == 0)
{
lean_object* v_one_3700_; lean_object* v_n_3701_; 
v_one_3700_ = lean_unsigned_to_nat(1u);
v_n_3701_ = lean_nat_sub(v_x_3692_, v_one_3700_);
lean_dec(v_x_3692_);
v_x_3690_ = v_fn_3697_;
v_x_3692_ = v_n_3701_;
goto _start;
}
else
{
uint8_t v___x_3703_; 
lean_dec(v_x_3692_);
v___x_3703_ = 0;
return v___x_3703_;
}
}
default: 
{
uint8_t v___x_3704_; 
lean_dec(v_x_3692_);
v___x_3704_ = 0;
return v___x_3704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3705_, lean_object* v_x_3706_, lean_object* v_x_3707_){
_start:
{
uint8_t v_res_3708_; lean_object* v_r_3709_; 
v_res_3708_ = l_Lean_Expr_isAppOfArity(v_x_3705_, v_x_3706_, v_x_3707_);
lean_dec(v_x_3706_);
lean_dec_ref(v_x_3705_);
v_r_3709_ = lean_box(v_res_3708_);
return v_r_3709_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3710_, lean_object* v_x_3711_, lean_object* v_x_3712_){
_start:
{
switch(lean_obj_tag(v_x_3710_))
{
case 10:
{
lean_object* v_expr_3713_; 
v_expr_3713_ = lean_ctor_get(v_x_3710_, 1);
v_x_3710_ = v_expr_3713_;
goto _start;
}
case 4:
{
lean_object* v_declName_3715_; lean_object* v___x_3716_; uint8_t v___x_3717_; 
v_declName_3715_ = lean_ctor_get(v_x_3710_, 0);
v___x_3716_ = lean_unsigned_to_nat(0u);
v___x_3717_ = lean_nat_dec_eq(v_x_3712_, v___x_3716_);
lean_dec(v_x_3712_);
if (v___x_3717_ == 0)
{
return v___x_3717_;
}
else
{
uint8_t v___x_3718_; 
v___x_3718_ = lean_name_eq(v_declName_3715_, v_x_3711_);
return v___x_3718_;
}
}
case 5:
{
lean_object* v_fn_3719_; lean_object* v_zero_3720_; uint8_t v_isZero_3721_; 
v_fn_3719_ = lean_ctor_get(v_x_3710_, 0);
v_zero_3720_ = lean_unsigned_to_nat(0u);
v_isZero_3721_ = lean_nat_dec_eq(v_x_3712_, v_zero_3720_);
if (v_isZero_3721_ == 0)
{
lean_object* v_one_3722_; lean_object* v_n_3723_; 
v_one_3722_ = lean_unsigned_to_nat(1u);
v_n_3723_ = lean_nat_sub(v_x_3712_, v_one_3722_);
lean_dec(v_x_3712_);
v_x_3710_ = v_fn_3719_;
v_x_3712_ = v_n_3723_;
goto _start;
}
else
{
uint8_t v___x_3725_; 
lean_dec(v_x_3712_);
v___x_3725_ = 0;
return v___x_3725_;
}
}
default: 
{
uint8_t v___x_3726_; 
lean_dec(v_x_3712_);
v___x_3726_ = 0;
return v___x_3726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3727_, lean_object* v_x_3728_, lean_object* v_x_3729_){
_start:
{
uint8_t v_res_3730_; lean_object* v_r_3731_; 
v_res_3730_ = l_Lean_Expr_isAppOfArity_x27(v_x_3727_, v_x_3728_, v_x_3729_);
lean_dec(v_x_3728_);
lean_dec_ref(v_x_3727_);
v_r_3731_ = lean_box(v_res_3730_);
return v_r_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3732_, lean_object* v_x_3733_){
_start:
{
if (lean_obj_tag(v_x_3732_) == 5)
{
lean_object* v_fn_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v_fn_3734_ = lean_ctor_get(v_x_3732_, 0);
v___x_3735_ = lean_unsigned_to_nat(1u);
v___x_3736_ = lean_nat_add(v_x_3733_, v___x_3735_);
lean_dec(v_x_3733_);
v_x_3732_ = v_fn_3734_;
v_x_3733_ = v___x_3736_;
goto _start;
}
else
{
return v_x_3733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3738_, lean_object* v_x_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3738_, v_x_3739_);
lean_dec_ref(v_x_3738_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3741_){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3742_ = lean_unsigned_to_nat(0u);
v___x_3743_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3741_, v___x_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_Expr_getAppNumArgs(v_e_3744_);
lean_dec_ref(v_e_3744_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3746_, lean_object* v_a_3747_){
_start:
{
switch(lean_obj_tag(v_a_3746_))
{
case 10:
{
lean_object* v_expr_3748_; 
v_expr_3748_ = lean_ctor_get(v_a_3746_, 1);
v_a_3746_ = v_expr_3748_;
goto _start;
}
case 5:
{
lean_object* v_fn_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v_fn_3750_ = lean_ctor_get(v_a_3746_, 0);
v___x_3751_ = lean_unsigned_to_nat(1u);
v___x_3752_ = lean_nat_add(v_a_3747_, v___x_3751_);
lean_dec(v_a_3747_);
v_a_3746_ = v_fn_3750_;
v_a_3747_ = v___x_3752_;
goto _start;
}
default: 
{
return v_a_3747_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3754_, lean_object* v_a_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3754_, v_a_3755_);
lean_dec_ref(v_a_3754_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3757_){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3758_ = lean_unsigned_to_nat(0u);
v___x_3759_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3757_, v___x_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3760_);
lean_dec_ref(v_e_3760_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3762_, lean_object* v_x_3763_){
_start:
{
lean_object* v_zero_3764_; uint8_t v_isZero_3765_; 
v_zero_3764_ = lean_unsigned_to_nat(0u);
v_isZero_3765_ = lean_nat_dec_eq(v_x_3762_, v_zero_3764_);
if (v_isZero_3765_ == 0)
{
if (lean_obj_tag(v_x_3763_) == 5)
{
lean_object* v_fn_3766_; lean_object* v_one_3767_; lean_object* v_n_3768_; 
v_fn_3766_ = lean_ctor_get(v_x_3763_, 0);
v_one_3767_ = lean_unsigned_to_nat(1u);
v_n_3768_ = lean_nat_sub(v_x_3762_, v_one_3767_);
lean_dec(v_x_3762_);
v_x_3762_ = v_n_3768_;
v_x_3763_ = v_fn_3766_;
goto _start;
}
else
{
lean_dec(v_x_3762_);
lean_inc_ref(v_x_3763_);
return v_x_3763_;
}
}
else
{
lean_dec(v_x_3762_);
lean_inc_ref(v_x_3763_);
return v_x_3763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_3770_, lean_object* v_x_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_Expr_getBoundedAppFn(v_x_3770_, v_x_3771_);
lean_dec_ref(v_x_3771_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_3773_, lean_object* v_x_3774_, lean_object* v_x_3775_){
_start:
{
if (lean_obj_tag(v_x_3773_) == 5)
{
lean_object* v_fn_3776_; lean_object* v_arg_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v_fn_3776_ = lean_ctor_get(v_x_3773_, 0);
lean_inc_ref(v_fn_3776_);
v_arg_3777_ = lean_ctor_get(v_x_3773_, 1);
lean_inc_ref(v_arg_3777_);
lean_dec_ref(v_x_3773_);
v___x_3778_ = lean_array_set(v_x_3774_, v_x_3775_, v_arg_3777_);
v___x_3779_ = lean_unsigned_to_nat(1u);
v___x_3780_ = lean_nat_sub(v_x_3775_, v___x_3779_);
lean_dec(v_x_3775_);
v_x_3773_ = v_fn_3776_;
v_x_3774_ = v___x_3778_;
v_x_3775_ = v___x_3780_;
goto _start;
}
else
{
lean_dec(v_x_3775_);
lean_dec_ref(v_x_3773_);
return v_x_3774_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_3782_; lean_object* v_dummy_3783_; 
v___x_3782_ = lean_box(0);
v_dummy_3783_ = l_Lean_Expr_sort___override(v___x_3782_);
return v_dummy_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_3784_){
_start:
{
lean_object* v_dummy_3785_; lean_object* v_nargs_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v_dummy_3785_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3786_ = l_Lean_Expr_getAppNumArgs(v_e_3784_);
lean_inc(v_nargs_3786_);
v___x_3787_ = lean_mk_array(v_nargs_3786_, v_dummy_3785_);
v___x_3788_ = lean_unsigned_to_nat(1u);
v___x_3789_ = lean_nat_sub(v_nargs_3786_, v___x_3788_);
lean_dec(v_nargs_3786_);
v___x_3790_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3784_, v___x_3787_, v___x_3789_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_3791_, lean_object* v_x_3792_, lean_object* v_x_3793_){
_start:
{
if (lean_obj_tag(v_x_3791_) == 5)
{
lean_object* v_fn_3794_; lean_object* v_arg_3795_; lean_object* v_zero_3796_; uint8_t v_isZero_3797_; 
v_fn_3794_ = lean_ctor_get(v_x_3791_, 0);
lean_inc_ref(v_fn_3794_);
v_arg_3795_ = lean_ctor_get(v_x_3791_, 1);
lean_inc_ref(v_arg_3795_);
lean_dec_ref(v_x_3791_);
v_zero_3796_ = lean_unsigned_to_nat(0u);
v_isZero_3797_ = lean_nat_dec_eq(v_x_3793_, v_zero_3796_);
if (v_isZero_3797_ == 0)
{
lean_object* v_one_3798_; lean_object* v_n_3799_; lean_object* v___x_3800_; 
v_one_3798_ = lean_unsigned_to_nat(1u);
v_n_3799_ = lean_nat_sub(v_x_3793_, v_one_3798_);
lean_dec(v_x_3793_);
v___x_3800_ = lean_array_set(v_x_3792_, v_n_3799_, v_arg_3795_);
v_x_3791_ = v_fn_3794_;
v_x_3792_ = v___x_3800_;
v_x_3793_ = v_n_3799_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3795_);
lean_dec_ref(v_fn_3794_);
lean_dec(v_x_3793_);
return v_x_3792_;
}
}
else
{
lean_dec(v_x_3793_);
lean_dec_ref(v_x_3791_);
return v_x_3792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_3802_, lean_object* v_e_3803_){
_start:
{
lean_object* v_dummy_3804_; lean_object* v___y_3806_; lean_object* v___x_3809_; uint8_t v___x_3810_; 
v_dummy_3804_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_3809_ = l_Lean_Expr_getAppNumArgs(v_e_3803_);
v___x_3810_ = lean_nat_dec_le(v_maxArgs_3802_, v___x_3809_);
if (v___x_3810_ == 0)
{
lean_dec(v_maxArgs_3802_);
v___y_3806_ = v___x_3809_;
goto v___jp_3805_;
}
else
{
lean_dec(v___x_3809_);
v___y_3806_ = v_maxArgs_3802_;
goto v___jp_3805_;
}
v___jp_3805_:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; 
lean_inc(v___y_3806_);
v___x_3807_ = lean_mk_array(v___y_3806_, v_dummy_3804_);
v___x_3808_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_3803_, v___x_3807_, v___y_3806_);
return v___x_3808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_3811_, lean_object* v_x_3812_){
_start:
{
if (lean_obj_tag(v_x_3811_) == 5)
{
lean_object* v_fn_3813_; lean_object* v_arg_3814_; lean_object* v___x_3815_; 
v_fn_3813_ = lean_ctor_get(v_x_3811_, 0);
lean_inc_ref(v_fn_3813_);
v_arg_3814_ = lean_ctor_get(v_x_3811_, 1);
lean_inc_ref(v_arg_3814_);
lean_dec_ref(v_x_3811_);
v___x_3815_ = lean_array_push(v_x_3812_, v_arg_3814_);
v_x_3811_ = v_fn_3813_;
v_x_3812_ = v___x_3815_;
goto _start;
}
else
{
lean_dec_ref(v_x_3811_);
return v_x_3812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_3817_){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3818_ = l_Lean_Expr_getAppNumArgs(v_e_3817_);
v___x_3819_ = lean_mk_empty_array_with_capacity(v___x_3818_);
lean_dec(v___x_3818_);
v___x_3820_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3817_, v___x_3819_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_3821_, lean_object* v_x_3822_, lean_object* v_x_3823_, lean_object* v_x_3824_){
_start:
{
if (lean_obj_tag(v_x_3822_) == 5)
{
lean_object* v_fn_3825_; lean_object* v_arg_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v_fn_3825_ = lean_ctor_get(v_x_3822_, 0);
lean_inc_ref(v_fn_3825_);
v_arg_3826_ = lean_ctor_get(v_x_3822_, 1);
lean_inc_ref(v_arg_3826_);
lean_dec_ref(v_x_3822_);
v___x_3827_ = lean_array_set(v_x_3823_, v_x_3824_, v_arg_3826_);
v___x_3828_ = lean_unsigned_to_nat(1u);
v___x_3829_ = lean_nat_sub(v_x_3824_, v___x_3828_);
lean_dec(v_x_3824_);
v_x_3822_ = v_fn_3825_;
v_x_3823_ = v___x_3827_;
v_x_3824_ = v___x_3829_;
goto _start;
}
else
{
lean_object* v___x_3831_; 
lean_dec(v_x_3824_);
v___x_3831_ = lean_apply_2(v_k_3821_, v_x_3822_, v_x_3823_);
return v___x_3831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_3832_, lean_object* v_k_3833_, lean_object* v_x_3834_, lean_object* v_x_3835_, lean_object* v_x_3836_){
_start:
{
lean_object* v___x_3837_; 
v___x_3837_ = l_Lean_Expr_withAppAux___redArg(v_k_3833_, v_x_3834_, v_x_3835_, v_x_3836_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_3838_, lean_object* v_k_3839_){
_start:
{
lean_object* v_dummy_3840_; lean_object* v_nargs_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v_dummy_3840_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3841_ = l_Lean_Expr_getAppNumArgs(v_e_3838_);
lean_inc(v_nargs_3841_);
v___x_3842_ = lean_mk_array(v_nargs_3841_, v_dummy_3840_);
v___x_3843_ = lean_unsigned_to_nat(1u);
v___x_3844_ = lean_nat_sub(v_nargs_3841_, v___x_3843_);
lean_dec(v_nargs_3841_);
v___x_3845_ = l_Lean_Expr_withAppAux___redArg(v_k_3839_, v_e_3838_, v___x_3842_, v___x_3844_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_3846_, lean_object* v_e_3847_, lean_object* v_k_3848_){
_start:
{
lean_object* v_dummy_3849_; lean_object* v_nargs_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v_dummy_3849_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3850_ = l_Lean_Expr_getAppNumArgs(v_e_3847_);
lean_inc(v_nargs_3850_);
v___x_3851_ = lean_mk_array(v_nargs_3850_, v_dummy_3849_);
v___x_3852_ = lean_unsigned_to_nat(1u);
v___x_3853_ = lean_nat_sub(v_nargs_3850_, v___x_3852_);
lean_dec(v_nargs_3850_);
v___x_3854_ = l_Lean_Expr_withAppAux___redArg(v_k_3848_, v_e_3847_, v___x_3851_, v___x_3853_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_3855_, lean_object* v_x_3856_, lean_object* v_x_3857_){
_start:
{
if (lean_obj_tag(v_x_3855_) == 5)
{
lean_object* v_fn_3858_; lean_object* v_arg_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v_fn_3858_ = lean_ctor_get(v_x_3855_, 0);
lean_inc_ref(v_fn_3858_);
v_arg_3859_ = lean_ctor_get(v_x_3855_, 1);
lean_inc_ref(v_arg_3859_);
lean_dec_ref(v_x_3855_);
v___x_3860_ = lean_array_set(v_x_3856_, v_x_3857_, v_arg_3859_);
v___x_3861_ = lean_unsigned_to_nat(1u);
v___x_3862_ = lean_nat_sub(v_x_3857_, v___x_3861_);
lean_dec(v_x_3857_);
v_x_3855_ = v_fn_3858_;
v_x_3856_ = v___x_3860_;
v_x_3857_ = v___x_3862_;
goto _start;
}
else
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
lean_dec(v_x_3857_);
v___x_3864_ = l_Lean_Expr_constName(v_x_3855_);
lean_dec_ref(v_x_3855_);
v___x_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
lean_ctor_set(v___x_3865_, 1, v_x_3856_);
return v___x_3865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_3866_){
_start:
{
lean_object* v_dummy_3867_; lean_object* v_nargs_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v_dummy_3867_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3868_ = l_Lean_Expr_getAppNumArgs(v_e_3866_);
lean_inc(v_nargs_3868_);
v___x_3869_ = lean_mk_array(v_nargs_3868_, v_dummy_3867_);
v___x_3870_ = lean_unsigned_to_nat(1u);
v___x_3871_ = lean_nat_sub(v_nargs_3868_, v___x_3870_);
lean_dec(v_nargs_3868_);
v___x_3872_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_3866_, v___x_3869_, v___x_3871_);
return v___x_3872_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3873_; 
v___x_3873_ = l_Array_instInhabited(lean_box(0));
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_3874_){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_3876_ = lean_panic_fn(v___x_3875_, v_msg_3874_);
return v___x_3876_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3879_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_3880_ = lean_unsigned_to_nat(27u);
v___x_3881_ = lean_unsigned_to_nat(1237u);
v___x_3882_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_3883_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3884_ = l_mkPanicMessageWithDecl(v___x_3883_, v___x_3882_, v___x_3881_, v___x_3880_, v___x_3879_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_){
_start:
{
lean_object* v_zero_3888_; uint8_t v_isZero_3889_; 
v_zero_3888_ = lean_unsigned_to_nat(0u);
v_isZero_3889_ = lean_nat_dec_eq(v_a_3885_, v_zero_3888_);
if (v_isZero_3889_ == 1)
{
lean_dec_ref(v_a_3886_);
lean_dec(v_a_3885_);
return v_a_3887_;
}
else
{
if (lean_obj_tag(v_a_3886_) == 5)
{
lean_object* v_fn_3890_; lean_object* v_arg_3891_; lean_object* v_one_3892_; lean_object* v_n_3893_; lean_object* v___x_3894_; 
v_fn_3890_ = lean_ctor_get(v_a_3886_, 0);
lean_inc_ref(v_fn_3890_);
v_arg_3891_ = lean_ctor_get(v_a_3886_, 1);
lean_inc_ref(v_arg_3891_);
lean_dec_ref(v_a_3886_);
v_one_3892_ = lean_unsigned_to_nat(1u);
v_n_3893_ = lean_nat_sub(v_a_3885_, v_one_3892_);
lean_dec(v_a_3885_);
v___x_3894_ = lean_array_set(v_a_3887_, v_n_3893_, v_arg_3891_);
v_a_3885_ = v_n_3893_;
v_a_3886_ = v_fn_3890_;
v_a_3887_ = v___x_3894_;
goto _start;
}
else
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
lean_dec_ref(v_a_3887_);
lean_dec_ref(v_a_3886_);
lean_dec(v_a_3885_);
v___x_3896_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_3897_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_3896_);
return v___x_3897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_3898_, lean_object* v_n_3899_){
_start:
{
lean_object* v_dummy_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v_dummy_3900_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_3899_);
v___x_3901_ = lean_mk_array(v_n_3899_, v_dummy_3900_);
v___x_3902_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_3899_, v_e_3898_, v___x_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_3903_, lean_object* v_n_3904_){
_start:
{
lean_object* v_zero_3905_; uint8_t v_isZero_3906_; 
v_zero_3905_ = lean_unsigned_to_nat(0u);
v_isZero_3906_ = lean_nat_dec_eq(v_n_3904_, v_zero_3905_);
if (v_isZero_3906_ == 1)
{
lean_dec(v_n_3904_);
lean_inc_ref(v_e_3903_);
return v_e_3903_;
}
else
{
if (lean_obj_tag(v_e_3903_) == 5)
{
lean_object* v_fn_3907_; lean_object* v_one_3908_; lean_object* v_n_3909_; 
v_fn_3907_ = lean_ctor_get(v_e_3903_, 0);
v_one_3908_ = lean_unsigned_to_nat(1u);
v_n_3909_ = lean_nat_sub(v_n_3904_, v_one_3908_);
lean_dec(v_n_3904_);
v_e_3903_ = v_fn_3907_;
v_n_3904_ = v_n_3909_;
goto _start;
}
else
{
lean_dec(v_n_3904_);
lean_inc_ref(v_e_3903_);
return v_e_3903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_3911_, lean_object* v_n_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Lean_Expr_stripArgsN(v_e_3911_, v_n_3912_);
lean_dec_ref(v_e_3911_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_3914_, lean_object* v_n_3915_){
_start:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3916_ = l_Lean_Expr_getAppNumArgs(v_e_3914_);
v___x_3917_ = lean_nat_sub(v___x_3916_, v_n_3915_);
lean_dec(v___x_3916_);
v___x_3918_ = l_Lean_Expr_stripArgsN(v_e_3914_, v___x_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_3919_, lean_object* v_n_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l_Lean_Expr_getAppPrefix(v_e_3919_, v_n_3920_);
lean_dec(v_n_3920_);
lean_dec_ref(v_e_3919_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_3922_, lean_object* v_inst_3923_, lean_object* v_f_3924_, lean_object* v_x_3925_){
_start:
{
size_t v_sz_3926_; size_t v___x_3927_; lean_object* v___x_3928_; 
v_sz_3926_ = lean_array_size(v_args_3922_);
v___x_3927_ = ((size_t)0ULL);
v___x_3928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3923_, v_f_3924_, v_sz_3926_, v___x_3927_, v_args_3922_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_3930_, lean_object* v_inst_3931_, lean_object* v_f_3932_, lean_object* v_toSeq_3933_, lean_object* v_fn_3934_, lean_object* v_args_3935_){
_start:
{
lean_object* v_map_3936_; lean_object* v___f_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v_map_3936_ = lean_ctor_get(v_toFunctor_3930_, 0);
lean_inc(v_map_3936_);
lean_dec_ref(v_toFunctor_3930_);
lean_inc(v_f_3932_);
v___f_3937_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3937_, 0, v_args_3935_);
lean_closure_set(v___f_3937_, 1, v_inst_3931_);
lean_closure_set(v___f_3937_, 2, v_f_3932_);
v___x_3938_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_3939_ = lean_apply_1(v_f_3932_, v_fn_3934_);
v___x_3940_ = lean_apply_4(v_map_3936_, lean_box(0), lean_box(0), v___x_3938_, v___x_3939_);
v___x_3941_ = lean_apply_4(v_toSeq_3933_, lean_box(0), lean_box(0), v___x_3940_, v___f_3937_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_3942_, lean_object* v_f_3943_, lean_object* v_e_3944_){
_start:
{
lean_object* v_toApplicative_3945_; lean_object* v_toFunctor_3946_; lean_object* v_toSeq_3947_; lean_object* v___f_3948_; lean_object* v_dummy_3949_; lean_object* v_nargs_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v_toApplicative_3945_ = lean_ctor_get(v_inst_3942_, 0);
v_toFunctor_3946_ = lean_ctor_get(v_toApplicative_3945_, 0);
lean_inc_ref(v_toFunctor_3946_);
v_toSeq_3947_ = lean_ctor_get(v_toApplicative_3945_, 2);
lean_inc(v_toSeq_3947_);
v___f_3948_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_3948_, 0, v_toFunctor_3946_);
lean_closure_set(v___f_3948_, 1, v_inst_3942_);
lean_closure_set(v___f_3948_, 2, v_f_3943_);
lean_closure_set(v___f_3948_, 3, v_toSeq_3947_);
v_dummy_3949_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3950_ = l_Lean_Expr_getAppNumArgs(v_e_3944_);
lean_inc(v_nargs_3950_);
v___x_3951_ = lean_mk_array(v_nargs_3950_, v_dummy_3949_);
v___x_3952_ = lean_unsigned_to_nat(1u);
v___x_3953_ = lean_nat_sub(v_nargs_3950_, v___x_3952_);
lean_dec(v_nargs_3950_);
v___x_3954_ = l_Lean_Expr_withAppAux___redArg(v___f_3948_, v_e_3944_, v___x_3951_, v___x_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_3955_, lean_object* v_inst_3956_, lean_object* v_f_3957_, lean_object* v_e_3958_){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Lean_Expr_traverseApp___redArg(v_inst_3956_, v_f_3957_, v_e_3958_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_3960_, lean_object* v_x_3961_, lean_object* v_x_3962_){
_start:
{
if (lean_obj_tag(v_x_3961_) == 5)
{
lean_object* v_fn_3963_; lean_object* v_arg_3964_; lean_object* v___x_3965_; 
v_fn_3963_ = lean_ctor_get(v_x_3961_, 0);
lean_inc_ref(v_fn_3963_);
v_arg_3964_ = lean_ctor_get(v_x_3961_, 1);
lean_inc_ref(v_arg_3964_);
lean_dec_ref(v_x_3961_);
v___x_3965_ = lean_array_push(v_x_3962_, v_arg_3964_);
v_x_3961_ = v_fn_3963_;
v_x_3962_ = v___x_3965_;
goto _start;
}
else
{
lean_object* v___x_3967_; 
v___x_3967_ = lean_apply_2(v_k_3960_, v_x_3961_, v_x_3962_);
return v___x_3967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_3968_, lean_object* v_k_3969_, lean_object* v_x_3970_, lean_object* v_x_3971_){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_3969_, v_x_3970_, v_x_3971_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_3973_, lean_object* v_k_3974_){
_start:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3975_ = l_Lean_Expr_getAppNumArgs(v_e_3973_);
v___x_3976_ = lean_mk_empty_array_with_capacity(v___x_3975_);
lean_dec(v___x_3975_);
v___x_3977_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_3974_, v_e_3973_, v___x_3976_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_3978_, lean_object* v_e_3979_, lean_object* v_k_3980_){
_start:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3981_ = l_Lean_Expr_getAppNumArgs(v_e_3979_);
v___x_3982_ = lean_mk_empty_array_with_capacity(v___x_3981_);
lean_dec(v___x_3981_);
v___x_3983_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_3980_, v_e_3979_, v___x_3982_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_3984_, lean_object* v_x_3985_, lean_object* v_x_3986_){
_start:
{
if (lean_obj_tag(v_x_3984_) == 5)
{
lean_object* v_fn_3987_; lean_object* v_arg_3988_; lean_object* v_zero_3989_; uint8_t v_isZero_3990_; 
v_fn_3987_ = lean_ctor_get(v_x_3984_, 0);
v_arg_3988_ = lean_ctor_get(v_x_3984_, 1);
v_zero_3989_ = lean_unsigned_to_nat(0u);
v_isZero_3990_ = lean_nat_dec_eq(v_x_3985_, v_zero_3989_);
if (v_isZero_3990_ == 1)
{
lean_dec(v_x_3985_);
lean_inc_ref(v_arg_3988_);
return v_arg_3988_;
}
else
{
lean_object* v_one_3991_; lean_object* v_n_3992_; 
v_one_3991_ = lean_unsigned_to_nat(1u);
v_n_3992_ = lean_nat_sub(v_x_3985_, v_one_3991_);
lean_dec(v_x_3985_);
v_x_3984_ = v_fn_3987_;
v_x_3985_ = v_n_3992_;
goto _start;
}
}
else
{
lean_dec(v_x_3985_);
lean_inc_ref(v_x_3986_);
return v_x_3986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_3994_, lean_object* v_x_3995_, lean_object* v_x_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lean_Expr_getRevArgD(v_x_3994_, v_x_3995_, v_x_3996_);
lean_dec_ref(v_x_3996_);
lean_dec_ref(v_x_3994_);
return v_res_3997_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4000_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4001_ = lean_unsigned_to_nat(20u);
v___x_4002_ = lean_unsigned_to_nat(1278u);
v___x_4003_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4004_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4005_ = l_mkPanicMessageWithDecl(v___x_4004_, v___x_4003_, v___x_4002_, v___x_4001_, v___x_4000_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4006_, lean_object* v_x_4007_){
_start:
{
if (lean_obj_tag(v_x_4006_) == 5)
{
lean_object* v_fn_4008_; lean_object* v_arg_4009_; lean_object* v_zero_4010_; uint8_t v_isZero_4011_; 
v_fn_4008_ = lean_ctor_get(v_x_4006_, 0);
v_arg_4009_ = lean_ctor_get(v_x_4006_, 1);
v_zero_4010_ = lean_unsigned_to_nat(0u);
v_isZero_4011_ = lean_nat_dec_eq(v_x_4007_, v_zero_4010_);
if (v_isZero_4011_ == 1)
{
lean_dec(v_x_4007_);
lean_inc_ref(v_arg_4009_);
return v_arg_4009_;
}
else
{
lean_object* v_one_4012_; lean_object* v_n_4013_; 
v_one_4012_ = lean_unsigned_to_nat(1u);
v_n_4013_ = lean_nat_sub(v_x_4007_, v_one_4012_);
lean_dec(v_x_4007_);
v_x_4006_ = v_fn_4008_;
v_x_4007_ = v_n_4013_;
goto _start;
}
}
else
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
lean_dec(v_x_4007_);
v___x_4015_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4016_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4015_);
return v___x_4016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4017_, lean_object* v_x_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_Lean_Expr_getRevArg_x21(v_x_4017_, v_x_4018_);
lean_dec_ref(v_x_4017_);
return v_res_4019_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4021_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4022_ = lean_unsigned_to_nat(20u);
v___x_4023_ = lean_unsigned_to_nat(1285u);
v___x_4024_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4025_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4026_ = l_mkPanicMessageWithDecl(v___x_4025_, v___x_4024_, v___x_4023_, v___x_4022_, v___x_4021_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4027_, lean_object* v_x_4028_){
_start:
{
switch(lean_obj_tag(v_x_4027_))
{
case 10:
{
lean_object* v_expr_4029_; 
v_expr_4029_ = lean_ctor_get(v_x_4027_, 1);
v_x_4027_ = v_expr_4029_;
goto _start;
}
case 5:
{
lean_object* v_fn_4031_; lean_object* v_arg_4032_; lean_object* v_zero_4033_; uint8_t v_isZero_4034_; 
v_fn_4031_ = lean_ctor_get(v_x_4027_, 0);
v_arg_4032_ = lean_ctor_get(v_x_4027_, 1);
v_zero_4033_ = lean_unsigned_to_nat(0u);
v_isZero_4034_ = lean_nat_dec_eq(v_x_4028_, v_zero_4033_);
if (v_isZero_4034_ == 1)
{
lean_dec(v_x_4028_);
lean_inc_ref(v_arg_4032_);
return v_arg_4032_;
}
else
{
lean_object* v_one_4035_; lean_object* v_n_4036_; 
v_one_4035_ = lean_unsigned_to_nat(1u);
v_n_4036_ = lean_nat_sub(v_x_4028_, v_one_4035_);
lean_dec(v_x_4028_);
v_x_4027_ = v_fn_4031_;
v_x_4028_ = v_n_4036_;
goto _start;
}
}
default: 
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
lean_dec(v_x_4028_);
v___x_4038_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4039_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4038_);
return v___x_4039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4040_, lean_object* v_x_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4040_, v_x_4041_);
lean_dec_ref(v_x_4040_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4043_, lean_object* v_i_4044_, lean_object* v_n_4045_){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4046_ = lean_nat_sub(v_n_4045_, v_i_4044_);
v___x_4047_ = lean_unsigned_to_nat(1u);
v___x_4048_ = lean_nat_sub(v___x_4046_, v___x_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = l_Lean_Expr_getRevArg_x21(v_e_4043_, v___x_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4050_, lean_object* v_i_4051_, lean_object* v_n_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Lean_Expr_getArg_x21(v_e_4050_, v_i_4051_, v_n_4052_);
lean_dec(v_n_4052_);
lean_dec(v_i_4051_);
lean_dec_ref(v_e_4050_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4054_, lean_object* v_i_4055_, lean_object* v_n_4056_){
_start:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4057_ = lean_nat_sub(v_n_4056_, v_i_4055_);
v___x_4058_ = lean_unsigned_to_nat(1u);
v___x_4059_ = lean_nat_sub(v___x_4057_, v___x_4058_);
lean_dec(v___x_4057_);
v___x_4060_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4054_, v___x_4059_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4061_, lean_object* v_i_4062_, lean_object* v_n_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l_Lean_Expr_getArg_x21_x27(v_e_4061_, v_i_4062_, v_n_4063_);
lean_dec(v_n_4063_);
lean_dec(v_i_4062_);
lean_dec_ref(v_e_4061_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4065_, lean_object* v_i_4066_, lean_object* v_v_u2080_4067_, lean_object* v_n_4068_){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4069_ = lean_nat_sub(v_n_4068_, v_i_4066_);
v___x_4070_ = lean_unsigned_to_nat(1u);
v___x_4071_ = lean_nat_sub(v___x_4069_, v___x_4070_);
lean_dec(v___x_4069_);
v___x_4072_ = l_Lean_Expr_getRevArgD(v_e_4065_, v___x_4071_, v_v_u2080_4067_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4073_, lean_object* v_i_4074_, lean_object* v_v_u2080_4075_, lean_object* v_n_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l_Lean_Expr_getArgD(v_e_4073_, v_i_4074_, v_v_u2080_4075_, v_n_4076_);
lean_dec(v_n_4076_);
lean_dec_ref(v_v_u2080_4075_);
lean_dec(v_i_4074_);
lean_dec_ref(v_e_4073_);
return v_res_4077_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4078_){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; uint8_t v___x_4081_; 
v___x_4079_ = lean_unsigned_to_nat(0u);
v___x_4080_ = l_Lean_Expr_looseBVarRange(v_e_4078_);
v___x_4081_ = lean_nat_dec_lt(v___x_4079_, v___x_4080_);
lean_dec(v___x_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4082_){
_start:
{
uint8_t v_res_4083_; lean_object* v_r_4084_; 
v_res_4083_ = l_Lean_Expr_hasLooseBVars(v_e_4082_);
lean_dec_ref(v_e_4082_);
v_r_4084_ = lean_box(v_res_4083_);
return v_r_4084_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4085_){
_start:
{
if (lean_obj_tag(v_e_4085_) == 7)
{
lean_object* v_body_4086_; uint8_t v___x_4087_; 
v_body_4086_ = lean_ctor_get(v_e_4085_, 2);
v___x_4087_ = l_Lean_Expr_hasLooseBVars(v_body_4086_);
if (v___x_4087_ == 0)
{
uint8_t v___x_4088_; 
v___x_4088_ = 1;
return v___x_4088_;
}
else
{
uint8_t v___x_4089_; 
v___x_4089_ = 0;
return v___x_4089_;
}
}
else
{
uint8_t v___x_4090_; 
v___x_4090_ = 0;
return v___x_4090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4091_){
_start:
{
uint8_t v_res_4092_; lean_object* v_r_4093_; 
v_res_4092_ = l_Lean_Expr_isArrow(v_e_4091_);
lean_dec_ref(v_e_4091_);
v_r_4093_ = lean_box(v_res_4092_);
return v_r_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4096_, lean_object* v_bvarIdx_4097_){
_start:
{
uint8_t v_res_4098_; lean_object* v_r_4099_; 
v_res_4098_ = lean_expr_has_loose_bvar(v_e_4096_, v_bvarIdx_4097_);
lean_dec(v_bvarIdx_4097_);
lean_dec_ref(v_e_4096_);
v_r_4099_ = lean_box(v_res_4098_);
return v_r_4099_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4100_, lean_object* v_bvarIdx_4101_, uint8_t v_considerRange_4102_){
_start:
{
if (lean_obj_tag(v_e_4100_) == 7)
{
lean_object* v_binderType_4103_; lean_object* v_body_4104_; uint8_t v_binderInfo_4105_; uint8_t v___y_4107_; uint8_t v___x_4111_; 
v_binderType_4103_ = lean_ctor_get(v_e_4100_, 1);
v_body_4104_ = lean_ctor_get(v_e_4100_, 2);
v_binderInfo_4105_ = lean_ctor_get_uint8(v_e_4100_, sizeof(void*)*3 + 8);
v___x_4111_ = lean_expr_has_loose_bvar(v_binderType_4103_, v_bvarIdx_4101_);
if (v___x_4111_ == 0)
{
v___y_4107_ = v___x_4111_;
goto v___jp_4106_;
}
else
{
uint8_t v___x_4112_; 
v___x_4112_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4105_);
if (v___x_4112_ == 0)
{
lean_object* v___x_4113_; uint8_t v___x_4114_; 
v___x_4113_ = lean_unsigned_to_nat(0u);
v___x_4114_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4104_, v___x_4113_, v_considerRange_4102_);
v___y_4107_ = v___x_4114_;
goto v___jp_4106_;
}
else
{
v___y_4107_ = v___x_4112_;
goto v___jp_4106_;
}
}
v___jp_4106_:
{
if (v___y_4107_ == 0)
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = lean_unsigned_to_nat(1u);
v___x_4109_ = lean_nat_add(v_bvarIdx_4101_, v___x_4108_);
lean_dec(v_bvarIdx_4101_);
v_e_4100_ = v_body_4104_;
v_bvarIdx_4101_ = v___x_4109_;
goto _start;
}
else
{
lean_dec(v_bvarIdx_4101_);
return v___y_4107_;
}
}
}
else
{
if (v_considerRange_4102_ == 0)
{
lean_dec(v_bvarIdx_4101_);
return v_considerRange_4102_;
}
else
{
uint8_t v___x_4115_; 
v___x_4115_ = lean_expr_has_loose_bvar(v_e_4100_, v_bvarIdx_4101_);
lean_dec(v_bvarIdx_4101_);
return v___x_4115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4116_, lean_object* v_bvarIdx_4117_, lean_object* v_considerRange_4118_){
_start:
{
uint8_t v_considerRange_boxed_4119_; uint8_t v_res_4120_; lean_object* v_r_4121_; 
v_considerRange_boxed_4119_ = lean_unbox(v_considerRange_4118_);
v_res_4120_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4116_, v_bvarIdx_4117_, v_considerRange_boxed_4119_);
lean_dec_ref(v_e_4116_);
v_r_4121_ = lean_box(v_res_4120_);
return v_r_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4125_, lean_object* v_s_4126_, lean_object* v_d_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = lean_expr_lower_loose_bvars(v_e_4125_, v_s_4126_, v_d_4127_);
lean_dec(v_d_4127_);
lean_dec(v_s_4126_);
lean_dec_ref(v_e_4125_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4132_, lean_object* v_s_4133_, lean_object* v_d_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = lean_expr_lift_loose_bvars(v_e_4132_, v_s_4133_, v_d_4134_);
lean_dec(v_d_4134_);
lean_dec(v_s_4133_);
lean_dec_ref(v_e_4132_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4136_, lean_object* v_numParams_4137_, uint8_t v_considerRange_4138_){
_start:
{
if (lean_obj_tag(v_e_4136_) == 7)
{
lean_object* v_binderName_4139_; lean_object* v_binderType_4140_; lean_object* v_body_4141_; uint8_t v_binderInfo_4142_; lean_object* v_zero_4143_; uint8_t v_isZero_4144_; 
v_binderName_4139_ = lean_ctor_get(v_e_4136_, 0);
v_binderType_4140_ = lean_ctor_get(v_e_4136_, 1);
v_body_4141_ = lean_ctor_get(v_e_4136_, 2);
v_binderInfo_4142_ = lean_ctor_get_uint8(v_e_4136_, sizeof(void*)*3 + 8);
v_zero_4143_ = lean_unsigned_to_nat(0u);
v_isZero_4144_ = lean_nat_dec_eq(v_numParams_4137_, v_zero_4143_);
if (v_isZero_4144_ == 0)
{
lean_object* v_one_4145_; lean_object* v_n_4146_; lean_object* v_b_4147_; uint8_t v___y_4149_; uint8_t v___x_4153_; 
lean_inc_ref(v_body_4141_);
lean_inc_ref(v_binderType_4140_);
lean_inc(v_binderName_4139_);
lean_dec_ref(v_e_4136_);
v_one_4145_ = lean_unsigned_to_nat(1u);
v_n_4146_ = lean_nat_sub(v_numParams_4137_, v_one_4145_);
v_b_4147_ = l_Lean_Expr_inferImplicit(v_body_4141_, v_n_4146_, v_considerRange_4138_);
lean_dec(v_n_4146_);
v___x_4153_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4142_);
if (v___x_4153_ == 0)
{
v___y_4149_ = v___x_4153_;
goto v___jp_4148_;
}
else
{
uint8_t v___x_4154_; 
v___x_4154_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4147_, v_zero_4143_, v_considerRange_4138_);
v___y_4149_ = v___x_4154_;
goto v___jp_4148_;
}
v___jp_4148_:
{
if (v___y_4149_ == 0)
{
lean_object* v___x_4150_; 
v___x_4150_ = l_Lean_Expr_forallE___override(v_binderName_4139_, v_binderType_4140_, v_b_4147_, v_binderInfo_4142_);
return v___x_4150_;
}
else
{
uint8_t v___x_4151_; lean_object* v___x_4152_; 
v___x_4151_ = 1;
v___x_4152_ = l_Lean_Expr_forallE___override(v_binderName_4139_, v_binderType_4140_, v_b_4147_, v___x_4151_);
return v___x_4152_;
}
}
}
else
{
return v_e_4136_;
}
}
else
{
return v_e_4136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4155_, lean_object* v_numParams_4156_, lean_object* v_considerRange_4157_){
_start:
{
uint8_t v_considerRange_boxed_4158_; lean_object* v_res_4159_; 
v_considerRange_boxed_4158_ = lean_unbox(v_considerRange_4157_);
v_res_4159_ = l_Lean_Expr_inferImplicit(v_e_4155_, v_numParams_4156_, v_considerRange_boxed_4158_);
lean_dec(v_numParams_4156_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4160_, lean_object* v_binderInfos_x3f_4161_){
_start:
{
if (lean_obj_tag(v_e_4160_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4161_) == 1)
{
lean_object* v_binderName_4162_; lean_object* v_binderType_4163_; lean_object* v_body_4164_; uint8_t v_binderInfo_4165_; lean_object* v_head_4166_; lean_object* v_tail_4167_; lean_object* v_b_4168_; 
v_binderName_4162_ = lean_ctor_get(v_e_4160_, 0);
lean_inc(v_binderName_4162_);
v_binderType_4163_ = lean_ctor_get(v_e_4160_, 1);
lean_inc_ref(v_binderType_4163_);
v_body_4164_ = lean_ctor_get(v_e_4160_, 2);
lean_inc_ref(v_body_4164_);
v_binderInfo_4165_ = lean_ctor_get_uint8(v_e_4160_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_4160_);
v_head_4166_ = lean_ctor_get(v_binderInfos_x3f_4161_, 0);
v_tail_4167_ = lean_ctor_get(v_binderInfos_x3f_4161_, 1);
v_b_4168_ = l_Lean_Expr_updateForallBinderInfos(v_body_4164_, v_tail_4167_);
if (lean_obj_tag(v_head_4166_) == 0)
{
lean_object* v___x_4169_; 
v___x_4169_ = l_Lean_Expr_forallE___override(v_binderName_4162_, v_binderType_4163_, v_b_4168_, v_binderInfo_4165_);
return v___x_4169_;
}
else
{
lean_object* v_val_4170_; uint8_t v___x_4171_; lean_object* v___x_4172_; 
v_val_4170_ = lean_ctor_get(v_head_4166_, 0);
v___x_4171_ = lean_unbox(v_val_4170_);
v___x_4172_ = l_Lean_Expr_forallE___override(v_binderName_4162_, v_binderType_4163_, v_b_4168_, v___x_4171_);
return v___x_4172_;
}
}
else
{
return v_e_4160_;
}
}
else
{
return v_e_4160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4173_, lean_object* v_binderInfos_x3f_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Lean_Expr_updateForallBinderInfos(v_e_4173_, v_binderInfos_x3f_4174_);
lean_dec(v_binderInfos_x3f_4174_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4176_, lean_object* v_binderNames_x3f_4177_){
_start:
{
switch(lean_obj_tag(v_e_4176_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4177_) == 1)
{
lean_object* v_binderName_4178_; lean_object* v_binderType_4179_; lean_object* v_body_4180_; uint8_t v_binderInfo_4181_; lean_object* v_head_4182_; lean_object* v_tail_4183_; lean_object* v_b_4184_; 
v_binderName_4178_ = lean_ctor_get(v_e_4176_, 0);
lean_inc(v_binderName_4178_);
v_binderType_4179_ = lean_ctor_get(v_e_4176_, 1);
lean_inc_ref(v_binderType_4179_);
v_body_4180_ = lean_ctor_get(v_e_4176_, 2);
lean_inc_ref(v_body_4180_);
v_binderInfo_4181_ = lean_ctor_get_uint8(v_e_4176_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_4176_);
v_head_4182_ = lean_ctor_get(v_binderNames_x3f_4177_, 0);
lean_inc(v_head_4182_);
v_tail_4183_ = lean_ctor_get(v_binderNames_x3f_4177_, 1);
lean_inc(v_tail_4183_);
lean_dec_ref(v_binderNames_x3f_4177_);
v_b_4184_ = l_Lean_Expr_updateBinderNames(v_body_4180_, v_tail_4183_);
if (lean_obj_tag(v_head_4182_) == 0)
{
lean_object* v___x_4185_; 
v___x_4185_ = l_Lean_Expr_forallE___override(v_binderName_4178_, v_binderType_4179_, v_b_4184_, v_binderInfo_4181_);
return v___x_4185_;
}
else
{
lean_object* v_val_4186_; lean_object* v___x_4187_; 
lean_dec(v_binderName_4178_);
v_val_4186_ = lean_ctor_get(v_head_4182_, 0);
lean_inc(v_val_4186_);
lean_dec_ref(v_head_4182_);
v___x_4187_ = l_Lean_Expr_forallE___override(v_val_4186_, v_binderType_4179_, v_b_4184_, v_binderInfo_4181_);
return v___x_4187_;
}
}
else
{
lean_dec(v_binderNames_x3f_4177_);
return v_e_4176_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4177_) == 1)
{
lean_object* v_binderName_4188_; lean_object* v_binderType_4189_; lean_object* v_body_4190_; uint8_t v_binderInfo_4191_; lean_object* v_head_4192_; lean_object* v_tail_4193_; lean_object* v_b_4194_; 
v_binderName_4188_ = lean_ctor_get(v_e_4176_, 0);
lean_inc(v_binderName_4188_);
v_binderType_4189_ = lean_ctor_get(v_e_4176_, 1);
lean_inc_ref(v_binderType_4189_);
v_body_4190_ = lean_ctor_get(v_e_4176_, 2);
lean_inc_ref(v_body_4190_);
v_binderInfo_4191_ = lean_ctor_get_uint8(v_e_4176_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_4176_);
v_head_4192_ = lean_ctor_get(v_binderNames_x3f_4177_, 0);
lean_inc(v_head_4192_);
v_tail_4193_ = lean_ctor_get(v_binderNames_x3f_4177_, 1);
lean_inc(v_tail_4193_);
lean_dec_ref(v_binderNames_x3f_4177_);
v_b_4194_ = l_Lean_Expr_updateBinderNames(v_body_4190_, v_tail_4193_);
if (lean_obj_tag(v_head_4192_) == 0)
{
lean_object* v___x_4195_; 
v___x_4195_ = l_Lean_Expr_lam___override(v_binderName_4188_, v_binderType_4189_, v_b_4194_, v_binderInfo_4191_);
return v___x_4195_;
}
else
{
lean_object* v_val_4196_; lean_object* v___x_4197_; 
lean_dec(v_binderName_4188_);
v_val_4196_ = lean_ctor_get(v_head_4192_, 0);
lean_inc(v_val_4196_);
lean_dec_ref(v_head_4192_);
v___x_4197_ = l_Lean_Expr_lam___override(v_val_4196_, v_binderType_4189_, v_b_4194_, v_binderInfo_4191_);
return v___x_4197_;
}
}
else
{
lean_dec(v_binderNames_x3f_4177_);
return v_e_4176_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4177_);
return v_e_4176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4200_, lean_object* v_subst_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = lean_expr_instantiate(v_e_4200_, v_subst_4201_);
lean_dec_ref(v_subst_4201_);
lean_dec_ref(v_e_4200_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4205_, lean_object* v_subst_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = lean_expr_instantiate1(v_e_4205_, v_subst_4206_);
lean_dec_ref(v_subst_4206_);
lean_dec_ref(v_e_4205_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4210_, lean_object* v_subst_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = lean_expr_instantiate_rev(v_e_4210_, v_subst_4211_);
lean_dec_ref(v_subst_4211_);
lean_dec_ref(v_e_4210_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4217_, lean_object* v_beginIdx_4218_, lean_object* v_endIdx_4219_, lean_object* v_subst_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = lean_expr_instantiate_range(v_e_4217_, v_beginIdx_4218_, v_endIdx_4219_, v_subst_4220_);
lean_dec_ref(v_subst_4220_);
lean_dec(v_endIdx_4219_);
lean_dec(v_beginIdx_4218_);
lean_dec_ref(v_e_4217_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4226_, lean_object* v_beginIdx_4227_, lean_object* v_endIdx_4228_, lean_object* v_subst_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = lean_expr_instantiate_rev_range(v_e_4226_, v_beginIdx_4227_, v_endIdx_4228_, v_subst_4229_);
lean_dec_ref(v_subst_4229_);
lean_dec(v_endIdx_4228_);
lean_dec(v_beginIdx_4227_);
lean_dec_ref(v_e_4226_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4233_, lean_object* v_xs_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = lean_expr_abstract(v_e_4233_, v_xs_4234_);
lean_dec_ref(v_xs_4234_);
lean_dec_ref(v_e_4233_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4239_, lean_object* v_n_4240_, lean_object* v_xs_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = lean_expr_abstract_range(v_e_4239_, v_n_4240_, v_xs_4241_);
lean_dec_ref(v_xs_4241_);
lean_dec(v_n_4240_);
lean_dec_ref(v_e_4239_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4243_, lean_object* v_fvar_4244_, lean_object* v_v_4245_){
_start:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4246_ = lean_unsigned_to_nat(1u);
v___x_4247_ = lean_mk_empty_array_with_capacity(v___x_4246_);
v___x_4248_ = lean_array_push(v___x_4247_, v_fvar_4244_);
v___x_4249_ = lean_expr_abstract(v_e_4243_, v___x_4248_);
lean_dec_ref(v___x_4248_);
v___x_4250_ = lean_expr_instantiate1(v___x_4249_, v_v_4245_);
lean_dec_ref(v___x_4249_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4251_, lean_object* v_fvar_4252_, lean_object* v_v_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_Expr_replaceFVar(v_e_4251_, v_fvar_4252_, v_v_4253_);
lean_dec_ref(v_v_4253_);
lean_dec_ref(v_e_4251_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4255_, lean_object* v_fvarId_4256_, lean_object* v_v_4257_){
_start:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; 
v___x_4258_ = l_Lean_Expr_fvar___override(v_fvarId_4256_);
v___x_4259_ = l_Lean_Expr_replaceFVar(v_e_4255_, v___x_4258_, v_v_4257_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4260_, lean_object* v_fvarId_4261_, lean_object* v_v_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l_Lean_Expr_replaceFVarId(v_e_4260_, v_fvarId_4261_, v_v_4262_);
lean_dec_ref(v_v_4262_);
lean_dec_ref(v_e_4260_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4264_, lean_object* v_fvars_4265_, lean_object* v_vs_4266_){
_start:
{
lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4267_ = lean_expr_abstract(v_e_4264_, v_fvars_4265_);
v___x_4268_ = lean_expr_instantiate_rev(v___x_4267_, v_vs_4266_);
lean_dec_ref(v___x_4267_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4269_, lean_object* v_fvars_4270_, lean_object* v_vs_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_Lean_Expr_replaceFVars(v_e_4269_, v_fvars_4270_, v_vs_4271_);
lean_dec_ref(v_vs_4271_);
lean_dec_ref(v_fvars_4270_);
lean_dec_ref(v_e_4269_);
return v_res_4272_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4275_){
_start:
{
switch(lean_obj_tag(v_x_4275_))
{
case 4:
{
uint8_t v___x_4276_; 
v___x_4276_ = 1;
return v___x_4276_;
}
case 3:
{
uint8_t v___x_4277_; 
v___x_4277_ = 1;
return v___x_4277_;
}
case 0:
{
uint8_t v___x_4278_; 
v___x_4278_ = 1;
return v___x_4278_;
}
case 9:
{
uint8_t v___x_4279_; 
v___x_4279_ = 1;
return v___x_4279_;
}
case 2:
{
uint8_t v___x_4280_; 
v___x_4280_ = 1;
return v___x_4280_;
}
case 1:
{
uint8_t v___x_4281_; 
v___x_4281_ = 1;
return v___x_4281_;
}
default: 
{
uint8_t v___x_4282_; 
v___x_4282_ = 0;
return v___x_4282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4283_){
_start:
{
uint8_t v_res_4284_; lean_object* v_r_4285_; 
v_res_4284_ = l_Lean_Expr_isAtomic(v_x_4283_);
lean_dec_ref(v_x_4283_);
v_r_4285_ = lean_box(v_res_4284_);
return v_r_4285_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4291_ = lean_box(0);
v___x_4292_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4293_ = l_Lean_Expr_const___override(v___x_4292_, v___x_4291_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4294_, lean_object* v_proof_4295_){
_start:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; 
v___x_4296_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4297_ = l_Lean_mkAppB(v___x_4296_, v_pred_4294_, v_proof_4295_);
return v___x_4297_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4302_ = lean_box(0);
v___x_4303_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4304_ = l_Lean_Expr_const___override(v___x_4303_, v___x_4302_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4305_, lean_object* v_proof_4306_){
_start:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4307_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4308_ = l_Lean_mkAppB(v___x_4307_, v_pred_4305_, v_proof_4306_);
return v___x_4308_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4309_; 
v___x_4309_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4309_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4310_; 
v___x_4310_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4310_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4311_){
_start:
{
lean_inc_ref(v_val_4311_);
return v_val_4311_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4312_);
lean_dec_ref(v_val_4312_);
return v_res_4313_;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4316_, lean_object* v_x_4317_){
_start:
{
uint8_t v___x_4318_; 
v___x_4318_ = lean_expr_equal(v_x_4316_, v_x_4317_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4319_, lean_object* v_x_4320_){
_start:
{
uint8_t v_res_4321_; lean_object* v_r_4322_; 
v_res_4321_ = l_Lean_ExprStructEq_beq(v_x_4319_, v_x_4320_);
lean_dec_ref(v_x_4320_);
lean_dec_ref(v_x_4319_);
v_r_4322_ = lean_box(v_res_4321_);
return v_r_4322_;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4323_){
_start:
{
uint64_t v___x_4324_; 
v___x_4324_ = l_Lean_Expr_hash(v_x_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4325_){
_start:
{
uint64_t v_res_4326_; lean_object* v_r_4327_; 
v_res_4326_ = l_Lean_ExprStructEq_hash(v_x_4325_);
lean_dec_ref(v_x_4325_);
v_r_4327_ = lean_box_uint64(v_res_4326_);
return v_r_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4334_, lean_object* v_start_4335_, lean_object* v_b_4336_, lean_object* v_i_4337_){
_start:
{
uint8_t v___x_4338_; 
v___x_4338_ = lean_nat_dec_le(v_i_4337_, v_start_4335_);
if (v___x_4338_ == 0)
{
lean_object* v___x_4339_; lean_object* v_i_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4339_ = lean_unsigned_to_nat(1u);
v_i_4340_ = lean_nat_sub(v_i_4337_, v___x_4339_);
lean_dec(v_i_4337_);
v___x_4341_ = l_Lean_instInhabitedExpr;
v___x_4342_ = lean_array_get_borrowed(v___x_4341_, v_revArgs_4334_, v_i_4340_);
lean_inc(v___x_4342_);
v___x_4343_ = l_Lean_Expr_app___override(v_b_4336_, v___x_4342_);
v_b_4336_ = v___x_4343_;
v_i_4337_ = v_i_4340_;
goto _start;
}
else
{
lean_dec(v_i_4337_);
return v_b_4336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4345_, lean_object* v_start_4346_, lean_object* v_b_4347_, lean_object* v_i_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4345_, v_start_4346_, v_b_4347_, v_i_4348_);
lean_dec(v_start_4346_);
lean_dec_ref(v_revArgs_4345_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4350_, lean_object* v_beginIdx_4351_, lean_object* v_endIdx_4352_, lean_object* v_revArgs_4353_){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4353_, v_beginIdx_4351_, v_f_4350_, v_endIdx_4352_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4355_, lean_object* v_beginIdx_4356_, lean_object* v_endIdx_4357_, lean_object* v_revArgs_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l_Lean_Expr_mkAppRevRange(v_f_4355_, v_beginIdx_4356_, v_endIdx_4357_, v_revArgs_4358_);
lean_dec_ref(v_revArgs_4358_);
lean_dec(v_beginIdx_4356_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4360_, uint8_t v_useZeta_4361_, uint8_t v_preserveMData_4362_, lean_object* v_sz_4363_, lean_object* v_e_4364_, lean_object* v_i_4365_){
_start:
{
switch(lean_obj_tag(v_e_4364_))
{
case 6:
{
lean_object* v_body_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; uint8_t v___x_4374_; 
v_body_4371_ = lean_ctor_get(v_e_4364_, 2);
lean_inc_ref(v_body_4371_);
lean_dec_ref(v_e_4364_);
v___x_4372_ = lean_unsigned_to_nat(1u);
v___x_4373_ = lean_nat_add(v_i_4365_, v___x_4372_);
lean_dec(v_i_4365_);
v___x_4374_ = lean_nat_dec_lt(v___x_4373_, v_sz_4363_);
if (v___x_4374_ == 0)
{
lean_object* v___x_4375_; 
lean_dec(v___x_4373_);
v___x_4375_ = lean_expr_instantiate(v_body_4371_, v_revArgs_4360_);
lean_dec_ref(v_body_4371_);
return v___x_4375_;
}
else
{
v_e_4364_ = v_body_4371_;
v_i_4365_ = v___x_4373_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4361_ == 0)
{
goto v___jp_4366_;
}
else
{
lean_object* v_value_4377_; lean_object* v_body_4378_; uint8_t v___x_4379_; 
v_value_4377_ = lean_ctor_get(v_e_4364_, 2);
v_body_4378_ = lean_ctor_get(v_e_4364_, 3);
v___x_4379_ = lean_nat_dec_lt(v_i_4365_, v_sz_4363_);
if (v___x_4379_ == 0)
{
goto v___jp_4366_;
}
else
{
lean_object* v___x_4380_; 
lean_inc_ref(v_body_4378_);
lean_inc_ref(v_value_4377_);
lean_dec_ref(v_e_4364_);
v___x_4380_ = lean_expr_instantiate1(v_body_4378_, v_value_4377_);
lean_dec_ref(v_value_4377_);
lean_dec_ref(v_body_4378_);
v_e_4364_ = v___x_4380_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4362_ == 0)
{
lean_object* v_expr_4382_; 
v_expr_4382_ = lean_ctor_get(v_e_4364_, 1);
lean_inc_ref(v_expr_4382_);
lean_dec_ref(v_e_4364_);
v_e_4364_ = v_expr_4382_;
goto _start;
}
else
{
goto v___jp_4366_;
}
}
default: 
{
goto v___jp_4366_;
}
}
v___jp_4366_:
{
lean_object* v_n_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v_n_4367_ = lean_nat_sub(v_sz_4363_, v_i_4365_);
lean_dec(v_i_4365_);
v___x_4368_ = lean_expr_instantiate_range(v_e_4364_, v_n_4367_, v_sz_4363_, v_revArgs_4360_);
lean_dec_ref(v_e_4364_);
v___x_4369_ = lean_unsigned_to_nat(0u);
v___x_4370_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4360_, v___x_4369_, v___x_4368_, v_n_4367_);
return v___x_4370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4384_, lean_object* v_useZeta_4385_, lean_object* v_preserveMData_4386_, lean_object* v_sz_4387_, lean_object* v_e_4388_, lean_object* v_i_4389_){
_start:
{
uint8_t v_useZeta_boxed_4390_; uint8_t v_preserveMData_boxed_4391_; lean_object* v_res_4392_; 
v_useZeta_boxed_4390_ = lean_unbox(v_useZeta_4385_);
v_preserveMData_boxed_4391_ = lean_unbox(v_preserveMData_4386_);
v_res_4392_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4384_, v_useZeta_boxed_4390_, v_preserveMData_boxed_4391_, v_sz_4387_, v_e_4388_, v_i_4389_);
lean_dec(v_sz_4387_);
lean_dec_ref(v_revArgs_4384_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4393_, lean_object* v_revArgs_4394_, uint8_t v_useZeta_4395_, uint8_t v_preserveMData_4396_){
_start:
{
lean_object* v_sz_4397_; lean_object* v___x_4398_; uint8_t v___x_4399_; 
v_sz_4397_ = lean_array_get_size(v_revArgs_4394_);
v___x_4398_ = lean_unsigned_to_nat(0u);
v___x_4399_ = lean_nat_dec_eq(v_sz_4397_, v___x_4398_);
if (v___x_4399_ == 0)
{
lean_object* v___x_4400_; 
v___x_4400_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4394_, v_useZeta_4395_, v_preserveMData_4396_, v_sz_4397_, v_f_4393_, v___x_4398_);
return v___x_4400_;
}
else
{
return v_f_4393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4401_, lean_object* v_revArgs_4402_, lean_object* v_useZeta_4403_, lean_object* v_preserveMData_4404_){
_start:
{
uint8_t v_useZeta_boxed_4405_; uint8_t v_preserveMData_boxed_4406_; lean_object* v_res_4407_; 
v_useZeta_boxed_4405_ = lean_unbox(v_useZeta_4403_);
v_preserveMData_boxed_4406_ = lean_unbox(v_preserveMData_4404_);
v_res_4407_ = l_Lean_Expr_betaRev(v_f_4401_, v_revArgs_4402_, v_useZeta_boxed_4405_, v_preserveMData_boxed_4406_);
lean_dec_ref(v_revArgs_4402_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4408_, lean_object* v_args_4409_){
_start:
{
lean_object* v___x_4410_; uint8_t v___x_4411_; lean_object* v___x_4412_; 
v___x_4410_ = l_Array_reverse___redArg(v_args_4409_);
v___x_4411_ = 0;
v___x_4412_ = l_Lean_Expr_betaRev(v_f_4408_, v___x_4410_, v___x_4411_, v___x_4411_);
lean_dec_ref(v___x_4410_);
return v___x_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4413_){
_start:
{
switch(lean_obj_tag(v_x_4413_))
{
case 6:
{
lean_object* v_body_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v_body_4414_ = lean_ctor_get(v_x_4413_, 2);
v___x_4415_ = l_Lean_Expr_getNumHeadLambdas(v_body_4414_);
v___x_4416_ = lean_unsigned_to_nat(1u);
v___x_4417_ = lean_nat_add(v___x_4415_, v___x_4416_);
lean_dec(v___x_4415_);
return v___x_4417_;
}
case 10:
{
lean_object* v_expr_4418_; 
v_expr_4418_ = lean_ctor_get(v_x_4413_, 1);
v_x_4413_ = v_expr_4418_;
goto _start;
}
default: 
{
lean_object* v___x_4420_; 
v___x_4420_ = lean_unsigned_to_nat(0u);
return v___x_4420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l_Lean_Expr_getNumHeadLambdas(v_x_4421_);
lean_dec_ref(v_x_4421_);
return v_res_4422_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4423_, lean_object* v_x_4424_){
_start:
{
switch(lean_obj_tag(v_x_4424_))
{
case 6:
{
uint8_t v___x_4425_; 
v___x_4425_ = 1;
return v___x_4425_;
}
case 8:
{
if (v_useZeta_4423_ == 0)
{
return v_useZeta_4423_;
}
else
{
lean_object* v_body_4426_; 
v_body_4426_ = lean_ctor_get(v_x_4424_, 3);
v_x_4424_ = v_body_4426_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4428_; 
v_expr_4428_ = lean_ctor_get(v_x_4424_, 1);
v_x_4424_ = v_expr_4428_;
goto _start;
}
default: 
{
uint8_t v___x_4430_; 
v___x_4430_ = 0;
return v___x_4430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4431_, lean_object* v_x_4432_){
_start:
{
uint8_t v_useZeta_boxed_4433_; uint8_t v_res_4434_; lean_object* v_r_4435_; 
v_useZeta_boxed_4433_ = lean_unbox(v_useZeta_4431_);
v_res_4434_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4433_, v_x_4432_);
lean_dec_ref(v_x_4432_);
v_r_4435_ = lean_box(v_res_4434_);
return v_r_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4436_){
_start:
{
lean_object* v_f_4437_; uint8_t v___x_4438_; uint8_t v___x_4439_; 
v_f_4437_ = l_Lean_Expr_getAppFn(v_e_4436_);
v___x_4438_ = 0;
v___x_4439_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4438_, v_f_4437_);
if (v___x_4439_ == 0)
{
lean_dec_ref(v_f_4437_);
return v_e_4436_;
}
else
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4440_ = l_Lean_Expr_getAppNumArgs(v_e_4436_);
v___x_4441_ = lean_mk_empty_array_with_capacity(v___x_4440_);
lean_dec(v___x_4440_);
v___x_4442_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4436_, v___x_4441_);
v___x_4443_ = l_Lean_Expr_betaRev(v_f_4437_, v___x_4442_, v___x_4438_, v___x_4438_);
lean_dec_ref(v___x_4442_);
return v___x_4443_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4444_, uint8_t v_useZeta_4445_){
_start:
{
uint8_t v___x_4446_; 
v___x_4446_ = l_Lean_Expr_isApp(v_e_4444_);
if (v___x_4446_ == 0)
{
return v___x_4446_;
}
else
{
lean_object* v___x_4447_; uint8_t v___x_4448_; 
v___x_4447_ = l_Lean_Expr_getAppFn(v_e_4444_);
v___x_4448_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4445_, v___x_4447_);
lean_dec_ref(v___x_4447_);
return v___x_4448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4449_, lean_object* v_useZeta_4450_){
_start:
{
uint8_t v_useZeta_boxed_4451_; uint8_t v_res_4452_; lean_object* v_r_4453_; 
v_useZeta_boxed_4451_ = lean_unbox(v_useZeta_4450_);
v_res_4452_ = l_Lean_Expr_isHeadBetaTarget(v_e_4449_, v_useZeta_boxed_4451_);
lean_dec_ref(v_e_4449_);
v_r_4453_ = lean_box(v_res_4452_);
return v_r_4453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4454_, lean_object* v_x_4455_, lean_object* v_x_4456_){
_start:
{
lean_object* v_f_4458_; 
if (lean_obj_tag(v_x_4454_) == 5)
{
lean_object* v_arg_4462_; 
v_arg_4462_ = lean_ctor_get(v_x_4454_, 1);
if (lean_obj_tag(v_arg_4462_) == 0)
{
lean_object* v_fn_4463_; lean_object* v_deBruijnIndex_4464_; lean_object* v_zero_4465_; uint8_t v_isZero_4466_; 
v_fn_4463_ = lean_ctor_get(v_x_4454_, 0);
v_deBruijnIndex_4464_ = lean_ctor_get(v_arg_4462_, 0);
v_zero_4465_ = lean_unsigned_to_nat(0u);
v_isZero_4466_ = lean_nat_dec_eq(v_x_4455_, v_zero_4465_);
if (v_isZero_4466_ == 1)
{
lean_dec(v_x_4456_);
lean_dec(v_x_4455_);
v_f_4458_ = v_x_4454_;
goto v___jp_4457_;
}
else
{
uint8_t v___x_4467_; 
lean_inc(v_deBruijnIndex_4464_);
lean_inc_ref(v_fn_4463_);
lean_dec_ref(v_x_4454_);
v___x_4467_ = lean_nat_dec_eq(v_deBruijnIndex_4464_, v_x_4456_);
lean_dec(v_deBruijnIndex_4464_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4468_; 
lean_dec_ref(v_fn_4463_);
lean_dec(v_x_4456_);
lean_dec(v_x_4455_);
v___x_4468_ = lean_box(0);
return v___x_4468_;
}
else
{
lean_object* v_one_4469_; lean_object* v_n_4470_; lean_object* v___x_4471_; 
v_one_4469_ = lean_unsigned_to_nat(1u);
v_n_4470_ = lean_nat_sub(v_x_4455_, v_one_4469_);
lean_dec(v_x_4455_);
v___x_4471_ = lean_nat_add(v_x_4456_, v_one_4469_);
lean_dec(v_x_4456_);
v_x_4454_ = v_fn_4463_;
v_x_4455_ = v_n_4470_;
v_x_4456_ = v___x_4471_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4473_; uint8_t v_isZero_4474_; 
lean_dec(v_x_4456_);
v_zero_4473_ = lean_unsigned_to_nat(0u);
v_isZero_4474_ = lean_nat_dec_eq(v_x_4455_, v_zero_4473_);
lean_dec(v_x_4455_);
if (v_isZero_4474_ == 1)
{
v_f_4458_ = v_x_4454_;
goto v___jp_4457_;
}
else
{
lean_object* v___x_4475_; 
lean_dec_ref(v_x_4454_);
v___x_4475_ = lean_box(0);
return v___x_4475_;
}
}
}
else
{
lean_object* v_zero_4476_; uint8_t v_isZero_4477_; 
lean_dec(v_x_4456_);
v_zero_4476_ = lean_unsigned_to_nat(0u);
v_isZero_4477_ = lean_nat_dec_eq(v_x_4455_, v_zero_4476_);
lean_dec(v_x_4455_);
if (v_isZero_4477_ == 1)
{
v_f_4458_ = v_x_4454_;
goto v___jp_4457_;
}
else
{
lean_object* v___x_4478_; 
lean_dec_ref(v_x_4454_);
v___x_4478_ = lean_box(0);
return v___x_4478_;
}
}
v___jp_4457_:
{
uint8_t v___x_4459_; 
v___x_4459_ = l_Lean_Expr_hasLooseBVars(v_f_4458_);
if (v___x_4459_ == 0)
{
lean_object* v___x_4460_; 
v___x_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4460_, 0, v_f_4458_);
return v___x_4460_;
}
else
{
lean_object* v___x_4461_; 
lean_dec_ref(v_f_4458_);
v___x_4461_ = lean_box(0);
return v___x_4461_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4479_, lean_object* v_x_4480_){
_start:
{
if (lean_obj_tag(v_x_4479_) == 6)
{
lean_object* v_body_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; 
v_body_4481_ = lean_ctor_get(v_x_4479_, 2);
lean_inc_ref(v_body_4481_);
lean_dec_ref(v_x_4479_);
v___x_4482_ = lean_unsigned_to_nat(1u);
v___x_4483_ = lean_nat_add(v_x_4480_, v___x_4482_);
lean_dec(v_x_4480_);
v_x_4479_ = v_body_4481_;
v_x_4480_ = v___x_4483_;
goto _start;
}
else
{
lean_object* v___x_4485_; lean_object* v___x_4486_; 
v___x_4485_ = lean_unsigned_to_nat(0u);
v___x_4486_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4479_, v_x_4480_, v___x_4485_);
return v___x_4486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4487_){
_start:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4488_ = lean_unsigned_to_nat(0u);
v___x_4489_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4487_, v___x_4488_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4490_){
_start:
{
if (lean_obj_tag(v_x_4490_) == 6)
{
lean_object* v_body_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v_body_4491_ = lean_ctor_get(v_x_4490_, 2);
lean_inc_ref(v_body_4491_);
lean_dec_ref(v_x_4490_);
v___x_4492_ = lean_unsigned_to_nat(1u);
v___x_4493_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4491_, v___x_4492_);
return v___x_4493_;
}
else
{
lean_object* v___x_4494_; 
lean_dec_ref(v_x_4490_);
v___x_4494_ = lean_box(0);
return v___x_4494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4498_){
_start:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; uint8_t v___x_4501_; 
v___x_4499_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4500_ = lean_unsigned_to_nat(2u);
v___x_4501_ = l_Lean_Expr_isAppOfArity(v_e_4498_, v___x_4499_, v___x_4500_);
if (v___x_4501_ == 0)
{
lean_object* v___x_4502_; 
v___x_4502_ = lean_box(0);
return v___x_4502_;
}
else
{
lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4503_ = l_Lean_Expr_appArg_x21(v_e_4498_);
v___x_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4503_);
return v___x_4504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4505_);
lean_dec_ref(v_e_4505_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4510_){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; uint8_t v___x_4513_; 
v___x_4511_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4512_ = lean_unsigned_to_nat(2u);
v___x_4513_ = l_Lean_Expr_isAppOfArity(v_e_4510_, v___x_4511_, v___x_4512_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; 
v___x_4514_ = lean_box(0);
return v___x_4514_;
}
else
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4515_ = l_Lean_Expr_appArg_x21(v_e_4510_);
v___x_4516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4515_);
return v___x_4516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4517_);
lean_dec_ref(v_e_4517_);
return v_res_4518_;
}
}
LEAN_EXPORT uint8_t lean_is_out_param(lean_object* v_e_4522_){
_start:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; uint8_t v___x_4525_; 
v___x_4523_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4524_ = lean_unsigned_to_nat(1u);
v___x_4525_ = l_Lean_Expr_isAppOfArity(v_e_4522_, v___x_4523_, v___x_4524_);
lean_dec_ref(v_e_4522_);
return v___x_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4526_){
_start:
{
uint8_t v_res_4527_; lean_object* v_r_4528_; 
v_res_4527_ = lean_is_out_param(v_e_4526_);
v_r_4528_ = lean_box(v_res_4527_);
return v_r_4528_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4532_){
_start:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4533_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4534_ = lean_unsigned_to_nat(1u);
v___x_4535_ = l_Lean_Expr_isAppOfArity(v_e_4532_, v___x_4533_, v___x_4534_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4536_){
_start:
{
uint8_t v_res_4537_; lean_object* v_r_4538_; 
v_res_4537_ = l_Lean_Expr_isSemiOutParam(v_e_4536_);
lean_dec_ref(v_e_4536_);
v_r_4538_ = lean_box(v_res_4537_);
return v_r_4538_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4539_){
_start:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; uint8_t v___x_4542_; 
v___x_4540_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4541_ = lean_unsigned_to_nat(2u);
v___x_4542_ = l_Lean_Expr_isAppOfArity(v_e_4539_, v___x_4540_, v___x_4541_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4543_){
_start:
{
uint8_t v_res_4544_; lean_object* v_r_4545_; 
v_res_4544_ = l_Lean_Expr_isOptParam(v_e_4543_);
lean_dec_ref(v_e_4543_);
v_r_4545_ = lean_box(v_res_4544_);
return v_r_4545_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4546_){
_start:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; uint8_t v___x_4549_; 
v___x_4547_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4548_ = lean_unsigned_to_nat(2u);
v___x_4549_ = l_Lean_Expr_isAppOfArity(v_e_4546_, v___x_4547_, v___x_4548_);
return v___x_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4550_){
_start:
{
uint8_t v_res_4551_; lean_object* v_r_4552_; 
v_res_4551_ = l_Lean_Expr_isAutoParam(v_e_4550_);
lean_dec_ref(v_e_4550_);
v_r_4552_ = lean_box(v_res_4551_);
return v_r_4552_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4553_){
_start:
{
lean_object* v___x_4554_; 
v___x_4554_ = l_Lean_Expr_getAppFn(v_e_4553_);
if (lean_obj_tag(v___x_4554_) == 4)
{
lean_object* v_declName_4555_; uint8_t v___y_4557_; lean_object* v___x_4562_; uint8_t v___x_4563_; 
v_declName_4555_ = lean_ctor_get(v___x_4554_, 0);
lean_inc(v_declName_4555_);
lean_dec_ref(v___x_4554_);
v___x_4562_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4563_ = lean_name_eq(v_declName_4555_, v___x_4562_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4564_; uint8_t v___x_4565_; 
v___x_4564_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4565_ = lean_name_eq(v_declName_4555_, v___x_4564_);
v___y_4557_ = v___x_4565_;
goto v___jp_4556_;
}
else
{
v___y_4557_ = v___x_4563_;
goto v___jp_4556_;
}
v___jp_4556_:
{
if (v___y_4557_ == 0)
{
lean_object* v___x_4558_; uint8_t v___x_4559_; 
v___x_4558_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4559_ = lean_name_eq(v_declName_4555_, v___x_4558_);
if (v___x_4559_ == 0)
{
lean_object* v___x_4560_; uint8_t v___x_4561_; 
v___x_4560_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4561_ = lean_name_eq(v_declName_4555_, v___x_4560_);
lean_dec(v_declName_4555_);
return v___x_4561_;
}
else
{
lean_dec(v_declName_4555_);
return v___x_4559_;
}
}
else
{
lean_dec(v_declName_4555_);
return v___y_4557_;
}
}
}
else
{
uint8_t v___x_4566_; 
lean_dec_ref(v___x_4554_);
v___x_4566_ = 0;
return v___x_4566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4567_){
_start:
{
uint8_t v_res_4568_; lean_object* v_r_4569_; 
v_res_4568_ = l_Lean_Expr_isTypeAnnotation(v_e_4567_);
lean_dec_ref(v_e_4567_);
v_r_4569_ = lean_box(v_res_4568_);
return v_r_4569_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4570_){
_start:
{
uint8_t v___y_4572_; uint8_t v___y_4576_; uint8_t v___x_4582_; 
v___x_4582_ = l_Lean_Expr_isOptParam(v_e_4570_);
if (v___x_4582_ == 0)
{
uint8_t v___x_4583_; 
v___x_4583_ = l_Lean_Expr_isAutoParam(v_e_4570_);
v___y_4576_ = v___x_4583_;
goto v___jp_4575_;
}
else
{
v___y_4576_ = v___x_4582_;
goto v___jp_4575_;
}
v___jp_4571_:
{
if (v___y_4572_ == 0)
{
return v_e_4570_;
}
else
{
lean_object* v___x_4573_; 
v___x_4573_ = l_Lean_Expr_appArg_x21(v_e_4570_);
lean_dec_ref(v_e_4570_);
v_e_4570_ = v___x_4573_;
goto _start;
}
}
v___jp_4575_:
{
if (v___y_4576_ == 0)
{
uint8_t v___x_4577_; 
lean_inc_ref(v_e_4570_);
v___x_4577_ = lean_is_out_param(v_e_4570_);
if (v___x_4577_ == 0)
{
uint8_t v___x_4578_; 
v___x_4578_ = l_Lean_Expr_isSemiOutParam(v_e_4570_);
v___y_4572_ = v___x_4578_;
goto v___jp_4571_;
}
else
{
v___y_4572_ = v___x_4577_;
goto v___jp_4571_;
}
}
else
{
lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4579_ = l_Lean_Expr_appFn_x21(v_e_4570_);
lean_dec_ref(v_e_4570_);
v___x_4580_ = l_Lean_Expr_appArg_x21(v___x_4579_);
lean_dec_ref(v___x_4579_);
v_e_4570_ = v___x_4580_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4584_){
_start:
{
lean_object* v___x_4585_; lean_object* v_e_x27_4586_; uint8_t v___x_4587_; 
v___x_4585_ = l_Lean_Expr_consumeMData(v_e_4584_);
v_e_x27_4586_ = lean_expr_consume_type_annotations(v___x_4585_);
v___x_4587_ = lean_expr_eqv(v_e_x27_4586_, v_e_4584_);
if (v___x_4587_ == 0)
{
lean_dec_ref(v_e_4584_);
v_e_4584_ = v_e_x27_4586_;
goto _start;
}
else
{
lean_dec_ref(v_e_x27_4586_);
return v_e_4584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4589_){
_start:
{
lean_object* v_fn_4590_; lean_object* v___x_4591_; 
v_fn_4590_ = lean_ctor_get(v_e_4589_, 0);
lean_inc_ref(v_fn_4590_);
lean_dec_ref(v_e_4589_);
v___x_4591_ = l_Lean_Expr_cleanupAnnotations(v_fn_4590_);
return v___x_4591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* v_e_4592_, lean_object* v_h_4593_){
_start:
{
lean_object* v___x_4594_; 
v___x_4594_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4592_);
return v___x_4594_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4598_){
_start:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; uint8_t v___x_4601_; 
v___x_4599_ = l_Lean_Expr_cleanupAnnotations(v_e_4598_);
v___x_4600_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4601_ = l_Lean_Expr_isConstOf(v___x_4599_, v___x_4600_);
lean_dec_ref(v___x_4599_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4602_){
_start:
{
uint8_t v_res_4603_; lean_object* v_r_4604_; 
v_res_4603_ = l_Lean_Expr_isFalse(v_e_4602_);
v_r_4604_ = lean_box(v_res_4603_);
return v_r_4604_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4608_){
_start:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; uint8_t v___x_4611_; 
v___x_4609_ = l_Lean_Expr_cleanupAnnotations(v_e_4608_);
v___x_4610_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4611_ = l_Lean_Expr_isConstOf(v___x_4609_, v___x_4610_);
lean_dec_ref(v___x_4609_);
return v___x_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4612_){
_start:
{
uint8_t v_res_4613_; lean_object* v_r_4614_; 
v_res_4613_ = l_Lean_Expr_isTrue(v_e_4612_);
v_r_4614_ = lean_box(v_res_4613_);
return v_r_4614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* v_x_4615_){
_start:
{
switch(lean_obj_tag(v_x_4615_))
{
case 10:
{
lean_object* v_expr_4616_; 
v_expr_4616_ = lean_ctor_get(v_x_4615_, 1);
lean_inc_ref(v_expr_4616_);
lean_dec_ref(v_x_4615_);
v_x_4615_ = v_expr_4616_;
goto _start;
}
case 7:
{
lean_object* v_body_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v_body_4618_ = lean_ctor_get(v_x_4615_, 2);
lean_inc_ref(v_body_4618_);
lean_dec_ref(v_x_4615_);
v___x_4619_ = l_Lean_Expr_getForallArity(v_body_4618_);
v___x_4620_ = lean_unsigned_to_nat(1u);
v___x_4621_ = lean_nat_add(v___x_4619_, v___x_4620_);
lean_dec(v___x_4619_);
return v___x_4621_;
}
default: 
{
uint8_t v___x_4622_; uint8_t v___x_4623_; 
v___x_4622_ = 0;
v___x_4623_ = l_Lean_Expr_isHeadBetaTarget(v_x_4615_, v___x_4622_);
if (v___x_4623_ == 0)
{
lean_object* v_e_x27_4624_; uint8_t v___x_4625_; 
lean_inc_ref(v_x_4615_);
v_e_x27_4624_ = l_Lean_Expr_cleanupAnnotations(v_x_4615_);
v___x_4625_ = lean_expr_eqv(v_x_4615_, v_e_x27_4624_);
lean_dec_ref(v_x_4615_);
if (v___x_4625_ == 0)
{
v_x_4615_ = v_e_x27_4624_;
goto _start;
}
else
{
lean_object* v___x_4627_; 
lean_dec_ref(v_e_x27_4624_);
v___x_4627_ = lean_unsigned_to_nat(0u);
return v___x_4627_;
}
}
else
{
lean_object* v___x_4628_; 
v___x_4628_ = l_Lean_Expr_headBeta(v_x_4615_);
v_x_4615_ = v___x_4628_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4630_){
_start:
{
lean_object* v___x_4631_; uint8_t v___x_4632_; 
v___x_4631_ = l_Lean_Expr_cleanupAnnotations(v_e_4630_);
v___x_4632_ = l_Lean_Expr_isApp(v___x_4631_);
if (v___x_4632_ == 0)
{
lean_object* v___x_4633_; 
lean_dec_ref(v___x_4631_);
v___x_4633_ = lean_box(0);
return v___x_4633_;
}
else
{
lean_object* v___x_4634_; uint8_t v___x_4635_; 
v___x_4634_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4631_);
v___x_4635_ = l_Lean_Expr_isApp(v___x_4634_);
if (v___x_4635_ == 0)
{
lean_object* v___x_4636_; 
lean_dec_ref(v___x_4634_);
v___x_4636_ = lean_box(0);
return v___x_4636_;
}
else
{
lean_object* v_arg_4637_; lean_object* v___x_4638_; uint8_t v___x_4639_; 
v_arg_4637_ = lean_ctor_get(v___x_4634_, 1);
lean_inc_ref(v_arg_4637_);
v___x_4638_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4634_);
v___x_4639_ = l_Lean_Expr_isApp(v___x_4638_);
if (v___x_4639_ == 0)
{
lean_object* v___x_4640_; 
lean_dec_ref(v___x_4638_);
lean_dec_ref(v_arg_4637_);
v___x_4640_ = lean_box(0);
return v___x_4640_;
}
else
{
lean_object* v___x_4641_; lean_object* v___x_4642_; uint8_t v___x_4643_; 
v___x_4641_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4638_);
v___x_4642_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4643_ = l_Lean_Expr_isConstOf(v___x_4641_, v___x_4642_);
lean_dec_ref(v___x_4641_);
if (v___x_4643_ == 0)
{
lean_object* v___x_4644_; 
lean_dec_ref(v_arg_4637_);
v___x_4644_ = lean_box(0);
return v___x_4644_;
}
else
{
if (lean_obj_tag(v_arg_4637_) == 9)
{
lean_object* v_a_4645_; 
v_a_4645_ = lean_ctor_get(v_arg_4637_, 0);
lean_inc_ref(v_a_4645_);
lean_dec_ref(v_arg_4637_);
if (lean_obj_tag(v_a_4645_) == 0)
{
lean_object* v_val_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4653_; 
v_val_4646_ = lean_ctor_get(v_a_4645_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v_a_4645_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4648_ = v_a_4645_;
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_val_4646_);
lean_dec(v_a_4645_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4651_; 
if (v_isShared_4649_ == 0)
{
lean_ctor_set_tag(v___x_4648_, 1);
v___x_4651_ = v___x_4648_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_val_4646_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
else
{
lean_object* v___x_4654_; 
lean_dec_ref(v_a_4645_);
v___x_4654_ = lean_box(0);
return v___x_4654_;
}
}
else
{
lean_object* v___x_4655_; 
lean_dec_ref(v_arg_4637_);
v___x_4655_ = lean_box(0);
return v___x_4655_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4661_){
_start:
{
lean_object* v___x_4674_; uint8_t v___x_4675_; 
lean_inc_ref(v_e_4661_);
v___x_4674_ = l_Lean_Expr_cleanupAnnotations(v_e_4661_);
v___x_4675_ = l_Lean_Expr_isApp(v___x_4674_);
if (v___x_4675_ == 0)
{
lean_dec_ref(v___x_4674_);
goto v___jp_4662_;
}
else
{
lean_object* v_arg_4676_; lean_object* v___x_4677_; uint8_t v___x_4678_; 
v_arg_4676_ = lean_ctor_get(v___x_4674_, 1);
lean_inc_ref(v_arg_4676_);
v___x_4677_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4674_);
v___x_4678_ = l_Lean_Expr_isApp(v___x_4677_);
if (v___x_4678_ == 0)
{
lean_dec_ref(v___x_4677_);
lean_dec_ref(v_arg_4676_);
goto v___jp_4662_;
}
else
{
lean_object* v___x_4679_; uint8_t v___x_4680_; 
v___x_4679_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4677_);
v___x_4680_ = l_Lean_Expr_isApp(v___x_4679_);
if (v___x_4680_ == 0)
{
lean_dec_ref(v___x_4679_);
lean_dec_ref(v_arg_4676_);
goto v___jp_4662_;
}
else
{
lean_object* v___x_4681_; lean_object* v___x_4682_; uint8_t v___x_4683_; 
v___x_4681_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4679_);
v___x_4682_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4683_ = l_Lean_Expr_isConstOf(v___x_4681_, v___x_4682_);
lean_dec_ref(v___x_4681_);
if (v___x_4683_ == 0)
{
lean_dec_ref(v_arg_4676_);
goto v___jp_4662_;
}
else
{
lean_object* v___x_4684_; 
lean_dec_ref(v_e_4661_);
v___x_4684_ = l_Lean_Expr_nat_x3f(v_arg_4676_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v___x_4685_; 
v___x_4685_ = lean_box(0);
return v___x_4685_;
}
else
{
lean_object* v_val_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4698_; 
v_val_4686_ = lean_ctor_get(v___x_4684_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4688_ = v___x_4684_;
v_isShared_4689_ = v_isSharedCheck_4698_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_val_4686_);
lean_dec(v___x_4684_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4698_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4690_; uint8_t v___x_4691_; 
v___x_4690_ = lean_unsigned_to_nat(0u);
v___x_4691_ = lean_nat_dec_eq(v_val_4686_, v___x_4690_);
if (v___x_4691_ == 0)
{
lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4695_; 
v___x_4692_ = lean_nat_to_int(v_val_4686_);
v___x_4693_ = lean_int_neg(v___x_4692_);
lean_dec(v___x_4692_);
if (v_isShared_4689_ == 0)
{
lean_ctor_set(v___x_4688_, 0, v___x_4693_);
v___x_4695_ = v___x_4688_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4693_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
else
{
lean_object* v___x_4697_; 
lean_del_object(v___x_4688_);
lean_dec(v_val_4686_);
v___x_4697_ = lean_box(0);
return v___x_4697_;
}
}
}
}
}
}
}
v___jp_4662_:
{
lean_object* v___x_4663_; 
v___x_4663_ = l_Lean_Expr_nat_x3f(v_e_4661_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_object* v___x_4664_; 
v___x_4664_ = lean_box(0);
return v___x_4664_;
}
else
{
lean_object* v_val_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4673_; 
v_val_4665_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4667_ = v___x_4663_;
v_isShared_4668_ = v_isSharedCheck_4673_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_val_4665_);
lean_dec(v___x_4663_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4673_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4669_; lean_object* v___x_4671_; 
v___x_4669_ = lean_nat_to_int(v_val_4665_);
if (v_isShared_4668_ == 0)
{
lean_ctor_set(v___x_4667_, 0, v___x_4669_);
v___x_4671_ = v___x_4667_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v___x_4669_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4699_, lean_object* v_e_4700_){
_start:
{
uint8_t v___x_4701_; lean_object* v_d_4703_; lean_object* v_b_4704_; 
v___x_4701_ = l_Lean_Expr_hasFVar(v_e_4700_);
if (v___x_4701_ == 0)
{
lean_dec_ref(v_e_4700_);
lean_dec_ref(v_p_4699_);
return v___x_4701_;
}
else
{
switch(lean_obj_tag(v_e_4700_))
{
case 7:
{
lean_object* v_binderType_4707_; lean_object* v_body_4708_; 
v_binderType_4707_ = lean_ctor_get(v_e_4700_, 1);
lean_inc_ref(v_binderType_4707_);
v_body_4708_ = lean_ctor_get(v_e_4700_, 2);
lean_inc_ref(v_body_4708_);
lean_dec_ref(v_e_4700_);
v_d_4703_ = v_binderType_4707_;
v_b_4704_ = v_body_4708_;
goto v___jp_4702_;
}
case 6:
{
lean_object* v_binderType_4709_; lean_object* v_body_4710_; 
v_binderType_4709_ = lean_ctor_get(v_e_4700_, 1);
lean_inc_ref(v_binderType_4709_);
v_body_4710_ = lean_ctor_get(v_e_4700_, 2);
lean_inc_ref(v_body_4710_);
lean_dec_ref(v_e_4700_);
v_d_4703_ = v_binderType_4709_;
v_b_4704_ = v_body_4710_;
goto v___jp_4702_;
}
case 10:
{
lean_object* v_expr_4711_; 
v_expr_4711_ = lean_ctor_get(v_e_4700_, 1);
lean_inc_ref(v_expr_4711_);
lean_dec_ref(v_e_4700_);
v_e_4700_ = v_expr_4711_;
goto _start;
}
case 8:
{
lean_object* v_type_4713_; lean_object* v_value_4714_; lean_object* v_body_4715_; uint8_t v___x_4716_; 
v_type_4713_ = lean_ctor_get(v_e_4700_, 1);
lean_inc_ref(v_type_4713_);
v_value_4714_ = lean_ctor_get(v_e_4700_, 2);
lean_inc_ref(v_value_4714_);
v_body_4715_ = lean_ctor_get(v_e_4700_, 3);
lean_inc_ref(v_body_4715_);
lean_dec_ref(v_e_4700_);
lean_inc_ref(v_p_4699_);
v___x_4716_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4699_, v_type_4713_);
if (v___x_4716_ == 0)
{
uint8_t v___x_4717_; 
lean_inc_ref(v_p_4699_);
v___x_4717_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4699_, v_value_4714_);
if (v___x_4717_ == 0)
{
v_e_4700_ = v_body_4715_;
goto _start;
}
else
{
lean_dec_ref(v_body_4715_);
lean_dec_ref(v_p_4699_);
return v___x_4701_;
}
}
else
{
lean_dec_ref(v_body_4715_);
lean_dec_ref(v_value_4714_);
lean_dec_ref(v_p_4699_);
return v___x_4701_;
}
}
case 5:
{
lean_object* v_fn_4719_; lean_object* v_arg_4720_; uint8_t v___x_4721_; 
v_fn_4719_ = lean_ctor_get(v_e_4700_, 0);
lean_inc_ref(v_fn_4719_);
v_arg_4720_ = lean_ctor_get(v_e_4700_, 1);
lean_inc_ref(v_arg_4720_);
lean_dec_ref(v_e_4700_);
lean_inc_ref(v_p_4699_);
v___x_4721_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4699_, v_fn_4719_);
if (v___x_4721_ == 0)
{
v_e_4700_ = v_arg_4720_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4720_);
lean_dec_ref(v_p_4699_);
return v___x_4701_;
}
}
case 11:
{
lean_object* v_struct_4723_; 
v_struct_4723_ = lean_ctor_get(v_e_4700_, 2);
lean_inc_ref(v_struct_4723_);
lean_dec_ref(v_e_4700_);
v_e_4700_ = v_struct_4723_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4725_; lean_object* v___x_4726_; uint8_t v___x_4727_; 
v_fvarId_4725_ = lean_ctor_get(v_e_4700_, 0);
lean_inc(v_fvarId_4725_);
lean_dec_ref(v_e_4700_);
v___x_4726_ = lean_apply_1(v_p_4699_, v_fvarId_4725_);
v___x_4727_ = lean_unbox(v___x_4726_);
return v___x_4727_;
}
default: 
{
uint8_t v___x_4728_; 
lean_dec_ref(v_e_4700_);
lean_dec_ref(v_p_4699_);
v___x_4728_ = 0;
return v___x_4728_;
}
}
}
v___jp_4702_:
{
uint8_t v___x_4705_; 
lean_inc_ref(v_p_4699_);
v___x_4705_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4699_, v_d_4703_);
if (v___x_4705_ == 0)
{
v_e_4700_ = v_b_4704_;
goto _start;
}
else
{
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_p_4699_);
return v___x_4701_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_4729_, lean_object* v_e_4730_){
_start:
{
uint8_t v_res_4731_; lean_object* v_r_4732_; 
v_res_4731_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4729_, v_e_4730_);
v_r_4732_ = lean_box(v_res_4731_);
return v_r_4732_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_4733_, lean_object* v_p_4734_){
_start:
{
uint8_t v___x_4735_; 
v___x_4735_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4734_, v_e_4733_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_4736_, lean_object* v_p_4737_){
_start:
{
uint8_t v_res_4738_; lean_object* v_r_4739_; 
v_res_4738_ = l_Lean_Expr_hasAnyFVar(v_e_4736_, v_p_4737_);
v_r_4739_ = lean_box(v_res_4738_);
return v_r_4739_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_4740_, lean_object* v_e_4741_){
_start:
{
uint8_t v___x_4742_; lean_object* v_d_4744_; lean_object* v_b_4745_; 
v___x_4742_ = l_Lean_Expr_hasFVar(v_e_4741_);
if (v___x_4742_ == 0)
{
return v___x_4742_;
}
else
{
switch(lean_obj_tag(v_e_4741_))
{
case 7:
{
lean_object* v_binderType_4748_; lean_object* v_body_4749_; 
v_binderType_4748_ = lean_ctor_get(v_e_4741_, 1);
v_body_4749_ = lean_ctor_get(v_e_4741_, 2);
v_d_4744_ = v_binderType_4748_;
v_b_4745_ = v_body_4749_;
goto v___jp_4743_;
}
case 6:
{
lean_object* v_binderType_4750_; lean_object* v_body_4751_; 
v_binderType_4750_ = lean_ctor_get(v_e_4741_, 1);
v_body_4751_ = lean_ctor_get(v_e_4741_, 2);
v_d_4744_ = v_binderType_4750_;
v_b_4745_ = v_body_4751_;
goto v___jp_4743_;
}
case 10:
{
lean_object* v_expr_4752_; 
v_expr_4752_ = lean_ctor_get(v_e_4741_, 1);
v_e_4741_ = v_expr_4752_;
goto _start;
}
case 8:
{
lean_object* v_type_4754_; lean_object* v_value_4755_; lean_object* v_body_4756_; uint8_t v___x_4757_; 
v_type_4754_ = lean_ctor_get(v_e_4741_, 1);
v_value_4755_ = lean_ctor_get(v_e_4741_, 2);
v_body_4756_ = lean_ctor_get(v_e_4741_, 3);
v___x_4757_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4740_, v_type_4754_);
if (v___x_4757_ == 0)
{
uint8_t v___x_4758_; 
v___x_4758_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4740_, v_value_4755_);
if (v___x_4758_ == 0)
{
v_e_4741_ = v_body_4756_;
goto _start;
}
else
{
return v___x_4742_;
}
}
else
{
return v___x_4742_;
}
}
case 5:
{
lean_object* v_fn_4760_; lean_object* v_arg_4761_; uint8_t v___x_4762_; 
v_fn_4760_ = lean_ctor_get(v_e_4741_, 0);
v_arg_4761_ = lean_ctor_get(v_e_4741_, 1);
v___x_4762_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4740_, v_fn_4760_);
if (v___x_4762_ == 0)
{
v_e_4741_ = v_arg_4761_;
goto _start;
}
else
{
return v___x_4742_;
}
}
case 11:
{
lean_object* v_struct_4764_; 
v_struct_4764_ = lean_ctor_get(v_e_4741_, 2);
v_e_4741_ = v_struct_4764_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4766_; uint8_t v___x_4767_; 
v_fvarId_4766_ = lean_ctor_get(v_e_4741_, 0);
v___x_4767_ = lean_name_eq(v_fvarId_4766_, v_fvarId_4740_);
return v___x_4767_;
}
default: 
{
uint8_t v___x_4768_; 
v___x_4768_ = 0;
return v___x_4768_;
}
}
}
v___jp_4743_:
{
uint8_t v___x_4746_; 
v___x_4746_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4740_, v_d_4744_);
if (v___x_4746_ == 0)
{
v_e_4741_ = v_b_4745_;
goto _start;
}
else
{
return v___x_4742_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_4769_, lean_object* v_e_4770_){
_start:
{
uint8_t v_res_4771_; lean_object* v_r_4772_; 
v_res_4771_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4769_, v_e_4770_);
lean_dec_ref(v_e_4770_);
lean_dec(v_fvarId_4769_);
v_r_4772_ = lean_box(v_res_4771_);
return v_r_4772_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_4773_, lean_object* v_fvarId_4774_){
_start:
{
uint8_t v___x_4775_; 
v___x_4775_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4774_, v_e_4773_);
return v___x_4775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_4776_, lean_object* v_fvarId_4777_){
_start:
{
uint8_t v_res_4778_; lean_object* v_r_4779_; 
v_res_4778_ = l_Lean_Expr_containsFVar(v_e_4776_, v_fvarId_4777_);
lean_dec(v_fvarId_4777_);
lean_dec_ref(v_e_4776_);
v_r_4779_ = lean_box(v_res_4778_);
return v_r_4779_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4781_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_4782_ = lean_unsigned_to_nat(18u);
v___x_4783_ = lean_unsigned_to_nat(1823u);
v___x_4784_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_4785_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4786_ = l_mkPanicMessageWithDecl(v___x_4785_, v___x_4784_, v___x_4783_, v___x_4782_, v___x_4781_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_4787_, lean_object* v_newFn_4788_, lean_object* v_newArg_4789_){
_start:
{
uint8_t v___y_4791_; 
if (lean_obj_tag(v_e_4787_) == 5)
{
lean_object* v_fn_4793_; lean_object* v_arg_4794_; size_t v___x_4795_; size_t v___x_4796_; uint8_t v___x_4797_; 
v_fn_4793_ = lean_ctor_get(v_e_4787_, 0);
v_arg_4794_ = lean_ctor_get(v_e_4787_, 1);
v___x_4795_ = lean_ptr_addr(v_fn_4793_);
v___x_4796_ = lean_ptr_addr(v_newFn_4788_);
v___x_4797_ = lean_usize_dec_eq(v___x_4795_, v___x_4796_);
if (v___x_4797_ == 0)
{
v___y_4791_ = v___x_4797_;
goto v___jp_4790_;
}
else
{
size_t v___x_4798_; size_t v___x_4799_; uint8_t v___x_4800_; 
v___x_4798_ = lean_ptr_addr(v_arg_4794_);
v___x_4799_ = lean_ptr_addr(v_newArg_4789_);
v___x_4800_ = lean_usize_dec_eq(v___x_4798_, v___x_4799_);
v___y_4791_ = v___x_4800_;
goto v___jp_4790_;
}
}
else
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
lean_dec_ref(v_newArg_4789_);
lean_dec_ref(v_newFn_4788_);
v___x_4801_ = l_Lean_instInhabitedExpr;
v___x_4802_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_4803_ = l_panic___redArg(v___x_4801_, v___x_4802_);
return v___x_4803_;
}
v___jp_4790_:
{
if (v___y_4791_ == 0)
{
lean_object* v___x_4792_; 
v___x_4792_ = l_Lean_Expr_app___override(v_newFn_4788_, v_newArg_4789_);
return v___x_4792_;
}
else
{
lean_dec_ref(v_newArg_4789_);
lean_dec_ref(v_newFn_4788_);
lean_inc_ref(v_e_4787_);
return v_e_4787_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_4804_, lean_object* v_newFn_4805_, lean_object* v_newArg_4806_){
_start:
{
lean_object* v_res_4807_; 
v_res_4807_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_4804_, v_newFn_4805_, v_newArg_4806_);
lean_dec_ref(v_e_4804_);
return v_res_4807_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v___x_4809_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_4810_ = lean_unsigned_to_nat(20u);
v___x_4811_ = lean_unsigned_to_nat(1834u);
v___x_4812_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_4813_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4814_ = l_mkPanicMessageWithDecl(v___x_4813_, v___x_4812_, v___x_4811_, v___x_4810_, v___x_4809_);
return v___x_4814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_4815_, lean_object* v_fvarIdNew_4816_){
_start:
{
if (lean_obj_tag(v_e_4815_) == 1)
{
lean_object* v_fvarId_4817_; uint8_t v___x_4818_; 
v_fvarId_4817_ = lean_ctor_get(v_e_4815_, 0);
v___x_4818_ = lean_name_eq(v_fvarId_4817_, v_fvarIdNew_4816_);
if (v___x_4818_ == 0)
{
lean_object* v___x_4819_; 
v___x_4819_ = l_Lean_Expr_fvar___override(v_fvarIdNew_4816_);
return v___x_4819_;
}
else
{
lean_dec(v_fvarIdNew_4816_);
lean_inc_ref(v_e_4815_);
return v_e_4815_;
}
}
else
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
lean_dec(v_fvarIdNew_4816_);
v___x_4820_ = l_Lean_instInhabitedExpr;
v___x_4821_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_4822_ = l_panic___redArg(v___x_4820_, v___x_4821_);
return v___x_4822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_4823_, lean_object* v_fvarIdNew_4824_){
_start:
{
lean_object* v_res_4825_; 
v_res_4825_ = l_Lean_Expr_updateFVar_x21(v_e_4823_, v_fvarIdNew_4824_);
lean_dec_ref(v_e_4823_);
return v_res_4825_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4827_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_4828_ = lean_unsigned_to_nat(18u);
v___x_4829_ = lean_unsigned_to_nat(1839u);
v___x_4830_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_4831_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4832_ = l_mkPanicMessageWithDecl(v___x_4831_, v___x_4830_, v___x_4829_, v___x_4828_, v___x_4827_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_4833_, lean_object* v_newLevels_4834_){
_start:
{
if (lean_obj_tag(v_e_4833_) == 4)
{
lean_object* v_declName_4835_; lean_object* v_us_4836_; uint8_t v___x_4837_; 
v_declName_4835_ = lean_ctor_get(v_e_4833_, 0);
v_us_4836_ = lean_ctor_get(v_e_4833_, 1);
v___x_4837_ = l_ptrEqList___redArg(v_us_4836_, v_newLevels_4834_);
if (v___x_4837_ == 0)
{
lean_object* v___x_4838_; 
lean_inc(v_declName_4835_);
lean_dec_ref(v_e_4833_);
v___x_4838_ = l_Lean_Expr_const___override(v_declName_4835_, v_newLevels_4834_);
return v___x_4838_;
}
else
{
lean_dec(v_newLevels_4834_);
return v_e_4833_;
}
}
else
{
lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
lean_dec(v_newLevels_4834_);
lean_dec_ref(v_e_4833_);
v___x_4839_ = l_Lean_instInhabitedExpr;
v___x_4840_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_4841_ = l_panic___redArg(v___x_4839_, v___x_4840_);
return v___x_4841_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4844_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_4845_ = lean_unsigned_to_nat(14u);
v___x_4846_ = lean_unsigned_to_nat(1850u);
v___x_4847_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_4848_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4849_ = l_mkPanicMessageWithDecl(v___x_4848_, v___x_4847_, v___x_4846_, v___x_4845_, v___x_4844_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_4850_, lean_object* v_u_x27_4851_){
_start:
{
if (lean_obj_tag(v_e_4850_) == 3)
{
lean_object* v_u_4852_; size_t v___x_4853_; size_t v___x_4854_; uint8_t v___x_4855_; 
v_u_4852_ = lean_ctor_get(v_e_4850_, 0);
v___x_4853_ = lean_ptr_addr(v_u_4852_);
v___x_4854_ = lean_ptr_addr(v_u_x27_4851_);
v___x_4855_ = lean_usize_dec_eq(v___x_4853_, v___x_4854_);
if (v___x_4855_ == 0)
{
lean_object* v___x_4856_; 
v___x_4856_ = l_Lean_Expr_sort___override(v_u_x27_4851_);
return v___x_4856_;
}
else
{
lean_dec(v_u_x27_4851_);
lean_inc_ref(v_e_4850_);
return v_e_4850_;
}
}
else
{
lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; 
lean_dec(v_u_x27_4851_);
v___x_4857_ = l_Lean_instInhabitedExpr;
v___x_4858_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_4859_ = l_panic___redArg(v___x_4857_, v___x_4858_);
return v___x_4859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_4860_, lean_object* v_u_x27_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_4860_, v_u_x27_4861_);
lean_dec_ref(v_e_4860_);
return v_res_4862_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4865_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_4866_ = lean_unsigned_to_nat(17u);
v___x_4867_ = lean_unsigned_to_nat(1861u);
v___x_4868_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_4869_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4870_ = l_mkPanicMessageWithDecl(v___x_4869_, v___x_4868_, v___x_4867_, v___x_4866_, v___x_4865_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_4871_, lean_object* v_newExpr_4872_){
_start:
{
if (lean_obj_tag(v_e_4871_) == 10)
{
lean_object* v_data_4873_; lean_object* v_expr_4874_; size_t v___x_4875_; size_t v___x_4876_; uint8_t v___x_4877_; 
v_data_4873_ = lean_ctor_get(v_e_4871_, 0);
v_expr_4874_ = lean_ctor_get(v_e_4871_, 1);
v___x_4875_ = lean_ptr_addr(v_expr_4874_);
v___x_4876_ = lean_ptr_addr(v_newExpr_4872_);
v___x_4877_ = lean_usize_dec_eq(v___x_4875_, v___x_4876_);
if (v___x_4877_ == 0)
{
lean_object* v___x_4878_; 
lean_inc(v_data_4873_);
lean_dec_ref(v_e_4871_);
v___x_4878_ = l_Lean_Expr_mdata___override(v_data_4873_, v_newExpr_4872_);
return v___x_4878_;
}
else
{
lean_dec_ref(v_newExpr_4872_);
return v_e_4871_;
}
}
else
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
lean_dec_ref(v_newExpr_4872_);
lean_dec_ref(v_e_4871_);
v___x_4879_ = l_Lean_instInhabitedExpr;
v___x_4880_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_4881_ = l_panic___redArg(v___x_4879_, v___x_4880_);
return v___x_4881_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4884_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_4885_ = lean_unsigned_to_nat(18u);
v___x_4886_ = lean_unsigned_to_nat(1872u);
v___x_4887_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_4888_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4889_ = l_mkPanicMessageWithDecl(v___x_4888_, v___x_4887_, v___x_4886_, v___x_4885_, v___x_4884_);
return v___x_4889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_4890_, lean_object* v_newExpr_4891_){
_start:
{
if (lean_obj_tag(v_e_4890_) == 11)
{
lean_object* v_typeName_4892_; lean_object* v_idx_4893_; lean_object* v_struct_4894_; size_t v___x_4895_; size_t v___x_4896_; uint8_t v___x_4897_; 
v_typeName_4892_ = lean_ctor_get(v_e_4890_, 0);
v_idx_4893_ = lean_ctor_get(v_e_4890_, 1);
v_struct_4894_ = lean_ctor_get(v_e_4890_, 2);
v___x_4895_ = lean_ptr_addr(v_struct_4894_);
v___x_4896_ = lean_ptr_addr(v_newExpr_4891_);
v___x_4897_ = lean_usize_dec_eq(v___x_4895_, v___x_4896_);
if (v___x_4897_ == 0)
{
lean_object* v___x_4898_; 
lean_inc(v_idx_4893_);
lean_inc(v_typeName_4892_);
lean_dec_ref(v_e_4890_);
v___x_4898_ = l_Lean_Expr_proj___override(v_typeName_4892_, v_idx_4893_, v_newExpr_4891_);
return v___x_4898_;
}
else
{
lean_dec_ref(v_newExpr_4891_);
return v_e_4890_;
}
}
else
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; 
lean_dec_ref(v_newExpr_4891_);
lean_dec_ref(v_e_4890_);
v___x_4899_ = l_Lean_instInhabitedExpr;
v___x_4900_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_4901_ = l_panic___redArg(v___x_4899_, v___x_4900_);
return v___x_4901_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4904_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_4905_ = lean_unsigned_to_nat(23u);
v___x_4906_ = lean_unsigned_to_nat(1887u);
v___x_4907_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_4908_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4909_ = l_mkPanicMessageWithDecl(v___x_4908_, v___x_4907_, v___x_4906_, v___x_4905_, v___x_4904_);
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_4910_, uint8_t v_newBinfo_4911_, lean_object* v_newDomain_4912_, lean_object* v_newBody_4913_){
_start:
{
if (lean_obj_tag(v_e_4910_) == 7)
{
lean_object* v_binderName_4914_; lean_object* v_binderType_4915_; lean_object* v_body_4916_; uint8_t v_binderInfo_4917_; uint8_t v___y_4919_; size_t v___x_4923_; size_t v___x_4924_; uint8_t v___x_4925_; 
v_binderName_4914_ = lean_ctor_get(v_e_4910_, 0);
v_binderType_4915_ = lean_ctor_get(v_e_4910_, 1);
v_body_4916_ = lean_ctor_get(v_e_4910_, 2);
v_binderInfo_4917_ = lean_ctor_get_uint8(v_e_4910_, sizeof(void*)*3 + 8);
v___x_4923_ = lean_ptr_addr(v_binderType_4915_);
v___x_4924_ = lean_ptr_addr(v_newDomain_4912_);
v___x_4925_ = lean_usize_dec_eq(v___x_4923_, v___x_4924_);
if (v___x_4925_ == 0)
{
v___y_4919_ = v___x_4925_;
goto v___jp_4918_;
}
else
{
size_t v___x_4926_; size_t v___x_4927_; uint8_t v___x_4928_; 
v___x_4926_ = lean_ptr_addr(v_body_4916_);
v___x_4927_ = lean_ptr_addr(v_newBody_4913_);
v___x_4928_ = lean_usize_dec_eq(v___x_4926_, v___x_4927_);
v___y_4919_ = v___x_4928_;
goto v___jp_4918_;
}
v___jp_4918_:
{
if (v___y_4919_ == 0)
{
lean_object* v___x_4920_; 
lean_inc(v_binderName_4914_);
lean_dec_ref(v_e_4910_);
v___x_4920_ = l_Lean_Expr_forallE___override(v_binderName_4914_, v_newDomain_4912_, v_newBody_4913_, v_newBinfo_4911_);
return v___x_4920_;
}
else
{
uint8_t v___x_4921_; 
v___x_4921_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_4917_, v_newBinfo_4911_);
if (v___x_4921_ == 0)
{
lean_object* v___x_4922_; 
lean_inc(v_binderName_4914_);
lean_dec_ref(v_e_4910_);
v___x_4922_ = l_Lean_Expr_forallE___override(v_binderName_4914_, v_newDomain_4912_, v_newBody_4913_, v_newBinfo_4911_);
return v___x_4922_;
}
else
{
lean_dec_ref(v_newBody_4913_);
lean_dec_ref(v_newDomain_4912_);
return v_e_4910_;
}
}
}
}
else
{
lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; 
lean_dec_ref(v_newBody_4913_);
lean_dec_ref(v_newDomain_4912_);
lean_dec_ref(v_e_4910_);
v___x_4929_ = l_Lean_instInhabitedExpr;
v___x_4930_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_4931_ = l_panic___redArg(v___x_4929_, v___x_4930_);
return v___x_4931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_4932_, lean_object* v_newBinfo_4933_, lean_object* v_newDomain_4934_, lean_object* v_newBody_4935_){
_start:
{
uint8_t v_newBinfo_boxed_4936_; lean_object* v_res_4937_; 
v_newBinfo_boxed_4936_ = lean_unbox(v_newBinfo_4933_);
v_res_4937_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_4932_, v_newBinfo_boxed_4936_, v_newDomain_4934_, v_newBody_4935_);
return v_res_4937_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4939_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_4940_ = lean_unsigned_to_nat(24u);
v___x_4941_ = lean_unsigned_to_nat(1898u);
v___x_4942_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_4943_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4944_ = l_mkPanicMessageWithDecl(v___x_4943_, v___x_4942_, v___x_4941_, v___x_4940_, v___x_4939_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_4945_, lean_object* v_newDomain_4946_, lean_object* v_newBody_4947_){
_start:
{
if (lean_obj_tag(v_e_4945_) == 7)
{
lean_object* v_binderName_4948_; lean_object* v_binderType_4949_; lean_object* v_body_4950_; uint8_t v_binderInfo_4951_; uint8_t v___y_4953_; size_t v___x_4957_; size_t v___x_4958_; uint8_t v___x_4959_; 
v_binderName_4948_ = lean_ctor_get(v_e_4945_, 0);
v_binderType_4949_ = lean_ctor_get(v_e_4945_, 1);
v_body_4950_ = lean_ctor_get(v_e_4945_, 2);
v_binderInfo_4951_ = lean_ctor_get_uint8(v_e_4945_, sizeof(void*)*3 + 8);
v___x_4957_ = lean_ptr_addr(v_binderType_4949_);
v___x_4958_ = lean_ptr_addr(v_newDomain_4946_);
v___x_4959_ = lean_usize_dec_eq(v___x_4957_, v___x_4958_);
if (v___x_4959_ == 0)
{
v___y_4953_ = v___x_4959_;
goto v___jp_4952_;
}
else
{
size_t v___x_4960_; size_t v___x_4961_; uint8_t v___x_4962_; 
v___x_4960_ = lean_ptr_addr(v_body_4950_);
v___x_4961_ = lean_ptr_addr(v_newBody_4947_);
v___x_4962_ = lean_usize_dec_eq(v___x_4960_, v___x_4961_);
v___y_4953_ = v___x_4962_;
goto v___jp_4952_;
}
v___jp_4952_:
{
if (v___y_4953_ == 0)
{
lean_object* v___x_4954_; 
lean_inc(v_binderName_4948_);
lean_dec_ref(v_e_4945_);
v___x_4954_ = l_Lean_Expr_forallE___override(v_binderName_4948_, v_newDomain_4946_, v_newBody_4947_, v_binderInfo_4951_);
return v___x_4954_;
}
else
{
uint8_t v___x_4955_; 
v___x_4955_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_4951_, v_binderInfo_4951_);
if (v___x_4955_ == 0)
{
lean_object* v___x_4956_; 
lean_inc(v_binderName_4948_);
lean_dec_ref(v_e_4945_);
v___x_4956_ = l_Lean_Expr_forallE___override(v_binderName_4948_, v_newDomain_4946_, v_newBody_4947_, v_binderInfo_4951_);
return v___x_4956_;
}
else
{
lean_dec_ref(v_newBody_4947_);
lean_dec_ref(v_newDomain_4946_);
return v_e_4945_;
}
}
}
}
else
{
lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; 
lean_dec_ref(v_newBody_4947_);
lean_dec_ref(v_newDomain_4946_);
lean_dec_ref(v_e_4945_);
v___x_4963_ = l_Lean_instInhabitedExpr;
v___x_4964_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_4965_ = l_panic___redArg(v___x_4963_, v___x_4964_);
return v___x_4965_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
v___x_4968_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_4969_ = lean_unsigned_to_nat(19u);
v___x_4970_ = lean_unsigned_to_nat(1907u);
v___x_4971_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_4972_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4973_ = l_mkPanicMessageWithDecl(v___x_4972_, v___x_4971_, v___x_4970_, v___x_4969_, v___x_4968_);
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_4974_, uint8_t v_newBinfo_4975_, lean_object* v_newDomain_4976_, lean_object* v_newBody_4977_){
_start:
{
if (lean_obj_tag(v_e_4974_) == 6)
{
lean_object* v_binderName_4978_; lean_object* v_binderType_4979_; lean_object* v_body_4980_; uint8_t v_binderInfo_4981_; uint8_t v___y_4983_; size_t v___x_4987_; size_t v___x_4988_; uint8_t v___x_4989_; 
v_binderName_4978_ = lean_ctor_get(v_e_4974_, 0);
v_binderType_4979_ = lean_ctor_get(v_e_4974_, 1);
v_body_4980_ = lean_ctor_get(v_e_4974_, 2);
v_binderInfo_4981_ = lean_ctor_get_uint8(v_e_4974_, sizeof(void*)*3 + 8);
v___x_4987_ = lean_ptr_addr(v_binderType_4979_);
v___x_4988_ = lean_ptr_addr(v_newDomain_4976_);
v___x_4989_ = lean_usize_dec_eq(v___x_4987_, v___x_4988_);
if (v___x_4989_ == 0)
{
v___y_4983_ = v___x_4989_;
goto v___jp_4982_;
}
else
{
size_t v___x_4990_; size_t v___x_4991_; uint8_t v___x_4992_; 
v___x_4990_ = lean_ptr_addr(v_body_4980_);
v___x_4991_ = lean_ptr_addr(v_newBody_4977_);
v___x_4992_ = lean_usize_dec_eq(v___x_4990_, v___x_4991_);
v___y_4983_ = v___x_4992_;
goto v___jp_4982_;
}
v___jp_4982_:
{
if (v___y_4983_ == 0)
{
lean_object* v___x_4984_; 
lean_inc(v_binderName_4978_);
lean_dec_ref(v_e_4974_);
v___x_4984_ = l_Lean_Expr_lam___override(v_binderName_4978_, v_newDomain_4976_, v_newBody_4977_, v_newBinfo_4975_);
return v___x_4984_;
}
else
{
uint8_t v___x_4985_; 
v___x_4985_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_4981_, v_newBinfo_4975_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; 
lean_inc(v_binderName_4978_);
lean_dec_ref(v_e_4974_);
v___x_4986_ = l_Lean_Expr_lam___override(v_binderName_4978_, v_newDomain_4976_, v_newBody_4977_, v_newBinfo_4975_);
return v___x_4986_;
}
else
{
lean_dec_ref(v_newBody_4977_);
lean_dec_ref(v_newDomain_4976_);
return v_e_4974_;
}
}
}
}
else
{
lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
lean_dec_ref(v_newBody_4977_);
lean_dec_ref(v_newDomain_4976_);
lean_dec_ref(v_e_4974_);
v___x_4993_ = l_Lean_instInhabitedExpr;
v___x_4994_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_4995_ = l_panic___redArg(v___x_4993_, v___x_4994_);
return v___x_4995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_4996_, lean_object* v_newBinfo_4997_, lean_object* v_newDomain_4998_, lean_object* v_newBody_4999_){
_start:
{
uint8_t v_newBinfo_boxed_5000_; lean_object* v_res_5001_; 
v_newBinfo_boxed_5000_ = lean_unbox(v_newBinfo_4997_);
v_res_5001_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_4996_, v_newBinfo_boxed_5000_, v_newDomain_4998_, v_newBody_4999_);
return v_res_5001_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; 
v___x_5003_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5004_ = lean_unsigned_to_nat(20u);
v___x_5005_ = lean_unsigned_to_nat(1918u);
v___x_5006_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5007_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5008_ = l_mkPanicMessageWithDecl(v___x_5007_, v___x_5006_, v___x_5005_, v___x_5004_, v___x_5003_);
return v___x_5008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5009_, lean_object* v_newDomain_5010_, lean_object* v_newBody_5011_){
_start:
{
if (lean_obj_tag(v_e_5009_) == 6)
{
lean_object* v_binderName_5012_; lean_object* v_binderType_5013_; lean_object* v_body_5014_; uint8_t v_binderInfo_5015_; uint8_t v___y_5017_; size_t v___x_5021_; size_t v___x_5022_; uint8_t v___x_5023_; 
v_binderName_5012_ = lean_ctor_get(v_e_5009_, 0);
v_binderType_5013_ = lean_ctor_get(v_e_5009_, 1);
v_body_5014_ = lean_ctor_get(v_e_5009_, 2);
v_binderInfo_5015_ = lean_ctor_get_uint8(v_e_5009_, sizeof(void*)*3 + 8);
v___x_5021_ = lean_ptr_addr(v_binderType_5013_);
v___x_5022_ = lean_ptr_addr(v_newDomain_5010_);
v___x_5023_ = lean_usize_dec_eq(v___x_5021_, v___x_5022_);
if (v___x_5023_ == 0)
{
v___y_5017_ = v___x_5023_;
goto v___jp_5016_;
}
else
{
size_t v___x_5024_; size_t v___x_5025_; uint8_t v___x_5026_; 
v___x_5024_ = lean_ptr_addr(v_body_5014_);
v___x_5025_ = lean_ptr_addr(v_newBody_5011_);
v___x_5026_ = lean_usize_dec_eq(v___x_5024_, v___x_5025_);
v___y_5017_ = v___x_5026_;
goto v___jp_5016_;
}
v___jp_5016_:
{
if (v___y_5017_ == 0)
{
lean_object* v___x_5018_; 
lean_inc(v_binderName_5012_);
lean_dec_ref(v_e_5009_);
v___x_5018_ = l_Lean_Expr_lam___override(v_binderName_5012_, v_newDomain_5010_, v_newBody_5011_, v_binderInfo_5015_);
return v___x_5018_;
}
else
{
uint8_t v___x_5019_; 
v___x_5019_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5015_, v_binderInfo_5015_);
if (v___x_5019_ == 0)
{
lean_object* v___x_5020_; 
lean_inc(v_binderName_5012_);
lean_dec_ref(v_e_5009_);
v___x_5020_ = l_Lean_Expr_lam___override(v_binderName_5012_, v_newDomain_5010_, v_newBody_5011_, v_binderInfo_5015_);
return v___x_5020_;
}
else
{
lean_dec_ref(v_newBody_5011_);
lean_dec_ref(v_newDomain_5010_);
return v_e_5009_;
}
}
}
}
else
{
lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
lean_dec_ref(v_newBody_5011_);
lean_dec_ref(v_newDomain_5010_);
lean_dec_ref(v_e_5009_);
v___x_5027_ = l_Lean_instInhabitedExpr;
v___x_5028_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5029_ = l_panic___redArg(v___x_5027_, v___x_5028_);
return v___x_5029_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; 
v___x_5031_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5032_ = lean_unsigned_to_nat(22u);
v___x_5033_ = lean_unsigned_to_nat(1927u);
v___x_5034_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5035_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5036_ = l_mkPanicMessageWithDecl(v___x_5035_, v___x_5034_, v___x_5033_, v___x_5032_, v___x_5031_);
return v___x_5036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5037_, lean_object* v_newType_5038_, lean_object* v_newVal_5039_, lean_object* v_newBody_5040_, uint8_t v_newNondep_5041_){
_start:
{
if (lean_obj_tag(v_e_5037_) == 8)
{
lean_object* v_declName_5042_; lean_object* v_type_5043_; lean_object* v_value_5044_; lean_object* v_body_5045_; uint8_t v_nondep_5046_; uint8_t v___y_5048_; size_t v___x_5056_; size_t v___x_5057_; uint8_t v___x_5058_; 
v_declName_5042_ = lean_ctor_get(v_e_5037_, 0);
v_type_5043_ = lean_ctor_get(v_e_5037_, 1);
v_value_5044_ = lean_ctor_get(v_e_5037_, 2);
v_body_5045_ = lean_ctor_get(v_e_5037_, 3);
v_nondep_5046_ = lean_ctor_get_uint8(v_e_5037_, sizeof(void*)*4 + 8);
v___x_5056_ = lean_ptr_addr(v_type_5043_);
v___x_5057_ = lean_ptr_addr(v_newType_5038_);
v___x_5058_ = lean_usize_dec_eq(v___x_5056_, v___x_5057_);
if (v___x_5058_ == 0)
{
v___y_5048_ = v___x_5058_;
goto v___jp_5047_;
}
else
{
size_t v___x_5059_; size_t v___x_5060_; uint8_t v___x_5061_; 
v___x_5059_ = lean_ptr_addr(v_value_5044_);
v___x_5060_ = lean_ptr_addr(v_newVal_5039_);
v___x_5061_ = lean_usize_dec_eq(v___x_5059_, v___x_5060_);
v___y_5048_ = v___x_5061_;
goto v___jp_5047_;
}
v___jp_5047_:
{
if (v___y_5048_ == 0)
{
lean_object* v___x_5049_; 
lean_inc(v_declName_5042_);
lean_dec_ref(v_e_5037_);
v___x_5049_ = l_Lean_Expr_letE___override(v_declName_5042_, v_newType_5038_, v_newVal_5039_, v_newBody_5040_, v_newNondep_5041_);
return v___x_5049_;
}
else
{
size_t v___x_5050_; size_t v___x_5051_; uint8_t v___x_5052_; 
v___x_5050_ = lean_ptr_addr(v_body_5045_);
v___x_5051_ = lean_ptr_addr(v_newBody_5040_);
v___x_5052_ = lean_usize_dec_eq(v___x_5050_, v___x_5051_);
if (v___x_5052_ == 0)
{
lean_object* v___x_5053_; 
lean_inc(v_declName_5042_);
lean_dec_ref(v_e_5037_);
v___x_5053_ = l_Lean_Expr_letE___override(v_declName_5042_, v_newType_5038_, v_newVal_5039_, v_newBody_5040_, v_newNondep_5041_);
return v___x_5053_;
}
else
{
if (v_nondep_5046_ == 0)
{
if (v_newNondep_5041_ == 0)
{
lean_dec_ref(v_newBody_5040_);
lean_dec_ref(v_newVal_5039_);
lean_dec_ref(v_newType_5038_);
return v_e_5037_;
}
else
{
lean_object* v___x_5054_; 
lean_inc(v_declName_5042_);
lean_dec_ref(v_e_5037_);
v___x_5054_ = l_Lean_Expr_letE___override(v_declName_5042_, v_newType_5038_, v_newVal_5039_, v_newBody_5040_, v_newNondep_5041_);
return v___x_5054_;
}
}
else
{
if (v_newNondep_5041_ == 0)
{
lean_object* v___x_5055_; 
lean_inc(v_declName_5042_);
lean_dec_ref(v_e_5037_);
v___x_5055_ = l_Lean_Expr_letE___override(v_declName_5042_, v_newType_5038_, v_newVal_5039_, v_newBody_5040_, v_newNondep_5041_);
return v___x_5055_;
}
else
{
lean_dec_ref(v_newBody_5040_);
lean_dec_ref(v_newVal_5039_);
lean_dec_ref(v_newType_5038_);
return v_e_5037_;
}
}
}
}
}
}
else
{
lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; 
lean_dec_ref(v_newBody_5040_);
lean_dec_ref(v_newVal_5039_);
lean_dec_ref(v_newType_5038_);
lean_dec_ref(v_e_5037_);
v___x_5062_ = l_Lean_instInhabitedExpr;
v___x_5063_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5064_ = l_panic___redArg(v___x_5062_, v___x_5063_);
return v___x_5064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5065_, lean_object* v_newType_5066_, lean_object* v_newVal_5067_, lean_object* v_newBody_5068_, lean_object* v_newNondep_5069_){
_start:
{
uint8_t v_newNondep_boxed_5070_; lean_object* v_res_5071_; 
v_newNondep_boxed_5070_ = lean_unbox(v_newNondep_5069_);
v_res_5071_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5065_, v_newType_5066_, v_newVal_5067_, v_newBody_5068_, v_newNondep_boxed_5070_);
return v_res_5071_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; 
v___x_5073_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5074_ = lean_unsigned_to_nat(27u);
v___x_5075_ = lean_unsigned_to_nat(1940u);
v___x_5076_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5077_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5078_ = l_mkPanicMessageWithDecl(v___x_5077_, v___x_5076_, v___x_5075_, v___x_5074_, v___x_5073_);
return v___x_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5079_, lean_object* v_newType_5080_, lean_object* v_newVal_5081_, lean_object* v_newBody_5082_){
_start:
{
if (lean_obj_tag(v_e_5079_) == 8)
{
lean_object* v_declName_5083_; lean_object* v_type_5084_; lean_object* v_value_5085_; lean_object* v_body_5086_; uint8_t v_nondep_5087_; uint8_t v___y_5089_; size_t v___x_5095_; size_t v___x_5096_; uint8_t v___x_5097_; 
v_declName_5083_ = lean_ctor_get(v_e_5079_, 0);
v_type_5084_ = lean_ctor_get(v_e_5079_, 1);
v_value_5085_ = lean_ctor_get(v_e_5079_, 2);
v_body_5086_ = lean_ctor_get(v_e_5079_, 3);
v_nondep_5087_ = lean_ctor_get_uint8(v_e_5079_, sizeof(void*)*4 + 8);
v___x_5095_ = lean_ptr_addr(v_type_5084_);
v___x_5096_ = lean_ptr_addr(v_newType_5080_);
v___x_5097_ = lean_usize_dec_eq(v___x_5095_, v___x_5096_);
if (v___x_5097_ == 0)
{
v___y_5089_ = v___x_5097_;
goto v___jp_5088_;
}
else
{
size_t v___x_5098_; size_t v___x_5099_; uint8_t v___x_5100_; 
v___x_5098_ = lean_ptr_addr(v_value_5085_);
v___x_5099_ = lean_ptr_addr(v_newVal_5081_);
v___x_5100_ = lean_usize_dec_eq(v___x_5098_, v___x_5099_);
v___y_5089_ = v___x_5100_;
goto v___jp_5088_;
}
v___jp_5088_:
{
if (v___y_5089_ == 0)
{
lean_object* v___x_5090_; 
lean_inc(v_declName_5083_);
lean_dec_ref(v_e_5079_);
v___x_5090_ = l_Lean_Expr_letE___override(v_declName_5083_, v_newType_5080_, v_newVal_5081_, v_newBody_5082_, v_nondep_5087_);
return v___x_5090_;
}
else
{
size_t v___x_5091_; size_t v___x_5092_; uint8_t v___x_5093_; 
v___x_5091_ = lean_ptr_addr(v_body_5086_);
v___x_5092_ = lean_ptr_addr(v_newBody_5082_);
v___x_5093_ = lean_usize_dec_eq(v___x_5091_, v___x_5092_);
if (v___x_5093_ == 0)
{
lean_object* v___x_5094_; 
lean_inc(v_declName_5083_);
lean_dec_ref(v_e_5079_);
v___x_5094_ = l_Lean_Expr_letE___override(v_declName_5083_, v_newType_5080_, v_newVal_5081_, v_newBody_5082_, v_nondep_5087_);
return v___x_5094_;
}
else
{
lean_dec_ref(v_newBody_5082_);
lean_dec_ref(v_newVal_5081_);
lean_dec_ref(v_newType_5080_);
return v_e_5079_;
}
}
}
}
else
{
lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
lean_dec_ref(v_newBody_5082_);
lean_dec_ref(v_newVal_5081_);
lean_dec_ref(v_newType_5080_);
lean_dec_ref(v_e_5079_);
v___x_5101_ = l_Lean_instInhabitedExpr;
v___x_5102_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5103_ = l_panic___redArg(v___x_5101_, v___x_5102_);
return v___x_5103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5104_, lean_object* v_x_5105_){
_start:
{
if (lean_obj_tag(v_x_5104_) == 5)
{
lean_object* v_fn_5106_; lean_object* v_arg_5107_; lean_object* v___x_5108_; uint8_t v___y_5110_; size_t v___x_5112_; size_t v___x_5113_; uint8_t v___x_5114_; 
v_fn_5106_ = lean_ctor_get(v_x_5104_, 0);
v_arg_5107_ = lean_ctor_get(v_x_5104_, 1);
lean_inc_ref(v_fn_5106_);
v___x_5108_ = l_Lean_Expr_updateFn(v_fn_5106_, v_x_5105_);
v___x_5112_ = lean_ptr_addr(v_fn_5106_);
v___x_5113_ = lean_ptr_addr(v___x_5108_);
v___x_5114_ = lean_usize_dec_eq(v___x_5112_, v___x_5113_);
if (v___x_5114_ == 0)
{
v___y_5110_ = v___x_5114_;
goto v___jp_5109_;
}
else
{
size_t v___x_5115_; uint8_t v___x_5116_; 
v___x_5115_ = lean_ptr_addr(v_arg_5107_);
v___x_5116_ = lean_usize_dec_eq(v___x_5115_, v___x_5115_);
v___y_5110_ = v___x_5116_;
goto v___jp_5109_;
}
v___jp_5109_:
{
if (v___y_5110_ == 0)
{
lean_object* v___x_5111_; 
lean_inc_ref(v_arg_5107_);
lean_dec_ref(v_x_5104_);
v___x_5111_ = l_Lean_Expr_app___override(v___x_5108_, v_arg_5107_);
return v___x_5111_;
}
else
{
lean_dec_ref(v___x_5108_);
return v_x_5104_;
}
}
}
else
{
lean_dec_ref(v_x_5104_);
lean_inc_ref(v_x_5105_);
return v_x_5105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5117_, lean_object* v_x_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l_Lean_Expr_updateFn(v_x_5117_, v_x_5118_);
lean_dec_ref(v_x_5118_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5120_){
_start:
{
if (lean_obj_tag(v_e_5120_) == 6)
{
lean_object* v_binderName_5121_; lean_object* v_binderType_5122_; lean_object* v_body_5123_; uint8_t v_binderInfo_5124_; lean_object* v_b_x27_5125_; uint8_t v___y_5127_; uint8_t v___y_5132_; 
v_binderName_5121_ = lean_ctor_get(v_e_5120_, 0);
v_binderType_5122_ = lean_ctor_get(v_e_5120_, 1);
v_body_5123_ = lean_ctor_get(v_e_5120_, 2);
v_binderInfo_5124_ = lean_ctor_get_uint8(v_e_5120_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5123_);
v_b_x27_5125_ = l_Lean_Expr_eta(v_body_5123_);
if (lean_obj_tag(v_b_x27_5125_) == 5)
{
lean_object* v_arg_5142_; 
v_arg_5142_ = lean_ctor_get(v_b_x27_5125_, 1);
lean_inc_ref(v_arg_5142_);
if (lean_obj_tag(v_arg_5142_) == 0)
{
lean_object* v_fn_5143_; lean_object* v_deBruijnIndex_5144_; lean_object* v___x_5145_; uint8_t v___x_5146_; 
v_fn_5143_ = lean_ctor_get(v_b_x27_5125_, 0);
lean_inc_ref(v_fn_5143_);
v_deBruijnIndex_5144_ = lean_ctor_get(v_arg_5142_, 0);
lean_inc(v_deBruijnIndex_5144_);
lean_dec_ref(v_arg_5142_);
v___x_5145_ = lean_unsigned_to_nat(0u);
v___x_5146_ = lean_nat_dec_eq(v_deBruijnIndex_5144_, v___x_5145_);
lean_dec(v_deBruijnIndex_5144_);
if (v___x_5146_ == 0)
{
lean_dec_ref(v_fn_5143_);
goto v___jp_5136_;
}
else
{
uint8_t v___x_5147_; 
v___x_5147_ = lean_expr_has_loose_bvar(v_fn_5143_, v___x_5145_);
if (v___x_5147_ == 0)
{
lean_object* v___x_5148_; lean_object* v___x_5149_; 
lean_dec_ref(v_b_x27_5125_);
lean_dec_ref(v_e_5120_);
v___x_5148_ = lean_unsigned_to_nat(1u);
v___x_5149_ = lean_expr_lower_loose_bvars(v_fn_5143_, v___x_5148_, v___x_5148_);
lean_dec_ref(v_fn_5143_);
return v___x_5149_;
}
else
{
size_t v___x_5150_; uint8_t v___x_5151_; 
lean_dec_ref(v_fn_5143_);
v___x_5150_ = lean_ptr_addr(v_binderType_5122_);
v___x_5151_ = lean_usize_dec_eq(v___x_5150_, v___x_5150_);
if (v___x_5151_ == 0)
{
v___y_5127_ = v___x_5151_;
goto v___jp_5126_;
}
else
{
size_t v___x_5152_; size_t v___x_5153_; uint8_t v___x_5154_; 
v___x_5152_ = lean_ptr_addr(v_body_5123_);
v___x_5153_ = lean_ptr_addr(v_b_x27_5125_);
v___x_5154_ = lean_usize_dec_eq(v___x_5152_, v___x_5153_);
v___y_5127_ = v___x_5154_;
goto v___jp_5126_;
}
}
}
}
else
{
lean_dec_ref(v_arg_5142_);
goto v___jp_5136_;
}
}
else
{
goto v___jp_5136_;
}
v___jp_5126_:
{
if (v___y_5127_ == 0)
{
lean_object* v___x_5128_; 
lean_inc_ref(v_binderType_5122_);
lean_inc(v_binderName_5121_);
lean_dec_ref(v_e_5120_);
v___x_5128_ = l_Lean_Expr_lam___override(v_binderName_5121_, v_binderType_5122_, v_b_x27_5125_, v_binderInfo_5124_);
return v___x_5128_;
}
else
{
uint8_t v___x_5129_; 
v___x_5129_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5124_, v_binderInfo_5124_);
if (v___x_5129_ == 0)
{
lean_object* v___x_5130_; 
lean_inc_ref(v_binderType_5122_);
lean_inc(v_binderName_5121_);
lean_dec_ref(v_e_5120_);
v___x_5130_ = l_Lean_Expr_lam___override(v_binderName_5121_, v_binderType_5122_, v_b_x27_5125_, v_binderInfo_5124_);
return v___x_5130_;
}
else
{
lean_dec_ref(v_b_x27_5125_);
return v_e_5120_;
}
}
}
v___jp_5131_:
{
if (v___y_5132_ == 0)
{
lean_object* v___x_5133_; 
lean_inc_ref(v_binderType_5122_);
lean_inc(v_binderName_5121_);
lean_dec_ref(v_e_5120_);
v___x_5133_ = l_Lean_Expr_lam___override(v_binderName_5121_, v_binderType_5122_, v_b_x27_5125_, v_binderInfo_5124_);
return v___x_5133_;
}
else
{
uint8_t v___x_5134_; 
v___x_5134_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5124_, v_binderInfo_5124_);
if (v___x_5134_ == 0)
{
lean_object* v___x_5135_; 
lean_inc_ref(v_binderType_5122_);
lean_inc(v_binderName_5121_);
lean_dec_ref(v_e_5120_);
v___x_5135_ = l_Lean_Expr_lam___override(v_binderName_5121_, v_binderType_5122_, v_b_x27_5125_, v_binderInfo_5124_);
return v___x_5135_;
}
else
{
lean_dec_ref(v_b_x27_5125_);
return v_e_5120_;
}
}
}
v___jp_5136_:
{
size_t v___x_5137_; uint8_t v___x_5138_; 
v___x_5137_ = lean_ptr_addr(v_binderType_5122_);
v___x_5138_ = lean_usize_dec_eq(v___x_5137_, v___x_5137_);
if (v___x_5138_ == 0)
{
v___y_5132_ = v___x_5138_;
goto v___jp_5131_;
}
else
{
size_t v___x_5139_; size_t v___x_5140_; uint8_t v___x_5141_; 
v___x_5139_ = lean_ptr_addr(v_body_5123_);
v___x_5140_ = lean_ptr_addr(v_b_x27_5125_);
v___x_5141_ = lean_usize_dec_eq(v___x_5139_, v___x_5140_);
v___y_5132_ = v___x_5141_;
goto v___jp_5131_;
}
}
}
else
{
return v_e_5120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5155_, lean_object* v_optionName_5156_, lean_object* v_inst_5157_, lean_object* v_val_5158_){
_start:
{
lean_object* v_toDataValue_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; 
v_toDataValue_5159_ = lean_ctor_get(v_inst_5157_, 0);
lean_inc_ref(v_toDataValue_5159_);
lean_dec_ref(v_inst_5157_);
v___x_5160_ = lean_box(0);
v___x_5161_ = lean_apply_1(v_toDataValue_5159_, v_val_5158_);
v___x_5162_ = l_Lean_KVMap_insert(v___x_5160_, v_optionName_5156_, v___x_5161_);
v___x_5163_ = l_Lean_Expr_mdata___override(v___x_5162_, v_e_5155_);
return v___x_5163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5164_, lean_object* v_e_5165_, lean_object* v_optionName_5166_, lean_object* v_inst_5167_, lean_object* v_val_5168_){
_start:
{
lean_object* v___x_5169_; 
v___x_5169_ = l_Lean_Expr_setOption___redArg(v_e_5165_, v_optionName_5166_, v_inst_5167_, v_val_5168_);
return v___x_5169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5170_, lean_object* v_optionName_5171_, uint8_t v_val_5172_){
_start:
{
lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; 
v___x_5173_ = lean_box(0);
v___x_5174_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5174_, 0, v_val_5172_);
v___x_5175_ = l_Lean_KVMap_insert(v___x_5173_, v_optionName_5171_, v___x_5174_);
v___x_5176_ = l_Lean_Expr_mdata___override(v___x_5175_, v_e_5170_);
return v___x_5176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5177_, lean_object* v_optionName_5178_, lean_object* v_val_5179_){
_start:
{
uint8_t v_val_boxed_5180_; lean_object* v_res_5181_; 
v_val_boxed_5180_ = lean_unbox(v_val_5179_);
v_res_5181_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5177_, v_optionName_5178_, v_val_boxed_5180_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5187_, uint8_t v_flag_5188_){
_start:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; 
v___x_5189_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5190_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5187_, v___x_5189_, v_flag_5188_);
return v___x_5190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5191_, lean_object* v_flag_5192_){
_start:
{
uint8_t v_flag_boxed_5193_; lean_object* v_res_5194_; 
v_flag_boxed_5193_ = lean_unbox(v_flag_5192_);
v_res_5194_ = l_Lean_Expr_setPPExplicit(v_e_5191_, v_flag_boxed_5193_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5199_, uint8_t v_flag_5200_){
_start:
{
lean_object* v___x_5201_; lean_object* v___x_5202_; 
v___x_5201_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5202_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5199_, v___x_5201_, v_flag_5200_);
return v___x_5202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5203_, lean_object* v_flag_5204_){
_start:
{
uint8_t v_flag_boxed_5205_; lean_object* v_res_5206_; 
v_flag_boxed_5205_ = lean_unbox(v_flag_5204_);
v_res_5206_ = l_Lean_Expr_setPPUniverses(v_e_5203_, v_flag_boxed_5205_);
return v_res_5206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5211_, uint8_t v_flag_5212_){
_start:
{
lean_object* v___x_5213_; lean_object* v___x_5214_; 
v___x_5213_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5214_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5211_, v___x_5213_, v_flag_5212_);
return v___x_5214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5215_, lean_object* v_flag_5216_){
_start:
{
uint8_t v_flag_boxed_5217_; lean_object* v_res_5218_; 
v_flag_boxed_5217_ = lean_unbox(v_flag_5216_);
v_res_5218_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5215_, v_flag_boxed_5217_);
return v_res_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5223_, uint8_t v_flag_5224_){
_start:
{
lean_object* v___x_5225_; lean_object* v___x_5226_; 
v___x_5225_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5226_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5223_, v___x_5225_, v_flag_5224_);
return v___x_5226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5227_, lean_object* v_flag_5228_){
_start:
{
uint8_t v_flag_boxed_5229_; lean_object* v_res_5230_; 
v_flag_boxed_5229_ = lean_unbox(v_flag_5228_);
v_res_5230_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5227_, v_flag_boxed_5229_);
return v_res_5230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5235_, uint8_t v_flag_5236_){
_start:
{
lean_object* v___x_5237_; lean_object* v___x_5238_; 
v___x_5237_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5238_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5235_, v___x_5237_, v_flag_5236_);
return v___x_5238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5239_, lean_object* v_flag_5240_){
_start:
{
uint8_t v_flag_boxed_5241_; lean_object* v_res_5242_; 
v_flag_boxed_5241_ = lean_unbox(v_flag_5240_);
v_res_5242_ = l_Lean_Expr_setPPNumericTypes(v_e_5239_, v_flag_boxed_5241_);
return v_res_5242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5243_, size_t v_i_5244_, lean_object* v_bs_5245_){
_start:
{
uint8_t v___x_5246_; 
v___x_5246_ = lean_usize_dec_lt(v_i_5244_, v_sz_5243_);
if (v___x_5246_ == 0)
{
return v_bs_5245_;
}
else
{
uint8_t v___x_5247_; lean_object* v_v_5248_; lean_object* v___x_5249_; lean_object* v_bs_x27_5250_; lean_object* v___x_5251_; size_t v___x_5252_; size_t v___x_5253_; lean_object* v___x_5254_; 
v___x_5247_ = 0;
v_v_5248_ = lean_array_uget(v_bs_5245_, v_i_5244_);
v___x_5249_ = lean_unsigned_to_nat(0u);
v_bs_x27_5250_ = lean_array_uset(v_bs_5245_, v_i_5244_, v___x_5249_);
v___x_5251_ = l_Lean_Expr_setPPExplicit(v_v_5248_, v___x_5247_);
v___x_5252_ = ((size_t)1ULL);
v___x_5253_ = lean_usize_add(v_i_5244_, v___x_5252_);
v___x_5254_ = lean_array_uset(v_bs_x27_5250_, v_i_5244_, v___x_5251_);
v_i_5244_ = v___x_5253_;
v_bs_5245_ = v___x_5254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5256_, lean_object* v_i_5257_, lean_object* v_bs_5258_){
_start:
{
size_t v_sz_boxed_5259_; size_t v_i_boxed_5260_; lean_object* v_res_5261_; 
v_sz_boxed_5259_ = lean_unbox_usize(v_sz_5256_);
lean_dec(v_sz_5256_);
v_i_boxed_5260_ = lean_unbox_usize(v_i_5257_);
lean_dec(v_i_5257_);
v_res_5261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5259_, v_i_boxed_5260_, v_bs_5258_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5262_){
_start:
{
if (lean_obj_tag(v_e_5262_) == 5)
{
lean_object* v___x_5263_; uint8_t v___x_5264_; lean_object* v_f_5265_; lean_object* v_dummy_5266_; lean_object* v_nargs_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; size_t v_sz_5272_; size_t v___x_5273_; lean_object* v_args_5274_; lean_object* v___x_5275_; uint8_t v___x_5276_; lean_object* v___x_5277_; 
v___x_5263_ = l_Lean_Expr_getAppFn(v_e_5262_);
v___x_5264_ = 0;
v_f_5265_ = l_Lean_Expr_setPPExplicit(v___x_5263_, v___x_5264_);
v_dummy_5266_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5267_ = l_Lean_Expr_getAppNumArgs(v_e_5262_);
lean_inc(v_nargs_5267_);
v___x_5268_ = lean_mk_array(v_nargs_5267_, v_dummy_5266_);
v___x_5269_ = lean_unsigned_to_nat(1u);
v___x_5270_ = lean_nat_sub(v_nargs_5267_, v___x_5269_);
lean_dec(v_nargs_5267_);
v___x_5271_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5262_, v___x_5268_, v___x_5270_);
v_sz_5272_ = lean_array_size(v___x_5271_);
v___x_5273_ = ((size_t)0ULL);
v_args_5274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5272_, v___x_5273_, v___x_5271_);
v___x_5275_ = l_Lean_mkAppN(v_f_5265_, v_args_5274_);
lean_dec_ref(v_args_5274_);
v___x_5276_ = 1;
v___x_5277_ = l_Lean_Expr_setPPExplicit(v___x_5275_, v___x_5276_);
return v___x_5277_;
}
else
{
return v_e_5262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5278_, size_t v_i_5279_, lean_object* v_bs_5280_){
_start:
{
uint8_t v___x_5281_; 
v___x_5281_ = lean_usize_dec_lt(v_i_5279_, v_sz_5278_);
if (v___x_5281_ == 0)
{
return v_bs_5280_;
}
else
{
lean_object* v_v_5282_; lean_object* v___x_5283_; lean_object* v_bs_x27_5284_; lean_object* v___y_5286_; uint8_t v___x_5291_; 
v_v_5282_ = lean_array_uget(v_bs_5280_, v_i_5279_);
v___x_5283_ = lean_unsigned_to_nat(0u);
v_bs_x27_5284_ = lean_array_uset(v_bs_5280_, v_i_5279_, v___x_5283_);
v___x_5291_ = l_Lean_Expr_hasMVar(v_v_5282_);
if (v___x_5291_ == 0)
{
lean_object* v___x_5292_; 
v___x_5292_ = l_Lean_Expr_setPPExplicit(v_v_5282_, v___x_5291_);
v___y_5286_ = v___x_5292_;
goto v___jp_5285_;
}
else
{
v___y_5286_ = v_v_5282_;
goto v___jp_5285_;
}
v___jp_5285_:
{
size_t v___x_5287_; size_t v___x_5288_; lean_object* v___x_5289_; 
v___x_5287_ = ((size_t)1ULL);
v___x_5288_ = lean_usize_add(v_i_5279_, v___x_5287_);
v___x_5289_ = lean_array_uset(v_bs_x27_5284_, v_i_5279_, v___y_5286_);
v_i_5279_ = v___x_5288_;
v_bs_5280_ = v___x_5289_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5293_, lean_object* v_i_5294_, lean_object* v_bs_5295_){
_start:
{
size_t v_sz_boxed_5296_; size_t v_i_boxed_5297_; lean_object* v_res_5298_; 
v_sz_boxed_5296_ = lean_unbox_usize(v_sz_5293_);
lean_dec(v_sz_5293_);
v_i_boxed_5297_ = lean_unbox_usize(v_i_5294_);
lean_dec(v_i_5294_);
v_res_5298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5296_, v_i_boxed_5297_, v_bs_5295_);
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5299_){
_start:
{
if (lean_obj_tag(v_e_5299_) == 5)
{
lean_object* v___x_5300_; uint8_t v___x_5301_; lean_object* v_f_5302_; lean_object* v_dummy_5303_; lean_object* v_nargs_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; size_t v_sz_5309_; size_t v___x_5310_; lean_object* v_args_5311_; lean_object* v___x_5312_; uint8_t v___x_5313_; lean_object* v___x_5314_; 
v___x_5300_ = l_Lean_Expr_getAppFn(v_e_5299_);
v___x_5301_ = 0;
v_f_5302_ = l_Lean_Expr_setPPExplicit(v___x_5300_, v___x_5301_);
v_dummy_5303_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5304_ = l_Lean_Expr_getAppNumArgs(v_e_5299_);
lean_inc(v_nargs_5304_);
v___x_5305_ = lean_mk_array(v_nargs_5304_, v_dummy_5303_);
v___x_5306_ = lean_unsigned_to_nat(1u);
v___x_5307_ = lean_nat_sub(v_nargs_5304_, v___x_5306_);
lean_dec(v_nargs_5304_);
v___x_5308_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5299_, v___x_5305_, v___x_5307_);
v_sz_5309_ = lean_array_size(v___x_5308_);
v___x_5310_ = ((size_t)0ULL);
v_args_5311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5309_, v___x_5310_, v___x_5308_);
v___x_5312_ = l_Lean_mkAppN(v_f_5302_, v_args_5311_);
lean_dec_ref(v_args_5311_);
v___x_5313_ = 1;
v___x_5314_ = l_Lean_Expr_setPPExplicit(v___x_5312_, v___x_5313_);
return v___x_5314_;
}
else
{
return v_e_5299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5315_, lean_object* v_body_5316_, lean_object* v_x_5317_){
_start:
{
lean_object* v___x_5318_; 
v___x_5318_ = lean_apply_1(v_f_5315_, v_body_5316_);
return v___x_5318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5319_, lean_object* v_binderType_5320_, lean_object* v_x_5321_){
_start:
{
lean_object* v___x_5322_; 
v___x_5322_ = lean_apply_1(v_f_5319_, v_binderType_5320_);
return v___x_5322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5323_, lean_object* v_value_5324_, lean_object* v_x_5325_){
_start:
{
lean_object* v___x_5326_; 
v___x_5326_ = lean_apply_1(v_f_5323_, v_value_5324_);
return v___x_5326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5327_, lean_object* v_type_5328_, lean_object* v_x_5329_){
_start:
{
lean_object* v___x_5330_; 
v___x_5330_ = lean_apply_1(v_f_5327_, v_type_5328_);
return v___x_5330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5331_, lean_object* v_arg_5332_, lean_object* v_x_5333_){
_start:
{
lean_object* v___x_5334_; 
v___x_5334_ = lean_apply_1(v_f_5331_, v_arg_5332_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5335_, lean_object* v_fn_5336_, lean_object* v_x_5337_){
_start:
{
lean_object* v___x_5338_; 
v___x_5338_ = lean_apply_1(v_f_5335_, v_fn_5336_);
return v___x_5338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5339_, lean_object* v_f_5340_, lean_object* v_x_5341_){
_start:
{
switch(lean_obj_tag(v_x_5341_))
{
case 7:
{
lean_object* v_toPure_5342_; lean_object* v_toSeq_5343_; lean_object* v_binderType_5344_; lean_object* v_body_5345_; lean_object* v___f_5346_; lean_object* v___f_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; 
v_toPure_5342_ = lean_ctor_get(v_inst_5339_, 1);
lean_inc(v_toPure_5342_);
v_toSeq_5343_ = lean_ctor_get(v_inst_5339_, 2);
lean_inc(v_toSeq_5343_);
lean_dec_ref(v_inst_5339_);
v_binderType_5344_ = lean_ctor_get(v_x_5341_, 1);
v_body_5345_ = lean_ctor_get(v_x_5341_, 2);
lean_inc_ref(v_body_5345_);
lean_inc(v_f_5340_);
v___f_5346_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5346_, 0, v_f_5340_);
lean_closure_set(v___f_5346_, 1, v_body_5345_);
lean_inc_ref(v_binderType_5344_);
v___f_5347_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5347_, 0, v_f_5340_);
lean_closure_set(v___f_5347_, 1, v_binderType_5344_);
v___x_5348_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5348_, 0, v_x_5341_);
v___x_5349_ = lean_apply_2(v_toPure_5342_, lean_box(0), v___x_5348_);
lean_inc(v_toSeq_5343_);
v___x_5350_ = lean_apply_4(v_toSeq_5343_, lean_box(0), lean_box(0), v___x_5349_, v___f_5347_);
v___x_5351_ = lean_apply_4(v_toSeq_5343_, lean_box(0), lean_box(0), v___x_5350_, v___f_5346_);
return v___x_5351_;
}
case 6:
{
lean_object* v_toPure_5352_; lean_object* v_toSeq_5353_; lean_object* v_binderType_5354_; lean_object* v_body_5355_; lean_object* v___f_5356_; lean_object* v___f_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; 
v_toPure_5352_ = lean_ctor_get(v_inst_5339_, 1);
lean_inc(v_toPure_5352_);
v_toSeq_5353_ = lean_ctor_get(v_inst_5339_, 2);
lean_inc(v_toSeq_5353_);
lean_dec_ref(v_inst_5339_);
v_binderType_5354_ = lean_ctor_get(v_x_5341_, 1);
v_body_5355_ = lean_ctor_get(v_x_5341_, 2);
lean_inc_ref(v_body_5355_);
lean_inc(v_f_5340_);
v___f_5356_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5356_, 0, v_f_5340_);
lean_closure_set(v___f_5356_, 1, v_body_5355_);
lean_inc_ref(v_binderType_5354_);
v___f_5357_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5357_, 0, v_f_5340_);
lean_closure_set(v___f_5357_, 1, v_binderType_5354_);
v___x_5358_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5358_, 0, v_x_5341_);
v___x_5359_ = lean_apply_2(v_toPure_5352_, lean_box(0), v___x_5358_);
lean_inc(v_toSeq_5353_);
v___x_5360_ = lean_apply_4(v_toSeq_5353_, lean_box(0), lean_box(0), v___x_5359_, v___f_5357_);
v___x_5361_ = lean_apply_4(v_toSeq_5353_, lean_box(0), lean_box(0), v___x_5360_, v___f_5356_);
return v___x_5361_;
}
case 10:
{
lean_object* v_toFunctor_5362_; lean_object* v_expr_5363_; lean_object* v_map_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; 
v_toFunctor_5362_ = lean_ctor_get(v_inst_5339_, 0);
lean_inc_ref(v_toFunctor_5362_);
lean_dec_ref(v_inst_5339_);
v_expr_5363_ = lean_ctor_get(v_x_5341_, 1);
lean_inc_ref(v_expr_5363_);
v_map_5364_ = lean_ctor_get(v_toFunctor_5362_, 0);
lean_inc(v_map_5364_);
lean_dec_ref(v_toFunctor_5362_);
v___x_5365_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5365_, 0, v_x_5341_);
v___x_5366_ = lean_apply_1(v_f_5340_, v_expr_5363_);
v___x_5367_ = lean_apply_4(v_map_5364_, lean_box(0), lean_box(0), v___x_5365_, v___x_5366_);
return v___x_5367_;
}
case 8:
{
lean_object* v_toPure_5368_; lean_object* v_toSeq_5369_; lean_object* v_type_5370_; lean_object* v_value_5371_; lean_object* v_body_5372_; lean_object* v___f_5373_; lean_object* v___f_5374_; lean_object* v___f_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; 
v_toPure_5368_ = lean_ctor_get(v_inst_5339_, 1);
lean_inc(v_toPure_5368_);
v_toSeq_5369_ = lean_ctor_get(v_inst_5339_, 2);
lean_inc(v_toSeq_5369_);
lean_dec_ref(v_inst_5339_);
v_type_5370_ = lean_ctor_get(v_x_5341_, 1);
v_value_5371_ = lean_ctor_get(v_x_5341_, 2);
v_body_5372_ = lean_ctor_get(v_x_5341_, 3);
lean_inc_ref(v_body_5372_);
lean_inc(v_f_5340_);
v___f_5373_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5373_, 0, v_f_5340_);
lean_closure_set(v___f_5373_, 1, v_body_5372_);
lean_inc_ref(v_value_5371_);
lean_inc(v_f_5340_);
v___f_5374_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5374_, 0, v_f_5340_);
lean_closure_set(v___f_5374_, 1, v_value_5371_);
lean_inc_ref(v_type_5370_);
v___f_5375_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5375_, 0, v_f_5340_);
lean_closure_set(v___f_5375_, 1, v_type_5370_);
v___x_5376_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5376_, 0, v_x_5341_);
v___x_5377_ = lean_apply_2(v_toPure_5368_, lean_box(0), v___x_5376_);
lean_inc(v_toSeq_5369_);
v___x_5378_ = lean_apply_4(v_toSeq_5369_, lean_box(0), lean_box(0), v___x_5377_, v___f_5375_);
lean_inc(v_toSeq_5369_);
v___x_5379_ = lean_apply_4(v_toSeq_5369_, lean_box(0), lean_box(0), v___x_5378_, v___f_5374_);
v___x_5380_ = lean_apply_4(v_toSeq_5369_, lean_box(0), lean_box(0), v___x_5379_, v___f_5373_);
return v___x_5380_;
}
case 5:
{
lean_object* v_toPure_5381_; lean_object* v_toSeq_5382_; lean_object* v_fn_5383_; lean_object* v_arg_5384_; lean_object* v___f_5385_; lean_object* v___f_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; 
v_toPure_5381_ = lean_ctor_get(v_inst_5339_, 1);
lean_inc(v_toPure_5381_);
v_toSeq_5382_ = lean_ctor_get(v_inst_5339_, 2);
lean_inc(v_toSeq_5382_);
lean_dec_ref(v_inst_5339_);
v_fn_5383_ = lean_ctor_get(v_x_5341_, 0);
v_arg_5384_ = lean_ctor_get(v_x_5341_, 1);
lean_inc_ref(v_arg_5384_);
lean_inc(v_f_5340_);
v___f_5385_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5385_, 0, v_f_5340_);
lean_closure_set(v___f_5385_, 1, v_arg_5384_);
lean_inc_ref(v_fn_5383_);
v___f_5386_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5386_, 0, v_f_5340_);
lean_closure_set(v___f_5386_, 1, v_fn_5383_);
v___x_5387_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5387_, 0, v_x_5341_);
v___x_5388_ = lean_apply_2(v_toPure_5381_, lean_box(0), v___x_5387_);
lean_inc(v_toSeq_5382_);
v___x_5389_ = lean_apply_4(v_toSeq_5382_, lean_box(0), lean_box(0), v___x_5388_, v___f_5386_);
v___x_5390_ = lean_apply_4(v_toSeq_5382_, lean_box(0), lean_box(0), v___x_5389_, v___f_5385_);
return v___x_5390_;
}
case 11:
{
lean_object* v_toFunctor_5391_; lean_object* v_struct_5392_; lean_object* v_map_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; 
v_toFunctor_5391_ = lean_ctor_get(v_inst_5339_, 0);
lean_inc_ref(v_toFunctor_5391_);
lean_dec_ref(v_inst_5339_);
v_struct_5392_ = lean_ctor_get(v_x_5341_, 2);
lean_inc_ref(v_struct_5392_);
v_map_5393_ = lean_ctor_get(v_toFunctor_5391_, 0);
lean_inc(v_map_5393_);
lean_dec_ref(v_toFunctor_5391_);
v___x_5394_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5394_, 0, v_x_5341_);
v___x_5395_ = lean_apply_1(v_f_5340_, v_struct_5392_);
v___x_5396_ = lean_apply_4(v_map_5393_, lean_box(0), lean_box(0), v___x_5394_, v___x_5395_);
return v___x_5396_;
}
default: 
{
lean_object* v_toPure_5397_; lean_object* v___x_5398_; 
lean_dec(v_f_5340_);
v_toPure_5397_ = lean_ctor_get(v_inst_5339_, 1);
lean_inc(v_toPure_5397_);
lean_dec_ref(v_inst_5339_);
v___x_5398_ = lean_apply_2(v_toPure_5397_, lean_box(0), v_x_5341_);
return v___x_5398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5399_, lean_object* v_inst_5400_, lean_object* v_f_5401_, lean_object* v_x_5402_){
_start:
{
lean_object* v___x_5403_; 
v___x_5403_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5400_, v_f_5401_, v_x_5402_);
return v___x_5403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5404_){
_start:
{
lean_object* v_snd_5405_; 
v_snd_5405_ = lean_ctor_get(v_self_5404_, 1);
lean_inc(v_snd_5405_);
return v_snd_5405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5406_){
_start:
{
lean_object* v_res_5407_; 
v_res_5407_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5406_);
lean_dec_ref(v_self_5406_);
return v_res_5407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5408_, lean_object* v_snd_5409_){
_start:
{
lean_object* v___x_5410_; 
v___x_5410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5410_, 0, v_e_x27_5408_);
lean_ctor_set(v___x_5410_, 1, v_snd_5409_);
return v___x_5410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5411_, lean_object* v_map_5412_, lean_object* v_e_x27_5413_, lean_object* v_a_5414_){
_start:
{
lean_object* v___f_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; 
lean_inc_ref(v_e_x27_5413_);
v___f_5415_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5415_, 0, v_e_x27_5413_);
v___x_5416_ = lean_apply_2(v_f_5411_, v_a_5414_, v_e_x27_5413_);
v___x_5417_ = lean_apply_4(v_map_5412_, lean_box(0), lean_box(0), v___f_5415_, v___x_5416_);
return v___x_5417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5419_, lean_object* v_f_5420_, lean_object* v_init_5421_, lean_object* v_e_5422_){
_start:
{
lean_object* v_toApplicative_5423_; lean_object* v_toFunctor_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5451_; 
v_toApplicative_5423_ = lean_ctor_get(v_inst_5419_, 0);
lean_inc_ref(v_toApplicative_5423_);
v_toFunctor_5424_ = lean_ctor_get(v_toApplicative_5423_, 0);
v_isSharedCheck_5451_ = !lean_is_exclusive(v_toApplicative_5423_);
if (v_isSharedCheck_5451_ == 0)
{
lean_object* v_unused_5452_; lean_object* v_unused_5453_; lean_object* v_unused_5454_; lean_object* v_unused_5455_; 
v_unused_5452_ = lean_ctor_get(v_toApplicative_5423_, 4);
lean_dec(v_unused_5452_);
v_unused_5453_ = lean_ctor_get(v_toApplicative_5423_, 3);
lean_dec(v_unused_5453_);
v_unused_5454_ = lean_ctor_get(v_toApplicative_5423_, 2);
lean_dec(v_unused_5454_);
v_unused_5455_ = lean_ctor_get(v_toApplicative_5423_, 1);
lean_dec(v_unused_5455_);
v___x_5426_ = v_toApplicative_5423_;
v_isShared_5427_ = v_isSharedCheck_5451_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_toFunctor_5424_);
lean_dec(v_toApplicative_5423_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5451_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v_map_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5449_; 
v_map_5428_ = lean_ctor_get(v_toFunctor_5424_, 0);
v_isSharedCheck_5449_ = !lean_is_exclusive(v_toFunctor_5424_);
if (v_isSharedCheck_5449_ == 0)
{
lean_object* v_unused_5450_; 
v_unused_5450_ = lean_ctor_get(v_toFunctor_5424_, 1);
lean_dec(v_unused_5450_);
v___x_5430_ = v_toFunctor_5424_;
v_isShared_5431_ = v_isSharedCheck_5449_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_map_5428_);
lean_dec(v_toFunctor_5424_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5449_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v___f_5432_; lean_object* v___f_5433_; lean_object* v___f_5434_; lean_object* v___f_5435_; lean_object* v___f_5436_; lean_object* v___f_5437_; lean_object* v___x_5438_; lean_object* v___x_5440_; 
v___f_5432_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5428_);
v___f_5433_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5433_, 0, v_f_5420_);
lean_closure_set(v___f_5433_, 1, v_map_5428_);
lean_inc_ref(v_inst_5419_);
v___f_5434_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5434_, 0, v_inst_5419_);
lean_inc_ref(v_inst_5419_);
v___f_5435_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5435_, 0, v_inst_5419_);
lean_inc_ref(v_inst_5419_);
v___f_5436_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5436_, 0, v_inst_5419_);
lean_inc_ref(v_inst_5419_);
v___f_5437_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5437_, 0, v_inst_5419_);
lean_inc_ref(v_inst_5419_);
v___x_5438_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5438_, 0, lean_box(0));
lean_closure_set(v___x_5438_, 1, lean_box(0));
lean_closure_set(v___x_5438_, 2, v_inst_5419_);
if (v_isShared_5431_ == 0)
{
lean_ctor_set(v___x_5430_, 1, v___f_5434_);
lean_ctor_set(v___x_5430_, 0, v___x_5438_);
v___x_5440_ = v___x_5430_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v___x_5438_);
lean_ctor_set(v_reuseFailAlloc_5448_, 1, v___f_5434_);
v___x_5440_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
lean_object* v___x_5441_; lean_object* v___x_5443_; 
v___x_5441_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5441_, 0, lean_box(0));
lean_closure_set(v___x_5441_, 1, lean_box(0));
lean_closure_set(v___x_5441_, 2, v_inst_5419_);
if (v_isShared_5427_ == 0)
{
lean_ctor_set(v___x_5426_, 4, v___f_5437_);
lean_ctor_set(v___x_5426_, 3, v___f_5436_);
lean_ctor_set(v___x_5426_, 2, v___f_5435_);
lean_ctor_set(v___x_5426_, 1, v___x_5441_);
lean_ctor_set(v___x_5426_, 0, v___x_5440_);
v___x_5443_ = v___x_5426_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5447_; 
v_reuseFailAlloc_5447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5447_, 0, v___x_5440_);
lean_ctor_set(v_reuseFailAlloc_5447_, 1, v___x_5441_);
lean_ctor_set(v_reuseFailAlloc_5447_, 2, v___f_5435_);
lean_ctor_set(v_reuseFailAlloc_5447_, 3, v___f_5436_);
lean_ctor_set(v_reuseFailAlloc_5447_, 4, v___f_5437_);
v___x_5443_ = v_reuseFailAlloc_5447_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
lean_object* v___x_18__overap_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; 
v___x_18__overap_5444_ = l_Lean_Expr_traverseChildren___redArg(v___x_5443_, v___f_5433_, v_e_5422_);
v___x_5445_ = lean_apply_1(v___x_18__overap_5444_, v_init_5421_);
v___x_5446_ = lean_apply_4(v_map_5428_, lean_box(0), lean_box(0), v___f_5432_, v___x_5445_);
return v___x_5446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5456_, lean_object* v_m_5457_, lean_object* v_inst_5458_, lean_object* v_f_5459_, lean_object* v_init_5460_, lean_object* v_e_5461_){
_start:
{
lean_object* v___x_5462_; 
v___x_5462_ = l_Lean_Expr_foldlM___redArg(v_inst_5458_, v_f_5459_, v_init_5460_, v_e_5461_);
return v___x_5462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5463_){
_start:
{
lean_object* v_d_5465_; lean_object* v_b_5466_; 
switch(lean_obj_tag(v_x_5463_))
{
case 5:
{
lean_object* v_fn_5472_; lean_object* v_arg_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; 
v_fn_5472_ = lean_ctor_get(v_x_5463_, 0);
v_arg_5473_ = lean_ctor_get(v_x_5463_, 1);
v___x_5474_ = lean_unsigned_to_nat(1u);
v___x_5475_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5472_);
v___x_5476_ = lean_nat_add(v___x_5474_, v___x_5475_);
lean_dec(v___x_5475_);
v___x_5477_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5473_);
v___x_5478_ = lean_nat_add(v___x_5476_, v___x_5477_);
lean_dec(v___x_5477_);
lean_dec(v___x_5476_);
return v___x_5478_;
}
case 6:
{
lean_object* v_binderType_5479_; lean_object* v_body_5480_; 
v_binderType_5479_ = lean_ctor_get(v_x_5463_, 1);
v_body_5480_ = lean_ctor_get(v_x_5463_, 2);
v_d_5465_ = v_binderType_5479_;
v_b_5466_ = v_body_5480_;
goto v___jp_5464_;
}
case 7:
{
lean_object* v_binderType_5481_; lean_object* v_body_5482_; 
v_binderType_5481_ = lean_ctor_get(v_x_5463_, 1);
v_body_5482_ = lean_ctor_get(v_x_5463_, 2);
v_d_5465_ = v_binderType_5481_;
v_b_5466_ = v_body_5482_;
goto v___jp_5464_;
}
case 8:
{
lean_object* v_type_5483_; lean_object* v_value_5484_; lean_object* v_body_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; 
v_type_5483_ = lean_ctor_get(v_x_5463_, 1);
v_value_5484_ = lean_ctor_get(v_x_5463_, 2);
v_body_5485_ = lean_ctor_get(v_x_5463_, 3);
v___x_5486_ = lean_unsigned_to_nat(1u);
v___x_5487_ = l_Lean_Expr_sizeWithoutSharing(v_type_5483_);
v___x_5488_ = lean_nat_add(v___x_5486_, v___x_5487_);
lean_dec(v___x_5487_);
v___x_5489_ = l_Lean_Expr_sizeWithoutSharing(v_value_5484_);
v___x_5490_ = lean_nat_add(v___x_5488_, v___x_5489_);
lean_dec(v___x_5489_);
lean_dec(v___x_5488_);
v___x_5491_ = l_Lean_Expr_sizeWithoutSharing(v_body_5485_);
v___x_5492_ = lean_nat_add(v___x_5490_, v___x_5491_);
lean_dec(v___x_5491_);
lean_dec(v___x_5490_);
return v___x_5492_;
}
case 10:
{
lean_object* v_expr_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; 
v_expr_5493_ = lean_ctor_get(v_x_5463_, 1);
v___x_5494_ = lean_unsigned_to_nat(1u);
v___x_5495_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5493_);
v___x_5496_ = lean_nat_add(v___x_5494_, v___x_5495_);
lean_dec(v___x_5495_);
return v___x_5496_;
}
case 11:
{
lean_object* v_struct_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; 
v_struct_5497_ = lean_ctor_get(v_x_5463_, 2);
v___x_5498_ = lean_unsigned_to_nat(1u);
v___x_5499_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5497_);
v___x_5500_ = lean_nat_add(v___x_5498_, v___x_5499_);
lean_dec(v___x_5499_);
return v___x_5500_;
}
default: 
{
lean_object* v___x_5501_; 
v___x_5501_ = lean_unsigned_to_nat(1u);
return v___x_5501_;
}
}
v___jp_5464_:
{
lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; 
v___x_5467_ = lean_unsigned_to_nat(1u);
v___x_5468_ = l_Lean_Expr_sizeWithoutSharing(v_d_5465_);
v___x_5469_ = lean_nat_add(v___x_5467_, v___x_5468_);
lean_dec(v___x_5468_);
v___x_5470_ = l_Lean_Expr_sizeWithoutSharing(v_b_5466_);
v___x_5471_ = lean_nat_add(v___x_5469_, v___x_5470_);
lean_dec(v___x_5470_);
lean_dec(v___x_5469_);
return v___x_5471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5502_){
_start:
{
lean_object* v_res_5503_; 
v_res_5503_ = l_Lean_Expr_sizeWithoutSharing(v_x_5502_);
lean_dec_ref(v_x_5502_);
return v_res_5503_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5506_, lean_object* v_e_5507_){
_start:
{
lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; 
v___x_5508_ = l_Lean_KVMap_empty;
v___x_5509_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5510_ = l_Lean_KVMap_insert(v___x_5508_, v_kind_5506_, v___x_5509_);
v___x_5511_ = l_Lean_Expr_mdata___override(v___x_5510_, v_e_5507_);
return v___x_5511_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5512_, lean_object* v_e_5513_){
_start:
{
if (lean_obj_tag(v_e_5513_) == 10)
{
lean_object* v_data_5514_; lean_object* v_expr_5515_; uint8_t v___y_5517_; lean_object* v___x_5520_; lean_object* v___x_5521_; uint8_t v___x_5522_; 
v_data_5514_ = lean_ctor_get(v_e_5513_, 0);
v_expr_5515_ = lean_ctor_get(v_e_5513_, 1);
v___x_5520_ = l_Lean_KVMap_size(v_data_5514_);
v___x_5521_ = lean_unsigned_to_nat(1u);
v___x_5522_ = lean_nat_dec_eq(v___x_5520_, v___x_5521_);
lean_dec(v___x_5520_);
if (v___x_5522_ == 0)
{
v___y_5517_ = v___x_5522_;
goto v___jp_5516_;
}
else
{
uint8_t v___x_5523_; uint8_t v___x_5524_; 
v___x_5523_ = 0;
v___x_5524_ = l_Lean_KVMap_getBool(v_data_5514_, v_kind_5512_, v___x_5523_);
v___y_5517_ = v___x_5524_;
goto v___jp_5516_;
}
v___jp_5516_:
{
if (v___y_5517_ == 0)
{
lean_object* v___x_5518_; 
v___x_5518_ = lean_box(0);
return v___x_5518_;
}
else
{
lean_object* v___x_5519_; 
lean_inc_ref(v_expr_5515_);
v___x_5519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5519_, 0, v_expr_5515_);
return v___x_5519_;
}
}
}
else
{
lean_object* v___x_5525_; 
v___x_5525_ = lean_box(0);
return v___x_5525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* v_kind_5526_, lean_object* v_e_5527_){
_start:
{
lean_object* v_res_5528_; 
v_res_5528_ = l_Lean_annotation_x3f(v_kind_5526_, v_e_5527_);
lean_dec_ref(v_e_5527_);
lean_dec(v_kind_5526_);
return v_res_5528_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* v_e_5532_){
_start:
{
lean_object* v___x_5533_; lean_object* v___x_5534_; 
v___x_5533_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5534_ = l_Lean_mkAnnotation(v___x_5533_, v_e_5532_);
return v___x_5534_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* v_e_5535_){
_start:
{
lean_object* v___x_5536_; lean_object* v___x_5537_; 
v___x_5536_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5537_ = l_Lean_annotation_x3f(v___x_5536_, v_e_5535_);
return v___x_5537_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* v_e_5538_){
_start:
{
lean_object* v_res_5539_; 
v_res_5539_ = l_Lean_inaccessible_x3f(v_e_5538_);
lean_dec_ref(v_e_5538_);
return v_res_5539_;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* v_p_5544_){
_start:
{
if (lean_obj_tag(v_p_5544_) == 10)
{
lean_object* v_data_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; 
v_data_5545_ = lean_ctor_get(v_p_5544_, 0);
v___x_5546_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5547_ = l_Lean_KVMap_find(v_data_5545_, v___x_5546_);
if (lean_obj_tag(v___x_5547_) == 1)
{
lean_object* v_val_5548_; lean_object* v___x_5550_; uint8_t v_isShared_5551_; uint8_t v_isSharedCheck_5559_; 
v_val_5548_ = lean_ctor_get(v___x_5547_, 0);
v_isSharedCheck_5559_ = !lean_is_exclusive(v___x_5547_);
if (v_isSharedCheck_5559_ == 0)
{
v___x_5550_ = v___x_5547_;
v_isShared_5551_ = v_isSharedCheck_5559_;
goto v_resetjp_5549_;
}
else
{
lean_inc(v_val_5548_);
lean_dec(v___x_5547_);
v___x_5550_ = lean_box(0);
v_isShared_5551_ = v_isSharedCheck_5559_;
goto v_resetjp_5549_;
}
v_resetjp_5549_:
{
if (lean_obj_tag(v_val_5548_) == 5)
{
lean_object* v_v_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5556_; 
v_v_5552_ = lean_ctor_get(v_val_5548_, 0);
lean_inc(v_v_5552_);
lean_dec_ref(v_val_5548_);
v___x_5553_ = l_Lean_Expr_mdataExpr_x21(v_p_5544_);
v___x_5554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5554_, 0, v_v_5552_);
lean_ctor_set(v___x_5554_, 1, v___x_5553_);
if (v_isShared_5551_ == 0)
{
lean_ctor_set(v___x_5550_, 0, v___x_5554_);
v___x_5556_ = v___x_5550_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v___x_5554_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
else
{
lean_object* v___x_5558_; 
lean_del_object(v___x_5550_);
lean_dec(v_val_5548_);
v___x_5558_ = lean_box(0);
return v___x_5558_;
}
}
}
else
{
lean_object* v___x_5560_; 
lean_dec(v___x_5547_);
v___x_5560_ = lean_box(0);
return v___x_5560_;
}
}
else
{
lean_object* v___x_5561_; 
v___x_5561_ = lean_box(0);
return v___x_5561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* v_p_5562_){
_start:
{
lean_object* v_res_5563_; 
v_res_5563_ = l_Lean_patternWithRef_x3f(v_p_5562_);
lean_dec_ref(v_p_5562_);
return v_res_5563_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object* v_p_5564_){
_start:
{
lean_object* v___x_5565_; 
v___x_5565_ = l_Lean_patternWithRef_x3f(v_p_5564_);
if (lean_obj_tag(v___x_5565_) == 0)
{
uint8_t v___x_5566_; 
v___x_5566_ = 0;
return v___x_5566_;
}
else
{
uint8_t v___x_5567_; 
lean_dec_ref(v___x_5565_);
v___x_5567_ = 1;
return v___x_5567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* v_p_5568_){
_start:
{
uint8_t v_res_5569_; lean_object* v_r_5570_; 
v_res_5569_ = l_Lean_isPatternWithRef(v_p_5568_);
lean_dec_ref(v_p_5568_);
v_r_5570_ = lean_box(v_res_5569_);
return v_r_5570_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* v_p_5571_, lean_object* v_stx_5572_){
_start:
{
lean_object* v___x_5573_; 
v___x_5573_ = l_Lean_patternWithRef_x3f(v_p_5571_);
if (lean_obj_tag(v___x_5573_) == 0)
{
lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; 
v___x_5574_ = l_Lean_KVMap_empty;
v___x_5575_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5576_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_5576_, 0, v_stx_5572_);
v___x_5577_ = l_Lean_KVMap_insert(v___x_5574_, v___x_5575_, v___x_5576_);
v___x_5578_ = l_Lean_Expr_mdata___override(v___x_5577_, v_p_5571_);
return v___x_5578_;
}
else
{
lean_dec_ref(v___x_5573_);
lean_dec(v_stx_5572_);
return v_p_5571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* v_e_5579_){
_start:
{
lean_object* v___x_5580_; 
v___x_5580_ = l_Lean_inaccessible_x3f(v_e_5579_);
if (lean_obj_tag(v___x_5580_) == 1)
{
return v___x_5580_;
}
else
{
lean_object* v___x_5581_; 
lean_dec(v___x_5580_);
v___x_5581_ = l_Lean_patternWithRef_x3f(v_e_5579_);
if (lean_obj_tag(v___x_5581_) == 1)
{
lean_object* v_val_5582_; lean_object* v___x_5584_; uint8_t v_isShared_5585_; uint8_t v_isSharedCheck_5590_; 
v_val_5582_ = lean_ctor_get(v___x_5581_, 0);
v_isSharedCheck_5590_ = !lean_is_exclusive(v___x_5581_);
if (v_isSharedCheck_5590_ == 0)
{
v___x_5584_ = v___x_5581_;
v_isShared_5585_ = v_isSharedCheck_5590_;
goto v_resetjp_5583_;
}
else
{
lean_inc(v_val_5582_);
lean_dec(v___x_5581_);
v___x_5584_ = lean_box(0);
v_isShared_5585_ = v_isSharedCheck_5590_;
goto v_resetjp_5583_;
}
v_resetjp_5583_:
{
lean_object* v_snd_5586_; lean_object* v___x_5588_; 
v_snd_5586_ = lean_ctor_get(v_val_5582_, 1);
lean_inc(v_snd_5586_);
lean_dec(v_val_5582_);
if (v_isShared_5585_ == 0)
{
lean_ctor_set(v___x_5584_, 0, v_snd_5586_);
v___x_5588_ = v___x_5584_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_snd_5586_);
v___x_5588_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
return v___x_5588_;
}
}
}
else
{
lean_object* v___x_5591_; 
lean_dec(v___x_5581_);
v___x_5591_ = lean_box(0);
return v___x_5591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* v_e_5592_){
_start:
{
lean_object* v_res_5593_; 
v_res_5593_ = l_Lean_patternAnnotation_x3f(v_e_5592_);
lean_dec_ref(v_e_5592_);
return v_res_5593_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* v_e_5597_){
_start:
{
lean_object* v___x_5598_; lean_object* v___x_5599_; 
v___x_5598_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5599_ = l_Lean_mkAnnotation(v___x_5598_, v_e_5597_);
return v___x_5599_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* v_e_5603_){
_start:
{
lean_object* v___x_5604_; lean_object* v___x_5605_; 
v___x_5604_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5605_ = l_Lean_annotation_x3f(v___x_5604_, v_e_5603_);
if (lean_obj_tag(v___x_5605_) == 0)
{
return v___x_5605_;
}
else
{
lean_object* v_val_5606_; lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5619_; 
v_val_5606_ = lean_ctor_get(v___x_5605_, 0);
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5605_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5608_ = v___x_5605_;
v_isShared_5609_ = v_isSharedCheck_5619_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_val_5606_);
lean_dec(v___x_5605_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5619_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v___x_5610_; lean_object* v___x_5611_; uint8_t v___x_5612_; 
v___x_5610_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5611_ = lean_unsigned_to_nat(3u);
v___x_5612_ = l_Lean_Expr_isAppOfArity(v_val_5606_, v___x_5610_, v___x_5611_);
if (v___x_5612_ == 0)
{
lean_object* v___x_5613_; 
lean_del_object(v___x_5608_);
lean_dec(v_val_5606_);
v___x_5613_ = lean_box(0);
return v___x_5613_;
}
else
{
lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5617_; 
v___x_5614_ = l_Lean_Expr_appFn_x21(v_val_5606_);
lean_dec(v_val_5606_);
v___x_5615_ = l_Lean_Expr_appArg_x21(v___x_5614_);
lean_dec_ref(v___x_5614_);
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 0, v___x_5615_);
v___x_5617_ = v___x_5608_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v___x_5615_);
v___x_5617_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
return v___x_5617_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* v_e_5620_){
_start:
{
lean_object* v_res_5621_; 
v_res_5621_ = l_Lean_isLHSGoal_x3f(v_e_5620_);
lean_dec_ref(v_e_5620_);
return v_res_5621_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* v_toPure_5622_, lean_object* v_____do__lift_5623_){
_start:
{
lean_object* v___x_5624_; 
v___x_5624_ = lean_apply_2(v_toPure_5622_, lean_box(0), v_____do__lift_5623_);
return v___x_5624_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* v_inst_5625_, lean_object* v_inst_5626_){
_start:
{
lean_object* v_toApplicative_5627_; lean_object* v_toBind_5628_; lean_object* v_toPure_5629_; lean_object* v___x_5630_; lean_object* v___f_5631_; lean_object* v___x_5632_; 
v_toApplicative_5627_ = lean_ctor_get(v_inst_5625_, 0);
v_toBind_5628_ = lean_ctor_get(v_inst_5625_, 1);
lean_inc(v_toBind_5628_);
v_toPure_5629_ = lean_ctor_get(v_toApplicative_5627_, 1);
lean_inc(v_toPure_5629_);
v___x_5630_ = l_Lean_mkFreshId___redArg(v_inst_5625_, v_inst_5626_);
v___f_5631_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5631_, 0, v_toPure_5629_);
v___x_5632_ = lean_apply_4(v_toBind_5628_, lean_box(0), lean_box(0), v___x_5630_, v___f_5631_);
return v___x_5632_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* v_m_5633_, lean_object* v_inst_5634_, lean_object* v_inst_5635_){
_start:
{
lean_object* v___x_5636_; 
v___x_5636_ = l_Lean_mkFreshFVarId___redArg(v_inst_5634_, v_inst_5635_);
return v___x_5636_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* v_inst_5637_, lean_object* v_inst_5638_){
_start:
{
lean_object* v_toApplicative_5639_; lean_object* v_toBind_5640_; lean_object* v_toPure_5641_; lean_object* v___x_5642_; lean_object* v___f_5643_; lean_object* v___x_5644_; 
v_toApplicative_5639_ = lean_ctor_get(v_inst_5637_, 0);
v_toBind_5640_ = lean_ctor_get(v_inst_5637_, 1);
lean_inc(v_toBind_5640_);
v_toPure_5641_ = lean_ctor_get(v_toApplicative_5639_, 1);
lean_inc(v_toPure_5641_);
v___x_5642_ = l_Lean_mkFreshId___redArg(v_inst_5637_, v_inst_5638_);
v___f_5643_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5643_, 0, v_toPure_5641_);
v___x_5644_ = lean_apply_4(v_toBind_5640_, lean_box(0), lean_box(0), v___x_5642_, v___f_5643_);
return v___x_5644_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* v_m_5645_, lean_object* v_inst_5646_, lean_object* v_inst_5647_){
_start:
{
lean_object* v___x_5648_; 
v___x_5648_ = l_Lean_mkFreshMVarId___redArg(v_inst_5646_, v_inst_5647_);
return v___x_5648_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* v_inst_5649_, lean_object* v_inst_5650_){
_start:
{
lean_object* v_toApplicative_5651_; lean_object* v_toBind_5652_; lean_object* v_toPure_5653_; lean_object* v___x_5654_; lean_object* v___f_5655_; lean_object* v___x_5656_; 
v_toApplicative_5651_ = lean_ctor_get(v_inst_5649_, 0);
v_toBind_5652_ = lean_ctor_get(v_inst_5649_, 1);
lean_inc(v_toBind_5652_);
v_toPure_5653_ = lean_ctor_get(v_toApplicative_5651_, 1);
lean_inc(v_toPure_5653_);
v___x_5654_ = l_Lean_mkFreshId___redArg(v_inst_5649_, v_inst_5650_);
v___f_5655_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5655_, 0, v_toPure_5653_);
v___x_5656_ = lean_apply_4(v_toBind_5652_, lean_box(0), lean_box(0), v___x_5654_, v___f_5655_);
return v___x_5656_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* v_m_5657_, lean_object* v_inst_5658_, lean_object* v_inst_5659_){
_start:
{
lean_object* v___x_5660_; 
v___x_5660_ = l_Lean_mkFreshLMVarId___redArg(v_inst_5658_, v_inst_5659_);
return v___x_5660_;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2(void){
_start:
{
lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; 
v___x_5664_ = lean_box(0);
v___x_5665_ = ((lean_object*)(l_Lean_mkNot___closed__1));
v___x_5666_ = l_Lean_Expr_const___override(v___x_5665_, v___x_5664_);
return v___x_5666_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* v_p_5667_){
_start:
{
lean_object* v___x_5668_; lean_object* v___x_5669_; 
v___x_5668_ = lean_obj_once(&l_Lean_mkNot___closed__2, &l_Lean_mkNot___closed__2_once, _init_l_Lean_mkNot___closed__2);
v___x_5669_ = l_Lean_Expr_app___override(v___x_5668_, v_p_5667_);
return v___x_5669_;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2(void){
_start:
{
lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; 
v___x_5673_ = lean_box(0);
v___x_5674_ = ((lean_object*)(l_Lean_mkOr___closed__1));
v___x_5675_ = l_Lean_Expr_const___override(v___x_5674_, v___x_5673_);
return v___x_5675_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* v_p_5676_, lean_object* v_q_5677_){
_start:
{
lean_object* v___x_5678_; lean_object* v___x_5679_; 
v___x_5678_ = lean_obj_once(&l_Lean_mkOr___closed__2, &l_Lean_mkOr___closed__2_once, _init_l_Lean_mkOr___closed__2);
v___x_5679_ = l_Lean_mkAppB(v___x_5678_, v_p_5676_, v_q_5677_);
return v___x_5679_;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2(void){
_start:
{
lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; 
v___x_5683_ = lean_box(0);
v___x_5684_ = ((lean_object*)(l_Lean_mkAnd___closed__1));
v___x_5685_ = l_Lean_Expr_const___override(v___x_5684_, v___x_5683_);
return v___x_5685_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* v_p_5686_, lean_object* v_q_5687_){
_start:
{
lean_object* v___x_5688_; lean_object* v___x_5689_; 
v___x_5688_ = lean_obj_once(&l_Lean_mkAnd___closed__2, &l_Lean_mkAnd___closed__2_once, _init_l_Lean_mkAnd___closed__2);
v___x_5689_ = l_Lean_mkAppB(v___x_5688_, v_p_5686_, v_q_5687_);
return v___x_5689_;
}
}
static lean_object* _init_l_Lean_mkAndN___closed__0(void){
_start:
{
lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; 
v___x_5690_ = lean_box(0);
v___x_5691_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_5692_ = l_Lean_Expr_const___override(v___x_5691_, v___x_5690_);
return v___x_5692_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* v_x_5693_){
_start:
{
if (lean_obj_tag(v_x_5693_) == 0)
{
lean_object* v___x_5694_; 
v___x_5694_ = lean_obj_once(&l_Lean_mkAndN___closed__0, &l_Lean_mkAndN___closed__0_once, _init_l_Lean_mkAndN___closed__0);
return v___x_5694_;
}
else
{
lean_object* v_tail_5695_; 
v_tail_5695_ = lean_ctor_get(v_x_5693_, 1);
if (lean_obj_tag(v_tail_5695_) == 0)
{
lean_object* v_head_5696_; 
v_head_5696_ = lean_ctor_get(v_x_5693_, 0);
lean_inc(v_head_5696_);
lean_dec_ref(v_x_5693_);
return v_head_5696_;
}
else
{
lean_object* v_head_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; 
lean_inc(v_tail_5695_);
v_head_5697_ = lean_ctor_get(v_x_5693_, 0);
lean_inc(v_head_5697_);
lean_dec_ref(v_x_5693_);
v___x_5698_ = l_Lean_mkAndN(v_tail_5695_);
v___x_5699_ = l_Lean_mkAnd(v_head_5697_, v___x_5698_);
return v___x_5699_;
}
}
}
}
static lean_object* _init_l_Lean_mkEM___closed__3(void){
_start:
{
lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; 
v___x_5705_ = lean_box(0);
v___x_5706_ = ((lean_object*)(l_Lean_mkEM___closed__2));
v___x_5707_ = l_Lean_Expr_const___override(v___x_5706_, v___x_5705_);
return v___x_5707_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* v_p_5708_){
_start:
{
lean_object* v___x_5709_; lean_object* v___x_5710_; 
v___x_5709_ = lean_obj_once(&l_Lean_mkEM___closed__3, &l_Lean_mkEM___closed__3_once, _init_l_Lean_mkEM___closed__3);
v___x_5710_ = l_Lean_Expr_app___override(v___x_5709_, v_p_5708_);
return v___x_5710_;
}
}
static lean_object* _init_l_Lean_mkIff___closed__2(void){
_start:
{
lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; 
v___x_5714_ = lean_box(0);
v___x_5715_ = ((lean_object*)(l_Lean_mkIff___closed__1));
v___x_5716_ = l_Lean_Expr_const___override(v___x_5715_, v___x_5714_);
return v___x_5716_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* v_p_5717_, lean_object* v_q_5718_){
_start:
{
lean_object* v___x_5719_; lean_object* v___x_5720_; 
v___x_5719_ = lean_obj_once(&l_Lean_mkIff___closed__2, &l_Lean_mkIff___closed__2_once, _init_l_Lean_mkIff___closed__2);
v___x_5720_ = l_Lean_mkAppB(v___x_5719_, v_p_5717_, v_q_5718_);
return v___x_5720_;
}
}
static lean_object* _init_l_Lean_Nat_mkType(void){
_start:
{
lean_object* v___x_5721_; 
v___x_5721_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_5721_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; 
v___x_5725_ = lean_box(0);
v___x_5726_ = ((lean_object*)(l_Lean_Nat_mkInstAdd___closed__1));
v___x_5727_ = l_Lean_Expr_const___override(v___x_5726_, v___x_5725_);
return v___x_5727_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd(void){
_start:
{
lean_object* v___x_5728_; 
v___x_5728_ = lean_obj_once(&l_Lean_Nat_mkInstAdd___closed__2, &l_Lean_Nat_mkInstAdd___closed__2_once, _init_l_Lean_Nat_mkInstAdd___closed__2);
return v___x_5728_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__2(void){
_start:
{
lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; 
v___x_5732_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5733_ = ((lean_object*)(l_Lean_Nat_mkInstHAdd___closed__1));
v___x_5734_ = l_Lean_Expr_const___override(v___x_5733_, v___x_5732_);
return v___x_5734_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__3(void){
_start:
{
lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; 
v___x_5735_ = l_Lean_Nat_mkInstAdd;
v___x_5736_ = l_Lean_Nat_mkType;
v___x_5737_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_5738_ = l_Lean_mkAppB(v___x_5737_, v___x_5736_, v___x_5735_);
return v___x_5738_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd(void){
_start:
{
lean_object* v___x_5739_; 
v___x_5739_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__3, &l_Lean_Nat_mkInstHAdd___closed__3_once, _init_l_Lean_Nat_mkInstHAdd___closed__3);
return v___x_5739_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; 
v___x_5743_ = lean_box(0);
v___x_5744_ = ((lean_object*)(l_Lean_Nat_mkInstSub___closed__1));
v___x_5745_ = l_Lean_Expr_const___override(v___x_5744_, v___x_5743_);
return v___x_5745_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub(void){
_start:
{
lean_object* v___x_5746_; 
v___x_5746_ = lean_obj_once(&l_Lean_Nat_mkInstSub___closed__2, &l_Lean_Nat_mkInstSub___closed__2_once, _init_l_Lean_Nat_mkInstSub___closed__2);
return v___x_5746_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__2(void){
_start:
{
lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; 
v___x_5750_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5751_ = ((lean_object*)(l_Lean_Nat_mkInstHSub___closed__1));
v___x_5752_ = l_Lean_Expr_const___override(v___x_5751_, v___x_5750_);
return v___x_5752_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__3(void){
_start:
{
lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; 
v___x_5753_ = l_Lean_Nat_mkInstSub;
v___x_5754_ = l_Lean_Nat_mkType;
v___x_5755_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_5756_ = l_Lean_mkAppB(v___x_5755_, v___x_5754_, v___x_5753_);
return v___x_5756_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub(void){
_start:
{
lean_object* v___x_5757_; 
v___x_5757_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__3, &l_Lean_Nat_mkInstHSub___closed__3_once, _init_l_Lean_Nat_mkInstHSub___closed__3);
return v___x_5757_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; 
v___x_5761_ = lean_box(0);
v___x_5762_ = ((lean_object*)(l_Lean_Nat_mkInstMul___closed__1));
v___x_5763_ = l_Lean_Expr_const___override(v___x_5762_, v___x_5761_);
return v___x_5763_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul(void){
_start:
{
lean_object* v___x_5764_; 
v___x_5764_ = lean_obj_once(&l_Lean_Nat_mkInstMul___closed__2, &l_Lean_Nat_mkInstMul___closed__2_once, _init_l_Lean_Nat_mkInstMul___closed__2);
return v___x_5764_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__2(void){
_start:
{
lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; 
v___x_5768_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5769_ = ((lean_object*)(l_Lean_Nat_mkInstHMul___closed__1));
v___x_5770_ = l_Lean_Expr_const___override(v___x_5769_, v___x_5768_);
return v___x_5770_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; 
v___x_5771_ = l_Lean_Nat_mkInstMul;
v___x_5772_ = l_Lean_Nat_mkType;
v___x_5773_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_5774_ = l_Lean_mkAppB(v___x_5773_, v___x_5772_, v___x_5771_);
return v___x_5774_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul(void){
_start:
{
lean_object* v___x_5775_; 
v___x_5775_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__3, &l_Lean_Nat_mkInstHMul___closed__3_once, _init_l_Lean_Nat_mkInstHMul___closed__3);
return v___x_5775_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv___closed__2(void){
_start:
{
lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; 
v___x_5780_ = lean_box(0);
v___x_5781_ = ((lean_object*)(l_Lean_Nat_mkInstDiv___closed__1));
v___x_5782_ = l_Lean_Expr_const___override(v___x_5781_, v___x_5780_);
return v___x_5782_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv(void){
_start:
{
lean_object* v___x_5783_; 
v___x_5783_ = lean_obj_once(&l_Lean_Nat_mkInstDiv___closed__2, &l_Lean_Nat_mkInstDiv___closed__2_once, _init_l_Lean_Nat_mkInstDiv___closed__2);
return v___x_5783_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__2(void){
_start:
{
lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; 
v___x_5787_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5788_ = ((lean_object*)(l_Lean_Nat_mkInstHDiv___closed__1));
v___x_5789_ = l_Lean_Expr_const___override(v___x_5788_, v___x_5787_);
return v___x_5789_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__3(void){
_start:
{
lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; 
v___x_5790_ = l_Lean_Nat_mkInstDiv;
v___x_5791_ = l_Lean_Nat_mkType;
v___x_5792_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_5793_ = l_Lean_mkAppB(v___x_5792_, v___x_5791_, v___x_5790_);
return v___x_5793_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv(void){
_start:
{
lean_object* v___x_5794_; 
v___x_5794_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__3, &l_Lean_Nat_mkInstHDiv___closed__3_once, _init_l_Lean_Nat_mkInstHDiv___closed__3);
return v___x_5794_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod___closed__2(void){
_start:
{
lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; 
v___x_5799_ = lean_box(0);
v___x_5800_ = ((lean_object*)(l_Lean_Nat_mkInstMod___closed__1));
v___x_5801_ = l_Lean_Expr_const___override(v___x_5800_, v___x_5799_);
return v___x_5801_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod(void){
_start:
{
lean_object* v___x_5802_; 
v___x_5802_ = lean_obj_once(&l_Lean_Nat_mkInstMod___closed__2, &l_Lean_Nat_mkInstMod___closed__2_once, _init_l_Lean_Nat_mkInstMod___closed__2);
return v___x_5802_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__2(void){
_start:
{
lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; 
v___x_5806_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5807_ = ((lean_object*)(l_Lean_Nat_mkInstHMod___closed__1));
v___x_5808_ = l_Lean_Expr_const___override(v___x_5807_, v___x_5806_);
return v___x_5808_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__3(void){
_start:
{
lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; 
v___x_5809_ = l_Lean_Nat_mkInstMod;
v___x_5810_ = l_Lean_Nat_mkType;
v___x_5811_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_5812_ = l_Lean_mkAppB(v___x_5811_, v___x_5810_, v___x_5809_);
return v___x_5812_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod(void){
_start:
{
lean_object* v___x_5813_; 
v___x_5813_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__3, &l_Lean_Nat_mkInstHMod___closed__3_once, _init_l_Lean_Nat_mkInstHMod___closed__3);
return v___x_5813_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow___closed__2(void){
_start:
{
lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; 
v___x_5817_ = lean_box(0);
v___x_5818_ = ((lean_object*)(l_Lean_Nat_mkInstNatPow___closed__1));
v___x_5819_ = l_Lean_Expr_const___override(v___x_5818_, v___x_5817_);
return v___x_5819_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow(void){
_start:
{
lean_object* v___x_5820_; 
v___x_5820_ = lean_obj_once(&l_Lean_Nat_mkInstNatPow___closed__2, &l_Lean_Nat_mkInstNatPow___closed__2_once, _init_l_Lean_Nat_mkInstNatPow___closed__2);
return v___x_5820_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; 
v___x_5824_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5825_ = ((lean_object*)(l_Lean_Nat_mkInstPow___closed__1));
v___x_5826_ = l_Lean_Expr_const___override(v___x_5825_, v___x_5824_);
return v___x_5826_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__3(void){
_start:
{
lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; 
v___x_5827_ = l_Lean_Nat_mkInstNatPow;
v___x_5828_ = l_Lean_Nat_mkType;
v___x_5829_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_5830_ = l_Lean_mkAppB(v___x_5829_, v___x_5828_, v___x_5827_);
return v___x_5830_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow(void){
_start:
{
lean_object* v___x_5831_; 
v___x_5831_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__3, &l_Lean_Nat_mkInstPow___closed__3_once, _init_l_Lean_Nat_mkInstPow___closed__3);
return v___x_5831_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__3(void){
_start:
{
lean_object* v___x_5838_; lean_object* v___x_5839_; lean_object* v___x_5840_; 
v___x_5838_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__2));
v___x_5839_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__1));
v___x_5840_ = l_Lean_Expr_const___override(v___x_5839_, v___x_5838_);
return v___x_5840_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__4(void){
_start:
{
lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; 
v___x_5841_ = l_Lean_Nat_mkInstPow;
v___x_5842_ = l_Lean_Nat_mkType;
v___x_5843_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_5844_ = l_Lean_mkApp3(v___x_5843_, v___x_5842_, v___x_5842_, v___x_5841_);
return v___x_5844_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow(void){
_start:
{
lean_object* v___x_5845_; 
v___x_5845_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__4, &l_Lean_Nat_mkInstHPow___closed__4_once, _init_l_Lean_Nat_mkInstHPow___closed__4);
return v___x_5845_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; 
v___x_5849_ = lean_box(0);
v___x_5850_ = ((lean_object*)(l_Lean_Nat_mkInstLT___closed__1));
v___x_5851_ = l_Lean_Expr_const___override(v___x_5850_, v___x_5849_);
return v___x_5851_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT(void){
_start:
{
lean_object* v___x_5852_; 
v___x_5852_ = lean_obj_once(&l_Lean_Nat_mkInstLT___closed__2, &l_Lean_Nat_mkInstLT___closed__2_once, _init_l_Lean_Nat_mkInstLT___closed__2);
return v___x_5852_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; 
v___x_5856_ = lean_box(0);
v___x_5857_ = ((lean_object*)(l_Lean_Nat_mkInstLE___closed__1));
v___x_5858_ = l_Lean_Expr_const___override(v___x_5857_, v___x_5856_);
return v___x_5858_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE(void){
_start:
{
lean_object* v___x_5859_; 
v___x_5859_ = lean_obj_once(&l_Lean_Nat_mkInstLE___closed__2, &l_Lean_Nat_mkInstLE___closed__2_once, _init_l_Lean_Nat_mkInstLE___closed__2);
return v___x_5859_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3(void){
_start:
{
lean_object* v___x_5865_; lean_object* v___x_5866_; 
v___x_5865_ = lean_unsigned_to_nat(0u);
v___x_5866_ = l_Lean_Level_ofNat(v___x_5865_);
return v___x_5866_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4(void){
_start:
{
lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; 
v___x_5867_ = lean_box(0);
v___x_5868_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_5869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5869_, 0, v___x_5868_);
lean_ctor_set(v___x_5869_, 1, v___x_5867_);
return v___x_5869_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5(void){
_start:
{
lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; 
v___x_5870_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_5871_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_5872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5872_, 0, v___x_5871_);
lean_ctor_set(v___x_5872_, 1, v___x_5870_);
return v___x_5872_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6(void){
_start:
{
lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; 
v___x_5873_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__5, &l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5);
v___x_5874_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_5875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5875_, 0, v___x_5874_);
lean_ctor_set(v___x_5875_, 1, v___x_5873_);
return v___x_5875_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7(void){
_start:
{
lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; 
v___x_5876_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_5877_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natAddFn___closed__2));
v___x_5878_ = l_Lean_Expr_const___override(v___x_5877_, v___x_5876_);
return v___x_5878_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8(void){
_start:
{
lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; 
v___x_5879_ = l_Lean_Nat_mkInstHAdd;
v___x_5880_ = l_Lean_Nat_mkType;
v___x_5881_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_5882_ = l_Lean_mkApp4(v___x_5881_, v___x_5880_, v___x_5880_, v___x_5880_, v___x_5879_);
return v___x_5882_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn(void){
_start:
{
lean_object* v___x_5883_; 
v___x_5883_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__8, &l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8);
return v___x_5883_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3(void){
_start:
{
lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; 
v___x_5889_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_5890_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natSubFn___closed__2));
v___x_5891_ = l_Lean_Expr_const___override(v___x_5890_, v___x_5889_);
return v___x_5891_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4(void){
_start:
{
lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; 
v___x_5892_ = l_Lean_Nat_mkInstHSub;
v___x_5893_ = l_Lean_Nat_mkType;
v___x_5894_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_5895_ = l_Lean_mkApp4(v___x_5894_, v___x_5893_, v___x_5893_, v___x_5893_, v___x_5892_);
return v___x_5895_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn(void){
_start:
{
lean_object* v___x_5896_; 
v___x_5896_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__4, &l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4);
return v___x_5896_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3(void){
_start:
{
lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; 
v___x_5902_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_5903_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natMulFn___closed__2));
v___x_5904_ = l_Lean_Expr_const___override(v___x_5903_, v___x_5902_);
return v___x_5904_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4(void){
_start:
{
lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; 
v___x_5905_ = l_Lean_Nat_mkInstHMul;
v___x_5906_ = l_Lean_Nat_mkType;
v___x_5907_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_5908_ = l_Lean_mkApp4(v___x_5907_, v___x_5906_, v___x_5906_, v___x_5906_, v___x_5905_);
return v___x_5908_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn(void){
_start:
{
lean_object* v___x_5909_; 
v___x_5909_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__4, &l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4);
return v___x_5909_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3(void){
_start:
{
lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; 
v___x_5915_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_5916_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natPowFn___closed__2));
v___x_5917_ = l_Lean_Expr_const___override(v___x_5916_, v___x_5915_);
return v___x_5917_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4(void){
_start:
{
lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; 
v___x_5918_ = l_Lean_Nat_mkInstHPow;
v___x_5919_ = l_Lean_Nat_mkType;
v___x_5920_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_5921_ = l_Lean_mkApp4(v___x_5920_, v___x_5919_, v___x_5919_, v___x_5919_, v___x_5918_);
return v___x_5921_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn(void){
_start:
{
lean_object* v___x_5922_; 
v___x_5922_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__4, &l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4);
return v___x_5922_;
}
}
static lean_object* _init_l_Lean_mkNatSucc___closed__2(void){
_start:
{
lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; 
v___x_5927_ = lean_box(0);
v___x_5928_ = ((lean_object*)(l_Lean_mkNatSucc___closed__1));
v___x_5929_ = l_Lean_Expr_const___override(v___x_5928_, v___x_5927_);
return v___x_5929_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* v_a_5930_){
_start:
{
lean_object* v___x_5931_; lean_object* v___x_5932_; 
v___x_5931_ = lean_obj_once(&l_Lean_mkNatSucc___closed__2, &l_Lean_mkNatSucc___closed__2_once, _init_l_Lean_mkNatSucc___closed__2);
v___x_5932_ = l_Lean_Expr_app___override(v___x_5931_, v_a_5930_);
return v___x_5932_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* v_a_5933_, lean_object* v_b_5934_){
_start:
{
lean_object* v___x_5935_; lean_object* v___x_5936_; 
v___x_5935_ = l___private_Lean_Expr_0__Lean_natAddFn;
v___x_5936_ = l_Lean_mkAppB(v___x_5935_, v_a_5933_, v_b_5934_);
return v___x_5936_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* v_a_5937_, lean_object* v_b_5938_){
_start:
{
lean_object* v___x_5939_; lean_object* v___x_5940_; 
v___x_5939_ = l___private_Lean_Expr_0__Lean_natSubFn;
v___x_5940_ = l_Lean_mkAppB(v___x_5939_, v_a_5937_, v_b_5938_);
return v___x_5940_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* v_a_5941_, lean_object* v_b_5942_){
_start:
{
lean_object* v___x_5943_; lean_object* v___x_5944_; 
v___x_5943_ = l___private_Lean_Expr_0__Lean_natMulFn;
v___x_5944_ = l_Lean_mkAppB(v___x_5943_, v_a_5941_, v_b_5942_);
return v___x_5944_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object* v_a_5945_, lean_object* v_b_5946_){
_start:
{
lean_object* v___x_5947_; lean_object* v___x_5948_; 
v___x_5947_ = l___private_Lean_Expr_0__Lean_natPowFn;
v___x_5948_ = l_Lean_mkAppB(v___x_5947_, v_a_5945_, v_b_5946_);
return v___x_5948_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3(void){
_start:
{
lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; 
v___x_5954_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_5955_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natLEPred___closed__2));
v___x_5956_ = l_Lean_Expr_const___override(v___x_5955_, v___x_5954_);
return v___x_5956_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4(void){
_start:
{
lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; 
v___x_5957_ = l_Lean_Nat_mkInstLE;
v___x_5958_ = l_Lean_Nat_mkType;
v___x_5959_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_5960_ = l_Lean_mkAppB(v___x_5959_, v___x_5958_, v___x_5957_);
return v___x_5960_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred(void){
_start:
{
lean_object* v___x_5961_; 
v___x_5961_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__4, &l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4);
return v___x_5961_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* v_a_5962_, lean_object* v_b_5963_){
_start:
{
lean_object* v___x_5964_; lean_object* v___x_5965_; 
v___x_5964_ = l___private_Lean_Expr_0__Lean_natLEPred;
v___x_5965_ = l_Lean_mkAppB(v___x_5964_, v_a_5962_, v_b_5963_);
return v___x_5965_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0(void){
_start:
{
lean_object* v___x_5966_; lean_object* v___x_5967_; 
v___x_5966_ = lean_unsigned_to_nat(1u);
v___x_5967_ = l_Lean_Level_ofNat(v___x_5966_);
return v___x_5967_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1(void){
_start:
{
lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; 
v___x_5968_ = lean_box(0);
v___x_5969_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__0, &l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0);
v___x_5970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5970_, 0, v___x_5969_);
lean_ctor_set(v___x_5970_, 1, v___x_5968_);
return v___x_5970_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2(void){
_start:
{
lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; 
v___x_5971_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__1, &l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1);
v___x_5972_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5973_ = l_Lean_Expr_const___override(v___x_5972_, v___x_5971_);
return v___x_5973_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3(void){
_start:
{
lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; 
v___x_5974_ = l_Lean_Nat_mkType;
v___x_5975_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_5976_ = l_Lean_Expr_app___override(v___x_5975_, v___x_5974_);
return v___x_5976_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred(void){
_start:
{
lean_object* v___x_5977_; 
v___x_5977_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__3, &l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3);
return v___x_5977_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* v_a_5978_, lean_object* v_b_5979_){
_start:
{
lean_object* v___x_5980_; lean_object* v___x_5981_; 
v___x_5980_ = l___private_Lean_Expr_0__Lean_natEqPred;
v___x_5981_ = l_Lean_mkAppB(v___x_5980_, v_a_5978_, v_b_5979_);
return v___x_5981_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__0(void){
_start:
{
lean_object* v___x_5982_; lean_object* v___x_5983_; 
v___x_5982_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_5983_ = l_Lean_Expr_sort___override(v___x_5982_);
return v___x_5983_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__1(void){
_start:
{
lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; 
v___x_5984_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__0, &l___private_Lean_Expr_0__Lean_propEq___closed__0_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__0);
v___x_5985_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_5986_ = l_Lean_Expr_app___override(v___x_5985_, v___x_5984_);
return v___x_5986_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq(void){
_start:
{
lean_object* v___x_5987_; 
v___x_5987_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__1, &l___private_Lean_Expr_0__Lean_propEq___closed__1_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__1);
return v___x_5987_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* v_a_5988_, lean_object* v_b_5989_){
_start:
{
lean_object* v___x_5990_; lean_object* v___x_5991_; 
v___x_5990_ = l___private_Lean_Expr_0__Lean_propEq;
v___x_5991_ = l_Lean_mkAppB(v___x_5990_, v_a_5988_, v_b_5989_);
return v___x_5991_;
}
}
static lean_object* _init_l_Lean_Int_mkType___closed__2(void){
_start:
{
lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; 
v___x_5995_ = lean_box(0);
v___x_5996_ = ((lean_object*)(l_Lean_Int_mkType___closed__1));
v___x_5997_ = l_Lean_Expr_const___override(v___x_5996_, v___x_5995_);
return v___x_5997_;
}
}
static lean_object* _init_l_Lean_Int_mkType(void){
_start:
{
lean_object* v___x_5998_; 
v___x_5998_ = lean_obj_once(&l_Lean_Int_mkType___closed__2, &l_Lean_Int_mkType___closed__2_once, _init_l_Lean_Int_mkType___closed__2);
return v___x_5998_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg___closed__2(void){
_start:
{
lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; 
v___x_6003_ = lean_box(0);
v___x_6004_ = ((lean_object*)(l_Lean_Int_mkInstNeg___closed__1));
v___x_6005_ = l_Lean_Expr_const___override(v___x_6004_, v___x_6003_);
return v___x_6005_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg(void){
_start:
{
lean_object* v___x_6006_; 
v___x_6006_ = lean_obj_once(&l_Lean_Int_mkInstNeg___closed__2, &l_Lean_Int_mkInstNeg___closed__2_once, _init_l_Lean_Int_mkInstNeg___closed__2);
return v___x_6006_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; 
v___x_6011_ = lean_box(0);
v___x_6012_ = ((lean_object*)(l_Lean_Int_mkInstAdd___closed__1));
v___x_6013_ = l_Lean_Expr_const___override(v___x_6012_, v___x_6011_);
return v___x_6013_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd(void){
_start:
{
lean_object* v___x_6014_; 
v___x_6014_ = lean_obj_once(&l_Lean_Int_mkInstAdd___closed__2, &l_Lean_Int_mkInstAdd___closed__2_once, _init_l_Lean_Int_mkInstAdd___closed__2);
return v___x_6014_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd___closed__0(void){
_start:
{
lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; 
v___x_6015_ = l_Lean_Int_mkInstAdd;
v___x_6016_ = l_Lean_Int_mkType;
v___x_6017_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6018_ = l_Lean_mkAppB(v___x_6017_, v___x_6016_, v___x_6015_);
return v___x_6018_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd(void){
_start:
{
lean_object* v___x_6019_; 
v___x_6019_ = lean_obj_once(&l_Lean_Int_mkInstHAdd___closed__0, &l_Lean_Int_mkInstHAdd___closed__0_once, _init_l_Lean_Int_mkInstHAdd___closed__0);
return v___x_6019_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; 
v___x_6024_ = lean_box(0);
v___x_6025_ = ((lean_object*)(l_Lean_Int_mkInstSub___closed__1));
v___x_6026_ = l_Lean_Expr_const___override(v___x_6025_, v___x_6024_);
return v___x_6026_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub(void){
_start:
{
lean_object* v___x_6027_; 
v___x_6027_ = lean_obj_once(&l_Lean_Int_mkInstSub___closed__2, &l_Lean_Int_mkInstSub___closed__2_once, _init_l_Lean_Int_mkInstSub___closed__2);
return v___x_6027_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub___closed__0(void){
_start:
{
lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; 
v___x_6028_ = l_Lean_Int_mkInstSub;
v___x_6029_ = l_Lean_Int_mkType;
v___x_6030_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6031_ = l_Lean_mkAppB(v___x_6030_, v___x_6029_, v___x_6028_);
return v___x_6031_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub(void){
_start:
{
lean_object* v___x_6032_; 
v___x_6032_ = lean_obj_once(&l_Lean_Int_mkInstHSub___closed__0, &l_Lean_Int_mkInstHSub___closed__0_once, _init_l_Lean_Int_mkInstHSub___closed__0);
return v___x_6032_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; 
v___x_6037_ = lean_box(0);
v___x_6038_ = ((lean_object*)(l_Lean_Int_mkInstMul___closed__1));
v___x_6039_ = l_Lean_Expr_const___override(v___x_6038_, v___x_6037_);
return v___x_6039_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul(void){
_start:
{
lean_object* v___x_6040_; 
v___x_6040_ = lean_obj_once(&l_Lean_Int_mkInstMul___closed__2, &l_Lean_Int_mkInstMul___closed__2_once, _init_l_Lean_Int_mkInstMul___closed__2);
return v___x_6040_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul___closed__0(void){
_start:
{
lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; 
v___x_6041_ = l_Lean_Int_mkInstMul;
v___x_6042_ = l_Lean_Int_mkType;
v___x_6043_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6044_ = l_Lean_mkAppB(v___x_6043_, v___x_6042_, v___x_6041_);
return v___x_6044_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul(void){
_start:
{
lean_object* v___x_6045_; 
v___x_6045_ = lean_obj_once(&l_Lean_Int_mkInstHMul___closed__0, &l_Lean_Int_mkInstHMul___closed__0_once, _init_l_Lean_Int_mkInstHMul___closed__0);
return v___x_6045_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv___closed__1(void){
_start:
{
lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; 
v___x_6049_ = lean_box(0);
v___x_6050_ = ((lean_object*)(l_Lean_Int_mkInstDiv___closed__0));
v___x_6051_ = l_Lean_Expr_const___override(v___x_6050_, v___x_6049_);
return v___x_6051_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv(void){
_start:
{
lean_object* v___x_6052_; 
v___x_6052_ = lean_obj_once(&l_Lean_Int_mkInstDiv___closed__1, &l_Lean_Int_mkInstDiv___closed__1_once, _init_l_Lean_Int_mkInstDiv___closed__1);
return v___x_6052_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv___closed__0(void){
_start:
{
lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; 
v___x_6053_ = l_Lean_Int_mkInstDiv;
v___x_6054_ = l_Lean_Int_mkType;
v___x_6055_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6056_ = l_Lean_mkAppB(v___x_6055_, v___x_6054_, v___x_6053_);
return v___x_6056_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv(void){
_start:
{
lean_object* v___x_6057_; 
v___x_6057_ = lean_obj_once(&l_Lean_Int_mkInstHDiv___closed__0, &l_Lean_Int_mkInstHDiv___closed__0_once, _init_l_Lean_Int_mkInstHDiv___closed__0);
return v___x_6057_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod___closed__1(void){
_start:
{
lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; 
v___x_6061_ = lean_box(0);
v___x_6062_ = ((lean_object*)(l_Lean_Int_mkInstMod___closed__0));
v___x_6063_ = l_Lean_Expr_const___override(v___x_6062_, v___x_6061_);
return v___x_6063_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod(void){
_start:
{
lean_object* v___x_6064_; 
v___x_6064_ = lean_obj_once(&l_Lean_Int_mkInstMod___closed__1, &l_Lean_Int_mkInstMod___closed__1_once, _init_l_Lean_Int_mkInstMod___closed__1);
return v___x_6064_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod___closed__0(void){
_start:
{
lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; 
v___x_6065_ = l_Lean_Int_mkInstMod;
v___x_6066_ = l_Lean_Int_mkType;
v___x_6067_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6068_ = l_Lean_mkAppB(v___x_6067_, v___x_6066_, v___x_6065_);
return v___x_6068_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod(void){
_start:
{
lean_object* v___x_6069_; 
v___x_6069_ = lean_obj_once(&l_Lean_Int_mkInstHMod___closed__0, &l_Lean_Int_mkInstHMod___closed__0_once, _init_l_Lean_Int_mkInstHMod___closed__0);
return v___x_6069_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; 
v___x_6074_ = lean_box(0);
v___x_6075_ = ((lean_object*)(l_Lean_Int_mkInstPow___closed__1));
v___x_6076_ = l_Lean_Expr_const___override(v___x_6075_, v___x_6074_);
return v___x_6076_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow(void){
_start:
{
lean_object* v___x_6077_; 
v___x_6077_ = lean_obj_once(&l_Lean_Int_mkInstPow___closed__2, &l_Lean_Int_mkInstPow___closed__2_once, _init_l_Lean_Int_mkInstPow___closed__2);
return v___x_6077_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat___closed__0(void){
_start:
{
lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; 
v___x_6078_ = l_Lean_Int_mkInstPow;
v___x_6079_ = l_Lean_Int_mkType;
v___x_6080_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6081_ = l_Lean_mkAppB(v___x_6080_, v___x_6079_, v___x_6078_);
return v___x_6081_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat(void){
_start:
{
lean_object* v___x_6082_; 
v___x_6082_ = lean_obj_once(&l_Lean_Int_mkInstPowNat___closed__0, &l_Lean_Int_mkInstPowNat___closed__0_once, _init_l_Lean_Int_mkInstPowNat___closed__0);
return v___x_6082_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow___closed__0(void){
_start:
{
lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; 
v___x_6083_ = l_Lean_Int_mkInstPowNat;
v___x_6084_ = l_Lean_Nat_mkType;
v___x_6085_ = l_Lean_Int_mkType;
v___x_6086_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6087_ = l_Lean_mkApp3(v___x_6086_, v___x_6085_, v___x_6084_, v___x_6083_);
return v___x_6087_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow(void){
_start:
{
lean_object* v___x_6088_; 
v___x_6088_ = lean_obj_once(&l_Lean_Int_mkInstHPow___closed__0, &l_Lean_Int_mkInstHPow___closed__0_once, _init_l_Lean_Int_mkInstHPow___closed__0);
return v___x_6088_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; 
v___x_6093_ = lean_box(0);
v___x_6094_ = ((lean_object*)(l_Lean_Int_mkInstLT___closed__1));
v___x_6095_ = l_Lean_Expr_const___override(v___x_6094_, v___x_6093_);
return v___x_6095_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT(void){
_start:
{
lean_object* v___x_6096_; 
v___x_6096_ = lean_obj_once(&l_Lean_Int_mkInstLT___closed__2, &l_Lean_Int_mkInstLT___closed__2_once, _init_l_Lean_Int_mkInstLT___closed__2);
return v___x_6096_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; 
v___x_6101_ = lean_box(0);
v___x_6102_ = ((lean_object*)(l_Lean_Int_mkInstLE___closed__1));
v___x_6103_ = l_Lean_Expr_const___override(v___x_6102_, v___x_6101_);
return v___x_6103_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE(void){
_start:
{
lean_object* v___x_6104_; 
v___x_6104_ = lean_obj_once(&l_Lean_Int_mkInstLE___closed__2, &l_Lean_Int_mkInstLE___closed__2_once, _init_l_Lean_Int_mkInstLE___closed__2);
return v___x_6104_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast___closed__2(void){
_start:
{
lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; 
v___x_6108_ = lean_box(0);
v___x_6109_ = ((lean_object*)(l_Lean_Int_mkInstNatCast___closed__1));
v___x_6110_ = l_Lean_Expr_const___override(v___x_6109_, v___x_6108_);
return v___x_6110_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast(void){
_start:
{
lean_object* v___x_6111_; 
v___x_6111_ = lean_obj_once(&l_Lean_Int_mkInstNatCast___closed__2, &l_Lean_Int_mkInstNatCast___closed__2_once, _init_l_Lean_Int_mkInstNatCast___closed__2);
return v___x_6111_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0(void){
_start:
{
lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; 
v___x_6112_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6113_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_6114_ = l_Lean_Expr_const___override(v___x_6113_, v___x_6112_);
return v___x_6114_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1(void){
_start:
{
lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; 
v___x_6115_ = l_Lean_Int_mkInstNeg;
v___x_6116_ = l_Lean_Int_mkType;
v___x_6117_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__0, &l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0);
v___x_6118_ = l_Lean_mkAppB(v___x_6117_, v___x_6116_, v___x_6115_);
return v___x_6118_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn(void){
_start:
{
lean_object* v___x_6119_; 
v___x_6119_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__1, &l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1);
return v___x_6119_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0(void){
_start:
{
lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; 
v___x_6120_ = l_Lean_Int_mkInstHAdd;
v___x_6121_ = l_Lean_Int_mkType;
v___x_6122_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6123_ = l_Lean_mkApp4(v___x_6122_, v___x_6121_, v___x_6121_, v___x_6121_, v___x_6120_);
return v___x_6123_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn(void){
_start:
{
lean_object* v___x_6124_; 
v___x_6124_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intAddFn___closed__0, &l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0);
return v___x_6124_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0(void){
_start:
{
lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; 
v___x_6125_ = l_Lean_Int_mkInstHSub;
v___x_6126_ = l_Lean_Int_mkType;
v___x_6127_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6128_ = l_Lean_mkApp4(v___x_6127_, v___x_6126_, v___x_6126_, v___x_6126_, v___x_6125_);
return v___x_6128_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn(void){
_start:
{
lean_object* v___x_6129_; 
v___x_6129_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intSubFn___closed__0, &l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0);
return v___x_6129_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0(void){
_start:
{
lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; 
v___x_6130_ = l_Lean_Int_mkInstHMul;
v___x_6131_ = l_Lean_Int_mkType;
v___x_6132_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6133_ = l_Lean_mkApp4(v___x_6132_, v___x_6131_, v___x_6131_, v___x_6131_, v___x_6130_);
return v___x_6133_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn(void){
_start:
{
lean_object* v___x_6134_; 
v___x_6134_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intMulFn___closed__0, &l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0);
return v___x_6134_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3(void){
_start:
{
lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; 
v___x_6140_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6141_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intDivFn___closed__2));
v___x_6142_ = l_Lean_Expr_const___override(v___x_6141_, v___x_6140_);
return v___x_6142_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4(void){
_start:
{
lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; 
v___x_6143_ = l_Lean_Int_mkInstHDiv;
v___x_6144_ = l_Lean_Int_mkType;
v___x_6145_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__3, &l___private_Lean_Expr_0__Lean_intDivFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3);
v___x_6146_ = l_Lean_mkApp4(v___x_6145_, v___x_6144_, v___x_6144_, v___x_6144_, v___x_6143_);
return v___x_6146_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn(void){
_start:
{
lean_object* v___x_6147_; 
v___x_6147_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__4, &l___private_Lean_Expr_0__Lean_intDivFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4);
return v___x_6147_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3(void){
_start:
{
lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; 
v___x_6153_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6154_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intModFn___closed__2));
v___x_6155_ = l_Lean_Expr_const___override(v___x_6154_, v___x_6153_);
return v___x_6155_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4(void){
_start:
{
lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; 
v___x_6156_ = l_Lean_Int_mkInstHMod;
v___x_6157_ = l_Lean_Int_mkType;
v___x_6158_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__3, &l___private_Lean_Expr_0__Lean_intModFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3);
v___x_6159_ = l_Lean_mkApp4(v___x_6158_, v___x_6157_, v___x_6157_, v___x_6157_, v___x_6156_);
return v___x_6159_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn(void){
_start:
{
lean_object* v___x_6160_; 
v___x_6160_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__4, &l___private_Lean_Expr_0__Lean_intModFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4);
return v___x_6160_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0(void){
_start:
{
lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; 
v___x_6161_ = l_Lean_Int_mkInstHPow;
v___x_6162_ = l_Lean_Nat_mkType;
v___x_6163_ = l_Lean_Int_mkType;
v___x_6164_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6165_ = l_Lean_mkApp4(v___x_6164_, v___x_6163_, v___x_6162_, v___x_6163_, v___x_6161_);
return v___x_6165_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn(void){
_start:
{
lean_object* v___x_6166_; 
v___x_6166_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0, &l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0);
return v___x_6166_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3(void){
_start:
{
lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; 
v___x_6172_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6173_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2));
v___x_6174_ = l_Lean_Expr_const___override(v___x_6173_, v___x_6172_);
return v___x_6174_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4(void){
_start:
{
lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; 
v___x_6175_ = l_Lean_Int_mkInstNatCast;
v___x_6176_ = l_Lean_Int_mkType;
v___x_6177_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3);
v___x_6178_ = l_Lean_mkAppB(v___x_6177_, v___x_6176_, v___x_6175_);
return v___x_6178_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn(void){
_start:
{
lean_object* v___x_6179_; 
v___x_6179_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4);
return v___x_6179_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* v_a_6180_){
_start:
{
lean_object* v___x_6181_; lean_object* v___x_6182_; 
v___x_6181_ = l___private_Lean_Expr_0__Lean_intNegFn;
v___x_6182_ = l_Lean_Expr_app___override(v___x_6181_, v_a_6180_);
return v___x_6182_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* v_a_6183_, lean_object* v_b_6184_){
_start:
{
lean_object* v___x_6185_; lean_object* v___x_6186_; 
v___x_6185_ = l___private_Lean_Expr_0__Lean_intAddFn;
v___x_6186_ = l_Lean_mkAppB(v___x_6185_, v_a_6183_, v_b_6184_);
return v___x_6186_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* v_a_6187_, lean_object* v_b_6188_){
_start:
{
lean_object* v___x_6189_; lean_object* v___x_6190_; 
v___x_6189_ = l___private_Lean_Expr_0__Lean_intSubFn;
v___x_6190_ = l_Lean_mkAppB(v___x_6189_, v_a_6187_, v_b_6188_);
return v___x_6190_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* v_a_6191_, lean_object* v_b_6192_){
_start:
{
lean_object* v___x_6193_; lean_object* v___x_6194_; 
v___x_6193_ = l___private_Lean_Expr_0__Lean_intMulFn;
v___x_6194_ = l_Lean_mkAppB(v___x_6193_, v_a_6191_, v_b_6192_);
return v___x_6194_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* v_a_6195_, lean_object* v_b_6196_){
_start:
{
lean_object* v___x_6197_; lean_object* v___x_6198_; 
v___x_6197_ = l___private_Lean_Expr_0__Lean_intDivFn;
v___x_6198_ = l_Lean_mkAppB(v___x_6197_, v_a_6195_, v_b_6196_);
return v___x_6198_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* v_a_6199_, lean_object* v_b_6200_){
_start:
{
lean_object* v___x_6201_; lean_object* v___x_6202_; 
v___x_6201_ = l___private_Lean_Expr_0__Lean_intModFn;
v___x_6202_ = l_Lean_mkAppB(v___x_6201_, v_a_6199_, v_b_6200_);
return v___x_6202_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* v_a_6203_){
_start:
{
lean_object* v___x_6204_; lean_object* v___x_6205_; 
v___x_6204_ = l___private_Lean_Expr_0__Lean_intNatCastFn;
v___x_6205_ = l_Lean_Expr_app___override(v___x_6204_, v_a_6203_);
return v___x_6205_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object* v_a_6206_, lean_object* v_b_6207_){
_start:
{
lean_object* v___x_6208_; lean_object* v___x_6209_; 
v___x_6208_ = l___private_Lean_Expr_0__Lean_intPowNatFn;
v___x_6209_ = l_Lean_mkAppB(v___x_6208_, v_a_6206_, v_b_6207_);
return v___x_6209_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0(void){
_start:
{
lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; 
v___x_6210_ = l_Lean_Int_mkInstLE;
v___x_6211_ = l_Lean_Int_mkType;
v___x_6212_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6213_ = l_Lean_mkAppB(v___x_6212_, v___x_6211_, v___x_6210_);
return v___x_6213_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred(void){
_start:
{
lean_object* v___x_6214_; 
v___x_6214_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLEPred___closed__0, &l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0);
return v___x_6214_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* v_a_6215_, lean_object* v_b_6216_){
_start:
{
lean_object* v___x_6217_; lean_object* v___x_6218_; 
v___x_6217_ = l___private_Lean_Expr_0__Lean_intLEPred;
v___x_6218_ = l_Lean_mkAppB(v___x_6217_, v_a_6215_, v_b_6216_);
return v___x_6218_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3(void){
_start:
{
lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; 
v___x_6224_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6225_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intLTPred___closed__2));
v___x_6226_ = l_Lean_Expr_const___override(v___x_6225_, v___x_6224_);
return v___x_6226_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4(void){
_start:
{
lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; 
v___x_6227_ = l_Lean_Int_mkInstLT;
v___x_6228_ = l_Lean_Int_mkType;
v___x_6229_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__3, &l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3);
v___x_6230_ = l_Lean_mkAppB(v___x_6229_, v___x_6228_, v___x_6227_);
return v___x_6230_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred(void){
_start:
{
lean_object* v___x_6231_; 
v___x_6231_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__4, &l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4);
return v___x_6231_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object* v_a_6232_, lean_object* v_b_6233_){
_start:
{
lean_object* v___x_6234_; lean_object* v___x_6235_; 
v___x_6234_ = l___private_Lean_Expr_0__Lean_intLTPred;
v___x_6235_ = l_Lean_mkAppB(v___x_6234_, v_a_6232_, v_b_6233_);
return v___x_6235_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0(void){
_start:
{
lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; 
v___x_6236_ = l_Lean_Int_mkType;
v___x_6237_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6238_ = l_Lean_Expr_app___override(v___x_6237_, v___x_6236_);
return v___x_6238_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred(void){
_start:
{
lean_object* v___x_6239_; 
v___x_6239_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intEqPred___closed__0, &l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0);
return v___x_6239_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* v_a_6240_, lean_object* v_b_6241_){
_start:
{
lean_object* v___x_6242_; lean_object* v___x_6243_; 
v___x_6242_ = l___private_Lean_Expr_0__Lean_intEqPred;
v___x_6243_ = l_Lean_mkAppB(v___x_6242_, v_a_6240_, v_b_6241_);
return v___x_6243_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__3(void){
_start:
{
lean_object* v___x_6249_; lean_object* v___x_6250_; lean_object* v___x_6251_; 
v___x_6249_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6250_ = ((lean_object*)(l_Lean_mkIntDvd___closed__2));
v___x_6251_ = l_Lean_Expr_const___override(v___x_6250_, v___x_6249_);
return v___x_6251_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__6(void){
_start:
{
lean_object* v___x_6256_; lean_object* v___x_6257_; lean_object* v___x_6258_; 
v___x_6256_ = lean_box(0);
v___x_6257_ = ((lean_object*)(l_Lean_mkIntDvd___closed__5));
v___x_6258_ = l_Lean_Expr_const___override(v___x_6257_, v___x_6256_);
return v___x_6258_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* v_a_6259_, lean_object* v_b_6260_){
_start:
{
lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; 
v___x_6261_ = lean_obj_once(&l_Lean_mkIntDvd___closed__3, &l_Lean_mkIntDvd___closed__3_once, _init_l_Lean_mkIntDvd___closed__3);
v___x_6262_ = l_Lean_Int_mkType;
v___x_6263_ = lean_obj_once(&l_Lean_mkIntDvd___closed__6, &l_Lean_mkIntDvd___closed__6_once, _init_l_Lean_mkIntDvd___closed__6);
v___x_6264_ = l_Lean_mkApp4(v___x_6261_, v___x_6262_, v___x_6263_, v_a_6259_, v_b_6260_);
return v___x_6264_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__2(void){
_start:
{
lean_object* v___x_6268_; lean_object* v___x_6269_; lean_object* v___x_6270_; 
v___x_6268_ = lean_box(0);
v___x_6269_ = ((lean_object*)(l_Lean_mkIntLit___closed__1));
v___x_6270_ = l_Lean_Expr_const___override(v___x_6269_, v___x_6268_);
return v___x_6270_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__3(void){
_start:
{
lean_object* v___x_6271_; lean_object* v___x_6272_; 
v___x_6271_ = lean_unsigned_to_nat(0u);
v___x_6272_ = lean_nat_to_int(v___x_6271_);
return v___x_6272_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* v_n_6273_){
_start:
{
lean_object* v___x_6274_; lean_object* v_r_6275_; lean_object* v___x_6276_; lean_object* v___x_6277_; lean_object* v___x_6278_; lean_object* v___x_6279_; lean_object* v_r_6280_; lean_object* v___x_6281_; uint8_t v___x_6282_; 
v___x_6274_ = lean_nat_abs(v_n_6273_);
v_r_6275_ = l_Lean_mkRawNatLit(v___x_6274_);
v___x_6276_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_6277_ = l_Lean_Int_mkType;
v___x_6278_ = lean_obj_once(&l_Lean_mkIntLit___closed__2, &l_Lean_mkIntLit___closed__2_once, _init_l_Lean_mkIntLit___closed__2);
lean_inc_ref(v_r_6275_);
v___x_6279_ = l_Lean_Expr_app___override(v___x_6278_, v_r_6275_);
v_r_6280_ = l_Lean_mkApp3(v___x_6276_, v___x_6277_, v_r_6275_, v___x_6279_);
v___x_6281_ = lean_obj_once(&l_Lean_mkIntLit___closed__3, &l_Lean_mkIntLit___closed__3_once, _init_l_Lean_mkIntLit___closed__3);
v___x_6282_ = lean_int_dec_lt(v_n_6273_, v___x_6281_);
if (v___x_6282_ == 0)
{
return v_r_6280_;
}
else
{
lean_object* v___x_6283_; 
v___x_6283_ = l_Lean_mkIntNeg(v_r_6280_);
return v___x_6283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* v_n_6284_){
_start:
{
lean_object* v_res_6285_; 
v_res_6285_ = l_Lean_mkIntLit(v_n_6284_);
lean_dec(v_n_6284_);
return v_res_6285_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6290_; lean_object* v___x_6291_; 
v___x_6290_ = lean_box(0);
v___x_6291_ = l_Lean_Level_succ___override(v___x_6290_);
return v___x_6291_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; 
v___x_6292_ = lean_box(0);
v___x_6293_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__2, &l_Lean_reflBoolTrue___closed__2_once, _init_l_Lean_reflBoolTrue___closed__2);
v___x_6294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6294_, 0, v___x_6293_);
lean_ctor_set(v___x_6294_, 1, v___x_6292_);
return v___x_6294_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; 
v___x_6295_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__3, &l_Lean_reflBoolTrue___closed__3_once, _init_l_Lean_reflBoolTrue___closed__3);
v___x_6296_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__1));
v___x_6297_ = l_Lean_Expr_const___override(v___x_6296_, v___x_6295_);
return v___x_6297_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__7(void){
_start:
{
lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; 
v___x_6301_ = lean_box(0);
v___x_6302_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__6));
v___x_6303_ = l_Lean_Expr_const___override(v___x_6302_, v___x_6301_);
return v___x_6303_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__9(void){
_start:
{
lean_object* v___x_6307_; lean_object* v___x_6308_; lean_object* v___x_6309_; 
v___x_6307_ = lean_box(0);
v___x_6308_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__8));
v___x_6309_ = l_Lean_Expr_const___override(v___x_6308_, v___x_6307_);
return v___x_6309_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__10(void){
_start:
{
lean_object* v___x_6310_; lean_object* v___x_6311_; lean_object* v___x_6312_; lean_object* v___x_6313_; 
v___x_6310_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__9, &l_Lean_reflBoolTrue___closed__9_once, _init_l_Lean_reflBoolTrue___closed__9);
v___x_6311_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6312_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6313_ = l_Lean_mkAppB(v___x_6312_, v___x_6311_, v___x_6310_);
return v___x_6313_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue(void){
_start:
{
lean_object* v___x_6314_; 
v___x_6314_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__10, &l_Lean_reflBoolTrue___closed__10_once, _init_l_Lean_reflBoolTrue___closed__10);
return v___x_6314_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6318_; lean_object* v___x_6319_; lean_object* v___x_6320_; 
v___x_6318_ = lean_box(0);
v___x_6319_ = ((lean_object*)(l_Lean_reflBoolFalse___closed__0));
v___x_6320_ = l_Lean_Expr_const___override(v___x_6319_, v___x_6318_);
return v___x_6320_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__2(void){
_start:
{
lean_object* v___x_6321_; lean_object* v___x_6322_; lean_object* v___x_6323_; lean_object* v___x_6324_; 
v___x_6321_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
v___x_6322_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6323_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6324_ = l_Lean_mkAppB(v___x_6323_, v___x_6322_, v___x_6321_);
return v___x_6324_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse(void){
_start:
{
lean_object* v___x_6325_; 
v___x_6325_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__2, &l_Lean_reflBoolFalse___closed__2_once, _init_l_Lean_reflBoolFalse___closed__2);
return v___x_6325_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; 
v___x_6329_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6330_ = ((lean_object*)(l_Lean_eagerReflBoolTrue___closed__1));
v___x_6331_ = l_Lean_Expr_const___override(v___x_6330_, v___x_6329_);
return v___x_6331_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6332_; lean_object* v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; 
v___x_6332_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__9, &l_Lean_reflBoolTrue___closed__9_once, _init_l_Lean_reflBoolTrue___closed__9);
v___x_6333_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6334_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6335_ = l_Lean_mkApp3(v___x_6334_, v___x_6333_, v___x_6332_, v___x_6332_);
return v___x_6335_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6336_; lean_object* v___x_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; 
v___x_6336_ = l_Lean_reflBoolTrue;
v___x_6337_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__3, &l_Lean_eagerReflBoolTrue___closed__3_once, _init_l_Lean_eagerReflBoolTrue___closed__3);
v___x_6338_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6339_ = l_Lean_mkAppB(v___x_6338_, v___x_6337_, v___x_6336_);
return v___x_6339_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue(void){
_start:
{
lean_object* v___x_6340_; 
v___x_6340_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__4, &l_Lean_eagerReflBoolTrue___closed__4_once, _init_l_Lean_eagerReflBoolTrue___closed__4);
return v___x_6340_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; lean_object* v___x_6344_; 
v___x_6341_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
v___x_6342_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6343_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6344_ = l_Lean_mkApp3(v___x_6343_, v___x_6342_, v___x_6341_, v___x_6341_);
return v___x_6344_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6345_; lean_object* v___x_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; 
v___x_6345_ = l_Lean_reflBoolFalse;
v___x_6346_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__0, &l_Lean_eagerReflBoolFalse___closed__0_once, _init_l_Lean_eagerReflBoolFalse___closed__0);
v___x_6347_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6348_ = l_Lean_mkAppB(v___x_6347_, v___x_6346_, v___x_6345_);
return v___x_6348_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse(void){
_start:
{
lean_object* v___x_6349_; 
v___x_6349_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__1, &l_Lean_eagerReflBoolFalse___closed__1_once, _init_l_Lean_eagerReflBoolFalse___closed__1);
return v___x_6349_;
}
}
static lean_object* _init_l_Lean_Expr_replaceFn___closed__2(void){
_start:
{
lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6356_; lean_object* v___x_6357_; 
v___x_6352_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__1));
v___x_6353_ = lean_unsigned_to_nat(9u);
v___x_6354_ = lean_unsigned_to_nat(2417u);
v___x_6355_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__0));
v___x_6356_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_6357_ = l_mkPanicMessageWithDecl(v___x_6356_, v___x_6355_, v___x_6354_, v___x_6353_, v___x_6352_);
return v___x_6357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object* v_e_6358_, lean_object* v_declName_6359_){
_start:
{
switch(lean_obj_tag(v_e_6358_))
{
case 5:
{
lean_object* v_fn_6360_; lean_object* v_arg_6361_; lean_object* v___x_6362_; lean_object* v___x_6363_; 
v_fn_6360_ = lean_ctor_get(v_e_6358_, 0);
lean_inc_ref(v_fn_6360_);
v_arg_6361_ = lean_ctor_get(v_e_6358_, 1);
lean_inc_ref(v_arg_6361_);
lean_dec_ref(v_e_6358_);
v___x_6362_ = l_Lean_Expr_replaceFn(v_fn_6360_, v_declName_6359_);
v___x_6363_ = l_Lean_Expr_app___override(v___x_6362_, v_arg_6361_);
return v___x_6363_;
}
case 4:
{
lean_object* v_us_6364_; lean_object* v___x_6365_; 
v_us_6364_ = lean_ctor_get(v_e_6358_, 1);
lean_inc(v_us_6364_);
lean_dec_ref(v_e_6358_);
v___x_6365_ = l_Lean_Expr_const___override(v_declName_6359_, v_us_6364_);
return v___x_6365_;
}
default: 
{
lean_object* v___x_6366_; lean_object* v___x_6367_; 
lean_dec(v_declName_6359_);
lean_dec_ref(v_e_6358_);
v___x_6366_ = lean_obj_once(&l_Lean_Expr_replaceFn___closed__2, &l_Lean_Expr_replaceFn___closed__2_once, _init_l_Lean_Expr_replaceFn___closed__2);
v___x_6367_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_6366_);
return v___x_6367_;
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
l_Lean_instInhabitedData__1 = _init_l_Lean_instInhabitedData__1();
l_Lean_instInhabitedFVarId_default = _init_l_Lean_instInhabitedFVarId_default();
lean_mark_persistent(l_Lean_instInhabitedFVarId_default);
l_Lean_instInhabitedFVarId = _init_l_Lean_instInhabitedFVarId();
lean_mark_persistent(l_Lean_instInhabitedFVarId);
l_Lean_instInhabitedFVarIdSet = _init_l_Lean_instInhabitedFVarIdSet();
lean_mark_persistent(l_Lean_instInhabitedFVarIdSet);
l_Lean_instEmptyCollectionFVarIdSet = _init_l_Lean_instEmptyCollectionFVarIdSet();
lean_mark_persistent(l_Lean_instEmptyCollectionFVarIdSet);
l_Lean_instInhabitedFVarIdHashSet = _init_l_Lean_instInhabitedFVarIdHashSet();
lean_mark_persistent(l_Lean_instInhabitedFVarIdHashSet);
l_Lean_instEmptyCollectionFVarIdHashSet = _init_l_Lean_instEmptyCollectionFVarIdHashSet();
lean_mark_persistent(l_Lean_instEmptyCollectionFVarIdHashSet);
l_Lean_instInhabitedMVarId_default = _init_l_Lean_instInhabitedMVarId_default();
lean_mark_persistent(l_Lean_instInhabitedMVarId_default);
l_Lean_instInhabitedMVarId = _init_l_Lean_instInhabitedMVarId();
lean_mark_persistent(l_Lean_instInhabitedMVarId);
l_Lean_instInhabitedMVarIdSet = _init_l_Lean_instInhabitedMVarIdSet();
lean_mark_persistent(l_Lean_instInhabitedMVarIdSet);
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
