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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Literal_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Literal_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Literal_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_val_7_; lean_object* v___x_8_; 
v_val_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_val_7_);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_10_; 
v_val_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_val_9_);
lean_dec_ref_known(v_t_5_, 1);
v___x_10_ = lean_apply_1(v_k_6_, v_val_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Literal_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Literal_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_natVal_elim___redArg(lean_object* v_t_23_, lean_object* v_natVal_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Literal_ctorElim___redArg(v_t_23_, v_natVal_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_natVal_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_natVal_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Literal_ctorElim___redArg(v_t_27_, v_natVal_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_strVal_elim___redArg(lean_object* v_t_31_, lean_object* v_strVal_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Literal_ctorElim___redArg(v_t_31_, v_strVal_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_strVal_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_strVal_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Literal_ctorElim___redArg(v_t_35_, v_strVal_37_);
return v___x_38_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLiteral_beq(lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v_val_45_; lean_object* v_val_46_; uint8_t v___x_47_; 
v_val_45_ = lean_ctor_get(v_x_43_, 0);
v_val_46_ = lean_ctor_get(v_x_44_, 0);
v___x_47_ = lean_nat_dec_eq(v_val_45_, v_val_46_);
return v___x_47_;
}
else
{
uint8_t v___x_48_; 
v___x_48_ = 0;
return v___x_48_;
}
}
else
{
if (lean_obj_tag(v_x_44_) == 1)
{
lean_object* v_val_49_; lean_object* v_val_50_; uint8_t v___x_51_; 
v_val_49_ = lean_ctor_get(v_x_43_, 0);
v_val_50_ = lean_ctor_get(v_x_44_, 0);
v___x_51_ = lean_string_dec_eq(v_val_49_, v_val_50_);
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLiteral_beq___boxed(lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l_Lean_instBEqLiteral_beq(v_x_53_, v_x_54_);
lean_dec_ref(v_x_54_);
lean_dec_ref(v_x_53_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
static lean_object* _init_l_Lean_instReprLiteral_repr___closed__3(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(2u);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_instReprLiteral_repr___closed__4(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_nat_to_int(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLiteral_repr(lean_object* v_x_75_, lean_object* v_prec_76_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_object* v_val_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_97_; 
v_val_77_ = lean_ctor_get(v_x_75_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_75_);
if (v_isSharedCheck_97_ == 0)
{
v___x_79_ = v_x_75_;
v_isShared_80_ = v_isSharedCheck_97_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_val_77_);
lean_dec(v_x_75_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_97_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___y_82_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(1024u);
v___x_94_ = lean_nat_dec_le(v___x_93_, v_prec_76_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_82_ = v___x_95_;
goto v___jp_81_;
}
else
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_82_ = v___x_96_;
goto v___jp_81_;
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_83_ = ((lean_object*)(l_Lean_instReprLiteral_repr___closed__2));
v___x_84_ = l_Nat_reprFast(v_val_77_);
if (v_isShared_80_ == 0)
{
lean_ctor_set_tag(v___x_79_, 3);
lean_ctor_set(v___x_79_, 0, v___x_84_);
v___x_86_ = v___x_79_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_92_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_83_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
lean_inc(v___y_82_);
v___x_88_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_88_, 0, v___y_82_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = 0;
v___x_90_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*1, v___x_89_);
v___x_91_ = l_Repr_addAppParen(v___x_90_, v_prec_76_);
return v___x_91_;
}
}
}
}
else
{
lean_object* v_val_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_118_; 
v_val_98_ = lean_ctor_get(v_x_75_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v_x_75_);
if (v_isSharedCheck_118_ == 0)
{
v___x_100_ = v_x_75_;
v_isShared_101_ = v_isSharedCheck_118_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_val_98_);
lean_dec(v_x_75_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_118_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___y_103_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = lean_unsigned_to_nat(1024u);
v___x_115_ = lean_nat_dec_le(v___x_114_, v_prec_76_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_103_ = v___x_116_;
goto v___jp_102_;
}
else
{
lean_object* v___x_117_; 
v___x_117_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_103_ = v___x_117_;
goto v___jp_102_;
}
v___jp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_104_ = ((lean_object*)(l_Lean_instReprLiteral_repr___closed__7));
v___x_105_ = l_String_quote(v_val_98_);
if (v_isShared_101_ == 0)
{
lean_ctor_set_tag(v___x_100_, 3);
lean_ctor_set(v___x_100_, 0, v___x_105_);
v___x_107_ = v___x_100_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_113_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_104_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
lean_inc(v___y_103_);
v___x_109_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_109_, 0, v___y_103_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = 0;
v___x_111_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*1, v___x_110_);
v___x_112_ = l_Repr_addAppParen(v___x_111_, v_prec_76_);
return v___x_112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLiteral_repr___boxed(lean_object* v_x_119_, lean_object* v_prec_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_instReprLiteral_repr(v_x_119_, v_prec_120_);
lean_dec(v_prec_120_);
return v_res_121_;
}
}
LEAN_EXPORT uint64_t l_Lean_Literal_hash(lean_object* v_x_124_){
_start:
{
if (lean_obj_tag(v_x_124_) == 0)
{
lean_object* v_val_125_; uint64_t v___x_126_; 
v_val_125_ = lean_ctor_get(v_x_124_, 0);
v___x_126_ = lean_uint64_of_nat(v_val_125_);
return v___x_126_;
}
else
{
lean_object* v_val_127_; uint64_t v___x_128_; 
v_val_127_ = lean_ctor_get(v_x_124_, 0);
v___x_128_ = lean_string_hash(v_val_127_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_hash___boxed(lean_object* v_x_129_){
_start:
{
uint64_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lean_Literal_hash(v_x_129_);
lean_dec_ref(v_x_129_);
v_r_131_ = lean_box_uint64(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint8_t l_Lean_Literal_lt(lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
if (lean_obj_tag(v_x_135_) == 0)
{
lean_object* v_val_136_; lean_object* v_val_137_; uint8_t v___x_138_; 
v_val_136_ = lean_ctor_get(v_x_134_, 0);
v_val_137_ = lean_ctor_get(v_x_135_, 0);
v___x_138_ = lean_nat_dec_lt(v_val_136_, v_val_137_);
return v___x_138_;
}
else
{
uint8_t v___x_139_; 
v___x_139_ = 1;
return v___x_139_;
}
}
else
{
if (lean_obj_tag(v_x_135_) == 1)
{
lean_object* v_val_140_; lean_object* v_val_141_; uint8_t v___x_142_; 
v_val_140_ = lean_ctor_get(v_x_134_, 0);
v_val_141_ = lean_ctor_get(v_x_135_, 0);
v___x_142_ = lean_string_dec_lt(v_val_140_, v_val_141_);
return v___x_142_;
}
else
{
uint8_t v___x_143_; 
v___x_143_ = 0;
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_lt___boxed(lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
uint8_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l_Lean_Literal_lt(v_x_144_, v_x_145_);
lean_dec_ref(v_x_145_);
lean_dec_ref(v_x_144_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
static lean_object* _init_l_Lean_instLTLiteral(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_box(0);
return v___x_148_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableLtLiteral(lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = l_Lean_Literal_lt(v_a_149_, v_b_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableLtLiteral___boxed(lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Lean_instDecidableLtLiteral(v_a_152_, v_b_153_);
lean_dec_ref(v_b_153_);
lean_dec_ref(v_a_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx___impl(uint8_t v_x_156_){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_box(v_x_156_);
v___x_158_ = lean_obj_tag_nat(v___x_157_);
lean_dec(v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx___impl___boxed(lean_object* v_x_159_){
_start:
{
uint8_t v_x_4__boxed_160_; lean_object* v_res_161_; 
v_x_4__boxed_160_ = lean_unbox(v_x_159_);
v_res_161_ = l_Lean_BinderInfo_ctorIdx___impl(v_x_4__boxed_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg(lean_object* v_k_162_){
_start:
{
lean_inc(v_k_162_);
return v_k_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg___boxed(lean_object* v_k_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_BinderInfo_ctorElim___redArg(v_k_163_);
lean_dec(v_k_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim(lean_object* v_motive_165_, lean_object* v_ctorIdx_166_, uint8_t v_t_167_, lean_object* v_h_168_, lean_object* v_k_169_){
_start:
{
lean_inc(v_k_169_);
return v_k_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___boxed(lean_object* v_motive_170_, lean_object* v_ctorIdx_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_k_174_){
_start:
{
uint8_t v_t_boxed_175_; lean_object* v_res_176_; 
v_t_boxed_175_ = lean_unbox(v_t_172_);
v_res_176_ = l_Lean_BinderInfo_ctorElim(v_motive_170_, v_ctorIdx_171_, v_t_boxed_175_, v_h_173_, v_k_174_);
lean_dec(v_k_174_);
lean_dec(v_ctorIdx_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg(lean_object* v_default_177_){
_start:
{
lean_inc(v_default_177_);
return v_default_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg___boxed(lean_object* v_default_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_BinderInfo_default_elim___redArg(v_default_178_);
lean_dec(v_default_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim(lean_object* v_motive_180_, uint8_t v_t_181_, lean_object* v_h_182_, lean_object* v_default_183_){
_start:
{
lean_inc(v_default_183_);
return v_default_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___boxed(lean_object* v_motive_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_default_187_){
_start:
{
uint8_t v_t_boxed_188_; lean_object* v_res_189_; 
v_t_boxed_188_ = lean_unbox(v_t_185_);
v_res_189_ = l_Lean_BinderInfo_default_elim(v_motive_184_, v_t_boxed_188_, v_h_186_, v_default_187_);
lean_dec(v_default_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg(lean_object* v_implicit_190_){
_start:
{
lean_inc(v_implicit_190_);
return v_implicit_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg___boxed(lean_object* v_implicit_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_BinderInfo_implicit_elim___redArg(v_implicit_191_);
lean_dec(v_implicit_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim(lean_object* v_motive_193_, uint8_t v_t_194_, lean_object* v_h_195_, lean_object* v_implicit_196_){
_start:
{
lean_inc(v_implicit_196_);
return v_implicit_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___boxed(lean_object* v_motive_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_implicit_200_){
_start:
{
uint8_t v_t_boxed_201_; lean_object* v_res_202_; 
v_t_boxed_201_ = lean_unbox(v_t_198_);
v_res_202_ = l_Lean_BinderInfo_implicit_elim(v_motive_197_, v_t_boxed_201_, v_h_199_, v_implicit_200_);
lean_dec(v_implicit_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___redArg(lean_object* v_strictImplicit_203_){
_start:
{
lean_inc(v_strictImplicit_203_);
return v_strictImplicit_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___redArg___boxed(lean_object* v_strictImplicit_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_BinderInfo_strictImplicit_elim___redArg(v_strictImplicit_204_);
lean_dec(v_strictImplicit_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim(lean_object* v_motive_206_, uint8_t v_t_207_, lean_object* v_h_208_, lean_object* v_strictImplicit_209_){
_start:
{
lean_inc(v_strictImplicit_209_);
return v_strictImplicit_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___boxed(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_strictImplicit_213_){
_start:
{
uint8_t v_t_boxed_214_; lean_object* v_res_215_; 
v_t_boxed_214_ = lean_unbox(v_t_211_);
v_res_215_ = l_Lean_BinderInfo_strictImplicit_elim(v_motive_210_, v_t_boxed_214_, v_h_212_, v_strictImplicit_213_);
lean_dec(v_strictImplicit_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg(lean_object* v_instImplicit_216_){
_start:
{
lean_inc(v_instImplicit_216_);
return v_instImplicit_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg___boxed(lean_object* v_instImplicit_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_BinderInfo_instImplicit_elim___redArg(v_instImplicit_217_);
lean_dec(v_instImplicit_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim(lean_object* v_motive_219_, uint8_t v_t_220_, lean_object* v_h_221_, lean_object* v_instImplicit_222_){
_start:
{
lean_inc(v_instImplicit_222_);
return v_instImplicit_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___boxed(lean_object* v_motive_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_instImplicit_226_){
_start:
{
uint8_t v_t_boxed_227_; lean_object* v_res_228_; 
v_t_boxed_227_ = lean_unbox(v_t_224_);
v_res_228_ = l_Lean_BinderInfo_instImplicit_elim(v_motive_223_, v_t_boxed_227_, v_h_225_, v_instImplicit_226_);
lean_dec(v_instImplicit_226_);
return v_res_228_;
}
}
static uint8_t _init_l_Lean_instInhabitedBinderInfo_default(void){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = 0;
return v___x_229_;
}
}
static uint8_t _init_l_Lean_instInhabitedBinderInfo(void){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = 0;
return v___x_230_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t v_x_231_, uint8_t v_y_232_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_233_ = lean_box(v_x_231_);
v___x_234_ = lean_obj_tag_nat(v___x_233_);
lean_dec(v___x_233_);
v___x_235_ = lean_box(v_y_232_);
v___x_236_ = lean_obj_tag_nat(v___x_235_);
lean_dec(v___x_235_);
v___x_237_ = lean_nat_dec_eq(v___x_234_, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqBinderInfo_beq___boxed(lean_object* v_x_238_, lean_object* v_y_239_){
_start:
{
uint8_t v_x_24__boxed_240_; uint8_t v_y_25__boxed_241_; uint8_t v_res_242_; lean_object* v_r_243_; 
v_x_24__boxed_240_ = lean_unbox(v_x_238_);
v_y_25__boxed_241_ = lean_unbox(v_y_239_);
v_res_242_ = l_Lean_instBEqBinderInfo_beq(v_x_24__boxed_240_, v_y_25__boxed_241_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr(uint8_t v_x_258_, lean_object* v_prec_259_){
_start:
{
lean_object* v___y_261_; lean_object* v___y_268_; lean_object* v___y_275_; lean_object* v___y_282_; 
switch(v_x_258_)
{
case 0:
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(1024u);
v___x_289_ = lean_nat_dec_le(v___x_288_, v_prec_259_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_261_ = v___x_290_;
goto v___jp_260_;
}
else
{
lean_object* v___x_291_; 
v___x_291_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_261_ = v___x_291_;
goto v___jp_260_;
}
}
case 1:
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_unsigned_to_nat(1024u);
v___x_293_ = lean_nat_dec_le(v___x_292_, v_prec_259_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; 
v___x_294_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_268_ = v___x_294_;
goto v___jp_267_;
}
else
{
lean_object* v___x_295_; 
v___x_295_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_268_ = v___x_295_;
goto v___jp_267_;
}
}
case 2:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(1024u);
v___x_297_ = lean_nat_dec_le(v___x_296_, v_prec_259_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_275_ = v___x_298_;
goto v___jp_274_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_275_ = v___x_299_;
goto v___jp_274_;
}
}
default: 
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(1024u);
v___x_301_ = lean_nat_dec_le(v___x_300_, v_prec_259_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_282_ = v___x_302_;
goto v___jp_281_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_282_ = v___x_303_;
goto v___jp_281_;
}
}
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_262_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__1));
lean_inc(v___y_261_);
v___x_263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_263_, 0, v___y_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = 0;
v___x_265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_264_);
v___x_266_ = l_Repr_addAppParen(v___x_265_, v_prec_259_);
return v___x_266_;
}
v___jp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_269_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__3));
lean_inc(v___y_268_);
v___x_270_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_270_, 0, v___y_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = 0;
v___x_272_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*1, v___x_271_);
v___x_273_ = l_Repr_addAppParen(v___x_272_, v_prec_259_);
return v___x_273_;
}
v___jp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_276_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__5));
lean_inc(v___y_275_);
v___x_277_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_277_, 0, v___y_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = 0;
v___x_279_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*1, v___x_278_);
v___x_280_ = l_Repr_addAppParen(v___x_279_, v_prec_259_);
return v___x_280_;
}
v___jp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_283_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__7));
lean_inc(v___y_282_);
v___x_284_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_284_, 0, v___y_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = 0;
v___x_286_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set_uint8(v___x_286_, sizeof(void*)*1, v___x_285_);
v___x_287_ = l_Repr_addAppParen(v___x_286_, v_prec_259_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr___boxed(lean_object* v_x_304_, lean_object* v_prec_305_){
_start:
{
uint8_t v_x_221__boxed_306_; lean_object* v_res_307_; 
v_x_221__boxed_306_ = lean_unbox(v_x_304_);
v_res_307_ = l_Lean_instReprBinderInfo_repr(v_x_221__boxed_306_, v_prec_305_);
lean_dec(v_prec_305_);
return v_res_307_;
}
}
LEAN_EXPORT uint64_t l_Lean_BinderInfo_hash(uint8_t v_x_310_){
_start:
{
switch(v_x_310_)
{
case 0:
{
uint64_t v___x_311_; 
v___x_311_ = 947ULL;
return v___x_311_;
}
case 1:
{
uint64_t v___x_312_; 
v___x_312_ = 1019ULL;
return v___x_312_;
}
case 2:
{
uint64_t v___x_313_; 
v___x_313_ = 1087ULL;
return v___x_313_;
}
default: 
{
uint64_t v___x_314_; 
v___x_314_ = 1153ULL;
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_hash___boxed(lean_object* v_x_315_){
_start:
{
uint8_t v_x_52__boxed_316_; uint64_t v_res_317_; lean_object* v_r_318_; 
v_x_52__boxed_316_ = lean_unbox(v_x_315_);
v_res_317_ = l_Lean_BinderInfo_hash(v_x_52__boxed_316_);
v_r_318_ = lean_box_uint64(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isExplicit(uint8_t v_x_319_){
_start:
{
switch(v_x_319_)
{
case 1:
{
uint8_t v___x_320_; 
v___x_320_ = 0;
return v___x_320_;
}
case 2:
{
uint8_t v___x_321_; 
v___x_321_ = 0;
return v___x_321_;
}
case 3:
{
uint8_t v___x_322_; 
v___x_322_ = 0;
return v___x_322_;
}
default: 
{
uint8_t v___x_323_; 
v___x_323_ = 1;
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object* v_x_324_){
_start:
{
uint8_t v_x_27__boxed_325_; uint8_t v_res_326_; lean_object* v_r_327_; 
v_x_27__boxed_325_ = lean_unbox(v_x_324_);
v_res_326_ = l_Lean_BinderInfo_isExplicit(v_x_27__boxed_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t v_x_330_){
_start:
{
if (v_x_330_ == 3)
{
uint8_t v___x_331_; 
v___x_331_ = 1;
return v___x_331_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object* v_x_333_){
_start:
{
uint8_t v_x_17__boxed_334_; uint8_t v_res_335_; lean_object* v_r_336_; 
v_x_17__boxed_334_ = lean_unbox(v_x_333_);
v_res_335_ = l_Lean_BinderInfo_isInstImplicit(v_x_17__boxed_334_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isImplicit(uint8_t v_x_337_){
_start:
{
if (v_x_337_ == 1)
{
uint8_t v___x_338_; 
v___x_338_ = 1;
return v___x_338_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = 0;
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isImplicit___boxed(lean_object* v_x_340_){
_start:
{
uint8_t v_x_17__boxed_341_; uint8_t v_res_342_; lean_object* v_r_343_; 
v_x_17__boxed_341_ = lean_unbox(v_x_340_);
v_res_342_ = l_Lean_BinderInfo_isImplicit(v_x_17__boxed_341_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isStrictImplicit(uint8_t v_x_344_){
_start:
{
if (v_x_344_ == 2)
{
uint8_t v___x_345_; 
v___x_345_ = 1;
return v___x_345_;
}
else
{
uint8_t v___x_346_; 
v___x_346_ = 0;
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isStrictImplicit___boxed(lean_object* v_x_347_){
_start:
{
uint8_t v_x_17__boxed_348_; uint8_t v_res_349_; lean_object* v_r_350_; 
v_x_17__boxed_348_ = lean_unbox(v_x_347_);
v_res_349_ = l_Lean_BinderInfo_isStrictImplicit(v_x_17__boxed_348_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
static lean_object* _init_l_Lean_MData_empty(void){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = lean_box(0);
return v___x_351_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1___aux__1(void){
_start:
{
uint64_t v___x_352_; 
v___x_352_ = 0ULL;
return v___x_352_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1(void){
_start:
{
uint64_t v___x_353_; 
v___x_353_ = 0ULL;
return v___x_353_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_Data_hash(uint64_t v_c_354_){
_start:
{
uint32_t v___x_355_; uint64_t v___x_356_; 
v___x_355_ = lean_uint64_to_uint32(v_c_354_);
v___x_356_ = lean_uint32_to_uint64(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object* v_c_357_){
_start:
{
uint64_t v_c_boxed_358_; uint64_t v_res_359_; lean_object* v_r_360_; 
v_c_boxed_358_ = lean_unbox_uint64(v_c_357_);
lean_dec_ref(v_c_357_);
v_res_359_ = l_Lean_Expr_Data_hash(v_c_boxed_358_);
v_r_360_ = lean_box_uint64(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t v_c_363_){
_start:
{
uint64_t v___x_364_; uint64_t v___x_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint8_t v___x_368_; 
v___x_364_ = 32ULL;
v___x_365_ = lean_uint64_shift_right(v_c_363_, v___x_364_);
v___x_366_ = 255ULL;
v___x_367_ = lean_uint64_land(v___x_365_, v___x_366_);
v___x_368_ = lean_uint64_to_uint8(v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object* v_c_369_){
_start:
{
uint64_t v_c_boxed_370_; uint8_t v_res_371_; lean_object* v_r_372_; 
v_c_boxed_370_ = lean_unbox_uint64(v_c_369_);
lean_dec_ref(v_c_369_);
v_res_371_ = l_Lean_Expr_Data_approxDepth(v_c_boxed_370_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t v_c_373_){
_start:
{
uint64_t v___x_374_; uint64_t v___x_375_; uint32_t v___x_376_; 
v___x_374_ = 44ULL;
v___x_375_ = lean_uint64_shift_right(v_c_373_, v___x_374_);
v___x_376_ = lean_uint64_to_uint32(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object* v_c_377_){
_start:
{
uint64_t v_c_boxed_378_; uint32_t v_res_379_; lean_object* v_r_380_; 
v_c_boxed_378_ = lean_unbox_uint64(v_c_377_);
lean_dec_ref(v_c_377_);
v_res_379_ = l_Lean_Expr_Data_looseBVarRange(v_c_boxed_378_);
v_r_380_ = lean_box_uint32(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t v_c_381_){
_start:
{
uint64_t v___x_382_; uint64_t v___x_383_; uint64_t v___x_384_; uint64_t v___x_385_; uint8_t v___x_386_; 
v___x_382_ = 40ULL;
v___x_383_ = lean_uint64_shift_right(v_c_381_, v___x_382_);
v___x_384_ = 1ULL;
v___x_385_ = lean_uint64_land(v___x_383_, v___x_384_);
v___x_386_ = lean_uint64_dec_eq(v___x_385_, v___x_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object* v_c_387_){
_start:
{
uint64_t v_c_boxed_388_; uint8_t v_res_389_; lean_object* v_r_390_; 
v_c_boxed_388_ = lean_unbox_uint64(v_c_387_);
lean_dec_ref(v_c_387_);
v_res_389_ = l_Lean_Expr_Data_hasFVar(v_c_boxed_388_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t v_c_391_){
_start:
{
uint64_t v___x_392_; uint64_t v___x_393_; uint64_t v___x_394_; uint64_t v___x_395_; uint8_t v___x_396_; 
v___x_392_ = 41ULL;
v___x_393_ = lean_uint64_shift_right(v_c_391_, v___x_392_);
v___x_394_ = 1ULL;
v___x_395_ = lean_uint64_land(v___x_393_, v___x_394_);
v___x_396_ = lean_uint64_dec_eq(v___x_395_, v___x_394_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object* v_c_397_){
_start:
{
uint64_t v_c_boxed_398_; uint8_t v_res_399_; lean_object* v_r_400_; 
v_c_boxed_398_ = lean_unbox_uint64(v_c_397_);
lean_dec_ref(v_c_397_);
v_res_399_ = l_Lean_Expr_Data_hasExprMVar(v_c_boxed_398_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t v_c_401_){
_start:
{
uint64_t v___x_402_; uint64_t v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint8_t v___x_406_; 
v___x_402_ = 42ULL;
v___x_403_ = lean_uint64_shift_right(v_c_401_, v___x_402_);
v___x_404_ = 1ULL;
v___x_405_ = lean_uint64_land(v___x_403_, v___x_404_);
v___x_406_ = lean_uint64_dec_eq(v___x_405_, v___x_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object* v_c_407_){
_start:
{
uint64_t v_c_boxed_408_; uint8_t v_res_409_; lean_object* v_r_410_; 
v_c_boxed_408_ = lean_unbox_uint64(v_c_407_);
lean_dec_ref(v_c_407_);
v_res_409_ = l_Lean_Expr_Data_hasLevelMVar(v_c_boxed_408_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t v_c_411_){
_start:
{
uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint8_t v___x_416_; 
v___x_412_ = 43ULL;
v___x_413_ = lean_uint64_shift_right(v_c_411_, v___x_412_);
v___x_414_ = 1ULL;
v___x_415_ = lean_uint64_land(v___x_413_, v___x_414_);
v___x_416_ = lean_uint64_dec_eq(v___x_415_, v___x_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object* v_c_417_){
_start:
{
uint64_t v_c_boxed_418_; uint8_t v_res_419_; lean_object* v_r_420_; 
v_c_boxed_418_ = lean_unbox_uint64(v_c_417_);
lean_dec_ref(v_c_417_);
v_res_419_ = l_Lean_Expr_Data_hasLevelParam(v_c_boxed_418_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_422_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_423_; uint64_t v_res_424_; lean_object* v_r_425_; 
v_a_00___x40___internal___hyg_1__boxed_423_ = lean_unbox(v_a_00___x40___internal___hyg_422_);
v_res_424_ = lean_uint8_to_uint64(v_a_00___x40___internal___hyg_1__boxed_423_);
v_r_425_ = lean_box_uint64(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object* v_h_433_, lean_object* v_looseBVarRange_434_, lean_object* v_approxDepth_435_, lean_object* v_hasFVar_436_, lean_object* v_hasExprMVar_437_, lean_object* v_hasLevelMVar_438_, lean_object* v_hasLevelParam_439_){
_start:
{
uint64_t v_h_boxed_440_; uint32_t v_approxDepth_boxed_441_; uint8_t v_hasFVar_boxed_442_; uint8_t v_hasExprMVar_boxed_443_; uint8_t v_hasLevelMVar_boxed_444_; uint8_t v_hasLevelParam_boxed_445_; uint64_t v_res_446_; lean_object* v_r_447_; 
v_h_boxed_440_ = lean_unbox_uint64(v_h_433_);
lean_dec_ref(v_h_433_);
v_approxDepth_boxed_441_ = lean_unbox_uint32(v_approxDepth_435_);
lean_dec(v_approxDepth_435_);
v_hasFVar_boxed_442_ = lean_unbox(v_hasFVar_436_);
v_hasExprMVar_boxed_443_ = lean_unbox(v_hasExprMVar_437_);
v_hasLevelMVar_boxed_444_ = lean_unbox(v_hasLevelMVar_438_);
v_hasLevelParam_boxed_445_ = lean_unbox(v_hasLevelParam_439_);
v_res_446_ = lean_expr_mk_data(v_h_boxed_440_, v_looseBVarRange_434_, v_approxDepth_boxed_441_, v_hasFVar_boxed_442_, v_hasExprMVar_boxed_443_, v_hasLevelMVar_boxed_444_, v_hasLevelParam_boxed_445_);
v_r_447_ = lean_box_uint64(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object* v_fData_450_, lean_object* v_aData_451_){
_start:
{
uint64_t v_fData_boxed_452_; uint64_t v_aData_boxed_453_; uint64_t v_res_454_; lean_object* v_r_455_; 
v_fData_boxed_452_ = lean_unbox_uint64(v_fData_450_);
lean_dec_ref(v_fData_450_);
v_aData_boxed_453_ = lean_unbox_uint64(v_aData_451_);
lean_dec_ref(v_aData_451_);
v_res_454_ = lean_expr_mk_app_data(v_fData_boxed_452_, v_aData_boxed_453_);
v_r_455_ = lean_box_uint64(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint64_t v_h_456_, lean_object* v_looseBVarRange_457_, uint32_t v_approxDepth_458_, uint8_t v_hasFVar_459_, uint8_t v_hasExprMVar_460_, uint8_t v_hasLevelMVar_461_, uint8_t v_hasLevelParam_462_){
_start:
{
uint64_t v___x_463_; 
v___x_463_ = lean_expr_mk_data(v_h_456_, v_looseBVarRange_457_, v_approxDepth_458_, v_hasFVar_459_, v_hasExprMVar_460_, v_hasLevelMVar_461_, v_hasLevelParam_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object* v_h_464_, lean_object* v_looseBVarRange_465_, lean_object* v_approxDepth_466_, lean_object* v_hasFVar_467_, lean_object* v_hasExprMVar_468_, lean_object* v_hasLevelMVar_469_, lean_object* v_hasLevelParam_470_){
_start:
{
uint64_t v_h_boxed_471_; uint32_t v_approxDepth_boxed_472_; uint8_t v_hasFVar_boxed_473_; uint8_t v_hasExprMVar_boxed_474_; uint8_t v_hasLevelMVar_boxed_475_; uint8_t v_hasLevelParam_boxed_476_; uint64_t v_res_477_; lean_object* v_r_478_; 
v_h_boxed_471_ = lean_unbox_uint64(v_h_464_);
lean_dec_ref(v_h_464_);
v_approxDepth_boxed_472_ = lean_unbox_uint32(v_approxDepth_466_);
lean_dec(v_approxDepth_466_);
v_hasFVar_boxed_473_ = lean_unbox(v_hasFVar_467_);
v_hasExprMVar_boxed_474_ = lean_unbox(v_hasExprMVar_468_);
v_hasLevelMVar_boxed_475_ = lean_unbox(v_hasLevelMVar_469_);
v_hasLevelParam_boxed_476_ = lean_unbox(v_hasLevelParam_470_);
v_res_477_ = l_Lean_Expr_mkDataForBinder(v_h_boxed_471_, v_looseBVarRange_465_, v_approxDepth_boxed_472_, v_hasFVar_boxed_473_, v_hasExprMVar_boxed_474_, v_hasLevelMVar_boxed_475_, v_hasLevelParam_boxed_476_);
v_r_478_ = lean_box_uint64(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint64_t v_h_479_, lean_object* v_looseBVarRange_480_, uint32_t v_approxDepth_481_, uint8_t v_hasFVar_482_, uint8_t v_hasExprMVar_483_, uint8_t v_hasLevelMVar_484_, uint8_t v_hasLevelParam_485_){
_start:
{
uint64_t v___x_486_; 
v___x_486_ = lean_expr_mk_data(v_h_479_, v_looseBVarRange_480_, v_approxDepth_481_, v_hasFVar_482_, v_hasExprMVar_483_, v_hasLevelMVar_484_, v_hasLevelParam_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object* v_h_487_, lean_object* v_looseBVarRange_488_, lean_object* v_approxDepth_489_, lean_object* v_hasFVar_490_, lean_object* v_hasExprMVar_491_, lean_object* v_hasLevelMVar_492_, lean_object* v_hasLevelParam_493_){
_start:
{
uint64_t v_h_boxed_494_; uint32_t v_approxDepth_boxed_495_; uint8_t v_hasFVar_boxed_496_; uint8_t v_hasExprMVar_boxed_497_; uint8_t v_hasLevelMVar_boxed_498_; uint8_t v_hasLevelParam_boxed_499_; uint64_t v_res_500_; lean_object* v_r_501_; 
v_h_boxed_494_ = lean_unbox_uint64(v_h_487_);
lean_dec_ref(v_h_487_);
v_approxDepth_boxed_495_ = lean_unbox_uint32(v_approxDepth_489_);
lean_dec(v_approxDepth_489_);
v_hasFVar_boxed_496_ = lean_unbox(v_hasFVar_490_);
v_hasExprMVar_boxed_497_ = lean_unbox(v_hasExprMVar_491_);
v_hasLevelMVar_boxed_498_ = lean_unbox(v_hasLevelMVar_492_);
v_hasLevelParam_boxed_499_ = lean_unbox(v_hasLevelParam_493_);
v_res_500_ = l_Lean_Expr_mkDataForLet(v_h_boxed_494_, v_looseBVarRange_488_, v_approxDepth_boxed_495_, v_hasFVar_boxed_496_, v_hasExprMVar_boxed_497_, v_hasLevelMVar_boxed_498_, v_hasLevelParam_boxed_499_);
v_r_501_ = lean_box_uint64(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0(uint64_t v_v_511_, lean_object* v_prec_512_){
_start:
{
lean_object* v_r_514_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v_r_524_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v_r_537_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v_r_550_; lean_object* v_r_557_; lean_object* v___x_568_; uint64_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v_r_572_; uint32_t v___x_573_; uint32_t v___x_574_; uint8_t v___x_575_; 
v___x_568_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__7));
v___x_569_ = l_Lean_Expr_Data_hash(v_v_511_);
v___x_570_ = lean_uint64_to_nat(v___x_569_);
v___x_571_ = l_Nat_reprFast(v___x_570_);
v_r_572_ = lean_string_append(v___x_568_, v___x_571_);
lean_dec_ref(v___x_571_);
v___x_573_ = l_Lean_Expr_Data_looseBVarRange(v_v_511_);
v___x_574_ = 0;
v___x_575_ = lean_uint32_dec_eq(v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v_r_582_; 
v___x_576_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__8));
v___x_577_ = lean_string_append(v_r_572_, v___x_576_);
v___x_578_ = lean_uint32_to_nat(v___x_573_);
v___x_579_ = l_Nat_reprFast(v___x_578_);
v___x_580_ = lean_string_append(v___x_577_, v___x_579_);
lean_dec_ref(v___x_579_);
v___x_581_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_582_ = lean_string_append(v___x_580_, v___x_581_);
v_r_557_ = v_r_582_;
goto v___jp_556_;
}
else
{
v_r_557_ = v_r_572_;
goto v___jp_556_;
}
v___jp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_515_, 0, v_r_514_);
v___x_516_ = l_Repr_addAppParen(v___x_515_, v_prec_512_);
return v___x_516_;
}
v___jp_517_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_r_522_; 
v___x_520_ = lean_string_append(v___y_518_, v___y_519_);
v___x_521_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_522_ = lean_string_append(v___x_520_, v___x_521_);
v_r_514_ = v_r_522_;
goto v___jp_513_;
}
v___jp_523_:
{
uint8_t v___x_525_; 
v___x_525_ = l_Lean_Expr_Data_hasLevelMVar(v_v_511_);
if (v___x_525_ == 0)
{
v_r_514_ = v_r_524_;
goto v___jp_513_;
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
v___x_527_ = lean_string_append(v_r_524_, v___x_526_);
if (v___x_525_ == 0)
{
lean_object* v___x_528_; 
v___x_528_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_518_ = v___x_527_;
v___y_519_ = v___x_528_;
goto v___jp_517_;
}
else
{
lean_object* v___x_529_; 
v___x_529_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_518_ = v___x_527_;
v___y_519_ = v___x_529_;
goto v___jp_517_;
}
}
}
v___jp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v_r_535_; 
v___x_533_ = lean_string_append(v___y_531_, v___y_532_);
v___x_534_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_535_ = lean_string_append(v___x_533_, v___x_534_);
v_r_524_ = v_r_535_;
goto v___jp_523_;
}
v___jp_536_:
{
uint8_t v___x_538_; 
v___x_538_ = l_Lean_Expr_Data_hasExprMVar(v_v_511_);
if (v___x_538_ == 0)
{
v_r_524_ = v_r_537_;
goto v___jp_523_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__4));
v___x_540_ = lean_string_append(v_r_537_, v___x_539_);
if (v___x_538_ == 0)
{
lean_object* v___x_541_; 
v___x_541_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_531_ = v___x_540_;
v___y_532_ = v___x_541_;
goto v___jp_530_;
}
else
{
lean_object* v___x_542_; 
v___x_542_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_531_ = v___x_540_;
v___y_532_ = v___x_542_;
goto v___jp_530_;
}
}
}
v___jp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v_r_548_; 
v___x_546_ = lean_string_append(v___y_544_, v___y_545_);
v___x_547_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_548_ = lean_string_append(v___x_546_, v___x_547_);
v_r_537_ = v_r_548_;
goto v___jp_536_;
}
v___jp_549_:
{
uint8_t v___x_551_; 
v___x_551_ = l_Lean_Expr_Data_hasFVar(v_v_511_);
if (v___x_551_ == 0)
{
v_r_537_ = v_r_550_;
goto v___jp_536_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__5));
v___x_553_ = lean_string_append(v_r_550_, v___x_552_);
if (v___x_551_ == 0)
{
lean_object* v___x_554_; 
v___x_554_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_544_ = v___x_553_;
v___y_545_ = v___x_554_;
goto v___jp_543_;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_544_ = v___x_553_;
v___y_545_ = v___x_555_;
goto v___jp_543_;
}
}
}
v___jp_556_:
{
uint8_t v___x_558_; uint8_t v___x_559_; uint8_t v___x_560_; 
v___x_558_ = l_Lean_Expr_Data_approxDepth(v_v_511_);
v___x_559_ = 0;
v___x_560_ = lean_uint8_dec_eq(v___x_558_, v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_r_567_; 
v___x_561_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__6));
v___x_562_ = lean_string_append(v_r_557_, v___x_561_);
v___x_563_ = lean_uint8_to_nat(v___x_558_);
v___x_564_ = l_Nat_reprFast(v___x_563_);
v___x_565_ = lean_string_append(v___x_562_, v___x_564_);
lean_dec_ref(v___x_564_);
v___x_566_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_567_ = lean_string_append(v___x_565_, v___x_566_);
v_r_550_ = v_r_567_;
goto v___jp_549_;
}
else
{
v_r_550_ = v_r_557_;
goto v___jp_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0___boxed(lean_object* v_v_583_, lean_object* v_prec_584_){
_start:
{
uint64_t v_v_boxed_585_; lean_object* v_res_586_; 
v_v_boxed_585_ = lean_unbox_uint64(v_v_583_);
lean_dec_ref(v_v_583_);
v_res_586_ = l_Lean_instReprData__1___lam__0(v_v_boxed_585_, v_prec_584_);
lean_dec(v_prec_584_);
return v_res_586_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId_default(void){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_box(0);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId(void){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = lean_box(0);
return v___x_590_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqFVarId_beq(lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = lean_name_eq(v_x_591_, v_x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
uint8_t v_res_596_; lean_object* v_r_597_; 
v_res_596_ = l_Lean_instBEqFVarId_beq(v_x_594_, v_x_595_);
lean_dec(v_x_595_);
lean_dec(v_x_594_);
v_r_597_ = lean_box(v_res_596_);
return v_r_597_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableFVarId_hash(lean_object* v_x_600_){
_start:
{
uint64_t v___x_601_; 
v___x_601_ = 0ULL;
if (lean_obj_tag(v_x_600_) == 0)
{
uint64_t v___x_602_; 
v___x_602_ = 8934034000889494153ULL;
return v___x_602_;
}
else
{
uint64_t v_hash_603_; uint64_t v___x_604_; 
v_hash_603_ = lean_ctor_get_uint64(v_x_600_, sizeof(void*)*2);
v___x_604_ = lean_uint64_mix_hash(v___x_601_, v_hash_603_);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object* v_x_605_){
_start:
{
uint64_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Lean_instHashableFVarId_hash(v_x_605_);
lean_dec(v_x_605_);
v_r_607_ = lean_box_uint64(v_res_606_);
return v_r_607_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_box(1);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet(void){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_box(1);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = lean_box(1);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet(void){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_box(1);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___aux__1(lean_object* v_e_617_){
_start:
{
lean_object* v___f_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___f_618_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_619_ = lean_box(1);
lean_inc(v_e_617_);
v___x_620_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___f_618_, v_e_617_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_box(0);
v___x_622_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_618_, v_e_617_, v___x_621_, v___x_619_);
return v___x_622_;
}
else
{
lean_dec(v_e_617_);
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object* v_k_623_, lean_object* v_v_624_, lean_object* v_t_625_){
_start:
{
if (lean_obj_tag(v_t_625_) == 0)
{
lean_object* v_size_626_; lean_object* v_k_627_; lean_object* v_v_628_; lean_object* v_l_629_; lean_object* v_r_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_910_; 
v_size_626_ = lean_ctor_get(v_t_625_, 0);
v_k_627_ = lean_ctor_get(v_t_625_, 1);
v_v_628_ = lean_ctor_get(v_t_625_, 2);
v_l_629_ = lean_ctor_get(v_t_625_, 3);
v_r_630_ = lean_ctor_get(v_t_625_, 4);
v_isSharedCheck_910_ = !lean_is_exclusive(v_t_625_);
if (v_isSharedCheck_910_ == 0)
{
v___x_632_ = v_t_625_;
v_isShared_633_ = v_isSharedCheck_910_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_r_630_);
lean_inc(v_l_629_);
lean_inc(v_v_628_);
lean_inc(v_k_627_);
lean_inc(v_size_626_);
lean_dec(v_t_625_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_910_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
uint8_t v___x_634_; 
v___x_634_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_623_, v_k_627_);
switch(v___x_634_)
{
case 0:
{
lean_object* v_impl_635_; lean_object* v___x_636_; 
lean_dec(v_size_626_);
v_impl_635_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_623_, v_v_624_, v_l_629_);
v___x_636_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_630_) == 0)
{
lean_object* v_size_637_; lean_object* v_size_638_; lean_object* v_k_639_; lean_object* v_v_640_; lean_object* v_l_641_; lean_object* v_r_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_size_637_ = lean_ctor_get(v_r_630_, 0);
v_size_638_ = lean_ctor_get(v_impl_635_, 0);
v_k_639_ = lean_ctor_get(v_impl_635_, 1);
v_v_640_ = lean_ctor_get(v_impl_635_, 2);
v_l_641_ = lean_ctor_get(v_impl_635_, 3);
v_r_642_ = lean_ctor_get(v_impl_635_, 4);
lean_inc(v_r_642_);
v___x_643_ = lean_unsigned_to_nat(3u);
v___x_644_ = lean_nat_mul(v___x_643_, v_size_637_);
v___x_645_ = lean_nat_dec_lt(v___x_644_, v_size_638_);
lean_dec(v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
lean_dec(v_r_642_);
v___x_646_ = lean_nat_add(v___x_636_, v_size_638_);
v___x_647_ = lean_nat_add(v___x_646_, v_size_637_);
lean_dec(v___x_646_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 3, v_impl_635_);
lean_ctor_set(v___x_632_, 0, v___x_647_);
v___x_649_ = v___x_632_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_impl_635_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v_r_630_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
else
{
lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_716_; 
lean_inc(v_l_641_);
lean_inc(v_v_640_);
lean_inc(v_k_639_);
lean_inc(v_size_638_);
v_isSharedCheck_716_ = !lean_is_exclusive(v_impl_635_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; lean_object* v_unused_718_; lean_object* v_unused_719_; lean_object* v_unused_720_; lean_object* v_unused_721_; 
v_unused_717_ = lean_ctor_get(v_impl_635_, 4);
lean_dec(v_unused_717_);
v_unused_718_ = lean_ctor_get(v_impl_635_, 3);
lean_dec(v_unused_718_);
v_unused_719_ = lean_ctor_get(v_impl_635_, 2);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_impl_635_, 1);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v_impl_635_, 0);
lean_dec(v_unused_721_);
v___x_652_ = v_impl_635_;
v_isShared_653_ = v_isSharedCheck_716_;
goto v_resetjp_651_;
}
else
{
lean_dec(v_impl_635_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_716_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_size_654_; lean_object* v_size_655_; lean_object* v_k_656_; lean_object* v_v_657_; lean_object* v_l_658_; lean_object* v_r_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v_size_654_ = lean_ctor_get(v_l_641_, 0);
v_size_655_ = lean_ctor_get(v_r_642_, 0);
v_k_656_ = lean_ctor_get(v_r_642_, 1);
v_v_657_ = lean_ctor_get(v_r_642_, 2);
v_l_658_ = lean_ctor_get(v_r_642_, 3);
v_r_659_ = lean_ctor_get(v_r_642_, 4);
v___x_660_ = lean_unsigned_to_nat(2u);
v___x_661_ = lean_nat_mul(v___x_660_, v_size_654_);
v___x_662_ = lean_nat_dec_lt(v_size_655_, v___x_661_);
lean_dec(v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_691_; 
lean_inc(v_r_659_);
lean_inc(v_l_658_);
lean_inc(v_v_657_);
lean_inc(v_k_656_);
v_isSharedCheck_691_ = !lean_is_exclusive(v_r_642_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; lean_object* v_unused_693_; lean_object* v_unused_694_; lean_object* v_unused_695_; lean_object* v_unused_696_; 
v_unused_692_ = lean_ctor_get(v_r_642_, 4);
lean_dec(v_unused_692_);
v_unused_693_ = lean_ctor_get(v_r_642_, 3);
lean_dec(v_unused_693_);
v_unused_694_ = lean_ctor_get(v_r_642_, 2);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v_r_642_, 1);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_r_642_, 0);
lean_dec(v_unused_696_);
v___x_664_ = v_r_642_;
v_isShared_665_ = v_isSharedCheck_691_;
goto v_resetjp_663_;
}
else
{
lean_dec(v_r_642_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_691_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___x_679_; lean_object* v___y_681_; 
v___x_666_ = lean_nat_add(v___x_636_, v_size_638_);
lean_dec(v_size_638_);
v___x_667_ = lean_nat_add(v___x_666_, v_size_637_);
lean_dec(v___x_666_);
v___x_679_ = lean_nat_add(v___x_636_, v_size_654_);
if (lean_obj_tag(v_l_658_) == 0)
{
lean_object* v_size_689_; 
v_size_689_ = lean_ctor_get(v_l_658_, 0);
lean_inc(v_size_689_);
v___y_681_ = v_size_689_;
goto v___jp_680_;
}
else
{
lean_object* v___x_690_; 
v___x_690_ = lean_unsigned_to_nat(0u);
v___y_681_ = v___x_690_;
goto v___jp_680_;
}
v___jp_668_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_nat_add(v___y_669_, v___y_671_);
lean_dec(v___y_671_);
lean_dec(v___y_669_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v_r_630_);
lean_ctor_set(v___x_664_, 3, v_r_659_);
lean_ctor_set(v___x_664_, 2, v_v_628_);
lean_ctor_set(v___x_664_, 1, v_k_627_);
lean_ctor_set(v___x_664_, 0, v___x_672_);
v___x_674_ = v___x_664_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v_r_659_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v_r_630_);
v___x_674_ = v_reuseFailAlloc_678_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_676_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 4, v___x_674_);
lean_ctor_set(v___x_652_, 3, v___y_670_);
lean_ctor_set(v___x_652_, 2, v_v_657_);
lean_ctor_set(v___x_652_, 1, v_k_656_);
lean_ctor_set(v___x_652_, 0, v___x_667_);
v___x_676_ = v___x_652_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_k_656_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_v_657_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v___y_670_);
lean_ctor_set(v_reuseFailAlloc_677_, 4, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
v___jp_680_:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = lean_nat_add(v___x_679_, v___y_681_);
lean_dec(v___y_681_);
lean_dec(v___x_679_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 4, v_l_658_);
lean_ctor_set(v___x_632_, 3, v_l_641_);
lean_ctor_set(v___x_632_, 2, v_v_640_);
lean_ctor_set(v___x_632_, 1, v_k_639_);
lean_ctor_set(v___x_632_, 0, v___x_682_);
v___x_684_ = v___x_632_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_k_639_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_v_640_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v_l_641_);
lean_ctor_set(v_reuseFailAlloc_688_, 4, v_l_658_);
v___x_684_ = v_reuseFailAlloc_688_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_685_; 
v___x_685_ = lean_nat_add(v___x_636_, v_size_637_);
if (lean_obj_tag(v_r_659_) == 0)
{
lean_object* v_size_686_; 
v_size_686_ = lean_ctor_get(v_r_659_, 0);
lean_inc(v_size_686_);
v___y_669_ = v___x_685_;
v___y_670_ = v___x_684_;
v___y_671_ = v_size_686_;
goto v___jp_668_;
}
else
{
lean_object* v___x_687_; 
v___x_687_ = lean_unsigned_to_nat(0u);
v___y_669_ = v___x_685_;
v___y_670_ = v___x_684_;
v___y_671_ = v___x_687_;
goto v___jp_668_;
}
}
}
}
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
lean_del_object(v___x_632_);
v___x_697_ = lean_nat_add(v___x_636_, v_size_638_);
lean_dec(v_size_638_);
v___x_698_ = lean_nat_add(v___x_697_, v_size_637_);
lean_dec(v___x_697_);
v___x_699_ = lean_nat_add(v___x_636_, v_size_637_);
v___x_700_ = lean_nat_add(v___x_699_, v_size_655_);
lean_dec(v___x_699_);
lean_inc_ref(v_r_630_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 4, v_r_630_);
lean_ctor_set(v___x_652_, 3, v_r_642_);
lean_ctor_set(v___x_652_, 2, v_v_628_);
lean_ctor_set(v___x_652_, 1, v_k_627_);
lean_ctor_set(v___x_652_, 0, v___x_700_);
v___x_702_ = v___x_652_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v_r_642_);
lean_ctor_set(v_reuseFailAlloc_715_, 4, v_r_630_);
v___x_702_ = v_reuseFailAlloc_715_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
v_isSharedCheck_709_ = !lean_is_exclusive(v_r_630_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; lean_object* v_unused_711_; lean_object* v_unused_712_; lean_object* v_unused_713_; lean_object* v_unused_714_; 
v_unused_710_ = lean_ctor_get(v_r_630_, 4);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_r_630_, 3);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_r_630_, 2);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_r_630_, 1);
lean_dec(v_unused_713_);
v_unused_714_ = lean_ctor_get(v_r_630_, 0);
lean_dec(v_unused_714_);
v___x_704_ = v_r_630_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_dec(v_r_630_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 4, v___x_702_);
lean_ctor_set(v___x_704_, 3, v_l_641_);
lean_ctor_set(v___x_704_, 2, v_v_640_);
lean_ctor_set(v___x_704_, 1, v_k_639_);
lean_ctor_set(v___x_704_, 0, v___x_698_);
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_k_639_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_v_640_);
lean_ctor_set(v_reuseFailAlloc_708_, 3, v_l_641_);
lean_ctor_set(v_reuseFailAlloc_708_, 4, v___x_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_722_; 
v_l_722_ = lean_ctor_get(v_impl_635_, 3);
if (lean_obj_tag(v_l_722_) == 0)
{
lean_object* v_r_723_; lean_object* v_k_724_; lean_object* v_v_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_736_; 
lean_inc_ref(v_l_722_);
v_r_723_ = lean_ctor_get(v_impl_635_, 4);
v_k_724_ = lean_ctor_get(v_impl_635_, 1);
v_v_725_ = lean_ctor_get(v_impl_635_, 2);
v_isSharedCheck_736_ = !lean_is_exclusive(v_impl_635_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; lean_object* v_unused_738_; 
v_unused_737_ = lean_ctor_get(v_impl_635_, 3);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v_impl_635_, 0);
lean_dec(v_unused_738_);
v___x_727_ = v_impl_635_;
v_isShared_728_ = v_isSharedCheck_736_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_r_723_);
lean_inc(v_v_725_);
lean_inc(v_k_724_);
lean_dec(v_impl_635_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_736_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_723_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 3, v_r_723_);
lean_ctor_set(v___x_727_, 2, v_v_628_);
lean_ctor_set(v___x_727_, 1, v_k_627_);
lean_ctor_set(v___x_727_, 0, v___x_636_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_735_, 3, v_r_723_);
lean_ctor_set(v_reuseFailAlloc_735_, 4, v_r_723_);
v___x_731_ = v_reuseFailAlloc_735_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_733_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 4, v___x_731_);
lean_ctor_set(v___x_632_, 3, v_l_722_);
lean_ctor_set(v___x_632_, 2, v_v_725_);
lean_ctor_set(v___x_632_, 1, v_k_724_);
lean_ctor_set(v___x_632_, 0, v___x_729_);
v___x_733_ = v___x_632_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_k_724_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_v_725_);
lean_ctor_set(v_reuseFailAlloc_734_, 3, v_l_722_);
lean_ctor_set(v_reuseFailAlloc_734_, 4, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
else
{
lean_object* v_r_739_; 
v_r_739_ = lean_ctor_get(v_impl_635_, 4);
lean_inc(v_r_739_);
if (lean_obj_tag(v_r_739_) == 0)
{
lean_object* v_k_740_; lean_object* v_v_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_764_; 
lean_inc(v_l_722_);
v_k_740_ = lean_ctor_get(v_impl_635_, 1);
v_v_741_ = lean_ctor_get(v_impl_635_, 2);
v_isSharedCheck_764_ = !lean_is_exclusive(v_impl_635_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; lean_object* v_unused_766_; lean_object* v_unused_767_; 
v_unused_765_ = lean_ctor_get(v_impl_635_, 4);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_impl_635_, 3);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_impl_635_, 0);
lean_dec(v_unused_767_);
v___x_743_ = v_impl_635_;
v_isShared_744_ = v_isSharedCheck_764_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_v_741_);
lean_inc(v_k_740_);
lean_dec(v_impl_635_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_764_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v_k_745_; lean_object* v_v_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_760_; 
v_k_745_ = lean_ctor_get(v_r_739_, 1);
v_v_746_ = lean_ctor_get(v_r_739_, 2);
v_isSharedCheck_760_ = !lean_is_exclusive(v_r_739_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; lean_object* v_unused_762_; lean_object* v_unused_763_; 
v_unused_761_ = lean_ctor_get(v_r_739_, 4);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_r_739_, 3);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_r_739_, 0);
lean_dec(v_unused_763_);
v___x_748_ = v_r_739_;
v_isShared_749_ = v_isSharedCheck_760_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_v_746_);
lean_inc(v_k_745_);
lean_dec(v_r_739_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_760_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_unsigned_to_nat(3u);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 4, v_l_722_);
lean_ctor_set(v___x_748_, 3, v_l_722_);
lean_ctor_set(v___x_748_, 2, v_v_741_);
lean_ctor_set(v___x_748_, 1, v_k_740_);
lean_ctor_set(v___x_748_, 0, v___x_636_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_k_740_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_v_741_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_l_722_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_l_722_);
v___x_752_ = v_reuseFailAlloc_759_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 4, v_l_722_);
lean_ctor_set(v___x_743_, 2, v_v_628_);
lean_ctor_set(v___x_743_, 1, v_k_627_);
lean_ctor_set(v___x_743_, 0, v___x_636_);
v___x_754_ = v___x_743_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_l_722_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_l_722_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_756_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 4, v___x_754_);
lean_ctor_set(v___x_632_, 3, v___x_752_);
lean_ctor_set(v___x_632_, 2, v_v_746_);
lean_ctor_set(v___x_632_, 1, v_k_745_);
lean_ctor_set(v___x_632_, 0, v___x_750_);
v___x_756_ = v___x_632_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_k_745_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_v_746_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_757_, 4, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
else
{
lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_768_ = lean_unsigned_to_nat(2u);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 4, v_r_739_);
lean_ctor_set(v___x_632_, 3, v_impl_635_);
lean_ctor_set(v___x_632_, 0, v___x_768_);
v___x_770_ = v___x_632_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_impl_635_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_r_739_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
case 1:
{
lean_object* v___x_773_; 
lean_dec(v_v_628_);
lean_dec(v_k_627_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 2, v_v_624_);
lean_ctor_set(v___x_632_, 1, v_k_623_);
v___x_773_ = v___x_632_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_size_626_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_k_623_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_v_624_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_l_629_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_r_630_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
default: 
{
lean_object* v_impl_775_; lean_object* v___x_776_; 
lean_dec(v_size_626_);
v_impl_775_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_623_, v_v_624_, v_r_630_);
v___x_776_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_629_) == 0)
{
lean_object* v_size_777_; lean_object* v_size_778_; lean_object* v_k_779_; lean_object* v_v_780_; lean_object* v_l_781_; lean_object* v_r_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_size_777_ = lean_ctor_get(v_l_629_, 0);
v_size_778_ = lean_ctor_get(v_impl_775_, 0);
v_k_779_ = lean_ctor_get(v_impl_775_, 1);
v_v_780_ = lean_ctor_get(v_impl_775_, 2);
v_l_781_ = lean_ctor_get(v_impl_775_, 3);
lean_inc(v_l_781_);
v_r_782_ = lean_ctor_get(v_impl_775_, 4);
v___x_783_ = lean_unsigned_to_nat(3u);
v___x_784_ = lean_nat_mul(v___x_783_, v_size_777_);
v___x_785_ = lean_nat_dec_lt(v___x_784_, v_size_778_);
lean_dec(v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
lean_dec(v_l_781_);
v___x_786_ = lean_nat_add(v___x_776_, v_size_777_);
v___x_787_ = lean_nat_add(v___x_786_, v_size_778_);
lean_dec(v___x_786_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 4, v_impl_775_);
lean_ctor_set(v___x_632_, 0, v___x_787_);
v___x_789_ = v___x_632_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_790_, 3, v_l_629_);
lean_ctor_set(v_reuseFailAlloc_790_, 4, v_impl_775_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
else
{
lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_854_; 
lean_inc(v_r_782_);
lean_inc(v_v_780_);
lean_inc(v_k_779_);
lean_inc(v_size_778_);
v_isSharedCheck_854_ = !lean_is_exclusive(v_impl_775_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; lean_object* v_unused_856_; lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; 
v_unused_855_ = lean_ctor_get(v_impl_775_, 4);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v_impl_775_, 3);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_impl_775_, 2);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_impl_775_, 1);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_impl_775_, 0);
lean_dec(v_unused_859_);
v___x_792_ = v_impl_775_;
v_isShared_793_ = v_isSharedCheck_854_;
goto v_resetjp_791_;
}
else
{
lean_dec(v_impl_775_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_854_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v_size_794_; lean_object* v_k_795_; lean_object* v_v_796_; lean_object* v_l_797_; lean_object* v_r_798_; lean_object* v_size_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_size_794_ = lean_ctor_get(v_l_781_, 0);
v_k_795_ = lean_ctor_get(v_l_781_, 1);
v_v_796_ = lean_ctor_get(v_l_781_, 2);
v_l_797_ = lean_ctor_get(v_l_781_, 3);
v_r_798_ = lean_ctor_get(v_l_781_, 4);
v_size_799_ = lean_ctor_get(v_r_782_, 0);
v___x_800_ = lean_unsigned_to_nat(2u);
v___x_801_ = lean_nat_mul(v___x_800_, v_size_799_);
v___x_802_ = lean_nat_dec_lt(v_size_794_, v___x_801_);
lean_dec(v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_830_; 
lean_inc(v_r_798_);
lean_inc(v_l_797_);
lean_inc(v_v_796_);
lean_inc(v_k_795_);
v_isSharedCheck_830_ = !lean_is_exclusive(v_l_781_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; lean_object* v_unused_832_; lean_object* v_unused_833_; lean_object* v_unused_834_; lean_object* v_unused_835_; 
v_unused_831_ = lean_ctor_get(v_l_781_, 4);
lean_dec(v_unused_831_);
v_unused_832_ = lean_ctor_get(v_l_781_, 3);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_l_781_, 2);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_l_781_, 1);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_l_781_, 0);
lean_dec(v_unused_835_);
v___x_804_ = v_l_781_;
v_isShared_805_ = v_isSharedCheck_830_;
goto v_resetjp_803_;
}
else
{
lean_dec(v_l_781_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_830_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_820_; 
v___x_806_ = lean_nat_add(v___x_776_, v_size_777_);
v___x_807_ = lean_nat_add(v___x_806_, v_size_778_);
lean_dec(v_size_778_);
if (lean_obj_tag(v_l_797_) == 0)
{
lean_object* v_size_828_; 
v_size_828_ = lean_ctor_get(v_l_797_, 0);
lean_inc(v_size_828_);
v___y_820_ = v_size_828_;
goto v___jp_819_;
}
else
{
lean_object* v___x_829_; 
v___x_829_ = lean_unsigned_to_nat(0u);
v___y_820_ = v___x_829_;
goto v___jp_819_;
}
v___jp_808_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_nat_add(v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec(v___y_810_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 4, v_r_782_);
lean_ctor_set(v___x_804_, 3, v_r_798_);
lean_ctor_set(v___x_804_, 2, v_v_780_);
lean_ctor_set(v___x_804_, 1, v_k_779_);
lean_ctor_set(v___x_804_, 0, v___x_812_);
v___x_814_ = v___x_804_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_k_779_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_v_780_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v_r_798_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v_r_782_);
v___x_814_ = v_reuseFailAlloc_818_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_816_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 4, v___x_814_);
lean_ctor_set(v___x_792_, 3, v___y_809_);
lean_ctor_set(v___x_792_, 2, v_v_796_);
lean_ctor_set(v___x_792_, 1, v_k_795_);
lean_ctor_set(v___x_792_, 0, v___x_807_);
v___x_816_ = v___x_792_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_k_795_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_v_796_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v___y_809_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
v___jp_819_:
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = lean_nat_add(v___x_806_, v___y_820_);
lean_dec(v___y_820_);
lean_dec(v___x_806_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 4, v_l_797_);
lean_ctor_set(v___x_632_, 0, v___x_821_);
v___x_823_ = v___x_632_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_827_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_827_, 3, v_l_629_);
lean_ctor_set(v_reuseFailAlloc_827_, 4, v_l_797_);
v___x_823_ = v_reuseFailAlloc_827_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_824_; 
v___x_824_ = lean_nat_add(v___x_776_, v_size_799_);
if (lean_obj_tag(v_r_798_) == 0)
{
lean_object* v_size_825_; 
v_size_825_ = lean_ctor_get(v_r_798_, 0);
lean_inc(v_size_825_);
v___y_809_ = v___x_823_;
v___y_810_ = v___x_824_;
v___y_811_ = v_size_825_;
goto v___jp_808_;
}
else
{
lean_object* v___x_826_; 
v___x_826_ = lean_unsigned_to_nat(0u);
v___y_809_ = v___x_823_;
v___y_810_ = v___x_824_;
v___y_811_ = v___x_826_;
goto v___jp_808_;
}
}
}
}
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
lean_del_object(v___x_632_);
v___x_836_ = lean_nat_add(v___x_776_, v_size_777_);
v___x_837_ = lean_nat_add(v___x_836_, v_size_778_);
lean_dec(v_size_778_);
v___x_838_ = lean_nat_add(v___x_836_, v_size_794_);
lean_dec(v___x_836_);
lean_inc_ref(v_l_629_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 4, v_l_781_);
lean_ctor_set(v___x_792_, 3, v_l_629_);
lean_ctor_set(v___x_792_, 2, v_v_628_);
lean_ctor_set(v___x_792_, 1, v_k_627_);
lean_ctor_set(v___x_792_, 0, v___x_838_);
v___x_840_ = v___x_792_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_853_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_853_, 3, v_l_629_);
lean_ctor_set(v_reuseFailAlloc_853_, 4, v_l_781_);
v___x_840_ = v_reuseFailAlloc_853_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
v_isSharedCheck_847_ = !lean_is_exclusive(v_l_629_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; lean_object* v_unused_849_; lean_object* v_unused_850_; lean_object* v_unused_851_; lean_object* v_unused_852_; 
v_unused_848_ = lean_ctor_get(v_l_629_, 4);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_l_629_, 3);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v_l_629_, 2);
lean_dec(v_unused_850_);
v_unused_851_ = lean_ctor_get(v_l_629_, 1);
lean_dec(v_unused_851_);
v_unused_852_ = lean_ctor_get(v_l_629_, 0);
lean_dec(v_unused_852_);
v___x_842_ = v_l_629_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_dec(v_l_629_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 4, v_r_782_);
lean_ctor_set(v___x_842_, 3, v___x_840_);
lean_ctor_set(v___x_842_, 2, v_v_780_);
lean_ctor_set(v___x_842_, 1, v_k_779_);
lean_ctor_set(v___x_842_, 0, v___x_837_);
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_k_779_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v_v_780_);
lean_ctor_set(v_reuseFailAlloc_846_, 3, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_846_, 4, v_r_782_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_860_; 
v_l_860_ = lean_ctor_get(v_impl_775_, 3);
lean_inc(v_l_860_);
if (lean_obj_tag(v_l_860_) == 0)
{
lean_object* v_r_861_; lean_object* v_k_862_; lean_object* v_v_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_886_; 
v_r_861_ = lean_ctor_get(v_impl_775_, 4);
v_k_862_ = lean_ctor_get(v_impl_775_, 1);
v_v_863_ = lean_ctor_get(v_impl_775_, 2);
v_isSharedCheck_886_ = !lean_is_exclusive(v_impl_775_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; lean_object* v_unused_888_; 
v_unused_887_ = lean_ctor_get(v_impl_775_, 3);
lean_dec(v_unused_887_);
v_unused_888_ = lean_ctor_get(v_impl_775_, 0);
lean_dec(v_unused_888_);
v___x_865_ = v_impl_775_;
v_isShared_866_ = v_isSharedCheck_886_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_r_861_);
lean_inc(v_v_863_);
lean_inc(v_k_862_);
lean_dec(v_impl_775_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_886_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_k_867_; lean_object* v_v_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_882_; 
v_k_867_ = lean_ctor_get(v_l_860_, 1);
v_v_868_ = lean_ctor_get(v_l_860_, 2);
v_isSharedCheck_882_ = !lean_is_exclusive(v_l_860_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; lean_object* v_unused_884_; lean_object* v_unused_885_; 
v_unused_883_ = lean_ctor_get(v_l_860_, 4);
lean_dec(v_unused_883_);
v_unused_884_ = lean_ctor_get(v_l_860_, 3);
lean_dec(v_unused_884_);
v_unused_885_ = lean_ctor_get(v_l_860_, 0);
lean_dec(v_unused_885_);
v___x_870_ = v_l_860_;
v_isShared_871_ = v_isSharedCheck_882_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_v_868_);
lean_inc(v_k_867_);
lean_dec(v_l_860_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_882_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_861_, 2);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 4, v_r_861_);
lean_ctor_set(v___x_870_, 3, v_r_861_);
lean_ctor_set(v___x_870_, 2, v_v_628_);
lean_ctor_set(v___x_870_, 1, v_k_627_);
lean_ctor_set(v___x_870_, 0, v___x_776_);
v___x_874_ = v___x_870_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v_r_861_);
lean_ctor_set(v_reuseFailAlloc_881_, 4, v_r_861_);
v___x_874_ = v_reuseFailAlloc_881_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_876_; 
lean_inc(v_r_861_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 3, v_r_861_);
lean_ctor_set(v___x_865_, 0, v___x_776_);
v___x_876_ = v___x_865_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_k_862_);
lean_ctor_set(v_reuseFailAlloc_880_, 2, v_v_863_);
lean_ctor_set(v_reuseFailAlloc_880_, 3, v_r_861_);
lean_ctor_set(v_reuseFailAlloc_880_, 4, v_r_861_);
v___x_876_ = v_reuseFailAlloc_880_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_878_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 4, v___x_876_);
lean_ctor_set(v___x_632_, 3, v___x_874_);
lean_ctor_set(v___x_632_, 2, v_v_868_);
lean_ctor_set(v___x_632_, 1, v_k_867_);
lean_ctor_set(v___x_632_, 0, v___x_872_);
v___x_878_ = v___x_632_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_k_867_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_v_868_);
lean_ctor_set(v_reuseFailAlloc_879_, 3, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_879_, 4, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
}
else
{
lean_object* v_r_889_; 
v_r_889_ = lean_ctor_get(v_impl_775_, 4);
lean_inc(v_r_889_);
if (lean_obj_tag(v_r_889_) == 0)
{
lean_object* v_k_890_; lean_object* v_v_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_902_; 
v_k_890_ = lean_ctor_get(v_impl_775_, 1);
v_v_891_ = lean_ctor_get(v_impl_775_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v_impl_775_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; lean_object* v_unused_904_; lean_object* v_unused_905_; 
v_unused_903_ = lean_ctor_get(v_impl_775_, 4);
lean_dec(v_unused_903_);
v_unused_904_ = lean_ctor_get(v_impl_775_, 3);
lean_dec(v_unused_904_);
v_unused_905_ = lean_ctor_get(v_impl_775_, 0);
lean_dec(v_unused_905_);
v___x_893_ = v_impl_775_;
v_isShared_894_ = v_isSharedCheck_902_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_v_891_);
lean_inc(v_k_890_);
lean_dec(v_impl_775_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_902_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = lean_unsigned_to_nat(3u);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 4, v_l_860_);
lean_ctor_set(v___x_893_, 2, v_v_628_);
lean_ctor_set(v___x_893_, 1, v_k_627_);
lean_ctor_set(v___x_893_, 0, v___x_776_);
v___x_897_ = v___x_893_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v_l_860_);
lean_ctor_set(v_reuseFailAlloc_901_, 4, v_l_860_);
v___x_897_ = v_reuseFailAlloc_901_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 4, v_r_889_);
lean_ctor_set(v___x_632_, 3, v___x_897_);
lean_ctor_set(v___x_632_, 2, v_v_891_);
lean_ctor_set(v___x_632_, 1, v_k_890_);
lean_ctor_set(v___x_632_, 0, v___x_895_);
v___x_899_ = v___x_632_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_900_, 3, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_900_, 4, v_r_889_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_906_ = lean_unsigned_to_nat(2u);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 4, v_impl_775_);
lean_ctor_set(v___x_632_, 3, v_r_889_);
lean_ctor_set(v___x_632_, 0, v___x_906_);
v___x_908_ = v___x_632_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_909_, 3, v_r_889_);
lean_ctor_set(v_reuseFailAlloc_909_, 4, v_impl_775_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
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
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v_k_623_);
lean_ctor_set(v___x_912_, 2, v_v_624_);
lean_ctor_set(v___x_912_, 3, v_t_625_);
lean_ctor_set(v___x_912_, 4, v_t_625_);
return v___x_912_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(lean_object* v_k_913_, lean_object* v_t_914_){
_start:
{
if (lean_obj_tag(v_t_914_) == 0)
{
lean_object* v_k_915_; lean_object* v_l_916_; lean_object* v_r_917_; uint8_t v___x_918_; 
v_k_915_ = lean_ctor_get(v_t_914_, 1);
v_l_916_ = lean_ctor_get(v_t_914_, 3);
v_r_917_ = lean_ctor_get(v_t_914_, 4);
v___x_918_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_913_, v_k_915_);
switch(v___x_918_)
{
case 0:
{
v_t_914_ = v_l_916_;
goto _start;
}
case 1:
{
uint8_t v___x_920_; 
v___x_920_ = 1;
return v___x_920_;
}
default: 
{
v_t_914_ = v_r_917_;
goto _start;
}
}
}
else
{
uint8_t v___x_922_; 
v___x_922_ = 0;
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg___boxed(lean_object* v_k_923_, lean_object* v_t_924_){
_start:
{
uint8_t v_res_925_; lean_object* v_r_926_; 
v_res_925_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_923_, v_t_924_);
lean_dec(v_t_924_);
lean_dec(v_k_923_);
v_r_926_ = lean_box(v_res_925_);
return v_r_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object* v___y_927_){
_start:
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = lean_box(1);
v___x_929_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v___y_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_box(0);
v___x_931_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___y_927_, v___x_930_, v___x_928_);
return v___x_931_;
}
else
{
lean_dec(v___y_927_);
return v___x_928_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(lean_object* v_00_u03b2_934_, lean_object* v_k_935_, lean_object* v_t_936_){
_start:
{
uint8_t v___x_937_; 
v___x_937_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_935_, v_t_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___boxed(lean_object* v_00_u03b2_938_, lean_object* v_k_939_, lean_object* v_t_940_){
_start:
{
uint8_t v_res_941_; lean_object* v_r_942_; 
v_res_941_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(v_00_u03b2_938_, v_k_939_, v_t_940_);
lean_dec(v_t_940_);
lean_dec(v_k_939_);
v_r_942_ = lean_box(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1(lean_object* v_00_u03b2_943_, lean_object* v_k_944_, lean_object* v_v_945_, lean_object* v_t_946_, lean_object* v_hl_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_944_, v_v_945_, v_t_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_949_, lean_object* v_a_950_, lean_object* v_b_951_, lean_object* v_c_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = lean_apply_2(v_f_949_, v_a_950_, v_c_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_954_, lean_object* v_____do__lift_955_){
_start:
{
lean_object* v_a_956_; lean_object* v___x_957_; 
v_a_956_ = lean_ctor_get(v_____do__lift_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref(v_____do__lift_955_);
v___x_957_ = lean_apply_2(v_toPure_954_, lean_box(0), v_a_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg(lean_object* v_inst_958_, lean_object* v_m_959_, lean_object* v_init_960_, lean_object* v_f_961_){
_start:
{
lean_object* v_toApplicative_962_; lean_object* v_toBind_963_; lean_object* v_toPure_964_; lean_object* v___f_965_; lean_object* v___x_966_; lean_object* v___f_967_; lean_object* v___x_968_; 
v_toApplicative_962_ = lean_ctor_get(v_inst_958_, 0);
v_toBind_963_ = lean_ctor_get(v_inst_958_, 1);
lean_inc(v_toBind_963_);
v_toPure_964_ = lean_ctor_get(v_toApplicative_962_, 1);
lean_inc(v_toPure_964_);
v___f_965_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_965_, 0, v_f_961_);
v___x_966_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_958_, v___f_965_, v_init_960_, v_m_959_);
v___f_967_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_967_, 0, v_toPure_964_);
v___x_968_ = lean_apply_4(v_toBind_963_, lean_box(0), lean_box(0), v___x_966_, v___f_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1(lean_object* v_m_969_, lean_object* v_inst_970_, lean_object* v_00_u03b2_971_, lean_object* v_m_972_, lean_object* v_init_973_, lean_object* v_f_974_){
_start:
{
lean_object* v_toApplicative_975_; lean_object* v_toBind_976_; lean_object* v_toPure_977_; lean_object* v___f_978_; lean_object* v___x_979_; lean_object* v___f_980_; lean_object* v___x_981_; 
v_toApplicative_975_ = lean_ctor_get(v_inst_970_, 0);
v_toBind_976_ = lean_ctor_get(v_inst_970_, 1);
lean_inc(v_toBind_976_);
v_toPure_977_ = lean_ctor_get(v_toApplicative_975_, 1);
lean_inc(v_toPure_977_);
v___f_978_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_978_, 0, v_f_974_);
v___x_979_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_970_, v___f_978_, v_init_973_, v_m_972_);
v___f_980_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_980_, 0, v_toPure_977_);
v___x_981_ = lean_apply_4(v_toBind_976_, lean_box(0), lean_box(0), v___x_979_, v___f_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___redArg(lean_object* v_inst_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_983_, 0, lean_box(0));
lean_closure_set(v___x_983_, 1, v_inst_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad(lean_object* v_m_984_, lean_object* v_inst_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_986_, 0, lean_box(0));
lean_closure_set(v___x_986_, 1, v_inst_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object* v_s_987_, lean_object* v_fvarId_988_){
_start:
{
uint8_t v___x_989_; 
v___x_989_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_fvarId_988_, v_s_987_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_box(0);
v___x_991_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_988_, v___x_990_, v_s_987_);
return v___x_991_;
}
else
{
lean_dec(v_fvarId_988_);
return v_s_987_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(lean_object* v_init_992_, lean_object* v_x_993_){
_start:
{
if (lean_obj_tag(v_x_993_) == 0)
{
lean_object* v_k_994_; lean_object* v_l_995_; lean_object* v_r_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_k_994_ = lean_ctor_get(v_x_993_, 1);
lean_inc(v_k_994_);
v_l_995_ = lean_ctor_get(v_x_993_, 3);
lean_inc(v_l_995_);
v_r_996_ = lean_ctor_get(v_x_993_, 4);
lean_inc(v_r_996_);
lean_dec_ref_known(v_x_993_, 5);
v___x_997_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_992_, v_l_995_);
v___x_998_ = l_Lean_FVarIdSet_insert(v___x_997_, v_k_994_);
v_init_992_ = v___x_998_;
v_x_993_ = v_r_996_;
goto _start;
}
else
{
return v_init_992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_union(lean_object* v_vs_u2081_1000_, lean_object* v_vs_u2082_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_vs_u2082_1001_, v_vs_u2081_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0(lean_object* v_init_1003_, lean_object* v_t_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_1003_, v_t_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList(lean_object* v_l_1006_){
_start:
{
lean_object* v___f_1007_; lean_object* v___x_1008_; 
v___f_1007_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1008_ = l_Std_TreeSet_ofList___redArg(v_l_1006_, v___f_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList___boxed(lean_object* v_l_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_FVarIdSet_ofList(v_l_1009_);
lean_dec(v_l_1009_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object* v_l_1011_){
_start:
{
lean_object* v___f_1012_; lean_object* v___x_1013_; 
v___f_1012_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1013_ = l_Std_TreeSet_ofArray___redArg(v_l_1011_, v___f_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object* v_l_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_FVarIdSet_ofArray(v_l_1014_);
lean_dec_ref(v_l_1014_);
return v_res_1015_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = lean_box(0);
v___x_1017_ = lean_unsigned_to_nat(16u);
v___x_1018_ = lean_mk_array(v___x_1017_, v___x_1016_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0);
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___x_1019_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet(void){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet(void){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object* v_s_1026_, lean_object* v_fvarId_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1027_, v_a_1028_, v_s_1026_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object* v_00_u03b1_1030_, lean_object* v_s_1031_, lean_object* v_fvarId_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1032_, v_a_1033_, v_s_1031_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_box(1);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg();
return v_res_1038_;
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
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg(){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_box(1);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg___boxed(lean_object* v___dummy_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_instEmptyCollectionFVarIdMap___redArg();
return v_res_1044_;
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg(){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_box(1);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg___boxed(lean_object* v___dummy_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_instInhabitedFVarIdMap___redArg();
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* v_00_u03b1_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_box(1);
return v___x_1052_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId_default(void){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_box(0);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId(void){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_box(0);
return v___x_1054_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMVarId_beq(lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_name_eq(v_x_1055_, v_x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object* v_x_1058_, lean_object* v_x_1059_){
_start:
{
uint8_t v_res_1060_; lean_object* v_r_1061_; 
v_res_1060_ = l_Lean_instBEqMVarId_beq(v_x_1058_, v_x_1059_);
lean_dec(v_x_1059_);
lean_dec(v_x_1058_);
v_r_1061_ = lean_box(v_res_1060_);
return v_r_1061_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableMVarId_hash(lean_object* v_x_1064_){
_start:
{
uint64_t v___x_1065_; 
v___x_1065_ = 0ULL;
if (lean_obj_tag(v_x_1064_) == 0)
{
uint64_t v___x_1066_; 
v___x_1066_ = 8934034000889494153ULL;
return v___x_1066_;
}
else
{
uint64_t v_hash_1067_; uint64_t v___x_1068_; 
v_hash_1067_ = lean_ctor_get_uint64(v_x_1064_, sizeof(void*)*2);
v___x_1068_ = lean_uint64_mix_hash(v___x_1065_, v_hash_1067_);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object* v_x_1069_){
_start:
{
uint64_t v_res_1070_; lean_object* v_r_1071_; 
v_res_1070_ = l_Lean_instHashableMVarId_hash(v_x_1069_);
lean_dec(v_x_1069_);
v_r_1071_ = lean_box_uint64(v_res_1070_);
return v_r_1071_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_box(1);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet(void){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_box(1);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_box(1);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet(void){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_box(1);
return v___x_1078_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object* v_k_1079_, lean_object* v_t_1080_){
_start:
{
if (lean_obj_tag(v_t_1080_) == 0)
{
lean_object* v_k_1081_; lean_object* v_l_1082_; lean_object* v_r_1083_; uint8_t v___x_1084_; 
v_k_1081_ = lean_ctor_get(v_t_1080_, 1);
v_l_1082_ = lean_ctor_get(v_t_1080_, 3);
v_r_1083_ = lean_ctor_get(v_t_1080_, 4);
v___x_1084_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1079_, v_k_1081_);
switch(v___x_1084_)
{
case 0:
{
v_t_1080_ = v_l_1082_;
goto _start;
}
case 1:
{
uint8_t v___x_1086_; 
v___x_1086_ = 1;
return v___x_1086_;
}
default: 
{
v_t_1080_ = v_r_1083_;
goto _start;
}
}
}
else
{
uint8_t v___x_1088_; 
v___x_1088_ = 0;
return v___x_1088_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object* v_k_1089_, lean_object* v_t_1090_){
_start:
{
uint8_t v_res_1091_; lean_object* v_r_1092_; 
v_res_1091_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1089_, v_t_1090_);
lean_dec(v_t_1090_);
lean_dec(v_k_1089_);
v_r_1092_ = lean_box(v_res_1091_);
return v_r_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object* v_k_1093_, lean_object* v_v_1094_, lean_object* v_t_1095_){
_start:
{
if (lean_obj_tag(v_t_1095_) == 0)
{
lean_object* v_size_1096_; lean_object* v_k_1097_; lean_object* v_v_1098_; lean_object* v_l_1099_; lean_object* v_r_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1380_; 
v_size_1096_ = lean_ctor_get(v_t_1095_, 0);
v_k_1097_ = lean_ctor_get(v_t_1095_, 1);
v_v_1098_ = lean_ctor_get(v_t_1095_, 2);
v_l_1099_ = lean_ctor_get(v_t_1095_, 3);
v_r_1100_ = lean_ctor_get(v_t_1095_, 4);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_t_1095_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1102_ = v_t_1095_;
v_isShared_1103_ = v_isSharedCheck_1380_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_r_1100_);
lean_inc(v_l_1099_);
lean_inc(v_v_1098_);
lean_inc(v_k_1097_);
lean_inc(v_size_1096_);
lean_dec(v_t_1095_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1380_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
uint8_t v___x_1104_; 
v___x_1104_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1093_, v_k_1097_);
switch(v___x_1104_)
{
case 0:
{
lean_object* v_impl_1105_; lean_object* v___x_1106_; 
lean_dec(v_size_1096_);
v_impl_1105_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1093_, v_v_1094_, v_l_1099_);
v___x_1106_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1100_) == 0)
{
lean_object* v_size_1107_; lean_object* v_size_1108_; lean_object* v_k_1109_; lean_object* v_v_1110_; lean_object* v_l_1111_; lean_object* v_r_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_size_1107_ = lean_ctor_get(v_r_1100_, 0);
v_size_1108_ = lean_ctor_get(v_impl_1105_, 0);
v_k_1109_ = lean_ctor_get(v_impl_1105_, 1);
v_v_1110_ = lean_ctor_get(v_impl_1105_, 2);
v_l_1111_ = lean_ctor_get(v_impl_1105_, 3);
v_r_1112_ = lean_ctor_get(v_impl_1105_, 4);
lean_inc(v_r_1112_);
v___x_1113_ = lean_unsigned_to_nat(3u);
v___x_1114_ = lean_nat_mul(v___x_1113_, v_size_1107_);
v___x_1115_ = lean_nat_dec_lt(v___x_1114_, v_size_1108_);
lean_dec(v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
lean_dec(v_r_1112_);
v___x_1116_ = lean_nat_add(v___x_1106_, v_size_1108_);
v___x_1117_ = lean_nat_add(v___x_1116_, v_size_1107_);
lean_dec(v___x_1116_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 3, v_impl_1105_);
lean_ctor_set(v___x_1102_, 0, v___x_1117_);
v___x_1119_ = v___x_1102_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_impl_1105_);
lean_ctor_set(v_reuseFailAlloc_1120_, 4, v_r_1100_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
else
{
lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1186_; 
lean_inc(v_l_1111_);
lean_inc(v_v_1110_);
lean_inc(v_k_1109_);
lean_inc(v_size_1108_);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_impl_1105_);
if (v_isSharedCheck_1186_ == 0)
{
lean_object* v_unused_1187_; lean_object* v_unused_1188_; lean_object* v_unused_1189_; lean_object* v_unused_1190_; lean_object* v_unused_1191_; 
v_unused_1187_ = lean_ctor_get(v_impl_1105_, 4);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_impl_1105_, 3);
lean_dec(v_unused_1188_);
v_unused_1189_ = lean_ctor_get(v_impl_1105_, 2);
lean_dec(v_unused_1189_);
v_unused_1190_ = lean_ctor_get(v_impl_1105_, 1);
lean_dec(v_unused_1190_);
v_unused_1191_ = lean_ctor_get(v_impl_1105_, 0);
lean_dec(v_unused_1191_);
v___x_1122_ = v_impl_1105_;
v_isShared_1123_ = v_isSharedCheck_1186_;
goto v_resetjp_1121_;
}
else
{
lean_dec(v_impl_1105_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1186_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v_size_1124_; lean_object* v_size_1125_; lean_object* v_k_1126_; lean_object* v_v_1127_; lean_object* v_l_1128_; lean_object* v_r_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_size_1124_ = lean_ctor_get(v_l_1111_, 0);
v_size_1125_ = lean_ctor_get(v_r_1112_, 0);
v_k_1126_ = lean_ctor_get(v_r_1112_, 1);
v_v_1127_ = lean_ctor_get(v_r_1112_, 2);
v_l_1128_ = lean_ctor_get(v_r_1112_, 3);
v_r_1129_ = lean_ctor_get(v_r_1112_, 4);
v___x_1130_ = lean_unsigned_to_nat(2u);
v___x_1131_ = lean_nat_mul(v___x_1130_, v_size_1124_);
v___x_1132_ = lean_nat_dec_lt(v_size_1125_, v___x_1131_);
lean_dec(v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1161_; 
lean_inc(v_r_1129_);
lean_inc(v_l_1128_);
lean_inc(v_v_1127_);
lean_inc(v_k_1126_);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_r_1112_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; lean_object* v_unused_1163_; lean_object* v_unused_1164_; lean_object* v_unused_1165_; lean_object* v_unused_1166_; 
v_unused_1162_ = lean_ctor_get(v_r_1112_, 4);
lean_dec(v_unused_1162_);
v_unused_1163_ = lean_ctor_get(v_r_1112_, 3);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_r_1112_, 2);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_r_1112_, 1);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_r_1112_, 0);
lean_dec(v_unused_1166_);
v___x_1134_ = v_r_1112_;
v_isShared_1135_ = v_isSharedCheck_1161_;
goto v_resetjp_1133_;
}
else
{
lean_dec(v_r_1112_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1161_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___x_1149_; lean_object* v___y_1151_; 
v___x_1136_ = lean_nat_add(v___x_1106_, v_size_1108_);
lean_dec(v_size_1108_);
v___x_1137_ = lean_nat_add(v___x_1136_, v_size_1107_);
lean_dec(v___x_1136_);
v___x_1149_ = lean_nat_add(v___x_1106_, v_size_1124_);
if (lean_obj_tag(v_l_1128_) == 0)
{
lean_object* v_size_1159_; 
v_size_1159_ = lean_ctor_get(v_l_1128_, 0);
lean_inc(v_size_1159_);
v___y_1151_ = v_size_1159_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_unsigned_to_nat(0u);
v___y_1151_ = v___x_1160_;
goto v___jp_1150_;
}
v___jp_1138_:
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1142_ = lean_nat_add(v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec(v___y_1140_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 4, v_r_1100_);
lean_ctor_set(v___x_1134_, 3, v_r_1129_);
lean_ctor_set(v___x_1134_, 2, v_v_1098_);
lean_ctor_set(v___x_1134_, 1, v_k_1097_);
lean_ctor_set(v___x_1134_, 0, v___x_1142_);
v___x_1144_ = v___x_1134_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_r_1129_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_r_1100_);
v___x_1144_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 4, v___x_1144_);
lean_ctor_set(v___x_1122_, 3, v___y_1139_);
lean_ctor_set(v___x_1122_, 2, v_v_1127_);
lean_ctor_set(v___x_1122_, 1, v_k_1126_);
lean_ctor_set(v___x_1122_, 0, v___x_1137_);
v___x_1146_ = v___x_1122_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_k_1126_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_v_1127_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v___y_1139_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
v___jp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = lean_nat_add(v___x_1149_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec(v___x_1149_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v_l_1128_);
lean_ctor_set(v___x_1102_, 3, v_l_1111_);
lean_ctor_set(v___x_1102_, 2, v_v_1110_);
lean_ctor_set(v___x_1102_, 1, v_k_1109_);
lean_ctor_set(v___x_1102_, 0, v___x_1152_);
v___x_1154_ = v___x_1102_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v_l_1111_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_l_1128_);
v___x_1154_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_nat_add(v___x_1106_, v_size_1107_);
if (lean_obj_tag(v_r_1129_) == 0)
{
lean_object* v_size_1156_; 
v_size_1156_ = lean_ctor_get(v_r_1129_, 0);
lean_inc(v_size_1156_);
v___y_1139_ = v___x_1154_;
v___y_1140_ = v___x_1155_;
v___y_1141_ = v_size_1156_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_unsigned_to_nat(0u);
v___y_1139_ = v___x_1154_;
v___y_1140_ = v___x_1155_;
v___y_1141_ = v___x_1157_;
goto v___jp_1138_;
}
}
}
}
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
lean_del_object(v___x_1102_);
v___x_1167_ = lean_nat_add(v___x_1106_, v_size_1108_);
lean_dec(v_size_1108_);
v___x_1168_ = lean_nat_add(v___x_1167_, v_size_1107_);
lean_dec(v___x_1167_);
v___x_1169_ = lean_nat_add(v___x_1106_, v_size_1107_);
v___x_1170_ = lean_nat_add(v___x_1169_, v_size_1125_);
lean_dec(v___x_1169_);
lean_inc_ref(v_r_1100_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 4, v_r_1100_);
lean_ctor_set(v___x_1122_, 3, v_r_1112_);
lean_ctor_set(v___x_1122_, 2, v_v_1098_);
lean_ctor_set(v___x_1122_, 1, v_k_1097_);
lean_ctor_set(v___x_1122_, 0, v___x_1170_);
v___x_1172_ = v___x_1122_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v_r_1112_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v_r_1100_);
v___x_1172_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
v_isSharedCheck_1179_ = !lean_is_exclusive(v_r_1100_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; lean_object* v_unused_1181_; lean_object* v_unused_1182_; lean_object* v_unused_1183_; lean_object* v_unused_1184_; 
v_unused_1180_ = lean_ctor_get(v_r_1100_, 4);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_r_1100_, 3);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_r_1100_, 2);
lean_dec(v_unused_1182_);
v_unused_1183_ = lean_ctor_get(v_r_1100_, 1);
lean_dec(v_unused_1183_);
v_unused_1184_ = lean_ctor_get(v_r_1100_, 0);
lean_dec(v_unused_1184_);
v___x_1174_ = v_r_1100_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_dec(v_r_1100_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 4, v___x_1172_);
lean_ctor_set(v___x_1174_, 3, v_l_1111_);
lean_ctor_set(v___x_1174_, 2, v_v_1110_);
lean_ctor_set(v___x_1174_, 1, v_k_1109_);
lean_ctor_set(v___x_1174_, 0, v___x_1168_);
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1178_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1178_, 3, v_l_1111_);
lean_ctor_set(v_reuseFailAlloc_1178_, 4, v___x_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1192_; 
v_l_1192_ = lean_ctor_get(v_impl_1105_, 3);
if (lean_obj_tag(v_l_1192_) == 0)
{
lean_object* v_r_1193_; lean_object* v_k_1194_; lean_object* v_v_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1206_; 
lean_inc_ref(v_l_1192_);
v_r_1193_ = lean_ctor_get(v_impl_1105_, 4);
v_k_1194_ = lean_ctor_get(v_impl_1105_, 1);
v_v_1195_ = lean_ctor_get(v_impl_1105_, 2);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_impl_1105_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; lean_object* v_unused_1208_; 
v_unused_1207_ = lean_ctor_get(v_impl_1105_, 3);
lean_dec(v_unused_1207_);
v_unused_1208_ = lean_ctor_get(v_impl_1105_, 0);
lean_dec(v_unused_1208_);
v___x_1197_ = v_impl_1105_;
v_isShared_1198_ = v_isSharedCheck_1206_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_r_1193_);
lean_inc(v_v_1195_);
lean_inc(v_k_1194_);
lean_dec(v_impl_1105_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1206_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1199_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1193_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 3, v_r_1193_);
lean_ctor_set(v___x_1197_, 2, v_v_1098_);
lean_ctor_set(v___x_1197_, 1, v_k_1097_);
lean_ctor_set(v___x_1197_, 0, v___x_1106_);
v___x_1201_ = v___x_1197_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_r_1193_);
lean_ctor_set(v_reuseFailAlloc_1205_, 4, v_r_1193_);
v___x_1201_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1203_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v___x_1201_);
lean_ctor_set(v___x_1102_, 3, v_l_1192_);
lean_ctor_set(v___x_1102_, 2, v_v_1195_);
lean_ctor_set(v___x_1102_, 1, v_k_1194_);
lean_ctor_set(v___x_1102_, 0, v___x_1199_);
v___x_1203_ = v___x_1102_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_k_1194_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_v_1195_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v_l_1192_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v_r_1209_; 
v_r_1209_ = lean_ctor_get(v_impl_1105_, 4);
lean_inc(v_r_1209_);
if (lean_obj_tag(v_r_1209_) == 0)
{
lean_object* v_k_1210_; lean_object* v_v_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1234_; 
lean_inc(v_l_1192_);
v_k_1210_ = lean_ctor_get(v_impl_1105_, 1);
v_v_1211_ = lean_ctor_get(v_impl_1105_, 2);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_impl_1105_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; lean_object* v_unused_1236_; lean_object* v_unused_1237_; 
v_unused_1235_ = lean_ctor_get(v_impl_1105_, 4);
lean_dec(v_unused_1235_);
v_unused_1236_ = lean_ctor_get(v_impl_1105_, 3);
lean_dec(v_unused_1236_);
v_unused_1237_ = lean_ctor_get(v_impl_1105_, 0);
lean_dec(v_unused_1237_);
v___x_1213_ = v_impl_1105_;
v_isShared_1214_ = v_isSharedCheck_1234_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_v_1211_);
lean_inc(v_k_1210_);
lean_dec(v_impl_1105_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1234_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_k_1215_; lean_object* v_v_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1230_; 
v_k_1215_ = lean_ctor_get(v_r_1209_, 1);
v_v_1216_ = lean_ctor_get(v_r_1209_, 2);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_r_1209_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; lean_object* v_unused_1232_; lean_object* v_unused_1233_; 
v_unused_1231_ = lean_ctor_get(v_r_1209_, 4);
lean_dec(v_unused_1231_);
v_unused_1232_ = lean_ctor_get(v_r_1209_, 3);
lean_dec(v_unused_1232_);
v_unused_1233_ = lean_ctor_get(v_r_1209_, 0);
lean_dec(v_unused_1233_);
v___x_1218_ = v_r_1209_;
v_isShared_1219_ = v_isSharedCheck_1230_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_v_1216_);
lean_inc(v_k_1215_);
lean_dec(v_r_1209_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1230_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1220_ = lean_unsigned_to_nat(3u);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 4, v_l_1192_);
lean_ctor_set(v___x_1218_, 3, v_l_1192_);
lean_ctor_set(v___x_1218_, 2, v_v_1211_);
lean_ctor_set(v___x_1218_, 1, v_k_1210_);
lean_ctor_set(v___x_1218_, 0, v___x_1106_);
v___x_1222_ = v___x_1218_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_k_1210_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v_v_1211_);
lean_ctor_set(v_reuseFailAlloc_1229_, 3, v_l_1192_);
lean_ctor_set(v_reuseFailAlloc_1229_, 4, v_l_1192_);
v___x_1222_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1224_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v_l_1192_);
lean_ctor_set(v___x_1213_, 2, v_v_1098_);
lean_ctor_set(v___x_1213_, 1, v_k_1097_);
lean_ctor_set(v___x_1213_, 0, v___x_1106_);
v___x_1224_ = v___x_1213_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_l_1192_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v_l_1192_);
v___x_1224_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1226_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v___x_1224_);
lean_ctor_set(v___x_1102_, 3, v___x_1222_);
lean_ctor_set(v___x_1102_, 2, v_v_1216_);
lean_ctor_set(v___x_1102_, 1, v_k_1215_);
lean_ctor_set(v___x_1102_, 0, v___x_1220_);
v___x_1226_ = v___x_1102_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_k_1215_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_v_1216_);
lean_ctor_set(v_reuseFailAlloc_1227_, 3, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1227_, 4, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1238_ = lean_unsigned_to_nat(2u);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v_r_1209_);
lean_ctor_set(v___x_1102_, 3, v_impl_1105_);
lean_ctor_set(v___x_1102_, 0, v___x_1238_);
v___x_1240_ = v___x_1102_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_impl_1105_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v_r_1209_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1243_; 
lean_dec(v_v_1098_);
lean_dec(v_k_1097_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 2, v_v_1094_);
lean_ctor_set(v___x_1102_, 1, v_k_1093_);
v___x_1243_ = v___x_1102_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_size_1096_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_k_1093_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_v_1094_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v_l_1099_);
lean_ctor_set(v_reuseFailAlloc_1244_, 4, v_r_1100_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
default: 
{
lean_object* v_impl_1245_; lean_object* v___x_1246_; 
lean_dec(v_size_1096_);
v_impl_1245_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1093_, v_v_1094_, v_r_1100_);
v___x_1246_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1099_) == 0)
{
lean_object* v_size_1247_; lean_object* v_size_1248_; lean_object* v_k_1249_; lean_object* v_v_1250_; lean_object* v_l_1251_; lean_object* v_r_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v_size_1247_ = lean_ctor_get(v_l_1099_, 0);
v_size_1248_ = lean_ctor_get(v_impl_1245_, 0);
v_k_1249_ = lean_ctor_get(v_impl_1245_, 1);
v_v_1250_ = lean_ctor_get(v_impl_1245_, 2);
v_l_1251_ = lean_ctor_get(v_impl_1245_, 3);
lean_inc(v_l_1251_);
v_r_1252_ = lean_ctor_get(v_impl_1245_, 4);
v___x_1253_ = lean_unsigned_to_nat(3u);
v___x_1254_ = lean_nat_mul(v___x_1253_, v_size_1247_);
v___x_1255_ = lean_nat_dec_lt(v___x_1254_, v_size_1248_);
lean_dec(v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
lean_dec(v_l_1251_);
v___x_1256_ = lean_nat_add(v___x_1246_, v_size_1247_);
v___x_1257_ = lean_nat_add(v___x_1256_, v_size_1248_);
lean_dec(v___x_1256_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v_impl_1245_);
lean_ctor_set(v___x_1102_, 0, v___x_1257_);
v___x_1259_ = v___x_1102_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_l_1099_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v_impl_1245_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
else
{
lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1324_; 
lean_inc(v_r_1252_);
lean_inc(v_v_1250_);
lean_inc(v_k_1249_);
lean_inc(v_size_1248_);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_impl_1245_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; lean_object* v_unused_1326_; lean_object* v_unused_1327_; lean_object* v_unused_1328_; lean_object* v_unused_1329_; 
v_unused_1325_ = lean_ctor_get(v_impl_1245_, 4);
lean_dec(v_unused_1325_);
v_unused_1326_ = lean_ctor_get(v_impl_1245_, 3);
lean_dec(v_unused_1326_);
v_unused_1327_ = lean_ctor_get(v_impl_1245_, 2);
lean_dec(v_unused_1327_);
v_unused_1328_ = lean_ctor_get(v_impl_1245_, 1);
lean_dec(v_unused_1328_);
v_unused_1329_ = lean_ctor_get(v_impl_1245_, 0);
lean_dec(v_unused_1329_);
v___x_1262_ = v_impl_1245_;
v_isShared_1263_ = v_isSharedCheck_1324_;
goto v_resetjp_1261_;
}
else
{
lean_dec(v_impl_1245_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1324_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_size_1264_; lean_object* v_k_1265_; lean_object* v_v_1266_; lean_object* v_l_1267_; lean_object* v_r_1268_; lean_object* v_size_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v_size_1264_ = lean_ctor_get(v_l_1251_, 0);
v_k_1265_ = lean_ctor_get(v_l_1251_, 1);
v_v_1266_ = lean_ctor_get(v_l_1251_, 2);
v_l_1267_ = lean_ctor_get(v_l_1251_, 3);
v_r_1268_ = lean_ctor_get(v_l_1251_, 4);
v_size_1269_ = lean_ctor_get(v_r_1252_, 0);
v___x_1270_ = lean_unsigned_to_nat(2u);
v___x_1271_ = lean_nat_mul(v___x_1270_, v_size_1269_);
v___x_1272_ = lean_nat_dec_lt(v_size_1264_, v___x_1271_);
lean_dec(v___x_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1300_; 
lean_inc(v_r_1268_);
lean_inc(v_l_1267_);
lean_inc(v_v_1266_);
lean_inc(v_k_1265_);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_l_1251_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; lean_object* v_unused_1302_; lean_object* v_unused_1303_; lean_object* v_unused_1304_; lean_object* v_unused_1305_; 
v_unused_1301_ = lean_ctor_get(v_l_1251_, 4);
lean_dec(v_unused_1301_);
v_unused_1302_ = lean_ctor_get(v_l_1251_, 3);
lean_dec(v_unused_1302_);
v_unused_1303_ = lean_ctor_get(v_l_1251_, 2);
lean_dec(v_unused_1303_);
v_unused_1304_ = lean_ctor_get(v_l_1251_, 1);
lean_dec(v_unused_1304_);
v_unused_1305_ = lean_ctor_get(v_l_1251_, 0);
lean_dec(v_unused_1305_);
v___x_1274_ = v_l_1251_;
v_isShared_1275_ = v_isSharedCheck_1300_;
goto v_resetjp_1273_;
}
else
{
lean_dec(v_l_1251_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1300_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1290_; 
v___x_1276_ = lean_nat_add(v___x_1246_, v_size_1247_);
v___x_1277_ = lean_nat_add(v___x_1276_, v_size_1248_);
lean_dec(v_size_1248_);
if (lean_obj_tag(v_l_1267_) == 0)
{
lean_object* v_size_1298_; 
v_size_1298_ = lean_ctor_get(v_l_1267_, 0);
lean_inc(v_size_1298_);
v___y_1290_ = v_size_1298_;
goto v___jp_1289_;
}
else
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_unsigned_to_nat(0u);
v___y_1290_ = v___x_1299_;
goto v___jp_1289_;
}
v___jp_1278_:
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1282_ = lean_nat_add(v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec(v___y_1280_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 4, v_r_1252_);
lean_ctor_set(v___x_1274_, 3, v_r_1268_);
lean_ctor_set(v___x_1274_, 2, v_v_1250_);
lean_ctor_set(v___x_1274_, 1, v_k_1249_);
lean_ctor_set(v___x_1274_, 0, v___x_1282_);
v___x_1284_ = v___x_1274_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1288_, 3, v_r_1268_);
lean_ctor_set(v_reuseFailAlloc_1288_, 4, v_r_1252_);
v___x_1284_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1286_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 4, v___x_1284_);
lean_ctor_set(v___x_1262_, 3, v___y_1279_);
lean_ctor_set(v___x_1262_, 2, v_v_1266_);
lean_ctor_set(v___x_1262_, 1, v_k_1265_);
lean_ctor_set(v___x_1262_, 0, v___x_1277_);
v___x_1286_ = v___x_1262_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_k_1265_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_v_1266_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v___y_1279_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
v___jp_1289_:
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1291_ = lean_nat_add(v___x_1276_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec(v___x_1276_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v_l_1267_);
lean_ctor_set(v___x_1102_, 0, v___x_1291_);
v___x_1293_ = v___x_1102_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1297_, 3, v_l_1099_);
lean_ctor_set(v_reuseFailAlloc_1297_, 4, v_l_1267_);
v___x_1293_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_nat_add(v___x_1246_, v_size_1269_);
if (lean_obj_tag(v_r_1268_) == 0)
{
lean_object* v_size_1295_; 
v_size_1295_ = lean_ctor_get(v_r_1268_, 0);
lean_inc(v_size_1295_);
v___y_1279_ = v___x_1293_;
v___y_1280_ = v___x_1294_;
v___y_1281_ = v_size_1295_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_unsigned_to_nat(0u);
v___y_1279_ = v___x_1293_;
v___y_1280_ = v___x_1294_;
v___y_1281_ = v___x_1296_;
goto v___jp_1278_;
}
}
}
}
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
lean_del_object(v___x_1102_);
v___x_1306_ = lean_nat_add(v___x_1246_, v_size_1247_);
v___x_1307_ = lean_nat_add(v___x_1306_, v_size_1248_);
lean_dec(v_size_1248_);
v___x_1308_ = lean_nat_add(v___x_1306_, v_size_1264_);
lean_dec(v___x_1306_);
lean_inc_ref(v_l_1099_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 4, v_l_1251_);
lean_ctor_set(v___x_1262_, 3, v_l_1099_);
lean_ctor_set(v___x_1262_, 2, v_v_1098_);
lean_ctor_set(v___x_1262_, 1, v_k_1097_);
lean_ctor_set(v___x_1262_, 0, v___x_1308_);
v___x_1310_ = v___x_1262_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_l_1099_);
lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_l_1251_);
v___x_1310_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
v_isSharedCheck_1317_ = !lean_is_exclusive(v_l_1099_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; lean_object* v_unused_1319_; lean_object* v_unused_1320_; lean_object* v_unused_1321_; lean_object* v_unused_1322_; 
v_unused_1318_ = lean_ctor_get(v_l_1099_, 4);
lean_dec(v_unused_1318_);
v_unused_1319_ = lean_ctor_get(v_l_1099_, 3);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_l_1099_, 2);
lean_dec(v_unused_1320_);
v_unused_1321_ = lean_ctor_get(v_l_1099_, 1);
lean_dec(v_unused_1321_);
v_unused_1322_ = lean_ctor_get(v_l_1099_, 0);
lean_dec(v_unused_1322_);
v___x_1312_ = v_l_1099_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_dec(v_l_1099_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 4, v_r_1252_);
lean_ctor_set(v___x_1312_, 3, v___x_1310_);
lean_ctor_set(v___x_1312_, 2, v_v_1250_);
lean_ctor_set(v___x_1312_, 1, v_k_1249_);
lean_ctor_set(v___x_1312_, 0, v___x_1307_);
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1316_, 3, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1316_, 4, v_r_1252_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1330_; 
v_l_1330_ = lean_ctor_get(v_impl_1245_, 3);
lean_inc(v_l_1330_);
if (lean_obj_tag(v_l_1330_) == 0)
{
lean_object* v_r_1331_; lean_object* v_k_1332_; lean_object* v_v_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1356_; 
v_r_1331_ = lean_ctor_get(v_impl_1245_, 4);
v_k_1332_ = lean_ctor_get(v_impl_1245_, 1);
v_v_1333_ = lean_ctor_get(v_impl_1245_, 2);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_impl_1245_);
if (v_isSharedCheck_1356_ == 0)
{
lean_object* v_unused_1357_; lean_object* v_unused_1358_; 
v_unused_1357_ = lean_ctor_get(v_impl_1245_, 3);
lean_dec(v_unused_1357_);
v_unused_1358_ = lean_ctor_get(v_impl_1245_, 0);
lean_dec(v_unused_1358_);
v___x_1335_ = v_impl_1245_;
v_isShared_1336_ = v_isSharedCheck_1356_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_r_1331_);
lean_inc(v_v_1333_);
lean_inc(v_k_1332_);
lean_dec(v_impl_1245_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1356_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_k_1337_; lean_object* v_v_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1352_; 
v_k_1337_ = lean_ctor_get(v_l_1330_, 1);
v_v_1338_ = lean_ctor_get(v_l_1330_, 2);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_l_1330_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; lean_object* v_unused_1354_; lean_object* v_unused_1355_; 
v_unused_1353_ = lean_ctor_get(v_l_1330_, 4);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_l_1330_, 3);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v_l_1330_, 0);
lean_dec(v_unused_1355_);
v___x_1340_ = v_l_1330_;
v_isShared_1341_ = v_isSharedCheck_1352_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_v_1338_);
lean_inc(v_k_1337_);
lean_dec(v_l_1330_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1352_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1342_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1331_, 2);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 4, v_r_1331_);
lean_ctor_set(v___x_1340_, 3, v_r_1331_);
lean_ctor_set(v___x_1340_, 2, v_v_1098_);
lean_ctor_set(v___x_1340_, 1, v_k_1097_);
lean_ctor_set(v___x_1340_, 0, v___x_1246_);
v___x_1344_ = v___x_1340_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v_r_1331_);
lean_ctor_set(v_reuseFailAlloc_1351_, 4, v_r_1331_);
v___x_1344_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1346_; 
lean_inc(v_r_1331_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 3, v_r_1331_);
lean_ctor_set(v___x_1335_, 0, v___x_1246_);
v___x_1346_ = v___x_1335_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_k_1332_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_v_1333_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_r_1331_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v_r_1331_);
v___x_1346_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1348_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v___x_1346_);
lean_ctor_set(v___x_1102_, 3, v___x_1344_);
lean_ctor_set(v___x_1102_, 2, v_v_1338_);
lean_ctor_set(v___x_1102_, 1, v_k_1337_);
lean_ctor_set(v___x_1102_, 0, v___x_1342_);
v___x_1348_ = v___x_1102_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v___x_1344_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
}
else
{
lean_object* v_r_1359_; 
v_r_1359_ = lean_ctor_get(v_impl_1245_, 4);
lean_inc(v_r_1359_);
if (lean_obj_tag(v_r_1359_) == 0)
{
lean_object* v_k_1360_; lean_object* v_v_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1372_; 
v_k_1360_ = lean_ctor_get(v_impl_1245_, 1);
v_v_1361_ = lean_ctor_get(v_impl_1245_, 2);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_impl_1245_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; lean_object* v_unused_1374_; lean_object* v_unused_1375_; 
v_unused_1373_ = lean_ctor_get(v_impl_1245_, 4);
lean_dec(v_unused_1373_);
v_unused_1374_ = lean_ctor_get(v_impl_1245_, 3);
lean_dec(v_unused_1374_);
v_unused_1375_ = lean_ctor_get(v_impl_1245_, 0);
lean_dec(v_unused_1375_);
v___x_1363_ = v_impl_1245_;
v_isShared_1364_ = v_isSharedCheck_1372_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_v_1361_);
lean_inc(v_k_1360_);
lean_dec(v_impl_1245_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1372_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = lean_unsigned_to_nat(3u);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 4, v_l_1330_);
lean_ctor_set(v___x_1363_, 2, v_v_1098_);
lean_ctor_set(v___x_1363_, 1, v_k_1097_);
lean_ctor_set(v___x_1363_, 0, v___x_1246_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v_l_1330_);
lean_ctor_set(v_reuseFailAlloc_1371_, 4, v_l_1330_);
v___x_1367_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1369_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v_r_1359_);
lean_ctor_set(v___x_1102_, 3, v___x_1367_);
lean_ctor_set(v___x_1102_, 2, v_v_1361_);
lean_ctor_set(v___x_1102_, 1, v_k_1360_);
lean_ctor_set(v___x_1102_, 0, v___x_1365_);
v___x_1369_ = v___x_1102_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_k_1360_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v_v_1361_);
lean_ctor_set(v_reuseFailAlloc_1370_, 3, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1370_, 4, v_r_1359_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1376_ = lean_unsigned_to_nat(2u);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v_impl_1245_);
lean_ctor_set(v___x_1102_, 3, v_r_1359_);
lean_ctor_set(v___x_1102_, 0, v___x_1376_);
v___x_1378_ = v___x_1102_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v_r_1359_);
lean_ctor_set(v_reuseFailAlloc_1379_, 4, v_impl_1245_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
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
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
lean_ctor_set(v___x_1382_, 1, v_k_1093_);
lean_ctor_set(v___x_1382_, 2, v_v_1094_);
lean_ctor_set(v___x_1382_, 3, v_t_1095_);
lean_ctor_set(v___x_1382_, 4, v_t_1095_);
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object* v_s_1383_, lean_object* v_mvarId_1384_){
_start:
{
uint8_t v___x_1385_; 
v___x_1385_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_mvarId_1384_, v_s_1383_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_box(0);
v___x_1387_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1384_, v___x_1386_, v_s_1383_);
return v___x_1387_;
}
else
{
lean_dec(v_mvarId_1384_);
return v_s_1383_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object* v_00_u03b2_1388_, lean_object* v_k_1389_, lean_object* v_t_1390_){
_start:
{
uint8_t v___x_1391_; 
v___x_1391_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1389_, v_t_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object* v_00_u03b2_1392_, lean_object* v_k_1393_, lean_object* v_t_1394_){
_start:
{
uint8_t v_res_1395_; lean_object* v_r_1396_; 
v_res_1395_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(v_00_u03b2_1392_, v_k_1393_, v_t_1394_);
lean_dec(v_t_1394_);
lean_dec(v_k_1393_);
v_r_1396_ = lean_box(v_res_1395_);
return v_r_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object* v_00_u03b2_1397_, lean_object* v_k_1398_, lean_object* v_v_1399_, lean_object* v_t_1400_, lean_object* v_hl_1401_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1398_, v_v_1399_, v_t_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object* v_l_1403_){
_start:
{
lean_object* v___f_1404_; lean_object* v___x_1405_; 
v___f_1404_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1405_ = l_Std_TreeSet_ofList___redArg(v_l_1403_, v___f_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList___boxed(lean_object* v_l_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_MVarIdSet_ofList(v_l_1406_);
lean_dec(v_l_1406_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object* v_l_1408_){
_start:
{
lean_object* v___f_1409_; lean_object* v___x_1410_; 
v___f_1409_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1410_ = l_Std_TreeSet_ofArray___redArg(v_l_1408_, v___f_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object* v_l_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_MVarIdSet_ofArray(v_l_1411_);
lean_dec_ref(v_l_1411_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1413_, lean_object* v_m_1414_, lean_object* v_init_1415_, lean_object* v_f_1416_){
_start:
{
lean_object* v_toApplicative_1417_; lean_object* v_toBind_1418_; lean_object* v_toPure_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; lean_object* v___f_1422_; lean_object* v___x_1423_; 
v_toApplicative_1417_ = lean_ctor_get(v_inst_1413_, 0);
v_toBind_1418_ = lean_ctor_get(v_inst_1413_, 1);
lean_inc(v_toBind_1418_);
v_toPure_1419_ = lean_ctor_get(v_toApplicative_1417_, 1);
lean_inc(v_toPure_1419_);
v___f_1420_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1420_, 0, v_f_1416_);
v___x_1421_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1413_, v___f_1420_, v_init_1415_, v_m_1414_);
v___f_1422_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1422_, 0, v_toPure_1419_);
v___x_1423_ = lean_apply_4(v_toBind_1418_, lean_box(0), lean_box(0), v___x_1421_, v___f_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1(lean_object* v_m_1424_, lean_object* v_inst_1425_, lean_object* v_00_u03b2_1426_, lean_object* v_m_1427_, lean_object* v_init_1428_, lean_object* v_f_1429_){
_start:
{
lean_object* v_toApplicative_1430_; lean_object* v_toBind_1431_; lean_object* v_toPure_1432_; lean_object* v___f_1433_; lean_object* v___x_1434_; lean_object* v___f_1435_; lean_object* v___x_1436_; 
v_toApplicative_1430_ = lean_ctor_get(v_inst_1425_, 0);
v_toBind_1431_ = lean_ctor_get(v_inst_1425_, 1);
lean_inc(v_toBind_1431_);
v_toPure_1432_ = lean_ctor_get(v_toApplicative_1430_, 1);
lean_inc(v_toPure_1432_);
v___f_1433_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1433_, 0, v_f_1429_);
v___x_1434_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1425_, v___f_1433_, v_init_1428_, v_m_1427_);
v___f_1435_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1435_, 0, v_toPure_1432_);
v___x_1436_ = lean_apply_4(v_toBind_1431_, lean_box(0), lean_box(0), v___x_1434_, v___f_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object* v_inst_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1438_, 0, lean_box(0));
lean_closure_set(v___x_1438_, 1, v_inst_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object* v_m_1439_, lean_object* v_inst_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1441_, 0, lean_box(0));
lean_closure_set(v___x_1441_, 1, v_inst_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object* v_s_1442_, lean_object* v_mvarId_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1443_, v_a_1444_, v_s_1442_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object* v_00_u03b1_1446_, lean_object* v_s_1447_, lean_object* v_mvarId_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1448_, v_a_1449_, v_s_1447_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_box(1);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg();
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object* v_00_u03b1_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_box(1);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg(){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_box(1);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg___boxed(lean_object* v___dummy_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_instEmptyCollectionMVarIdMap___redArg();
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* v_00_u03b1_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_box(1);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_1463_, lean_object* v_a_1464_, lean_object* v_b_1465_, lean_object* v_c_1466_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v_a_1464_);
lean_ctor_set(v___x_1467_, 1, v_b_1465_);
v___x_1468_ = lean_apply_2(v_f_1463_, v___x_1467_, v_c_1466_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1469_, lean_object* v_m_1470_, lean_object* v_init_1471_, lean_object* v_f_1472_){
_start:
{
lean_object* v_toApplicative_1473_; lean_object* v_toBind_1474_; lean_object* v_toPure_1475_; lean_object* v___f_1476_; lean_object* v___x_1477_; lean_object* v___f_1478_; lean_object* v___x_1479_; 
v_toApplicative_1473_ = lean_ctor_get(v_inst_1469_, 0);
v_toBind_1474_ = lean_ctor_get(v_inst_1469_, 1);
lean_inc(v_toBind_1474_);
v_toPure_1475_ = lean_ctor_get(v_toApplicative_1473_, 1);
lean_inc(v_toPure_1475_);
v___f_1476_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1476_, 0, v_f_1472_);
v___x_1477_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1469_, v___f_1476_, v_init_1471_, v_m_1470_);
v___f_1478_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1478_, 0, v_toPure_1475_);
v___x_1479_ = lean_apply_4(v_toBind_1474_, lean_box(0), lean_box(0), v___x_1477_, v___f_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object* v_m_1480_, lean_object* v_00_u03b1_1481_, lean_object* v_inst_1482_, lean_object* v_00_u03b2_1483_, lean_object* v_m_1484_, lean_object* v_init_1485_, lean_object* v_f_1486_){
_start:
{
lean_object* v_toApplicative_1487_; lean_object* v_toBind_1488_; lean_object* v_toPure_1489_; lean_object* v___f_1490_; lean_object* v___x_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; 
v_toApplicative_1487_ = lean_ctor_get(v_inst_1482_, 0);
v_toBind_1488_ = lean_ctor_get(v_inst_1482_, 1);
lean_inc(v_toBind_1488_);
v_toPure_1489_ = lean_ctor_get(v_toApplicative_1487_, 1);
lean_inc(v_toPure_1489_);
v___f_1490_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1490_, 0, v_f_1486_);
v___x_1491_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1482_, v___f_1490_, v_init_1485_, v_m_1484_);
v___f_1492_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1492_, 0, v_toPure_1489_);
v___x_1493_ = lean_apply_4(v_toBind_1488_, lean_box(0), lean_box(0), v___x_1491_, v___f_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object* v_inst_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1495_, 0, lean_box(0));
lean_closure_set(v___x_1495_, 1, lean_box(0));
lean_closure_set(v___x_1495_, 2, v_inst_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object* v_m_1496_, lean_object* v_00_u03b1_1497_, lean_object* v_inst_1498_){
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg(){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_box(1);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg___boxed(lean_object* v___dummy_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_instInhabitedMVarIdMap___redArg();
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* v_00_u03b1_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_box(1);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___impl(lean_object* v_x_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_obj_tag_nat(v_x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___impl___boxed(lean_object* v_x_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Expr_ctorIdx___impl(v_x_1508_);
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
lean_object* v___y_1823_; uint64_t v___y_1824_; uint8_t v___y_1825_; uint32_t v___y_1826_; uint8_t v___y_1827_; uint8_t v___y_1828_; uint8_t v___y_1829_; uint64_t v___x_1832_; uint8_t v___x_1833_; uint32_t v___x_1834_; uint64_t v___x_1835_; uint64_t v___y_1837_; lean_object* v___y_1838_; uint8_t v___y_1839_; uint32_t v___y_1840_; uint8_t v___y_1841_; uint8_t v___y_1842_; lean_object* v___y_1846_; uint64_t v___y_1847_; uint8_t v___y_1848_; uint32_t v___y_1849_; uint8_t v___y_1850_; uint64_t v___y_1854_; lean_object* v___y_1855_; uint32_t v___y_1856_; uint8_t v___y_1857_; uint64_t v___y_1861_; uint32_t v___y_1862_; lean_object* v___y_1863_; uint32_t v___y_1867_; uint8_t v___x_1882_; uint32_t v___x_1883_; uint8_t v___x_1884_; 
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
v___x_1830_ = lean_expr_mk_data(v___y_1824_, v___y_1823_, v___y_1826_, v___y_1825_, v___y_1827_, v___y_1828_, v___y_1829_);
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
v___y_1823_ = v___y_1838_;
v___y_1824_ = v___y_1837_;
v___y_1825_ = v___y_1839_;
v___y_1826_ = v___y_1840_;
v___y_1827_ = v___y_1841_;
v___y_1828_ = v___y_1842_;
v___y_1829_ = v___x_1844_;
goto v___jp_1822_;
}
else
{
v___y_1823_ = v___y_1838_;
v___y_1824_ = v___y_1837_;
v___y_1825_ = v___y_1839_;
v___y_1826_ = v___y_1840_;
v___y_1827_ = v___y_1841_;
v___y_1828_ = v___y_1842_;
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
v___y_1837_ = v___y_1847_;
v___y_1838_ = v___y_1846_;
v___y_1839_ = v___y_1848_;
v___y_1840_ = v___y_1849_;
v___y_1841_ = v___y_1850_;
v___y_1842_ = v___x_1852_;
goto v___jp_1836_;
}
else
{
v___y_1837_ = v___y_1847_;
v___y_1838_ = v___y_1846_;
v___y_1839_ = v___y_1848_;
v___y_1840_ = v___y_1849_;
v___y_1841_ = v___y_1850_;
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
v___y_1846_ = v___y_1855_;
v___y_1847_ = v___y_1854_;
v___y_1848_ = v___y_1857_;
v___y_1849_ = v___y_1856_;
v___y_1850_ = v___x_1859_;
goto v___jp_1845_;
}
else
{
v___y_1846_ = v___y_1855_;
v___y_1847_ = v___y_1854_;
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
v___y_1854_ = v___y_1861_;
v___y_1855_ = v___y_1863_;
v___y_1856_ = v___y_1862_;
v___y_1857_ = v___x_1865_;
goto v___jp_1853_;
}
else
{
v___y_1854_ = v___y_1861_;
v___y_1855_ = v___y_1863_;
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
v___y_1861_ = v___x_1875_;
v___y_1862_ = v___x_1870_;
v___y_1863_ = v___x_1877_;
goto v___jp_1860_;
}
else
{
lean_dec(v___x_1877_);
v___y_1861_ = v___x_1875_;
v___y_1862_ = v___x_1870_;
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
uint8_t v___y_1896_; uint8_t v___y_1897_; lean_object* v___y_1898_; uint8_t v___y_1899_; uint64_t v___y_1900_; uint32_t v___y_1901_; uint8_t v___y_1902_; uint64_t v___x_1905_; uint8_t v___x_1906_; uint32_t v___x_1907_; uint64_t v___x_1908_; uint8_t v___y_1910_; lean_object* v___y_1911_; uint8_t v___y_1912_; uint64_t v___y_1913_; uint32_t v___y_1914_; uint8_t v___y_1915_; uint8_t v___y_1919_; lean_object* v___y_1920_; uint64_t v___y_1921_; uint32_t v___y_1922_; uint8_t v___y_1923_; lean_object* v___y_1927_; uint64_t v___y_1928_; uint32_t v___y_1929_; uint8_t v___y_1930_; uint64_t v___y_1934_; uint32_t v___y_1935_; lean_object* v___y_1936_; uint32_t v___y_1940_; uint8_t v___x_1955_; uint32_t v___x_1956_; uint8_t v___x_1957_; 
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
v___x_1903_ = lean_expr_mk_data(v___y_1900_, v___y_1898_, v___y_1901_, v___y_1896_, v___y_1899_, v___y_1897_, v___y_1902_);
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
v___y_1896_ = v___y_1910_;
v___y_1897_ = v___y_1915_;
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v___y_1900_ = v___y_1913_;
v___y_1901_ = v___y_1914_;
v___y_1902_ = v___x_1917_;
goto v___jp_1895_;
}
else
{
v___y_1896_ = v___y_1910_;
v___y_1897_ = v___y_1915_;
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
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
v___y_1910_ = v___y_1919_;
v___y_1911_ = v___y_1920_;
v___y_1912_ = v___y_1923_;
v___y_1913_ = v___y_1921_;
v___y_1914_ = v___y_1922_;
v___y_1915_ = v___x_1925_;
goto v___jp_1909_;
}
else
{
v___y_1910_ = v___y_1919_;
v___y_1911_ = v___y_1920_;
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
uint64_t v___y_1970_; uint32_t v___y_1971_; uint8_t v___y_1972_; uint8_t v___y_1973_; lean_object* v___y_1974_; uint8_t v___y_1975_; uint8_t v___y_1976_; uint64_t v___y_1980_; uint32_t v___y_1981_; uint8_t v___y_1982_; uint8_t v___y_1983_; lean_object* v___y_1984_; uint8_t v___y_1985_; uint64_t v___y_1986_; uint8_t v___y_1987_; uint64_t v___x_1989_; uint8_t v___x_1990_; uint32_t v___x_1991_; uint64_t v___x_1992_; uint64_t v___y_1994_; uint32_t v___y_1995_; uint8_t v___y_1996_; uint8_t v___y_1997_; lean_object* v___y_1998_; uint64_t v___y_1999_; uint8_t v___y_2000_; uint64_t v___y_2004_; uint32_t v___y_2005_; uint8_t v___y_2006_; uint8_t v___y_2007_; lean_object* v___y_2008_; uint64_t v___y_2009_; uint8_t v___y_2010_; uint64_t v___y_2013_; uint32_t v___y_2014_; uint8_t v___y_2015_; lean_object* v___y_2016_; uint64_t v___y_2017_; uint8_t v___y_2018_; uint64_t v___y_2022_; uint32_t v___y_2023_; uint8_t v___y_2024_; lean_object* v___y_2025_; uint64_t v___y_2026_; uint8_t v___y_2027_; uint64_t v___y_2030_; uint32_t v___y_2031_; lean_object* v___y_2032_; uint64_t v___y_2033_; uint8_t v___y_2034_; uint64_t v___y_2038_; uint32_t v___y_2039_; lean_object* v___y_2040_; uint64_t v___y_2041_; uint8_t v___y_2042_; uint64_t v___y_2045_; uint32_t v___y_2046_; uint64_t v___y_2047_; lean_object* v___y_2048_; uint64_t v___y_2052_; uint32_t v___y_2053_; lean_object* v___y_2054_; uint64_t v___y_2055_; lean_object* v___y_2056_; uint64_t v___y_2062_; uint32_t v___y_2063_; uint32_t v___y_2080_; uint8_t v___x_2085_; uint32_t v___x_2086_; uint8_t v___x_2087_; 
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
v___x_1977_ = lean_expr_mk_data(v___y_1970_, v___y_1974_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1975_, v___y_1976_);
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
v___x_1988_ = l_Lean_Expr_Data_hasLevelParam(v___y_1986_);
v___y_1970_ = v___y_1980_;
v___y_1971_ = v___y_1981_;
v___y_1972_ = v___y_1982_;
v___y_1973_ = v___y_1983_;
v___y_1974_ = v___y_1984_;
v___y_1975_ = v___y_1985_;
v___y_1976_ = v___x_1988_;
goto v___jp_1969_;
}
else
{
v___y_1970_ = v___y_1980_;
v___y_1971_ = v___y_1981_;
v___y_1972_ = v___y_1982_;
v___y_1973_ = v___y_1983_;
v___y_1974_ = v___y_1984_;
v___y_1975_ = v___y_1985_;
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
v___y_1981_ = v___y_1995_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1997_;
v___y_1984_ = v___y_1998_;
v___y_1985_ = v___y_2000_;
v___y_1986_ = v___y_1999_;
v___y_1987_ = v___x_2002_;
goto v___jp_1979_;
}
else
{
v___y_1980_ = v___y_1994_;
v___y_1981_ = v___y_1995_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1997_;
v___y_1984_ = v___y_1998_;
v___y_1985_ = v___y_2000_;
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
v___x_2011_ = l_Lean_Expr_Data_hasLevelMVar(v___y_2009_);
v___y_1994_ = v___y_2004_;
v___y_1995_ = v___y_2005_;
v___y_1996_ = v___y_2006_;
v___y_1997_ = v___y_2007_;
v___y_1998_ = v___y_2008_;
v___y_1999_ = v___y_2009_;
v___y_2000_ = v___x_2011_;
goto v___jp_1993_;
}
else
{
v___y_1994_ = v___y_2004_;
v___y_1995_ = v___y_2005_;
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
v___y_2007_ = v___y_2018_;
v___y_2008_ = v___y_2016_;
v___y_2009_ = v___y_2017_;
v___y_2010_ = v___x_2020_;
goto v___jp_2003_;
}
else
{
v___y_2004_ = v___y_2013_;
v___y_2005_ = v___y_2014_;
v___y_2006_ = v___y_2015_;
v___y_2007_ = v___y_2018_;
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
v___x_2028_ = l_Lean_Expr_Data_hasExprMVar(v___y_2026_);
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
v___y_2024_ = v___y_2034_;
v___y_2025_ = v___y_2032_;
v___y_2026_ = v___y_2033_;
v___y_2027_ = v___x_2036_;
goto v___jp_2021_;
}
else
{
v___y_2022_ = v___y_2030_;
v___y_2023_ = v___y_2031_;
v___y_2024_ = v___y_2034_;
v___y_2025_ = v___y_2032_;
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
v___x_2043_ = l_Lean_Expr_Data_hasFVar(v___y_2041_);
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
v___y_2040_ = v___y_2048_;
v___y_2041_ = v___y_2047_;
v___y_2042_ = v___x_2050_;
goto v___jp_2037_;
}
else
{
v___y_2038_ = v___y_2045_;
v___y_2039_ = v___y_2046_;
v___y_2040_ = v___y_2048_;
v___y_2041_ = v___y_2047_;
v___y_2042_ = v___x_2049_;
goto v___jp_2037_;
}
}
v___jp_2051_:
{
uint32_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2057_ = l_Lean_Expr_Data_looseBVarRange(v___y_2055_);
v___x_2058_ = lean_uint32_to_nat(v___x_2057_);
v___x_2059_ = lean_nat_sub(v___x_2058_, v___y_2054_);
lean_dec(v___x_2058_);
v___x_2060_ = lean_nat_dec_le(v___y_2056_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_dec(v___x_2059_);
v___y_2045_ = v___y_2052_;
v___y_2046_ = v___y_2053_;
v___y_2047_ = v___y_2055_;
v___y_2048_ = v___y_2056_;
goto v___jp_2044_;
}
else
{
lean_dec(v___y_2056_);
v___y_2045_ = v___y_2052_;
v___y_2046_ = v___y_2053_;
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
v___y_2053_ = v___x_2066_;
v___y_2054_ = v___x_2064_;
v___y_2055_ = v___y_2062_;
v___y_2056_ = v___x_2075_;
goto v___jp_2051_;
}
else
{
lean_dec(v___x_2075_);
v___y_2052_ = v___x_2073_;
v___y_2053_ = v___x_2066_;
v___y_2054_ = v___x_2064_;
v___y_2055_ = v___y_2062_;
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
v___x_2146_ = 1723ULL;
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
uint64_t v_x_1715__boxed_2175_; uint64_t v_res_2176_; lean_object* v_r_2177_; 
v_x_1715__boxed_2175_ = lean_unbox_uint64(v_x_2173_);
lean_dec_ref(v_x_2173_);
v_res_2176_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_1715__boxed_2175_, v_x_2174_);
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
v___x_2194_ = 1723ULL;
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
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Expr_sort___override(v_u_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_2956_, lean_object* v_lvls_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_Expr_const___override(v_c_2956_, v_lvls_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_Expr_app___override(v_f_2959_, v_a_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* v_n_2962_, lean_object* v_d_2963_, lean_object* v_b_2964_, uint8_t v_bi_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_Expr_lam___override(v_n_2962_, v_d_2963_, v_b_2964_, v_bi_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_2967_, lean_object* v_d_2968_, lean_object* v_b_2969_, lean_object* v_bi_2970_){
_start:
{
uint8_t v_bi_boxed_2971_; lean_object* v_res_2972_; 
v_bi_boxed_2971_ = lean_unbox(v_bi_2970_);
v_res_2972_ = lean_expr_mk_lambda(v_n_2967_, v_d_2968_, v_b_2969_, v_bi_boxed_2971_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* v_n_2973_, lean_object* v_d_2974_, lean_object* v_b_2975_, uint8_t v_bi_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Lean_Expr_forallE___override(v_n_2973_, v_d_2974_, v_b_2975_, v_bi_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_2978_, lean_object* v_d_2979_, lean_object* v_b_2980_, lean_object* v_bi_2981_){
_start:
{
uint8_t v_bi_boxed_2982_; lean_object* v_res_2983_; 
v_bi_boxed_2982_ = lean_unbox(v_bi_2981_);
v_res_2983_ = lean_expr_mk_forall(v_n_2978_, v_d_2979_, v_b_2980_, v_bi_boxed_2982_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* v_n_2984_, lean_object* v_t_2985_, lean_object* v_v_2986_, lean_object* v_b_2987_, uint8_t v_nondep_2988_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Lean_Expr_letE___override(v_n_2984_, v_t_2985_, v_v_2986_, v_b_2987_, v_nondep_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_2990_, lean_object* v_t_2991_, lean_object* v_v_2992_, lean_object* v_b_2993_, lean_object* v_nondep_2994_){
_start:
{
uint8_t v_nondep_boxed_2995_; lean_object* v_res_2996_; 
v_nondep_boxed_2995_ = lean_unbox(v_nondep_2994_);
v_res_2996_ = lean_expr_mk_let(v_n_2990_, v_t_2991_, v_v_2992_, v_b_2993_, v_nondep_boxed_2995_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_Expr_lit___override(v_l_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_2999_, lean_object* v_e_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lean_Expr_mdata___override(v_m_2999_, v_e_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_3002_, lean_object* v_idx_3003_, lean_object* v_struct_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_Expr_proj___override(v_structName_3002_, v_idx_3003_, v_struct_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_3006_, size_t v_i_3007_, size_t v_stop_3008_, lean_object* v_b_3009_){
_start:
{
uint8_t v___x_3010_; 
v___x_3010_ = lean_usize_dec_eq(v_i_3007_, v_stop_3008_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; size_t v___x_3013_; size_t v___x_3014_; 
v___x_3011_ = lean_array_uget_borrowed(v_as_3006_, v_i_3007_);
lean_inc(v___x_3011_);
v___x_3012_ = l_Lean_Expr_app___override(v_b_3009_, v___x_3011_);
v___x_3013_ = ((size_t)1ULL);
v___x_3014_ = lean_usize_add(v_i_3007_, v___x_3013_);
v_i_3007_ = v___x_3014_;
v_b_3009_ = v___x_3012_;
goto _start;
}
else
{
return v_b_3009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_3016_, lean_object* v_i_3017_, lean_object* v_stop_3018_, lean_object* v_b_3019_){
_start:
{
size_t v_i_boxed_3020_; size_t v_stop_boxed_3021_; lean_object* v_res_3022_; 
v_i_boxed_3020_ = lean_unbox_usize(v_i_3017_);
lean_dec(v_i_3017_);
v_stop_boxed_3021_ = lean_unbox_usize(v_stop_3018_);
lean_dec(v_stop_3018_);
v_res_3022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_3016_, v_i_boxed_3020_, v_stop_boxed_3021_, v_b_3019_);
lean_dec_ref(v_as_3016_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_3023_, lean_object* v_args_3024_){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; uint8_t v___x_3027_; 
v___x_3025_ = lean_unsigned_to_nat(0u);
v___x_3026_ = lean_array_get_size(v_args_3024_);
v___x_3027_ = lean_nat_dec_lt(v___x_3025_, v___x_3026_);
if (v___x_3027_ == 0)
{
return v_f_3023_;
}
else
{
uint8_t v___x_3028_; 
v___x_3028_ = lean_nat_dec_le(v___x_3026_, v___x_3026_);
if (v___x_3028_ == 0)
{
if (v___x_3027_ == 0)
{
return v_f_3023_;
}
else
{
size_t v___x_3029_; size_t v___x_3030_; lean_object* v___x_3031_; 
v___x_3029_ = ((size_t)0ULL);
v___x_3030_ = lean_usize_of_nat(v___x_3026_);
v___x_3031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3024_, v___x_3029_, v___x_3030_, v_f_3023_);
return v___x_3031_;
}
}
else
{
size_t v___x_3032_; size_t v___x_3033_; lean_object* v___x_3034_; 
v___x_3032_ = ((size_t)0ULL);
v___x_3033_ = lean_usize_of_nat(v___x_3026_);
v___x_3034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3024_, v___x_3032_, v___x_3033_, v_f_3023_);
return v___x_3034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_3035_, lean_object* v_args_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_mkAppN(v_f_3035_, v_args_3036_);
lean_dec_ref(v_args_3036_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_3038_, lean_object* v_args_3039_, lean_object* v_i_3040_, lean_object* v_e_3041_){
_start:
{
uint8_t v___x_3042_; 
v___x_3042_ = lean_nat_dec_lt(v_i_3040_, v_n_3038_);
if (v___x_3042_ == 0)
{
lean_dec(v_i_3040_);
return v_e_3041_;
}
else
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3043_ = l_Lean_instInhabitedExpr;
v___x_3044_ = lean_unsigned_to_nat(1u);
v___x_3045_ = lean_nat_add(v_i_3040_, v___x_3044_);
v___x_3046_ = lean_array_get_borrowed(v___x_3043_, v_args_3039_, v_i_3040_);
lean_dec(v_i_3040_);
lean_inc(v___x_3046_);
v___x_3047_ = l_Lean_Expr_app___override(v_e_3041_, v___x_3046_);
v_i_3040_ = v___x_3045_;
v_e_3041_ = v___x_3047_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_3049_, lean_object* v_args_3050_, lean_object* v_i_3051_, lean_object* v_e_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_3049_, v_args_3050_, v_i_3051_, v_e_3052_);
lean_dec_ref(v_args_3050_);
lean_dec(v_n_3049_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_3054_, lean_object* v_i_3055_, lean_object* v_j_3056_, lean_object* v_args_3057_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_3056_, v_args_3057_, v_i_3055_, v_f_3054_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_3059_, lean_object* v_i_3060_, lean_object* v_j_3061_, lean_object* v_args_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_Lean_mkAppRange(v_f_3059_, v_i_3060_, v_j_3061_, v_args_3062_);
lean_dec_ref(v_args_3062_);
lean_dec(v_j_3061_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_3064_, size_t v_i_3065_, size_t v_stop_3066_, lean_object* v_b_3067_){
_start:
{
uint8_t v___x_3068_; 
v___x_3068_ = lean_usize_dec_eq(v_i_3065_, v_stop_3066_);
if (v___x_3068_ == 0)
{
size_t v___x_3069_; size_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3069_ = ((size_t)1ULL);
v___x_3070_ = lean_usize_sub(v_i_3065_, v___x_3069_);
v___x_3071_ = lean_array_uget_borrowed(v_as_3064_, v___x_3070_);
lean_inc(v___x_3071_);
v___x_3072_ = l_Lean_Expr_app___override(v_b_3067_, v___x_3071_);
v_i_3065_ = v___x_3070_;
v_b_3067_ = v___x_3072_;
goto _start;
}
else
{
return v_b_3067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_3074_, lean_object* v_i_3075_, lean_object* v_stop_3076_, lean_object* v_b_3077_){
_start:
{
size_t v_i_boxed_3078_; size_t v_stop_boxed_3079_; lean_object* v_res_3080_; 
v_i_boxed_3078_ = lean_unbox_usize(v_i_3075_);
lean_dec(v_i_3075_);
v_stop_boxed_3079_ = lean_unbox_usize(v_stop_3076_);
lean_dec(v_stop_3076_);
v_res_3080_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3074_, v_i_boxed_3078_, v_stop_boxed_3079_, v_b_3077_);
lean_dec_ref(v_as_3074_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_3081_, lean_object* v_revArgs_3082_){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3083_ = lean_array_get_size(v_revArgs_3082_);
v___x_3084_ = lean_unsigned_to_nat(0u);
v___x_3085_ = lean_nat_dec_lt(v___x_3084_, v___x_3083_);
if (v___x_3085_ == 0)
{
return v_fn_3081_;
}
else
{
size_t v___x_3086_; size_t v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = lean_usize_of_nat(v___x_3083_);
v___x_3087_ = ((size_t)0ULL);
v___x_3088_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_3082_, v___x_3086_, v___x_3087_, v_fn_3081_);
return v___x_3088_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_3089_, lean_object* v_revArgs_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_mkAppRev(v_fn_3089_, v_revArgs_3090_);
lean_dec_ref(v_revArgs_3090_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = lean_expr_dbg_to_string(v_e_3093_);
lean_dec_ref(v_e_3093_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_3097_, lean_object* v_b_3098_){
_start:
{
uint8_t v_res_3099_; lean_object* v_r_3100_; 
v_res_3099_ = lean_expr_quick_lt(v_a_3097_, v_b_3098_);
lean_dec_ref(v_b_3098_);
lean_dec_ref(v_a_3097_);
v_r_3100_ = lean_box(v_res_3099_);
return v_r_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_3103_, lean_object* v_b_3104_){
_start:
{
uint8_t v_res_3105_; lean_object* v_r_3106_; 
v_res_3105_ = lean_expr_lt(v_a_3103_, v_b_3104_);
lean_dec_ref(v_b_3104_);
lean_dec_ref(v_a_3103_);
v_r_3106_ = lean_box(v_res_3105_);
return v_r_3106_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* v_a_3107_, lean_object* v_b_3108_){
_start:
{
uint8_t v___x_3109_; 
v___x_3109_ = lean_expr_quick_lt(v_a_3107_, v_b_3108_);
if (v___x_3109_ == 0)
{
uint8_t v___x_3110_; 
v___x_3110_ = lean_expr_quick_lt(v_b_3108_, v_a_3107_);
if (v___x_3110_ == 0)
{
uint8_t v___x_3111_; 
v___x_3111_ = 1;
return v___x_3111_;
}
else
{
uint8_t v___x_3112_; 
v___x_3112_ = 2;
return v___x_3112_;
}
}
else
{
uint8_t v___x_3113_; 
v___x_3113_ = 0;
return v___x_3113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_3114_, lean_object* v_b_3115_){
_start:
{
uint8_t v_res_3116_; lean_object* v_r_3117_; 
v_res_3116_ = l_Lean_Expr_quickComp(v_a_3114_, v_b_3115_);
lean_dec_ref(v_b_3115_);
lean_dec_ref(v_a_3114_);
v_r_3117_ = lean_box(v_res_3116_);
return v_r_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_3120_, lean_object* v_b_3121_){
_start:
{
uint8_t v_res_3122_; lean_object* v_r_3123_; 
v_res_3122_ = lean_expr_eqv(v_a_3120_, v_b_3121_);
lean_dec_ref(v_b_3121_);
lean_dec_ref(v_a_3120_);
v_r_3123_ = lean_box(v_res_3122_);
return v_r_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3128_, lean_object* v_b_3129_){
_start:
{
uint8_t v_res_3130_; lean_object* v_r_3131_; 
v_res_3130_ = lean_expr_equal(v_a_3128_, v_b_3129_);
lean_dec_ref(v_b_3129_);
lean_dec_ref(v_a_3128_);
v_r_3131_ = lean_box(v_res_3130_);
return v_r_3131_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* v_x_3132_){
_start:
{
if (lean_obj_tag(v_x_3132_) == 3)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3135_){
_start:
{
uint8_t v_res_3136_; lean_object* v_r_3137_; 
v_res_3136_ = l_Lean_Expr_isSort(v_x_3135_);
lean_dec_ref(v_x_3135_);
v_r_3137_ = lean_box(v_res_3136_);
return v_r_3137_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* v_x_3138_){
_start:
{
if (lean_obj_tag(v_x_3138_) == 3)
{
lean_object* v_u_3139_; 
v_u_3139_ = lean_ctor_get(v_x_3138_, 0);
if (lean_obj_tag(v_u_3139_) == 1)
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
else
{
uint8_t v___x_3142_; 
v___x_3142_ = 0;
return v___x_3142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3143_){
_start:
{
uint8_t v_res_3144_; lean_object* v_r_3145_; 
v_res_3144_ = l_Lean_Expr_isType(v_x_3143_);
lean_dec_ref(v_x_3143_);
v_r_3145_ = lean_box(v_res_3144_);
return v_r_3145_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* v_x_3146_){
_start:
{
if (lean_obj_tag(v_x_3146_) == 3)
{
lean_object* v_u_3147_; 
v_u_3147_ = lean_ctor_get(v_x_3146_, 0);
if (lean_obj_tag(v_u_3147_) == 1)
{
lean_object* v_a_3148_; 
v_a_3148_ = lean_ctor_get(v_u_3147_, 0);
if (lean_obj_tag(v_a_3148_) == 0)
{
uint8_t v___x_3149_; 
v___x_3149_ = 1;
return v___x_3149_;
}
else
{
uint8_t v___x_3150_; 
v___x_3150_ = 0;
return v___x_3150_;
}
}
else
{
uint8_t v___x_3151_; 
v___x_3151_ = 0;
return v___x_3151_;
}
}
else
{
uint8_t v___x_3152_; 
v___x_3152_ = 0;
return v___x_3152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3153_){
_start:
{
uint8_t v_res_3154_; lean_object* v_r_3155_; 
v_res_3154_ = l_Lean_Expr_isType0(v_x_3153_);
lean_dec_ref(v_x_3153_);
v_r_3155_ = lean_box(v_res_3154_);
return v_r_3155_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* v_x_3156_){
_start:
{
if (lean_obj_tag(v_x_3156_) == 3)
{
lean_object* v_u_3157_; 
v_u_3157_ = lean_ctor_get(v_x_3156_, 0);
if (lean_obj_tag(v_u_3157_) == 0)
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
else
{
uint8_t v___x_3160_; 
v___x_3160_ = 0;
return v___x_3160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3161_){
_start:
{
uint8_t v_res_3162_; lean_object* v_r_3163_; 
v_res_3162_ = l_Lean_Expr_isProp(v_x_3161_);
lean_dec_ref(v_x_3161_);
v_r_3163_ = lean_box(v_res_3162_);
return v_r_3163_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3164_){
_start:
{
if (lean_obj_tag(v_x_3164_) == 0)
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3167_){
_start:
{
uint8_t v_res_3168_; lean_object* v_r_3169_; 
v_res_3168_ = l_Lean_Expr_isBVar(v_x_3167_);
lean_dec_ref(v_x_3167_);
v_r_3169_ = lean_box(v_res_3168_);
return v_r_3169_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3170_){
_start:
{
if (lean_obj_tag(v_x_3170_) == 2)
{
uint8_t v___x_3171_; 
v___x_3171_ = 1;
return v___x_3171_;
}
else
{
uint8_t v___x_3172_; 
v___x_3172_ = 0;
return v___x_3172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3173_){
_start:
{
uint8_t v_res_3174_; lean_object* v_r_3175_; 
v_res_3174_ = l_Lean_Expr_isMVar(v_x_3173_);
lean_dec_ref(v_x_3173_);
v_r_3175_ = lean_box(v_res_3174_);
return v_r_3175_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3176_){
_start:
{
if (lean_obj_tag(v_x_3176_) == 1)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3179_){
_start:
{
uint8_t v_res_3180_; lean_object* v_r_3181_; 
v_res_3180_ = l_Lean_Expr_isFVar(v_x_3179_);
lean_dec_ref(v_x_3179_);
v_r_3181_ = lean_box(v_res_3180_);
return v_r_3181_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* v_x_3182_){
_start:
{
if (lean_obj_tag(v_x_3182_) == 5)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3185_){
_start:
{
uint8_t v_res_3186_; lean_object* v_r_3187_; 
v_res_3186_ = l_Lean_Expr_isApp(v_x_3185_);
lean_dec_ref(v_x_3185_);
v_r_3187_ = lean_box(v_res_3186_);
return v_r_3187_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* v_x_3188_){
_start:
{
if (lean_obj_tag(v_x_3188_) == 11)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3191_){
_start:
{
uint8_t v_res_3192_; lean_object* v_r_3193_; 
v_res_3192_ = l_Lean_Expr_isProj(v_x_3191_);
lean_dec_ref(v_x_3191_);
v_r_3193_ = lean_box(v_res_3192_);
return v_r_3193_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* v_x_3194_){
_start:
{
if (lean_obj_tag(v_x_3194_) == 4)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3197_){
_start:
{
uint8_t v_res_3198_; lean_object* v_r_3199_; 
v_res_3198_ = l_Lean_Expr_isConst(v_x_3197_);
lean_dec_ref(v_x_3197_);
v_r_3199_ = lean_box(v_res_3198_);
return v_r_3199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3200_, lean_object* v_x_3201_){
_start:
{
if (lean_obj_tag(v_x_3200_) == 4)
{
lean_object* v_declName_3202_; uint8_t v___x_3203_; 
v_declName_3202_ = lean_ctor_get(v_x_3200_, 0);
v___x_3203_ = lean_name_eq(v_declName_3202_, v_x_3201_);
return v___x_3203_;
}
else
{
uint8_t v___x_3204_; 
v___x_3204_ = 0;
return v___x_3204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3205_, lean_object* v_x_3206_){
_start:
{
uint8_t v_res_3207_; lean_object* v_r_3208_; 
v_res_3207_ = l_Lean_Expr_isConstOf(v_x_3205_, v_x_3206_);
lean_dec(v_x_3206_);
lean_dec_ref(v_x_3205_);
v_r_3208_ = lean_box(v_res_3207_);
return v_r_3208_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3209_, lean_object* v_x_3210_){
_start:
{
if (lean_obj_tag(v_x_3209_) == 1)
{
lean_object* v_fvarId_3211_; uint8_t v___x_3212_; 
v_fvarId_3211_ = lean_ctor_get(v_x_3209_, 0);
v___x_3212_ = lean_name_eq(v_fvarId_3211_, v_x_3210_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3214_, lean_object* v_x_3215_){
_start:
{
uint8_t v_res_3216_; lean_object* v_r_3217_; 
v_res_3216_ = l_Lean_Expr_isFVarOf(v_x_3214_, v_x_3215_);
lean_dec(v_x_3215_);
lean_dec_ref(v_x_3214_);
v_r_3217_ = lean_box(v_res_3216_);
return v_r_3217_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* v_x_3218_){
_start:
{
if (lean_obj_tag(v_x_3218_) == 7)
{
uint8_t v___x_3219_; 
v___x_3219_ = 1;
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
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3221_){
_start:
{
uint8_t v_res_3222_; lean_object* v_r_3223_; 
v_res_3222_ = l_Lean_Expr_isForall(v_x_3221_);
lean_dec_ref(v_x_3221_);
v_r_3223_ = lean_box(v_res_3222_);
return v_r_3223_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3224_){
_start:
{
if (lean_obj_tag(v_x_3224_) == 6)
{
uint8_t v___x_3225_; 
v___x_3225_ = 1;
return v___x_3225_;
}
else
{
uint8_t v___x_3226_; 
v___x_3226_ = 0;
return v___x_3226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3227_){
_start:
{
uint8_t v_res_3228_; lean_object* v_r_3229_; 
v_res_3228_ = l_Lean_Expr_isLambda(v_x_3227_);
lean_dec_ref(v_x_3227_);
v_r_3229_ = lean_box(v_res_3228_);
return v_r_3229_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3230_){
_start:
{
switch(lean_obj_tag(v_x_3230_))
{
case 6:
{
uint8_t v___x_3231_; 
v___x_3231_ = 1;
return v___x_3231_;
}
case 7:
{
uint8_t v___x_3232_; 
v___x_3232_ = 1;
return v___x_3232_;
}
default: 
{
uint8_t v___x_3233_; 
v___x_3233_ = 0;
return v___x_3233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3234_){
_start:
{
uint8_t v_res_3235_; lean_object* v_r_3236_; 
v_res_3235_ = l_Lean_Expr_isBinding(v_x_3234_);
lean_dec_ref(v_x_3234_);
v_r_3236_ = lean_box(v_res_3235_);
return v_r_3236_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* v_x_3237_){
_start:
{
if (lean_obj_tag(v_x_3237_) == 8)
{
uint8_t v___x_3238_; 
v___x_3238_ = 1;
return v___x_3238_;
}
else
{
uint8_t v___x_3239_; 
v___x_3239_ = 0;
return v___x_3239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3240_){
_start:
{
uint8_t v_res_3241_; lean_object* v_r_3242_; 
v_res_3241_ = l_Lean_Expr_isLet(v_x_3240_);
lean_dec_ref(v_x_3240_);
v_r_3242_ = lean_box(v_res_3241_);
return v_r_3242_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object* v_x_3243_){
_start:
{
if (lean_obj_tag(v_x_3243_) == 8)
{
uint8_t v_nondep_3244_; 
v_nondep_3244_ = lean_ctor_get_uint8(v_x_3243_, sizeof(void*)*4 + 8);
return v_nondep_3244_;
}
else
{
uint8_t v___x_3245_; 
v___x_3245_ = 0;
return v___x_3245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3246_){
_start:
{
uint8_t v_res_3247_; lean_object* v_r_3248_; 
v_res_3247_ = l_Lean_Expr_isHave(v_x_3246_);
lean_dec_ref(v_x_3246_);
v_r_3248_ = lean_box(v_res_3247_);
return v_r_3248_;
}
}
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object* v_a_3249_){
_start:
{
uint8_t v___x_3250_; 
v___x_3250_ = l_Lean_Expr_isHave(v_a_3249_);
lean_dec_ref(v_a_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3251_){
_start:
{
uint8_t v_res_3252_; lean_object* v_r_3253_; 
v_res_3252_ = lean_expr_is_have(v_a_3251_);
v_r_3253_ = lean_box(v_res_3252_);
return v_r_3253_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* v_x_3254_){
_start:
{
if (lean_obj_tag(v_x_3254_) == 10)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3257_){
_start:
{
uint8_t v_res_3258_; lean_object* v_r_3259_; 
v_res_3258_ = l_Lean_Expr_isMData(v_x_3257_);
lean_dec_ref(v_x_3257_);
v_r_3259_ = lean_box(v_res_3258_);
return v_r_3259_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* v_x_3260_){
_start:
{
if (lean_obj_tag(v_x_3260_) == 9)
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3263_){
_start:
{
uint8_t v_res_3264_; lean_object* v_r_3265_; 
v_res_3264_ = l_Lean_Expr_isLit(v_x_3263_);
lean_dec_ref(v_x_3263_);
v_r_3265_ = lean_box(v_res_3264_);
return v_r_3265_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3266_){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = l_Lean_instInhabitedExpr;
v___x_3268_ = lean_panic_fn_borrowed(v___x_3267_, v_msg_3266_);
return v___x_3268_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3272_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3273_ = lean_unsigned_to_nat(15u);
v___x_3274_ = lean_unsigned_to_nat(931u);
v___x_3275_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3276_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3277_ = l_mkPanicMessageWithDecl(v___x_3276_, v___x_3275_, v___x_3274_, v___x_3273_, v___x_3272_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3278_){
_start:
{
if (lean_obj_tag(v_x_3278_) == 5)
{
lean_object* v_fn_3279_; 
v_fn_3279_ = lean_ctor_get(v_x_3278_, 0);
lean_inc_ref(v_fn_3279_);
return v_fn_3279_;
}
else
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3281_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3280_);
return v___x_3281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Lean_Expr_appFn_x21(v_x_3282_);
lean_dec_ref(v_x_3282_);
return v_res_3283_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3285_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3286_ = lean_unsigned_to_nat(15u);
v___x_3287_ = lean_unsigned_to_nat(935u);
v___x_3288_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3289_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3290_ = l_mkPanicMessageWithDecl(v___x_3289_, v___x_3288_, v___x_3287_, v___x_3286_, v___x_3285_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3291_){
_start:
{
if (lean_obj_tag(v_x_3291_) == 5)
{
lean_object* v_arg_3292_; 
v_arg_3292_ = lean_ctor_get(v_x_3291_, 1);
lean_inc_ref(v_arg_3292_);
return v_arg_3292_;
}
else
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3294_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3293_);
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_Expr_appArg_x21(v_x_3295_);
lean_dec_ref(v_x_3295_);
return v_res_3296_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3298_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3299_ = lean_unsigned_to_nat(17u);
v___x_3300_ = lean_unsigned_to_nat(940u);
v___x_3301_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3302_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3303_ = l_mkPanicMessageWithDecl(v___x_3302_, v___x_3301_, v___x_3300_, v___x_3299_, v___x_3298_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3304_){
_start:
{
switch(lean_obj_tag(v_x_3304_))
{
case 10:
{
lean_object* v_expr_3305_; 
v_expr_3305_ = lean_ctor_get(v_x_3304_, 1);
v_x_3304_ = v_expr_3305_;
goto _start;
}
case 5:
{
lean_object* v_fn_3307_; 
v_fn_3307_ = lean_ctor_get(v_x_3304_, 0);
lean_inc_ref(v_fn_3307_);
return v_fn_3307_;
}
default: 
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3309_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3308_);
return v___x_3309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Lean_Expr_appFn_x21_x27(v_x_3310_);
lean_dec_ref(v_x_3310_);
return v_res_3311_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3313_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3314_ = lean_unsigned_to_nat(17u);
v___x_3315_ = lean_unsigned_to_nat(945u);
v___x_3316_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3317_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3318_ = l_mkPanicMessageWithDecl(v___x_3317_, v___x_3316_, v___x_3315_, v___x_3314_, v___x_3313_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3319_){
_start:
{
switch(lean_obj_tag(v_x_3319_))
{
case 10:
{
lean_object* v_expr_3320_; 
v_expr_3320_ = lean_ctor_get(v_x_3319_, 1);
v_x_3319_ = v_expr_3320_;
goto _start;
}
case 5:
{
lean_object* v_arg_3322_; 
v_arg_3322_ = lean_ctor_get(v_x_3319_, 1);
lean_inc_ref(v_arg_3322_);
return v_arg_3322_;
}
default: 
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3324_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3323_);
return v___x_3324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Lean_Expr_appArg_x21_x27(v_x_3325_);
lean_dec_ref(v_x_3325_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3327_){
_start:
{
lean_object* v_arg_3328_; 
v_arg_3328_ = lean_ctor_get(v_e_3327_, 1);
lean_inc_ref(v_arg_3328_);
return v_arg_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Lean_Expr_appArg___redArg(v_e_3329_);
lean_dec_ref(v_e_3329_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3331_, lean_object* v_h_3332_){
_start:
{
lean_object* v_arg_3333_; 
v_arg_3333_ = lean_ctor_get(v_e_3331_, 1);
lean_inc_ref(v_arg_3333_);
return v_arg_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3334_, lean_object* v_h_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_Expr_appArg(v_e_3334_, v_h_3335_);
lean_dec_ref(v_e_3334_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3337_){
_start:
{
lean_object* v_fn_3338_; 
v_fn_3338_ = lean_ctor_get(v_e_3337_, 0);
lean_inc_ref(v_fn_3338_);
return v_fn_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_Expr_appFn___redArg(v_e_3339_);
lean_dec_ref(v_e_3339_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3341_, lean_object* v_h_3342_){
_start:
{
lean_object* v_fn_3343_; 
v_fn_3343_ = lean_ctor_get(v_e_3341_, 0);
lean_inc_ref(v_fn_3343_);
return v_fn_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3344_, lean_object* v_h_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_Lean_Expr_appFn(v_e_3344_, v_h_3345_);
lean_dec_ref(v_e_3344_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3347_){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = lean_box(0);
v___x_3349_ = lean_panic_fn_borrowed(v___x_3348_, v_msg_3347_);
return v___x_3349_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3352_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3353_ = lean_unsigned_to_nat(14u);
v___x_3354_ = lean_unsigned_to_nat(957u);
v___x_3355_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3356_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3357_ = l_mkPanicMessageWithDecl(v___x_3356_, v___x_3355_, v___x_3354_, v___x_3353_, v___x_3352_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3358_){
_start:
{
if (lean_obj_tag(v_x_3358_) == 3)
{
lean_object* v_u_3359_; 
v_u_3359_ = lean_ctor_get(v_x_3358_, 0);
lean_inc(v_u_3359_);
return v_u_3359_;
}
else
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3361_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3360_);
return v___x_3361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l_Lean_Expr_sortLevel_x21(v_x_3362_);
lean_dec_ref(v_x_3362_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3364_){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3366_ = lean_panic_fn_borrowed(v___x_3365_, v_msg_3364_);
return v___x_3366_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3369_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3370_ = lean_unsigned_to_nat(13u);
v___x_3371_ = lean_unsigned_to_nat(961u);
v___x_3372_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3373_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3374_ = l_mkPanicMessageWithDecl(v___x_3373_, v___x_3372_, v___x_3371_, v___x_3370_, v___x_3369_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3375_){
_start:
{
if (lean_obj_tag(v_x_3375_) == 9)
{
lean_object* v_a_3376_; 
v_a_3376_ = lean_ctor_get(v_x_3375_, 0);
lean_inc_ref(v_a_3376_);
return v_a_3376_;
}
else
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3378_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3377_);
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Lean_Expr_litValue_x21(v_x_3379_);
lean_dec_ref(v_x_3379_);
return v_res_3380_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3381_){
_start:
{
if (lean_obj_tag(v_x_3381_) == 9)
{
lean_object* v_a_3382_; 
v_a_3382_ = lean_ctor_get(v_x_3381_, 0);
if (lean_obj_tag(v_a_3382_) == 0)
{
uint8_t v___x_3383_; 
v___x_3383_ = 1;
return v___x_3383_;
}
else
{
uint8_t v___x_3384_; 
v___x_3384_ = 0;
return v___x_3384_;
}
}
else
{
uint8_t v___x_3385_; 
v___x_3385_ = 0;
return v___x_3385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3386_){
_start:
{
uint8_t v_res_3387_; lean_object* v_r_3388_; 
v_res_3387_ = l_Lean_Expr_isRawNatLit(v_x_3386_);
lean_dec_ref(v_x_3386_);
v_r_3388_ = lean_box(v_res_3387_);
return v_r_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3389_){
_start:
{
if (lean_obj_tag(v_x_3389_) == 9)
{
lean_object* v_a_3390_; 
v_a_3390_ = lean_ctor_get(v_x_3389_, 0);
lean_inc_ref(v_a_3390_);
lean_dec_ref_known(v_x_3389_, 1);
if (lean_obj_tag(v_a_3390_) == 0)
{
lean_object* v_val_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
v_val_3391_ = lean_ctor_get(v_a_3390_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v_a_3390_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v_a_3390_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_val_3391_);
lean_dec(v_a_3390_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
lean_ctor_set_tag(v___x_3393_, 1);
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_val_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
else
{
lean_object* v___x_3399_; 
lean_dec_ref(v_a_3390_);
v___x_3399_ = lean_box(0);
return v___x_3399_;
}
}
else
{
lean_object* v___x_3400_; 
lean_dec_ref(v_x_3389_);
v___x_3400_ = lean_box(0);
return v___x_3400_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3401_){
_start:
{
if (lean_obj_tag(v_x_3401_) == 9)
{
lean_object* v_a_3402_; 
v_a_3402_ = lean_ctor_get(v_x_3401_, 0);
if (lean_obj_tag(v_a_3402_) == 1)
{
uint8_t v___x_3403_; 
v___x_3403_ = 1;
return v___x_3403_;
}
else
{
uint8_t v___x_3404_; 
v___x_3404_ = 0;
return v___x_3404_;
}
}
else
{
uint8_t v___x_3405_; 
v___x_3405_ = 0;
return v___x_3405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3406_){
_start:
{
uint8_t v_res_3407_; lean_object* v_r_3408_; 
v_res_3407_ = l_Lean_Expr_isStringLit(v_x_3406_);
lean_dec_ref(v_x_3406_);
v_r_3408_ = lean_box(v_res_3407_);
return v_r_3408_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3413_){
_start:
{
if (lean_obj_tag(v_x_3413_) == 5)
{
lean_object* v_fn_3414_; 
v_fn_3414_ = lean_ctor_get(v_x_3413_, 0);
if (lean_obj_tag(v_fn_3414_) == 4)
{
lean_object* v_arg_3415_; lean_object* v_declName_3416_; lean_object* v___x_3417_; uint8_t v___x_3418_; 
v_arg_3415_ = lean_ctor_get(v_x_3413_, 1);
v_declName_3416_ = lean_ctor_get(v_fn_3414_, 0);
v___x_3417_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3418_ = lean_name_eq(v_declName_3416_, v___x_3417_);
if (v___x_3418_ == 0)
{
return v___x_3418_;
}
else
{
uint8_t v___x_3419_; 
v___x_3419_ = l_Lean_Expr_isRawNatLit(v_arg_3415_);
return v___x_3419_;
}
}
else
{
uint8_t v___x_3420_; 
v___x_3420_ = 0;
return v___x_3420_;
}
}
else
{
uint8_t v___x_3421_; 
v___x_3421_ = 0;
return v___x_3421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3422_){
_start:
{
uint8_t v_res_3423_; lean_object* v_r_3424_; 
v_res_3423_ = l_Lean_Expr_isCharLit(v_x_3422_);
lean_dec_ref(v_x_3422_);
v_r_3424_ = lean_box(v_res_3423_);
return v_r_3424_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3425_){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = lean_box(0);
v___x_3427_ = lean_panic_fn_borrowed(v___x_3426_, v_msg_3425_);
return v___x_3427_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3430_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3431_ = lean_unsigned_to_nat(17u);
v___x_3432_ = lean_unsigned_to_nat(985u);
v___x_3433_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3434_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3435_ = l_mkPanicMessageWithDecl(v___x_3434_, v___x_3433_, v___x_3432_, v___x_3431_, v___x_3430_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3436_){
_start:
{
if (lean_obj_tag(v_x_3436_) == 4)
{
lean_object* v_declName_3437_; 
v_declName_3437_ = lean_ctor_get(v_x_3436_, 0);
lean_inc(v_declName_3437_);
return v_declName_3437_;
}
else
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3439_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3438_);
return v___x_3439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Lean_Expr_constName_x21(v_x_3440_);
lean_dec_ref(v_x_3440_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3442_){
_start:
{
if (lean_obj_tag(v_x_3442_) == 4)
{
lean_object* v_declName_3443_; lean_object* v___x_3444_; 
v_declName_3443_ = lean_ctor_get(v_x_3442_, 0);
lean_inc(v_declName_3443_);
v___x_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3444_, 0, v_declName_3443_);
return v___x_3444_;
}
else
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_box(0);
return v___x_3445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Lean_Expr_constName_x3f(v_x_3446_);
lean_dec_ref(v_x_3446_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3448_){
_start:
{
lean_object* v___x_3449_; 
v___x_3449_ = l_Lean_Expr_constName_x3f(v_e_3448_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v___x_3450_; 
v___x_3450_ = lean_box(0);
return v___x_3450_;
}
else
{
lean_object* v_val_3451_; 
v_val_3451_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_val_3451_);
lean_dec_ref_known(v___x_3449_, 1);
return v_val_3451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l_Lean_Expr_constName(v_e_3452_);
lean_dec_ref(v_e_3452_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3454_){
_start:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = lean_box(0);
v___x_3456_ = lean_panic_fn_borrowed(v___x_3455_, v_msg_3454_);
return v___x_3456_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3458_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3459_ = lean_unsigned_to_nat(18u);
v___x_3460_ = lean_unsigned_to_nat(1005u);
v___x_3461_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3462_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3463_ = l_mkPanicMessageWithDecl(v___x_3462_, v___x_3461_, v___x_3460_, v___x_3459_, v___x_3458_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3464_){
_start:
{
if (lean_obj_tag(v_x_3464_) == 4)
{
lean_object* v_us_3465_; 
v_us_3465_ = lean_ctor_get(v_x_3464_, 1);
lean_inc(v_us_3465_);
return v_us_3465_;
}
else
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3467_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3466_);
return v___x_3467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3468_){
_start:
{
lean_object* v_res_3469_; 
v_res_3469_ = l_Lean_Expr_constLevels_x21(v_x_3468_);
lean_dec_ref(v_x_3468_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3470_){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = lean_unsigned_to_nat(0u);
v___x_3472_ = lean_panic_fn_borrowed(v___x_3471_, v_msg_3470_);
return v___x_3472_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3475_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3476_ = lean_unsigned_to_nat(16u);
v___x_3477_ = lean_unsigned_to_nat(1009u);
v___x_3478_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3479_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3480_ = l_mkPanicMessageWithDecl(v___x_3479_, v___x_3478_, v___x_3477_, v___x_3476_, v___x_3475_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3481_){
_start:
{
if (lean_obj_tag(v_x_3481_) == 0)
{
lean_object* v_deBruijnIndex_3482_; 
v_deBruijnIndex_3482_ = lean_ctor_get(v_x_3481_, 0);
lean_inc(v_deBruijnIndex_3482_);
return v_deBruijnIndex_3482_;
}
else
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3484_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3483_);
return v___x_3484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Lean_Expr_bvarIdx_x21(v_x_3485_);
lean_dec_ref(v_x_3485_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3487_){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3488_ = lean_box(0);
v___x_3489_ = lean_panic_fn_borrowed(v___x_3488_, v_msg_3487_);
return v___x_3489_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3492_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3493_ = lean_unsigned_to_nat(14u);
v___x_3494_ = lean_unsigned_to_nat(1013u);
v___x_3495_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3496_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3497_ = l_mkPanicMessageWithDecl(v___x_3496_, v___x_3495_, v___x_3494_, v___x_3493_, v___x_3492_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3498_){
_start:
{
if (lean_obj_tag(v_x_3498_) == 1)
{
lean_object* v_fvarId_3499_; 
v_fvarId_3499_ = lean_ctor_get(v_x_3498_, 0);
lean_inc(v_fvarId_3499_);
return v_fvarId_3499_;
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3501_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3500_);
return v___x_3501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Expr_fvarId_x21(v_x_3502_);
lean_dec_ref(v_x_3502_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3504_){
_start:
{
if (lean_obj_tag(v_x_3504_) == 1)
{
lean_object* v_fvarId_3505_; lean_object* v___x_3506_; 
v_fvarId_3505_ = lean_ctor_get(v_x_3504_, 0);
lean_inc(v_fvarId_3505_);
v___x_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3506_, 0, v_fvarId_3505_);
return v___x_3506_;
}
else
{
lean_object* v___x_3507_; 
v___x_3507_ = lean_box(0);
return v___x_3507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Lean_Expr_fvarId_x3f(v_x_3508_);
lean_dec_ref(v_x_3508_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3510_){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = lean_box(0);
v___x_3512_ = lean_panic_fn_borrowed(v___x_3511_, v_msg_3510_);
return v___x_3512_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3515_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3516_ = lean_unsigned_to_nat(14u);
v___x_3517_ = lean_unsigned_to_nat(1021u);
v___x_3518_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3519_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3520_ = l_mkPanicMessageWithDecl(v___x_3519_, v___x_3518_, v___x_3517_, v___x_3516_, v___x_3515_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3521_){
_start:
{
if (lean_obj_tag(v_x_3521_) == 2)
{
lean_object* v_mvarId_3522_; 
v_mvarId_3522_ = lean_ctor_get(v_x_3521_, 0);
lean_inc(v_mvarId_3522_);
return v_mvarId_3522_;
}
else
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3523_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3524_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3523_);
return v___x_3524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Lean_Expr_mvarId_x21(v_x_3525_);
lean_dec_ref(v_x_3525_);
return v_res_3526_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3529_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3530_ = lean_unsigned_to_nat(23u);
v___x_3531_ = lean_unsigned_to_nat(1026u);
v___x_3532_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3533_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3534_ = l_mkPanicMessageWithDecl(v___x_3533_, v___x_3532_, v___x_3531_, v___x_3530_, v___x_3529_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3535_){
_start:
{
switch(lean_obj_tag(v_x_3535_))
{
case 7:
{
lean_object* v_binderName_3536_; 
v_binderName_3536_ = lean_ctor_get(v_x_3535_, 0);
lean_inc(v_binderName_3536_);
return v_binderName_3536_;
}
case 6:
{
lean_object* v_binderName_3537_; 
v_binderName_3537_ = lean_ctor_get(v_x_3535_, 0);
lean_inc(v_binderName_3537_);
return v_binderName_3537_;
}
default: 
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3539_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3538_);
return v___x_3539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_Expr_bindingName_x21(v_x_3540_);
lean_dec_ref(v_x_3540_);
return v_res_3541_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3543_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3544_ = lean_unsigned_to_nat(23u);
v___x_3545_ = lean_unsigned_to_nat(1031u);
v___x_3546_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3547_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3548_ = l_mkPanicMessageWithDecl(v___x_3547_, v___x_3546_, v___x_3545_, v___x_3544_, v___x_3543_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3549_){
_start:
{
switch(lean_obj_tag(v_x_3549_))
{
case 7:
{
lean_object* v_binderType_3550_; 
v_binderType_3550_ = lean_ctor_get(v_x_3549_, 1);
lean_inc_ref(v_binderType_3550_);
return v_binderType_3550_;
}
case 6:
{
lean_object* v_binderType_3551_; 
v_binderType_3551_ = lean_ctor_get(v_x_3549_, 1);
lean_inc_ref(v_binderType_3551_);
return v_binderType_3551_;
}
default: 
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3553_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3552_);
return v___x_3553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Lean_Expr_bindingDomain_x21(v_x_3554_);
lean_dec_ref(v_x_3554_);
return v_res_3555_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3557_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3558_ = lean_unsigned_to_nat(23u);
v___x_3559_ = lean_unsigned_to_nat(1036u);
v___x_3560_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3561_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3562_ = l_mkPanicMessageWithDecl(v___x_3561_, v___x_3560_, v___x_3559_, v___x_3558_, v___x_3557_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3563_){
_start:
{
switch(lean_obj_tag(v_x_3563_))
{
case 7:
{
lean_object* v_body_3564_; 
v_body_3564_ = lean_ctor_get(v_x_3563_, 2);
lean_inc_ref(v_body_3564_);
return v_body_3564_;
}
case 6:
{
lean_object* v_body_3565_; 
v_body_3565_ = lean_ctor_get(v_x_3563_, 2);
lean_inc_ref(v_body_3565_);
return v_body_3565_;
}
default: 
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3567_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3566_);
return v___x_3567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_Expr_bindingBody_x21(v_x_3568_);
lean_dec_ref(v_x_3568_);
return v_res_3569_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3570_){
_start:
{
uint8_t v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; uint8_t v___x_3574_; 
v___x_3571_ = 0;
v___x_3572_ = lean_box(v___x_3571_);
v___x_3573_ = lean_panic_fn_borrowed(v___x_3572_, v_msg_3570_);
lean_dec(v___x_3572_);
v___x_3574_ = lean_unbox(v___x_3573_);
lean_dec(v___x_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3575_){
_start:
{
uint8_t v_res_3576_; lean_object* v_r_3577_; 
v_res_3576_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3575_);
v_r_3577_ = lean_box(v_res_3576_);
return v_r_3577_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3579_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3580_ = lean_unsigned_to_nat(24u);
v___x_3581_ = lean_unsigned_to_nat(1041u);
v___x_3582_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3583_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3584_ = l_mkPanicMessageWithDecl(v___x_3583_, v___x_3582_, v___x_3581_, v___x_3580_, v___x_3579_);
return v___x_3584_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3585_){
_start:
{
switch(lean_obj_tag(v_x_3585_))
{
case 7:
{
uint8_t v_binderInfo_3586_; 
v_binderInfo_3586_ = lean_ctor_get_uint8(v_x_3585_, sizeof(void*)*3 + 8);
return v_binderInfo_3586_;
}
case 6:
{
uint8_t v_binderInfo_3587_; 
v_binderInfo_3587_ = lean_ctor_get_uint8(v_x_3585_, sizeof(void*)*3 + 8);
return v_binderInfo_3587_;
}
default: 
{
lean_object* v___x_3588_; uint8_t v___x_3589_; 
v___x_3588_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3589_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3588_);
return v___x_3589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3590_){
_start:
{
uint8_t v_res_3591_; lean_object* v_r_3592_; 
v_res_3591_ = l_Lean_Expr_bindingInfo_x21(v_x_3590_);
lean_dec_ref(v_x_3590_);
v_r_3592_ = lean_box(v_res_3591_);
return v_r_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3593_){
_start:
{
lean_object* v_binderName_3594_; 
v_binderName_3594_ = lean_ctor_get(v_x_3593_, 0);
lean_inc(v_binderName_3594_);
return v_binderName_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Lean_Expr_forallName___redArg(v_x_3595_);
lean_dec_ref(v_x_3595_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3597_, lean_object* v_x_3598_){
_start:
{
lean_object* v_binderName_3599_; 
v_binderName_3599_ = lean_ctor_get(v_x_3597_, 0);
lean_inc(v_binderName_3599_);
return v_binderName_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3600_, lean_object* v_x_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lean_Expr_forallName(v_x_3600_, v_x_3601_);
lean_dec_ref(v_x_3600_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3603_){
_start:
{
lean_object* v_binderType_3604_; 
v_binderType_3604_ = lean_ctor_get(v_x_3603_, 1);
lean_inc_ref(v_binderType_3604_);
return v_binderType_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Lean_Expr_forallDomain___redArg(v_x_3605_);
lean_dec_ref(v_x_3605_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3607_, lean_object* v_x_3608_){
_start:
{
lean_object* v_binderType_3609_; 
v_binderType_3609_ = lean_ctor_get(v_x_3607_, 1);
lean_inc_ref(v_binderType_3609_);
return v_binderType_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3610_, lean_object* v_x_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Lean_Expr_forallDomain(v_x_3610_, v_x_3611_);
lean_dec_ref(v_x_3610_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3613_){
_start:
{
lean_object* v_body_3614_; 
v_body_3614_ = lean_ctor_get(v_x_3613_, 2);
lean_inc_ref(v_body_3614_);
return v_body_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Lean_Expr_forallBody___redArg(v_x_3615_);
lean_dec_ref(v_x_3615_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3617_, lean_object* v_x_3618_){
_start:
{
lean_object* v_body_3619_; 
v_body_3619_ = lean_ctor_get(v_x_3617_, 2);
lean_inc_ref(v_body_3619_);
return v_body_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3620_, lean_object* v_x_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_Expr_forallBody(v_x_3620_, v_x_3621_);
lean_dec_ref(v_x_3620_);
return v_res_3622_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3623_){
_start:
{
uint8_t v_binderInfo_3624_; 
v_binderInfo_3624_ = lean_ctor_get_uint8(v_x_3623_, sizeof(void*)*3 + 8);
return v_binderInfo_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3625_){
_start:
{
uint8_t v_res_3626_; lean_object* v_r_3627_; 
v_res_3626_ = l_Lean_Expr_forallInfo___redArg(v_x_3625_);
lean_dec_ref(v_x_3625_);
v_r_3627_ = lean_box(v_res_3626_);
return v_r_3627_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3628_, lean_object* v_x_3629_){
_start:
{
uint8_t v_binderInfo_3630_; 
v_binderInfo_3630_ = lean_ctor_get_uint8(v_x_3628_, sizeof(void*)*3 + 8);
return v_binderInfo_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3631_, lean_object* v_x_3632_){
_start:
{
uint8_t v_res_3633_; lean_object* v_r_3634_; 
v_res_3633_ = l_Lean_Expr_forallInfo(v_x_3631_, v_x_3632_);
lean_dec_ref(v_x_3631_);
v_r_3634_ = lean_box(v_res_3633_);
return v_r_3634_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3637_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3638_ = lean_unsigned_to_nat(17u);
v___x_3639_ = lean_unsigned_to_nat(1057u);
v___x_3640_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3641_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3642_ = l_mkPanicMessageWithDecl(v___x_3641_, v___x_3640_, v___x_3639_, v___x_3638_, v___x_3637_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3643_){
_start:
{
if (lean_obj_tag(v_x_3643_) == 8)
{
lean_object* v_declName_3644_; 
v_declName_3644_ = lean_ctor_get(v_x_3643_, 0);
lean_inc(v_declName_3644_);
return v_declName_3644_;
}
else
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3646_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3645_);
return v___x_3646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Lean_Expr_letName_x21(v_x_3647_);
lean_dec_ref(v_x_3647_);
return v_res_3648_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3650_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3651_ = lean_unsigned_to_nat(19u);
v___x_3652_ = lean_unsigned_to_nat(1061u);
v___x_3653_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3654_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3655_ = l_mkPanicMessageWithDecl(v___x_3654_, v___x_3653_, v___x_3652_, v___x_3651_, v___x_3650_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3656_){
_start:
{
if (lean_obj_tag(v_x_3656_) == 8)
{
lean_object* v_type_3657_; 
v_type_3657_ = lean_ctor_get(v_x_3656_, 1);
lean_inc_ref(v_type_3657_);
return v_type_3657_;
}
else
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3659_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3658_);
return v___x_3659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l_Lean_Expr_letType_x21(v_x_3660_);
lean_dec_ref(v_x_3660_);
return v_res_3661_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3663_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3664_ = lean_unsigned_to_nat(21u);
v___x_3665_ = lean_unsigned_to_nat(1065u);
v___x_3666_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3667_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3668_ = l_mkPanicMessageWithDecl(v___x_3667_, v___x_3666_, v___x_3665_, v___x_3664_, v___x_3663_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3669_){
_start:
{
if (lean_obj_tag(v_x_3669_) == 8)
{
lean_object* v_value_3670_; 
v_value_3670_ = lean_ctor_get(v_x_3669_, 2);
lean_inc_ref(v_value_3670_);
return v_value_3670_;
}
else
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3671_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3672_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3671_);
return v___x_3672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_Expr_letValue_x21(v_x_3673_);
lean_dec_ref(v_x_3673_);
return v_res_3674_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3676_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3677_ = lean_unsigned_to_nat(23u);
v___x_3678_ = lean_unsigned_to_nat(1069u);
v___x_3679_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3680_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3681_ = l_mkPanicMessageWithDecl(v___x_3680_, v___x_3679_, v___x_3678_, v___x_3677_, v___x_3676_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3682_){
_start:
{
if (lean_obj_tag(v_x_3682_) == 8)
{
lean_object* v_body_3683_; 
v_body_3683_ = lean_ctor_get(v_x_3682_, 3);
lean_inc_ref(v_body_3683_);
return v_body_3683_;
}
else
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3685_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3684_);
return v___x_3685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Lean_Expr_letBody_x21(v_x_3686_);
lean_dec_ref(v_x_3686_);
return v_res_3687_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3688_){
_start:
{
uint8_t v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; uint8_t v___x_3692_; 
v___x_3689_ = 0;
v___x_3690_ = lean_box(v___x_3689_);
v___x_3691_ = lean_panic_fn_borrowed(v___x_3690_, v_msg_3688_);
lean_dec(v___x_3690_);
v___x_3692_ = lean_unbox(v___x_3691_);
lean_dec(v___x_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3693_){
_start:
{
uint8_t v_res_3694_; lean_object* v_r_3695_; 
v_res_3694_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3693_);
v_r_3695_ = lean_box(v_res_3694_);
return v_r_3695_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3697_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3698_ = lean_unsigned_to_nat(27u);
v___x_3699_ = lean_unsigned_to_nat(1073u);
v___x_3700_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3701_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3702_ = l_mkPanicMessageWithDecl(v___x_3701_, v___x_3700_, v___x_3699_, v___x_3698_, v___x_3697_);
return v___x_3702_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3703_){
_start:
{
if (lean_obj_tag(v_x_3703_) == 8)
{
uint8_t v_nondep_3704_; 
v_nondep_3704_ = lean_ctor_get_uint8(v_x_3703_, sizeof(void*)*4 + 8);
return v_nondep_3704_;
}
else
{
lean_object* v___x_3705_; uint8_t v___x_3706_; 
v___x_3705_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3706_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3705_);
return v___x_3706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3707_){
_start:
{
uint8_t v_res_3708_; lean_object* v_r_3709_; 
v_res_3708_ = l_Lean_Expr_letNondep_x21(v_x_3707_);
lean_dec_ref(v_x_3707_);
v_r_3709_ = lean_box(v_res_3708_);
return v_r_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3710_){
_start:
{
if (lean_obj_tag(v_x_3710_) == 10)
{
lean_object* v_expr_3711_; 
v_expr_3711_ = lean_ctor_get(v_x_3710_, 1);
v_x_3710_ = v_expr_3711_;
goto _start;
}
else
{
lean_inc_ref(v_x_3710_);
return v_x_3710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l_Lean_Expr_consumeMData(v_x_3713_);
lean_dec_ref(v_x_3713_);
return v_res_3714_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3717_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3718_ = lean_unsigned_to_nat(17u);
v___x_3719_ = lean_unsigned_to_nat(1081u);
v___x_3720_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3721_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3722_ = l_mkPanicMessageWithDecl(v___x_3721_, v___x_3720_, v___x_3719_, v___x_3718_, v___x_3717_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3723_){
_start:
{
if (lean_obj_tag(v_x_3723_) == 10)
{
lean_object* v_expr_3724_; 
v_expr_3724_ = lean_ctor_get(v_x_3723_, 1);
lean_inc_ref(v_expr_3724_);
return v_expr_3724_;
}
else
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3725_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3726_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3725_);
return v___x_3726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_Lean_Expr_mdataExpr_x21(v_x_3727_);
lean_dec_ref(v_x_3727_);
return v_res_3728_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3731_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3732_ = lean_unsigned_to_nat(18u);
v___x_3733_ = lean_unsigned_to_nat(1085u);
v___x_3734_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3735_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3736_ = l_mkPanicMessageWithDecl(v___x_3735_, v___x_3734_, v___x_3733_, v___x_3732_, v___x_3731_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3737_){
_start:
{
if (lean_obj_tag(v_x_3737_) == 11)
{
lean_object* v_struct_3738_; 
v_struct_3738_ = lean_ctor_get(v_x_3737_, 2);
lean_inc_ref(v_struct_3738_);
return v_struct_3738_;
}
else
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3740_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3739_);
return v___x_3740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_Expr_projExpr_x21(v_x_3741_);
lean_dec_ref(v_x_3741_);
return v_res_3742_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3744_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3745_ = lean_unsigned_to_nat(18u);
v___x_3746_ = lean_unsigned_to_nat(1089u);
v___x_3747_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3748_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3749_ = l_mkPanicMessageWithDecl(v___x_3748_, v___x_3747_, v___x_3746_, v___x_3745_, v___x_3744_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3750_){
_start:
{
if (lean_obj_tag(v_x_3750_) == 11)
{
lean_object* v_idx_3751_; 
v_idx_3751_ = lean_ctor_get(v_x_3750_, 1);
lean_inc(v_idx_3751_);
return v_idx_3751_;
}
else
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3753_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3752_);
return v___x_3753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_Expr_projIdx_x21(v_x_3754_);
lean_dec_ref(v_x_3754_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3756_){
_start:
{
if (lean_obj_tag(v_x_3756_) == 7)
{
lean_object* v_body_3757_; 
v_body_3757_ = lean_ctor_get(v_x_3756_, 2);
v_x_3756_ = v_body_3757_;
goto _start;
}
else
{
lean_inc_ref(v_x_3756_);
return v_x_3756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l_Lean_Expr_getForallBody(v_x_3759_);
lean_dec_ref(v_x_3759_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3761_, lean_object* v_x_3762_){
_start:
{
lean_object* v_zero_3763_; uint8_t v_isZero_3764_; 
v_zero_3763_ = lean_unsigned_to_nat(0u);
v_isZero_3764_ = lean_nat_dec_eq(v_x_3761_, v_zero_3763_);
if (v_isZero_3764_ == 1)
{
lean_dec(v_x_3761_);
lean_inc_ref(v_x_3762_);
return v_x_3762_;
}
else
{
if (lean_obj_tag(v_x_3762_) == 7)
{
lean_object* v_body_3765_; lean_object* v_one_3766_; lean_object* v_n_3767_; 
v_body_3765_ = lean_ctor_get(v_x_3762_, 2);
v_one_3766_ = lean_unsigned_to_nat(1u);
v_n_3767_ = lean_nat_sub(v_x_3761_, v_one_3766_);
lean_dec(v_x_3761_);
v_x_3761_ = v_n_3767_;
v_x_3762_ = v_body_3765_;
goto _start;
}
else
{
lean_dec(v_x_3761_);
lean_inc_ref(v_x_3762_);
return v_x_3762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3769_, lean_object* v_x_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3769_, v_x_3770_);
lean_dec_ref(v_x_3770_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3772_){
_start:
{
if (lean_obj_tag(v_x_3772_) == 7)
{
lean_object* v_binderName_3773_; lean_object* v_body_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v_binderName_3773_ = lean_ctor_get(v_x_3772_, 0);
v_body_3774_ = lean_ctor_get(v_x_3772_, 2);
v___x_3775_ = l_Lean_Expr_getForallBinderNames(v_body_3774_);
lean_inc(v_binderName_3773_);
v___x_3776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3776_, 0, v_binderName_3773_);
lean_ctor_set(v___x_3776_, 1, v___x_3775_);
return v___x_3776_;
}
else
{
lean_object* v___x_3777_; 
v___x_3777_ = lean_box(0);
return v___x_3777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l_Lean_Expr_getForallBinderNames(v_x_3778_);
lean_dec_ref(v_x_3778_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3780_){
_start:
{
switch(lean_obj_tag(v_x_3780_))
{
case 10:
{
lean_object* v_expr_3781_; 
v_expr_3781_ = lean_ctor_get(v_x_3780_, 1);
v_x_3780_ = v_expr_3781_;
goto _start;
}
case 7:
{
lean_object* v_body_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v_body_3783_ = lean_ctor_get(v_x_3780_, 2);
v___x_3784_ = l_Lean_Expr_getNumHeadForalls(v_body_3783_);
v___x_3785_ = lean_unsigned_to_nat(1u);
v___x_3786_ = lean_nat_add(v___x_3784_, v___x_3785_);
lean_dec(v___x_3784_);
return v___x_3786_;
}
default: 
{
lean_object* v___x_3787_; 
v___x_3787_ = lean_unsigned_to_nat(0u);
return v___x_3787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l_Lean_Expr_getNumHeadForalls(v_x_3788_);
lean_dec_ref(v_x_3788_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3790_){
_start:
{
if (lean_obj_tag(v_x_3790_) == 5)
{
lean_object* v_fn_3791_; 
v_fn_3791_ = lean_ctor_get(v_x_3790_, 0);
v_x_3790_ = v_fn_3791_;
goto _start;
}
else
{
lean_inc_ref(v_x_3790_);
return v_x_3790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_Lean_Expr_getAppFn(v_x_3793_);
lean_dec_ref(v_x_3793_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3795_){
_start:
{
switch(lean_obj_tag(v_x_3795_))
{
case 5:
{
lean_object* v_fn_3796_; 
v_fn_3796_ = lean_ctor_get(v_x_3795_, 0);
v_x_3795_ = v_fn_3796_;
goto _start;
}
case 10:
{
lean_object* v_expr_3798_; 
v_expr_3798_ = lean_ctor_get(v_x_3795_, 1);
v_x_3795_ = v_expr_3798_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3795_);
return v_x_3795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_Expr_getAppFn_x27(v_x_3800_);
lean_dec_ref(v_x_3800_);
return v_res_3801_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3802_, lean_object* v_n_3803_){
_start:
{
lean_object* v___x_3804_; 
v___x_3804_ = l_Lean_Expr_getAppFn(v_e_3802_);
if (lean_obj_tag(v___x_3804_) == 4)
{
lean_object* v_declName_3805_; uint8_t v___x_3806_; 
v_declName_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_declName_3805_);
lean_dec_ref_known(v___x_3804_, 2);
v___x_3806_ = lean_name_eq(v_declName_3805_, v_n_3803_);
lean_dec(v_declName_3805_);
return v___x_3806_;
}
else
{
uint8_t v___x_3807_; 
lean_dec_ref(v___x_3804_);
v___x_3807_ = 0;
return v___x_3807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3808_, lean_object* v_n_3809_){
_start:
{
uint8_t v_res_3810_; lean_object* v_r_3811_; 
v_res_3810_ = l_Lean_Expr_isAppOf(v_e_3808_, v_n_3809_);
lean_dec(v_n_3809_);
lean_dec_ref(v_e_3808_);
v_r_3811_ = lean_box(v_res_3810_);
return v_r_3811_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3812_, lean_object* v_x_3813_, lean_object* v_x_3814_){
_start:
{
switch(lean_obj_tag(v_x_3812_))
{
case 4:
{
lean_object* v_declName_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; 
v_declName_3815_ = lean_ctor_get(v_x_3812_, 0);
v___x_3816_ = lean_unsigned_to_nat(0u);
v___x_3817_ = lean_nat_dec_eq(v_x_3814_, v___x_3816_);
lean_dec(v_x_3814_);
if (v___x_3817_ == 0)
{
return v___x_3817_;
}
else
{
uint8_t v___x_3818_; 
v___x_3818_ = lean_name_eq(v_declName_3815_, v_x_3813_);
return v___x_3818_;
}
}
case 5:
{
lean_object* v_fn_3819_; lean_object* v_zero_3820_; uint8_t v_isZero_3821_; 
v_fn_3819_ = lean_ctor_get(v_x_3812_, 0);
v_zero_3820_ = lean_unsigned_to_nat(0u);
v_isZero_3821_ = lean_nat_dec_eq(v_x_3814_, v_zero_3820_);
if (v_isZero_3821_ == 0)
{
lean_object* v_one_3822_; lean_object* v_n_3823_; 
v_one_3822_ = lean_unsigned_to_nat(1u);
v_n_3823_ = lean_nat_sub(v_x_3814_, v_one_3822_);
lean_dec(v_x_3814_);
v_x_3812_ = v_fn_3819_;
v_x_3814_ = v_n_3823_;
goto _start;
}
else
{
uint8_t v___x_3825_; 
lean_dec(v_x_3814_);
v___x_3825_ = 0;
return v___x_3825_;
}
}
default: 
{
uint8_t v___x_3826_; 
lean_dec(v_x_3814_);
v___x_3826_ = 0;
return v___x_3826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3827_, lean_object* v_x_3828_, lean_object* v_x_3829_){
_start:
{
uint8_t v_res_3830_; lean_object* v_r_3831_; 
v_res_3830_ = l_Lean_Expr_isAppOfArity(v_x_3827_, v_x_3828_, v_x_3829_);
lean_dec(v_x_3828_);
lean_dec_ref(v_x_3827_);
v_r_3831_ = lean_box(v_res_3830_);
return v_r_3831_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3832_, lean_object* v_x_3833_, lean_object* v_x_3834_){
_start:
{
switch(lean_obj_tag(v_x_3832_))
{
case 10:
{
lean_object* v_expr_3835_; 
v_expr_3835_ = lean_ctor_get(v_x_3832_, 1);
v_x_3832_ = v_expr_3835_;
goto _start;
}
case 4:
{
lean_object* v_declName_3837_; lean_object* v___x_3838_; uint8_t v___x_3839_; 
v_declName_3837_ = lean_ctor_get(v_x_3832_, 0);
v___x_3838_ = lean_unsigned_to_nat(0u);
v___x_3839_ = lean_nat_dec_eq(v_x_3834_, v___x_3838_);
lean_dec(v_x_3834_);
if (v___x_3839_ == 0)
{
return v___x_3839_;
}
else
{
uint8_t v___x_3840_; 
v___x_3840_ = lean_name_eq(v_declName_3837_, v_x_3833_);
return v___x_3840_;
}
}
case 5:
{
lean_object* v_fn_3841_; lean_object* v_zero_3842_; uint8_t v_isZero_3843_; 
v_fn_3841_ = lean_ctor_get(v_x_3832_, 0);
v_zero_3842_ = lean_unsigned_to_nat(0u);
v_isZero_3843_ = lean_nat_dec_eq(v_x_3834_, v_zero_3842_);
if (v_isZero_3843_ == 0)
{
lean_object* v_one_3844_; lean_object* v_n_3845_; 
v_one_3844_ = lean_unsigned_to_nat(1u);
v_n_3845_ = lean_nat_sub(v_x_3834_, v_one_3844_);
lean_dec(v_x_3834_);
v_x_3832_ = v_fn_3841_;
v_x_3834_ = v_n_3845_;
goto _start;
}
else
{
uint8_t v___x_3847_; 
lean_dec(v_x_3834_);
v___x_3847_ = 0;
return v___x_3847_;
}
}
default: 
{
uint8_t v___x_3848_; 
lean_dec(v_x_3834_);
v___x_3848_ = 0;
return v___x_3848_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3849_, lean_object* v_x_3850_, lean_object* v_x_3851_){
_start:
{
uint8_t v_res_3852_; lean_object* v_r_3853_; 
v_res_3852_ = l_Lean_Expr_isAppOfArity_x27(v_x_3849_, v_x_3850_, v_x_3851_);
lean_dec(v_x_3850_);
lean_dec_ref(v_x_3849_);
v_r_3853_ = lean_box(v_res_3852_);
return v_r_3853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3854_, lean_object* v_x_3855_){
_start:
{
if (lean_obj_tag(v_x_3854_) == 5)
{
lean_object* v_fn_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v_fn_3856_ = lean_ctor_get(v_x_3854_, 0);
v___x_3857_ = lean_unsigned_to_nat(1u);
v___x_3858_ = lean_nat_add(v_x_3855_, v___x_3857_);
lean_dec(v_x_3855_);
v_x_3854_ = v_fn_3856_;
v_x_3855_ = v___x_3858_;
goto _start;
}
else
{
return v_x_3855_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3860_, lean_object* v_x_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3860_, v_x_3861_);
lean_dec_ref(v_x_3860_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3863_){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = lean_unsigned_to_nat(0u);
v___x_3865_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3863_, v___x_3864_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Lean_Expr_getAppNumArgs(v_e_3866_);
lean_dec_ref(v_e_3866_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3868_, lean_object* v_a_3869_){
_start:
{
switch(lean_obj_tag(v_a_3868_))
{
case 10:
{
lean_object* v_expr_3870_; 
v_expr_3870_ = lean_ctor_get(v_a_3868_, 1);
v_a_3868_ = v_expr_3870_;
goto _start;
}
case 5:
{
lean_object* v_fn_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v_fn_3872_ = lean_ctor_get(v_a_3868_, 0);
v___x_3873_ = lean_unsigned_to_nat(1u);
v___x_3874_ = lean_nat_add(v_a_3869_, v___x_3873_);
lean_dec(v_a_3869_);
v_a_3868_ = v_fn_3872_;
v_a_3869_ = v___x_3874_;
goto _start;
}
default: 
{
return v_a_3869_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3876_, lean_object* v_a_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3876_, v_a_3877_);
lean_dec_ref(v_a_3876_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3879_){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = lean_unsigned_to_nat(0u);
v___x_3881_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3879_, v___x_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3882_);
lean_dec_ref(v_e_3882_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3884_, lean_object* v_x_3885_){
_start:
{
lean_object* v_zero_3886_; uint8_t v_isZero_3887_; 
v_zero_3886_ = lean_unsigned_to_nat(0u);
v_isZero_3887_ = lean_nat_dec_eq(v_x_3884_, v_zero_3886_);
if (v_isZero_3887_ == 0)
{
if (lean_obj_tag(v_x_3885_) == 5)
{
lean_object* v_fn_3888_; lean_object* v_one_3889_; lean_object* v_n_3890_; 
v_fn_3888_ = lean_ctor_get(v_x_3885_, 0);
v_one_3889_ = lean_unsigned_to_nat(1u);
v_n_3890_ = lean_nat_sub(v_x_3884_, v_one_3889_);
lean_dec(v_x_3884_);
v_x_3884_ = v_n_3890_;
v_x_3885_ = v_fn_3888_;
goto _start;
}
else
{
lean_dec(v_x_3884_);
lean_inc_ref(v_x_3885_);
return v_x_3885_;
}
}
else
{
lean_dec(v_x_3884_);
lean_inc_ref(v_x_3885_);
return v_x_3885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_3892_, lean_object* v_x_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Lean_Expr_getBoundedAppFn(v_x_3892_, v_x_3893_);
lean_dec_ref(v_x_3893_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_3895_, lean_object* v_x_3896_, lean_object* v_x_3897_){
_start:
{
if (lean_obj_tag(v_x_3895_) == 5)
{
lean_object* v_fn_3898_; lean_object* v_arg_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v_fn_3898_ = lean_ctor_get(v_x_3895_, 0);
lean_inc_ref(v_fn_3898_);
v_arg_3899_ = lean_ctor_get(v_x_3895_, 1);
lean_inc_ref(v_arg_3899_);
lean_dec_ref_known(v_x_3895_, 2);
v___x_3900_ = lean_array_set(v_x_3896_, v_x_3897_, v_arg_3899_);
v___x_3901_ = lean_unsigned_to_nat(1u);
v___x_3902_ = lean_nat_sub(v_x_3897_, v___x_3901_);
lean_dec(v_x_3897_);
v_x_3895_ = v_fn_3898_;
v_x_3896_ = v___x_3900_;
v_x_3897_ = v___x_3902_;
goto _start;
}
else
{
lean_dec(v_x_3897_);
lean_dec_ref(v_x_3895_);
return v_x_3896_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_3904_; lean_object* v_dummy_3905_; 
v___x_3904_ = lean_box(0);
v_dummy_3905_ = l_Lean_Expr_sort___override(v___x_3904_);
return v_dummy_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_3906_){
_start:
{
lean_object* v_dummy_3907_; lean_object* v_nargs_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v_dummy_3907_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3908_ = l_Lean_Expr_getAppNumArgs(v_e_3906_);
lean_inc(v_nargs_3908_);
v___x_3909_ = lean_mk_array(v_nargs_3908_, v_dummy_3907_);
v___x_3910_ = lean_unsigned_to_nat(1u);
v___x_3911_ = lean_nat_sub(v_nargs_3908_, v___x_3910_);
lean_dec(v_nargs_3908_);
v___x_3912_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3906_, v___x_3909_, v___x_3911_);
return v___x_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_3913_, lean_object* v_x_3914_, lean_object* v_x_3915_){
_start:
{
if (lean_obj_tag(v_x_3913_) == 5)
{
lean_object* v_fn_3916_; lean_object* v_arg_3917_; lean_object* v_zero_3918_; uint8_t v_isZero_3919_; 
v_fn_3916_ = lean_ctor_get(v_x_3913_, 0);
lean_inc_ref(v_fn_3916_);
v_arg_3917_ = lean_ctor_get(v_x_3913_, 1);
lean_inc_ref(v_arg_3917_);
lean_dec_ref_known(v_x_3913_, 2);
v_zero_3918_ = lean_unsigned_to_nat(0u);
v_isZero_3919_ = lean_nat_dec_eq(v_x_3915_, v_zero_3918_);
if (v_isZero_3919_ == 0)
{
lean_object* v_one_3920_; lean_object* v_n_3921_; lean_object* v___x_3922_; 
v_one_3920_ = lean_unsigned_to_nat(1u);
v_n_3921_ = lean_nat_sub(v_x_3915_, v_one_3920_);
lean_dec(v_x_3915_);
v___x_3922_ = lean_array_set(v_x_3914_, v_n_3921_, v_arg_3917_);
v_x_3913_ = v_fn_3916_;
v_x_3914_ = v___x_3922_;
v_x_3915_ = v_n_3921_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3917_);
lean_dec_ref(v_fn_3916_);
lean_dec(v_x_3915_);
return v_x_3914_;
}
}
else
{
lean_dec(v_x_3915_);
lean_dec_ref(v_x_3913_);
return v_x_3914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_3924_, lean_object* v_e_3925_){
_start:
{
lean_object* v_dummy_3926_; lean_object* v___y_3928_; lean_object* v___x_3931_; uint8_t v___x_3932_; 
v_dummy_3926_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_3931_ = l_Lean_Expr_getAppNumArgs(v_e_3925_);
v___x_3932_ = lean_nat_dec_le(v_maxArgs_3924_, v___x_3931_);
if (v___x_3932_ == 0)
{
lean_dec(v_maxArgs_3924_);
v___y_3928_ = v___x_3931_;
goto v___jp_3927_;
}
else
{
lean_dec(v___x_3931_);
v___y_3928_ = v_maxArgs_3924_;
goto v___jp_3927_;
}
v___jp_3927_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
lean_inc(v___y_3928_);
v___x_3929_ = lean_mk_array(v___y_3928_, v_dummy_3926_);
v___x_3930_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_3925_, v___x_3929_, v___y_3928_);
return v___x_3930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_3933_, lean_object* v_x_3934_){
_start:
{
if (lean_obj_tag(v_x_3933_) == 5)
{
lean_object* v_fn_3935_; lean_object* v_arg_3936_; lean_object* v___x_3937_; 
v_fn_3935_ = lean_ctor_get(v_x_3933_, 0);
lean_inc_ref(v_fn_3935_);
v_arg_3936_ = lean_ctor_get(v_x_3933_, 1);
lean_inc_ref(v_arg_3936_);
lean_dec_ref_known(v_x_3933_, 2);
v___x_3937_ = lean_array_push(v_x_3934_, v_arg_3936_);
v_x_3933_ = v_fn_3935_;
v_x_3934_ = v___x_3937_;
goto _start;
}
else
{
lean_dec_ref(v_x_3933_);
return v_x_3934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_3939_){
_start:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3940_ = l_Lean_Expr_getAppNumArgs(v_e_3939_);
v___x_3941_ = lean_mk_empty_array_with_capacity(v___x_3940_);
lean_dec(v___x_3940_);
v___x_3942_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3939_, v___x_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_3943_, lean_object* v_x_3944_, lean_object* v_x_3945_, lean_object* v_x_3946_){
_start:
{
if (lean_obj_tag(v_x_3944_) == 5)
{
lean_object* v_fn_3947_; lean_object* v_arg_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v_fn_3947_ = lean_ctor_get(v_x_3944_, 0);
lean_inc_ref(v_fn_3947_);
v_arg_3948_ = lean_ctor_get(v_x_3944_, 1);
lean_inc_ref(v_arg_3948_);
lean_dec_ref_known(v_x_3944_, 2);
v___x_3949_ = lean_array_set(v_x_3945_, v_x_3946_, v_arg_3948_);
v___x_3950_ = lean_unsigned_to_nat(1u);
v___x_3951_ = lean_nat_sub(v_x_3946_, v___x_3950_);
lean_dec(v_x_3946_);
v_x_3944_ = v_fn_3947_;
v_x_3945_ = v___x_3949_;
v_x_3946_ = v___x_3951_;
goto _start;
}
else
{
lean_object* v___x_3953_; 
lean_dec(v_x_3946_);
v___x_3953_ = lean_apply_2(v_k_3943_, v_x_3944_, v_x_3945_);
return v___x_3953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_3954_, lean_object* v_k_3955_, lean_object* v_x_3956_, lean_object* v_x_3957_, lean_object* v_x_3958_){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Lean_Expr_withAppAux___redArg(v_k_3955_, v_x_3956_, v_x_3957_, v_x_3958_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_3960_, lean_object* v_k_3961_){
_start:
{
lean_object* v_dummy_3962_; lean_object* v_nargs_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v_dummy_3962_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3963_ = l_Lean_Expr_getAppNumArgs(v_e_3960_);
lean_inc(v_nargs_3963_);
v___x_3964_ = lean_mk_array(v_nargs_3963_, v_dummy_3962_);
v___x_3965_ = lean_unsigned_to_nat(1u);
v___x_3966_ = lean_nat_sub(v_nargs_3963_, v___x_3965_);
lean_dec(v_nargs_3963_);
v___x_3967_ = l_Lean_Expr_withAppAux___redArg(v_k_3961_, v_e_3960_, v___x_3964_, v___x_3966_);
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_3968_, lean_object* v_e_3969_, lean_object* v_k_3970_){
_start:
{
lean_object* v_dummy_3971_; lean_object* v_nargs_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v_dummy_3971_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3972_ = l_Lean_Expr_getAppNumArgs(v_e_3969_);
lean_inc(v_nargs_3972_);
v___x_3973_ = lean_mk_array(v_nargs_3972_, v_dummy_3971_);
v___x_3974_ = lean_unsigned_to_nat(1u);
v___x_3975_ = lean_nat_sub(v_nargs_3972_, v___x_3974_);
lean_dec(v_nargs_3972_);
v___x_3976_ = l_Lean_Expr_withAppAux___redArg(v_k_3970_, v_e_3969_, v___x_3973_, v___x_3975_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_3977_, lean_object* v_x_3978_, lean_object* v_x_3979_){
_start:
{
if (lean_obj_tag(v_x_3977_) == 5)
{
lean_object* v_fn_3980_; lean_object* v_arg_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v_fn_3980_ = lean_ctor_get(v_x_3977_, 0);
lean_inc_ref(v_fn_3980_);
v_arg_3981_ = lean_ctor_get(v_x_3977_, 1);
lean_inc_ref(v_arg_3981_);
lean_dec_ref_known(v_x_3977_, 2);
v___x_3982_ = lean_array_set(v_x_3978_, v_x_3979_, v_arg_3981_);
v___x_3983_ = lean_unsigned_to_nat(1u);
v___x_3984_ = lean_nat_sub(v_x_3979_, v___x_3983_);
lean_dec(v_x_3979_);
v_x_3977_ = v_fn_3980_;
v_x_3978_ = v___x_3982_;
v_x_3979_ = v___x_3984_;
goto _start;
}
else
{
lean_object* v___x_3986_; lean_object* v___x_3987_; 
lean_dec(v_x_3979_);
v___x_3986_ = l_Lean_Expr_constName(v_x_3977_);
lean_dec_ref(v_x_3977_);
v___x_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
lean_ctor_set(v___x_3987_, 1, v_x_3978_);
return v___x_3987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_3988_){
_start:
{
lean_object* v_dummy_3989_; lean_object* v_nargs_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v_dummy_3989_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3990_ = l_Lean_Expr_getAppNumArgs(v_e_3988_);
lean_inc(v_nargs_3990_);
v___x_3991_ = lean_mk_array(v_nargs_3990_, v_dummy_3989_);
v___x_3992_ = lean_unsigned_to_nat(1u);
v___x_3993_ = lean_nat_sub(v_nargs_3990_, v___x_3992_);
lean_dec(v_nargs_3990_);
v___x_3994_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_3988_, v___x_3991_, v___x_3993_);
return v___x_3994_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3995_; 
v___x_3995_ = l_Array_instInhabited___redArg();
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_3996_){
_start:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3997_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_3998_ = lean_panic_fn_borrowed(v___x_3997_, v_msg_3996_);
return v___x_3998_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4001_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_4002_ = lean_unsigned_to_nat(27u);
v___x_4003_ = lean_unsigned_to_nat(1246u);
v___x_4004_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_4005_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4006_ = l_mkPanicMessageWithDecl(v___x_4005_, v___x_4004_, v___x_4003_, v___x_4002_, v___x_4001_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v_zero_4010_; uint8_t v_isZero_4011_; 
v_zero_4010_ = lean_unsigned_to_nat(0u);
v_isZero_4011_ = lean_nat_dec_eq(v_a_4007_, v_zero_4010_);
if (v_isZero_4011_ == 1)
{
lean_dec_ref(v_a_4008_);
lean_dec(v_a_4007_);
return v_a_4009_;
}
else
{
if (lean_obj_tag(v_a_4008_) == 5)
{
lean_object* v_fn_4012_; lean_object* v_arg_4013_; lean_object* v_one_4014_; lean_object* v_n_4015_; lean_object* v___x_4016_; 
v_fn_4012_ = lean_ctor_get(v_a_4008_, 0);
lean_inc_ref(v_fn_4012_);
v_arg_4013_ = lean_ctor_get(v_a_4008_, 1);
lean_inc_ref(v_arg_4013_);
lean_dec_ref_known(v_a_4008_, 2);
v_one_4014_ = lean_unsigned_to_nat(1u);
v_n_4015_ = lean_nat_sub(v_a_4007_, v_one_4014_);
lean_dec(v_a_4007_);
v___x_4016_ = lean_array_set(v_a_4009_, v_n_4015_, v_arg_4013_);
v_a_4007_ = v_n_4015_;
v_a_4008_ = v_fn_4012_;
v_a_4009_ = v___x_4016_;
goto _start;
}
else
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
lean_dec_ref(v_a_4009_);
lean_dec_ref(v_a_4008_);
lean_dec(v_a_4007_);
v___x_4018_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_4019_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_4018_);
return v___x_4019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_4020_, lean_object* v_n_4021_){
_start:
{
lean_object* v_dummy_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v_dummy_4022_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_4021_);
v___x_4023_ = lean_mk_array(v_n_4021_, v_dummy_4022_);
v___x_4024_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_4021_, v_e_4020_, v___x_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_4025_, lean_object* v_n_4026_){
_start:
{
lean_object* v_zero_4027_; uint8_t v_isZero_4028_; 
v_zero_4027_ = lean_unsigned_to_nat(0u);
v_isZero_4028_ = lean_nat_dec_eq(v_n_4026_, v_zero_4027_);
if (v_isZero_4028_ == 1)
{
lean_dec(v_n_4026_);
lean_inc_ref(v_e_4025_);
return v_e_4025_;
}
else
{
if (lean_obj_tag(v_e_4025_) == 5)
{
lean_object* v_fn_4029_; lean_object* v_one_4030_; lean_object* v_n_4031_; 
v_fn_4029_ = lean_ctor_get(v_e_4025_, 0);
v_one_4030_ = lean_unsigned_to_nat(1u);
v_n_4031_ = lean_nat_sub(v_n_4026_, v_one_4030_);
lean_dec(v_n_4026_);
v_e_4025_ = v_fn_4029_;
v_n_4026_ = v_n_4031_;
goto _start;
}
else
{
lean_dec(v_n_4026_);
lean_inc_ref(v_e_4025_);
return v_e_4025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_4033_, lean_object* v_n_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_Expr_stripArgsN(v_e_4033_, v_n_4034_);
lean_dec_ref(v_e_4033_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_4036_, lean_object* v_n_4037_){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4038_ = l_Lean_Expr_getAppNumArgs(v_e_4036_);
v___x_4039_ = lean_nat_sub(v___x_4038_, v_n_4037_);
lean_dec(v___x_4038_);
v___x_4040_ = l_Lean_Expr_stripArgsN(v_e_4036_, v___x_4039_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_4041_, lean_object* v_n_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l_Lean_Expr_getAppPrefix(v_e_4041_, v_n_4042_);
lean_dec(v_n_4042_);
lean_dec_ref(v_e_4041_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_4044_, lean_object* v_inst_4045_, lean_object* v_f_4046_, lean_object* v_x_4047_){
_start:
{
size_t v_sz_4048_; size_t v___x_4049_; lean_object* v___x_4050_; 
v_sz_4048_ = lean_array_size(v_args_4044_);
v___x_4049_ = ((size_t)0ULL);
v___x_4050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4045_, v_f_4046_, v_sz_4048_, v___x_4049_, v_args_4044_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_4052_, lean_object* v_inst_4053_, lean_object* v_f_4054_, lean_object* v_toSeq_4055_, lean_object* v_fn_4056_, lean_object* v_args_4057_){
_start:
{
lean_object* v_map_4058_; lean_object* v___f_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v_map_4058_ = lean_ctor_get(v_toFunctor_4052_, 0);
lean_inc(v_map_4058_);
lean_dec_ref(v_toFunctor_4052_);
lean_inc(v_f_4054_);
v___f_4059_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4059_, 0, v_args_4057_);
lean_closure_set(v___f_4059_, 1, v_inst_4053_);
lean_closure_set(v___f_4059_, 2, v_f_4054_);
v___x_4060_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_4061_ = lean_apply_1(v_f_4054_, v_fn_4056_);
v___x_4062_ = lean_apply_4(v_map_4058_, lean_box(0), lean_box(0), v___x_4060_, v___x_4061_);
v___x_4063_ = lean_apply_4(v_toSeq_4055_, lean_box(0), lean_box(0), v___x_4062_, v___f_4059_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_4064_, lean_object* v_f_4065_, lean_object* v_e_4066_){
_start:
{
lean_object* v_toApplicative_4067_; lean_object* v_toFunctor_4068_; lean_object* v_toSeq_4069_; lean_object* v___f_4070_; lean_object* v_dummy_4071_; lean_object* v_nargs_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v_toApplicative_4067_ = lean_ctor_get(v_inst_4064_, 0);
v_toFunctor_4068_ = lean_ctor_get(v_toApplicative_4067_, 0);
lean_inc_ref(v_toFunctor_4068_);
v_toSeq_4069_ = lean_ctor_get(v_toApplicative_4067_, 2);
lean_inc(v_toSeq_4069_);
v___f_4070_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_4070_, 0, v_toFunctor_4068_);
lean_closure_set(v___f_4070_, 1, v_inst_4064_);
lean_closure_set(v___f_4070_, 2, v_f_4065_);
lean_closure_set(v___f_4070_, 3, v_toSeq_4069_);
v_dummy_4071_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4072_ = l_Lean_Expr_getAppNumArgs(v_e_4066_);
lean_inc(v_nargs_4072_);
v___x_4073_ = lean_mk_array(v_nargs_4072_, v_dummy_4071_);
v___x_4074_ = lean_unsigned_to_nat(1u);
v___x_4075_ = lean_nat_sub(v_nargs_4072_, v___x_4074_);
lean_dec(v_nargs_4072_);
v___x_4076_ = l_Lean_Expr_withAppAux___redArg(v___f_4070_, v_e_4066_, v___x_4073_, v___x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_4077_, lean_object* v_inst_4078_, lean_object* v_f_4079_, lean_object* v_e_4080_){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = l_Lean_Expr_traverseApp___redArg(v_inst_4078_, v_f_4079_, v_e_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_4082_, lean_object* v_x_4083_, lean_object* v_x_4084_){
_start:
{
if (lean_obj_tag(v_x_4083_) == 5)
{
lean_object* v_fn_4085_; lean_object* v_arg_4086_; lean_object* v___x_4087_; 
v_fn_4085_ = lean_ctor_get(v_x_4083_, 0);
lean_inc_ref(v_fn_4085_);
v_arg_4086_ = lean_ctor_get(v_x_4083_, 1);
lean_inc_ref(v_arg_4086_);
lean_dec_ref_known(v_x_4083_, 2);
v___x_4087_ = lean_array_push(v_x_4084_, v_arg_4086_);
v_x_4083_ = v_fn_4085_;
v_x_4084_ = v___x_4087_;
goto _start;
}
else
{
lean_object* v___x_4089_; 
v___x_4089_ = lean_apply_2(v_k_4082_, v_x_4083_, v_x_4084_);
return v___x_4089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_4090_, lean_object* v_k_4091_, lean_object* v_x_4092_, lean_object* v_x_4093_){
_start:
{
lean_object* v___x_4094_; 
v___x_4094_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4091_, v_x_4092_, v_x_4093_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_4095_, lean_object* v_k_4096_){
_start:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4097_ = l_Lean_Expr_getAppNumArgs(v_e_4095_);
v___x_4098_ = lean_mk_empty_array_with_capacity(v___x_4097_);
lean_dec(v___x_4097_);
v___x_4099_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4096_, v_e_4095_, v___x_4098_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_4100_, lean_object* v_e_4101_, lean_object* v_k_4102_){
_start:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4103_ = l_Lean_Expr_getAppNumArgs(v_e_4101_);
v___x_4104_ = lean_mk_empty_array_with_capacity(v___x_4103_);
lean_dec(v___x_4103_);
v___x_4105_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4102_, v_e_4101_, v___x_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_4106_, lean_object* v_x_4107_, lean_object* v_x_4108_){
_start:
{
if (lean_obj_tag(v_x_4106_) == 5)
{
lean_object* v_fn_4109_; lean_object* v_arg_4110_; lean_object* v_zero_4111_; uint8_t v_isZero_4112_; 
v_fn_4109_ = lean_ctor_get(v_x_4106_, 0);
v_arg_4110_ = lean_ctor_get(v_x_4106_, 1);
v_zero_4111_ = lean_unsigned_to_nat(0u);
v_isZero_4112_ = lean_nat_dec_eq(v_x_4107_, v_zero_4111_);
if (v_isZero_4112_ == 1)
{
lean_dec(v_x_4107_);
lean_inc_ref(v_arg_4110_);
return v_arg_4110_;
}
else
{
lean_object* v_one_4113_; lean_object* v_n_4114_; 
v_one_4113_ = lean_unsigned_to_nat(1u);
v_n_4114_ = lean_nat_sub(v_x_4107_, v_one_4113_);
lean_dec(v_x_4107_);
v_x_4106_ = v_fn_4109_;
v_x_4107_ = v_n_4114_;
goto _start;
}
}
else
{
lean_dec(v_x_4107_);
lean_inc_ref(v_x_4108_);
return v_x_4108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_4116_, lean_object* v_x_4117_, lean_object* v_x_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Lean_Expr_getRevArgD(v_x_4116_, v_x_4117_, v_x_4118_);
lean_dec_ref(v_x_4118_);
lean_dec_ref(v_x_4116_);
return v_res_4119_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4122_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4123_ = lean_unsigned_to_nat(20u);
v___x_4124_ = lean_unsigned_to_nat(1287u);
v___x_4125_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4126_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4127_ = l_mkPanicMessageWithDecl(v___x_4126_, v___x_4125_, v___x_4124_, v___x_4123_, v___x_4122_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4128_, lean_object* v_x_4129_){
_start:
{
if (lean_obj_tag(v_x_4128_) == 5)
{
lean_object* v_fn_4130_; lean_object* v_arg_4131_; lean_object* v_zero_4132_; uint8_t v_isZero_4133_; 
v_fn_4130_ = lean_ctor_get(v_x_4128_, 0);
v_arg_4131_ = lean_ctor_get(v_x_4128_, 1);
v_zero_4132_ = lean_unsigned_to_nat(0u);
v_isZero_4133_ = lean_nat_dec_eq(v_x_4129_, v_zero_4132_);
if (v_isZero_4133_ == 1)
{
lean_dec(v_x_4129_);
lean_inc_ref(v_arg_4131_);
return v_arg_4131_;
}
else
{
lean_object* v_one_4134_; lean_object* v_n_4135_; 
v_one_4134_ = lean_unsigned_to_nat(1u);
v_n_4135_ = lean_nat_sub(v_x_4129_, v_one_4134_);
lean_dec(v_x_4129_);
v_x_4128_ = v_fn_4130_;
v_x_4129_ = v_n_4135_;
goto _start;
}
}
else
{
lean_object* v___x_4137_; lean_object* v___x_4138_; 
lean_dec(v_x_4129_);
v___x_4137_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4138_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4137_);
return v___x_4138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4139_, lean_object* v_x_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l_Lean_Expr_getRevArg_x21(v_x_4139_, v_x_4140_);
lean_dec_ref(v_x_4139_);
return v_res_4141_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4143_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4144_ = lean_unsigned_to_nat(20u);
v___x_4145_ = lean_unsigned_to_nat(1294u);
v___x_4146_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4147_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4148_ = l_mkPanicMessageWithDecl(v___x_4147_, v___x_4146_, v___x_4145_, v___x_4144_, v___x_4143_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4149_, lean_object* v_x_4150_){
_start:
{
switch(lean_obj_tag(v_x_4149_))
{
case 10:
{
lean_object* v_expr_4151_; 
v_expr_4151_ = lean_ctor_get(v_x_4149_, 1);
v_x_4149_ = v_expr_4151_;
goto _start;
}
case 5:
{
lean_object* v_fn_4153_; lean_object* v_arg_4154_; lean_object* v_zero_4155_; uint8_t v_isZero_4156_; 
v_fn_4153_ = lean_ctor_get(v_x_4149_, 0);
v_arg_4154_ = lean_ctor_get(v_x_4149_, 1);
v_zero_4155_ = lean_unsigned_to_nat(0u);
v_isZero_4156_ = lean_nat_dec_eq(v_x_4150_, v_zero_4155_);
if (v_isZero_4156_ == 1)
{
lean_dec(v_x_4150_);
lean_inc_ref(v_arg_4154_);
return v_arg_4154_;
}
else
{
lean_object* v_one_4157_; lean_object* v_n_4158_; 
v_one_4157_ = lean_unsigned_to_nat(1u);
v_n_4158_ = lean_nat_sub(v_x_4150_, v_one_4157_);
lean_dec(v_x_4150_);
v_x_4149_ = v_fn_4153_;
v_x_4150_ = v_n_4158_;
goto _start;
}
}
default: 
{
lean_object* v___x_4160_; lean_object* v___x_4161_; 
lean_dec(v_x_4150_);
v___x_4160_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4161_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4160_);
return v___x_4161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4162_, lean_object* v_x_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4162_, v_x_4163_);
lean_dec_ref(v_x_4162_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4165_, lean_object* v_i_4166_, lean_object* v_n_4167_){
_start:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4168_ = lean_nat_sub(v_n_4167_, v_i_4166_);
v___x_4169_ = lean_unsigned_to_nat(1u);
v___x_4170_ = lean_nat_sub(v___x_4168_, v___x_4169_);
lean_dec(v___x_4168_);
v___x_4171_ = l_Lean_Expr_getRevArg_x21(v_e_4165_, v___x_4170_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4172_, lean_object* v_i_4173_, lean_object* v_n_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Lean_Expr_getArg_x21(v_e_4172_, v_i_4173_, v_n_4174_);
lean_dec(v_n_4174_);
lean_dec(v_i_4173_);
lean_dec_ref(v_e_4172_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4176_, lean_object* v_i_4177_, lean_object* v_n_4178_){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4179_ = lean_nat_sub(v_n_4178_, v_i_4177_);
v___x_4180_ = lean_unsigned_to_nat(1u);
v___x_4181_ = lean_nat_sub(v___x_4179_, v___x_4180_);
lean_dec(v___x_4179_);
v___x_4182_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4176_, v___x_4181_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4183_, lean_object* v_i_4184_, lean_object* v_n_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Lean_Expr_getArg_x21_x27(v_e_4183_, v_i_4184_, v_n_4185_);
lean_dec(v_n_4185_);
lean_dec(v_i_4184_);
lean_dec_ref(v_e_4183_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4187_, lean_object* v_i_4188_, lean_object* v_v_u2080_4189_, lean_object* v_n_4190_){
_start:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4191_ = lean_nat_sub(v_n_4190_, v_i_4188_);
v___x_4192_ = lean_unsigned_to_nat(1u);
v___x_4193_ = lean_nat_sub(v___x_4191_, v___x_4192_);
lean_dec(v___x_4191_);
v___x_4194_ = l_Lean_Expr_getRevArgD(v_e_4187_, v___x_4193_, v_v_u2080_4189_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4195_, lean_object* v_i_4196_, lean_object* v_v_u2080_4197_, lean_object* v_n_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Lean_Expr_getArgD(v_e_4195_, v_i_4196_, v_v_u2080_4197_, v_n_4198_);
lean_dec(v_n_4198_);
lean_dec_ref(v_v_u2080_4197_);
lean_dec(v_i_4196_);
lean_dec_ref(v_e_4195_);
return v_res_4199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4200_){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; uint8_t v___x_4203_; 
v___x_4201_ = lean_unsigned_to_nat(0u);
v___x_4202_ = l_Lean_Expr_looseBVarRange(v_e_4200_);
v___x_4203_ = lean_nat_dec_lt(v___x_4201_, v___x_4202_);
lean_dec(v___x_4202_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4204_){
_start:
{
uint8_t v_res_4205_; lean_object* v_r_4206_; 
v_res_4205_ = l_Lean_Expr_hasLooseBVars(v_e_4204_);
lean_dec_ref(v_e_4204_);
v_r_4206_ = lean_box(v_res_4205_);
return v_r_4206_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4207_){
_start:
{
if (lean_obj_tag(v_e_4207_) == 7)
{
lean_object* v_body_4208_; uint8_t v___x_4209_; 
v_body_4208_ = lean_ctor_get(v_e_4207_, 2);
v___x_4209_ = l_Lean_Expr_hasLooseBVars(v_body_4208_);
if (v___x_4209_ == 0)
{
uint8_t v___x_4210_; 
v___x_4210_ = 1;
return v___x_4210_;
}
else
{
uint8_t v___x_4211_; 
v___x_4211_ = 0;
return v___x_4211_;
}
}
else
{
uint8_t v___x_4212_; 
v___x_4212_ = 0;
return v___x_4212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4213_){
_start:
{
uint8_t v_res_4214_; lean_object* v_r_4215_; 
v_res_4214_ = l_Lean_Expr_isArrow(v_e_4213_);
lean_dec_ref(v_e_4213_);
v_r_4215_ = lean_box(v_res_4214_);
return v_r_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4218_, lean_object* v_bvarIdx_4219_){
_start:
{
uint8_t v_res_4220_; lean_object* v_r_4221_; 
v_res_4220_ = lean_expr_has_loose_bvar(v_e_4218_, v_bvarIdx_4219_);
lean_dec(v_bvarIdx_4219_);
lean_dec_ref(v_e_4218_);
v_r_4221_ = lean_box(v_res_4220_);
return v_r_4221_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4222_, lean_object* v_bvarIdx_4223_, uint8_t v_considerRange_4224_){
_start:
{
if (lean_obj_tag(v_e_4222_) == 7)
{
lean_object* v_binderType_4225_; lean_object* v_body_4226_; uint8_t v_binderInfo_4227_; uint8_t v___y_4229_; uint8_t v___x_4233_; 
v_binderType_4225_ = lean_ctor_get(v_e_4222_, 1);
v_body_4226_ = lean_ctor_get(v_e_4222_, 2);
v_binderInfo_4227_ = lean_ctor_get_uint8(v_e_4222_, sizeof(void*)*3 + 8);
v___x_4233_ = lean_expr_has_loose_bvar(v_binderType_4225_, v_bvarIdx_4223_);
if (v___x_4233_ == 0)
{
v___y_4229_ = v___x_4233_;
goto v___jp_4228_;
}
else
{
uint8_t v___x_4234_; 
v___x_4234_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4227_);
if (v___x_4234_ == 0)
{
lean_object* v___x_4235_; uint8_t v___x_4236_; 
v___x_4235_ = lean_unsigned_to_nat(0u);
v___x_4236_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4226_, v___x_4235_, v_considerRange_4224_);
v___y_4229_ = v___x_4236_;
goto v___jp_4228_;
}
else
{
v___y_4229_ = v___x_4234_;
goto v___jp_4228_;
}
}
v___jp_4228_:
{
if (v___y_4229_ == 0)
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4230_ = lean_unsigned_to_nat(1u);
v___x_4231_ = lean_nat_add(v_bvarIdx_4223_, v___x_4230_);
lean_dec(v_bvarIdx_4223_);
v_e_4222_ = v_body_4226_;
v_bvarIdx_4223_ = v___x_4231_;
goto _start;
}
else
{
lean_dec(v_bvarIdx_4223_);
return v___y_4229_;
}
}
}
else
{
if (v_considerRange_4224_ == 0)
{
lean_dec(v_bvarIdx_4223_);
return v_considerRange_4224_;
}
else
{
uint8_t v___x_4237_; 
v___x_4237_ = lean_expr_has_loose_bvar(v_e_4222_, v_bvarIdx_4223_);
lean_dec(v_bvarIdx_4223_);
return v___x_4237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4238_, lean_object* v_bvarIdx_4239_, lean_object* v_considerRange_4240_){
_start:
{
uint8_t v_considerRange_boxed_4241_; uint8_t v_res_4242_; lean_object* v_r_4243_; 
v_considerRange_boxed_4241_ = lean_unbox(v_considerRange_4240_);
v_res_4242_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4238_, v_bvarIdx_4239_, v_considerRange_boxed_4241_);
lean_dec_ref(v_e_4238_);
v_r_4243_ = lean_box(v_res_4242_);
return v_r_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4247_, lean_object* v_s_4248_, lean_object* v_d_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = lean_expr_lower_loose_bvars(v_e_4247_, v_s_4248_, v_d_4249_);
lean_dec(v_d_4249_);
lean_dec(v_s_4248_);
lean_dec_ref(v_e_4247_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4254_, lean_object* v_s_4255_, lean_object* v_d_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = lean_expr_lift_loose_bvars(v_e_4254_, v_s_4255_, v_d_4256_);
lean_dec(v_d_4256_);
lean_dec(v_s_4255_);
lean_dec_ref(v_e_4254_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4258_, lean_object* v_numParams_4259_, uint8_t v_considerRange_4260_){
_start:
{
if (lean_obj_tag(v_e_4258_) == 7)
{
lean_object* v_binderName_4261_; lean_object* v_binderType_4262_; lean_object* v_body_4263_; uint8_t v_binderInfo_4264_; lean_object* v_zero_4265_; uint8_t v_isZero_4266_; 
v_binderName_4261_ = lean_ctor_get(v_e_4258_, 0);
v_binderType_4262_ = lean_ctor_get(v_e_4258_, 1);
v_body_4263_ = lean_ctor_get(v_e_4258_, 2);
v_binderInfo_4264_ = lean_ctor_get_uint8(v_e_4258_, sizeof(void*)*3 + 8);
v_zero_4265_ = lean_unsigned_to_nat(0u);
v_isZero_4266_ = lean_nat_dec_eq(v_numParams_4259_, v_zero_4265_);
if (v_isZero_4266_ == 0)
{
lean_object* v_one_4267_; lean_object* v_n_4268_; lean_object* v_b_4269_; uint8_t v___y_4271_; uint8_t v___x_4275_; 
lean_inc_ref(v_body_4263_);
lean_inc_ref(v_binderType_4262_);
lean_inc(v_binderName_4261_);
lean_dec_ref_known(v_e_4258_, 3);
v_one_4267_ = lean_unsigned_to_nat(1u);
v_n_4268_ = lean_nat_sub(v_numParams_4259_, v_one_4267_);
v_b_4269_ = l_Lean_Expr_inferImplicit(v_body_4263_, v_n_4268_, v_considerRange_4260_);
lean_dec(v_n_4268_);
v___x_4275_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4264_);
if (v___x_4275_ == 0)
{
v___y_4271_ = v___x_4275_;
goto v___jp_4270_;
}
else
{
uint8_t v___x_4276_; 
v___x_4276_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4269_, v_zero_4265_, v_considerRange_4260_);
v___y_4271_ = v___x_4276_;
goto v___jp_4270_;
}
v___jp_4270_:
{
if (v___y_4271_ == 0)
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Lean_Expr_forallE___override(v_binderName_4261_, v_binderType_4262_, v_b_4269_, v_binderInfo_4264_);
return v___x_4272_;
}
else
{
uint8_t v___x_4273_; lean_object* v___x_4274_; 
v___x_4273_ = 1;
v___x_4274_ = l_Lean_Expr_forallE___override(v_binderName_4261_, v_binderType_4262_, v_b_4269_, v___x_4273_);
return v___x_4274_;
}
}
}
else
{
return v_e_4258_;
}
}
else
{
return v_e_4258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4277_, lean_object* v_numParams_4278_, lean_object* v_considerRange_4279_){
_start:
{
uint8_t v_considerRange_boxed_4280_; lean_object* v_res_4281_; 
v_considerRange_boxed_4280_ = lean_unbox(v_considerRange_4279_);
v_res_4281_ = l_Lean_Expr_inferImplicit(v_e_4277_, v_numParams_4278_, v_considerRange_boxed_4280_);
lean_dec(v_numParams_4278_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4282_, lean_object* v_binderInfos_x3f_4283_){
_start:
{
if (lean_obj_tag(v_e_4282_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4283_) == 1)
{
lean_object* v_binderName_4284_; lean_object* v_binderType_4285_; lean_object* v_body_4286_; uint8_t v_binderInfo_4287_; lean_object* v_head_4288_; lean_object* v_tail_4289_; lean_object* v_b_4290_; 
v_binderName_4284_ = lean_ctor_get(v_e_4282_, 0);
lean_inc(v_binderName_4284_);
v_binderType_4285_ = lean_ctor_get(v_e_4282_, 1);
lean_inc_ref(v_binderType_4285_);
v_body_4286_ = lean_ctor_get(v_e_4282_, 2);
lean_inc_ref(v_body_4286_);
v_binderInfo_4287_ = lean_ctor_get_uint8(v_e_4282_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4282_, 3);
v_head_4288_ = lean_ctor_get(v_binderInfos_x3f_4283_, 0);
v_tail_4289_ = lean_ctor_get(v_binderInfos_x3f_4283_, 1);
v_b_4290_ = l_Lean_Expr_updateForallBinderInfos(v_body_4286_, v_tail_4289_);
if (lean_obj_tag(v_head_4288_) == 0)
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Lean_Expr_forallE___override(v_binderName_4284_, v_binderType_4285_, v_b_4290_, v_binderInfo_4287_);
return v___x_4291_;
}
else
{
lean_object* v_val_4292_; uint8_t v___x_4293_; lean_object* v___x_4294_; 
v_val_4292_ = lean_ctor_get(v_head_4288_, 0);
v___x_4293_ = lean_unbox(v_val_4292_);
v___x_4294_ = l_Lean_Expr_forallE___override(v_binderName_4284_, v_binderType_4285_, v_b_4290_, v___x_4293_);
return v___x_4294_;
}
}
else
{
return v_e_4282_;
}
}
else
{
return v_e_4282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4295_, lean_object* v_binderInfos_x3f_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_Lean_Expr_updateForallBinderInfos(v_e_4295_, v_binderInfos_x3f_4296_);
lean_dec(v_binderInfos_x3f_4296_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4298_, lean_object* v_binderNames_x3f_4299_){
_start:
{
switch(lean_obj_tag(v_e_4298_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4299_) == 1)
{
lean_object* v_binderName_4300_; lean_object* v_binderType_4301_; lean_object* v_body_4302_; uint8_t v_binderInfo_4303_; lean_object* v_head_4304_; lean_object* v_tail_4305_; lean_object* v_b_4306_; 
v_binderName_4300_ = lean_ctor_get(v_e_4298_, 0);
lean_inc(v_binderName_4300_);
v_binderType_4301_ = lean_ctor_get(v_e_4298_, 1);
lean_inc_ref(v_binderType_4301_);
v_body_4302_ = lean_ctor_get(v_e_4298_, 2);
lean_inc_ref(v_body_4302_);
v_binderInfo_4303_ = lean_ctor_get_uint8(v_e_4298_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4298_, 3);
v_head_4304_ = lean_ctor_get(v_binderNames_x3f_4299_, 0);
lean_inc(v_head_4304_);
v_tail_4305_ = lean_ctor_get(v_binderNames_x3f_4299_, 1);
lean_inc(v_tail_4305_);
lean_dec_ref_known(v_binderNames_x3f_4299_, 2);
v_b_4306_ = l_Lean_Expr_updateBinderNames(v_body_4302_, v_tail_4305_);
if (lean_obj_tag(v_head_4304_) == 0)
{
lean_object* v___x_4307_; 
v___x_4307_ = l_Lean_Expr_forallE___override(v_binderName_4300_, v_binderType_4301_, v_b_4306_, v_binderInfo_4303_);
return v___x_4307_;
}
else
{
lean_object* v_val_4308_; lean_object* v___x_4309_; 
lean_dec(v_binderName_4300_);
v_val_4308_ = lean_ctor_get(v_head_4304_, 0);
lean_inc(v_val_4308_);
lean_dec_ref_known(v_head_4304_, 1);
v___x_4309_ = l_Lean_Expr_forallE___override(v_val_4308_, v_binderType_4301_, v_b_4306_, v_binderInfo_4303_);
return v___x_4309_;
}
}
else
{
lean_dec(v_binderNames_x3f_4299_);
return v_e_4298_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4299_) == 1)
{
lean_object* v_binderName_4310_; lean_object* v_binderType_4311_; lean_object* v_body_4312_; uint8_t v_binderInfo_4313_; lean_object* v_head_4314_; lean_object* v_tail_4315_; lean_object* v_b_4316_; 
v_binderName_4310_ = lean_ctor_get(v_e_4298_, 0);
lean_inc(v_binderName_4310_);
v_binderType_4311_ = lean_ctor_get(v_e_4298_, 1);
lean_inc_ref(v_binderType_4311_);
v_body_4312_ = lean_ctor_get(v_e_4298_, 2);
lean_inc_ref(v_body_4312_);
v_binderInfo_4313_ = lean_ctor_get_uint8(v_e_4298_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4298_, 3);
v_head_4314_ = lean_ctor_get(v_binderNames_x3f_4299_, 0);
lean_inc(v_head_4314_);
v_tail_4315_ = lean_ctor_get(v_binderNames_x3f_4299_, 1);
lean_inc(v_tail_4315_);
lean_dec_ref_known(v_binderNames_x3f_4299_, 2);
v_b_4316_ = l_Lean_Expr_updateBinderNames(v_body_4312_, v_tail_4315_);
if (lean_obj_tag(v_head_4314_) == 0)
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Lean_Expr_lam___override(v_binderName_4310_, v_binderType_4311_, v_b_4316_, v_binderInfo_4313_);
return v___x_4317_;
}
else
{
lean_object* v_val_4318_; lean_object* v___x_4319_; 
lean_dec(v_binderName_4310_);
v_val_4318_ = lean_ctor_get(v_head_4314_, 0);
lean_inc(v_val_4318_);
lean_dec_ref_known(v_head_4314_, 1);
v___x_4319_ = l_Lean_Expr_lam___override(v_val_4318_, v_binderType_4311_, v_b_4316_, v_binderInfo_4313_);
return v___x_4319_;
}
}
else
{
lean_dec(v_binderNames_x3f_4299_);
return v_e_4298_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4299_);
return v_e_4298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4322_, lean_object* v_subst_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = lean_expr_instantiate(v_e_4322_, v_subst_4323_);
lean_dec_ref(v_subst_4323_);
lean_dec_ref(v_e_4322_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4327_, lean_object* v_subst_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = lean_expr_instantiate1(v_e_4327_, v_subst_4328_);
lean_dec_ref(v_subst_4328_);
lean_dec_ref(v_e_4327_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4332_, lean_object* v_subst_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = lean_expr_instantiate_rev(v_e_4332_, v_subst_4333_);
lean_dec_ref(v_subst_4333_);
lean_dec_ref(v_e_4332_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4339_, lean_object* v_beginIdx_4340_, lean_object* v_endIdx_4341_, lean_object* v_subst_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = lean_expr_instantiate_range(v_e_4339_, v_beginIdx_4340_, v_endIdx_4341_, v_subst_4342_);
lean_dec_ref(v_subst_4342_);
lean_dec(v_endIdx_4341_);
lean_dec(v_beginIdx_4340_);
lean_dec_ref(v_e_4339_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4348_, lean_object* v_beginIdx_4349_, lean_object* v_endIdx_4350_, lean_object* v_subst_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = lean_expr_instantiate_rev_range(v_e_4348_, v_beginIdx_4349_, v_endIdx_4350_, v_subst_4351_);
lean_dec_ref(v_subst_4351_);
lean_dec(v_endIdx_4350_);
lean_dec(v_beginIdx_4349_);
lean_dec_ref(v_e_4348_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4355_, lean_object* v_xs_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = lean_expr_abstract(v_e_4355_, v_xs_4356_);
lean_dec_ref(v_xs_4356_);
lean_dec_ref(v_e_4355_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4361_, lean_object* v_n_4362_, lean_object* v_xs_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = lean_expr_abstract_range(v_e_4361_, v_n_4362_, v_xs_4363_);
lean_dec_ref(v_xs_4363_);
lean_dec(v_n_4362_);
lean_dec_ref(v_e_4361_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4365_, lean_object* v_fvar_4366_, lean_object* v_v_4367_){
_start:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4368_ = lean_unsigned_to_nat(1u);
v___x_4369_ = lean_mk_empty_array_with_capacity(v___x_4368_);
v___x_4370_ = lean_array_push(v___x_4369_, v_fvar_4366_);
v___x_4371_ = lean_expr_abstract(v_e_4365_, v___x_4370_);
lean_dec_ref(v___x_4370_);
v___x_4372_ = lean_expr_instantiate1(v___x_4371_, v_v_4367_);
lean_dec_ref(v___x_4371_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4373_, lean_object* v_fvar_4374_, lean_object* v_v_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l_Lean_Expr_replaceFVar(v_e_4373_, v_fvar_4374_, v_v_4375_);
lean_dec_ref(v_v_4375_);
lean_dec_ref(v_e_4373_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4377_, lean_object* v_fvarId_4378_, lean_object* v_v_4379_){
_start:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4380_ = l_Lean_Expr_fvar___override(v_fvarId_4378_);
v___x_4381_ = l_Lean_Expr_replaceFVar(v_e_4377_, v___x_4380_, v_v_4379_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4382_, lean_object* v_fvarId_4383_, lean_object* v_v_4384_){
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l_Lean_Expr_replaceFVarId(v_e_4382_, v_fvarId_4383_, v_v_4384_);
lean_dec_ref(v_v_4384_);
lean_dec_ref(v_e_4382_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4386_, lean_object* v_fvars_4387_, lean_object* v_vs_4388_){
_start:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4389_ = lean_expr_abstract(v_e_4386_, v_fvars_4387_);
v___x_4390_ = lean_expr_instantiate_rev(v___x_4389_, v_vs_4388_);
lean_dec_ref(v___x_4389_);
return v___x_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4391_, lean_object* v_fvars_4392_, lean_object* v_vs_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_Lean_Expr_replaceFVars(v_e_4391_, v_fvars_4392_, v_vs_4393_);
lean_dec_ref(v_vs_4393_);
lean_dec_ref(v_fvars_4392_);
lean_dec_ref(v_e_4391_);
return v_res_4394_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4397_){
_start:
{
switch(lean_obj_tag(v_x_4397_))
{
case 4:
{
uint8_t v___x_4398_; 
v___x_4398_ = 1;
return v___x_4398_;
}
case 3:
{
uint8_t v___x_4399_; 
v___x_4399_ = 1;
return v___x_4399_;
}
case 0:
{
uint8_t v___x_4400_; 
v___x_4400_ = 1;
return v___x_4400_;
}
case 9:
{
uint8_t v___x_4401_; 
v___x_4401_ = 1;
return v___x_4401_;
}
case 2:
{
uint8_t v___x_4402_; 
v___x_4402_ = 1;
return v___x_4402_;
}
case 1:
{
uint8_t v___x_4403_; 
v___x_4403_ = 1;
return v___x_4403_;
}
default: 
{
uint8_t v___x_4404_; 
v___x_4404_ = 0;
return v___x_4404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4405_){
_start:
{
uint8_t v_res_4406_; lean_object* v_r_4407_; 
v_res_4406_ = l_Lean_Expr_isAtomic(v_x_4405_);
lean_dec_ref(v_x_4405_);
v_r_4407_ = lean_box(v_res_4406_);
return v_r_4407_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4413_ = lean_box(0);
v___x_4414_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4415_ = l_Lean_Expr_const___override(v___x_4414_, v___x_4413_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4416_, lean_object* v_proof_4417_){
_start:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4418_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4419_ = l_Lean_mkAppB(v___x_4418_, v_pred_4416_, v_proof_4417_);
return v___x_4419_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4424_ = lean_box(0);
v___x_4425_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4426_ = l_Lean_Expr_const___override(v___x_4425_, v___x_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4427_, lean_object* v_proof_4428_){
_start:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4429_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4430_ = l_Lean_mkAppB(v___x_4429_, v_pred_4427_, v_proof_4428_);
return v___x_4430_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4431_; 
v___x_4431_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4431_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4432_; 
v___x_4432_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4433_){
_start:
{
lean_inc_ref(v_val_4433_);
return v_val_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4434_);
lean_dec_ref(v_val_4434_);
return v_res_4435_;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4438_, lean_object* v_x_4439_){
_start:
{
uint8_t v___x_4440_; 
v___x_4440_ = lean_expr_equal(v_x_4438_, v_x_4439_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4441_, lean_object* v_x_4442_){
_start:
{
uint8_t v_res_4443_; lean_object* v_r_4444_; 
v_res_4443_ = l_Lean_ExprStructEq_beq(v_x_4441_, v_x_4442_);
lean_dec_ref(v_x_4442_);
lean_dec_ref(v_x_4441_);
v_r_4444_ = lean_box(v_res_4443_);
return v_r_4444_;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4445_){
_start:
{
uint64_t v___x_4446_; 
v___x_4446_ = l_Lean_Expr_hash(v_x_4445_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4447_){
_start:
{
uint64_t v_res_4448_; lean_object* v_r_4449_; 
v_res_4448_ = l_Lean_ExprStructEq_hash(v_x_4447_);
lean_dec_ref(v_x_4447_);
v_r_4449_ = lean_box_uint64(v_res_4448_);
return v_r_4449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4456_, lean_object* v_start_4457_, lean_object* v_b_4458_, lean_object* v_i_4459_){
_start:
{
uint8_t v___x_4460_; 
v___x_4460_ = lean_nat_dec_le(v_i_4459_, v_start_4457_);
if (v___x_4460_ == 0)
{
lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v_i_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4461_ = l_Lean_instInhabitedExpr;
v___x_4462_ = lean_unsigned_to_nat(1u);
v_i_4463_ = lean_nat_sub(v_i_4459_, v___x_4462_);
lean_dec(v_i_4459_);
v___x_4464_ = lean_array_get_borrowed(v___x_4461_, v_revArgs_4456_, v_i_4463_);
lean_inc(v___x_4464_);
v___x_4465_ = l_Lean_Expr_app___override(v_b_4458_, v___x_4464_);
v_b_4458_ = v___x_4465_;
v_i_4459_ = v_i_4463_;
goto _start;
}
else
{
lean_dec(v_i_4459_);
return v_b_4458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4467_, lean_object* v_start_4468_, lean_object* v_b_4469_, lean_object* v_i_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4467_, v_start_4468_, v_b_4469_, v_i_4470_);
lean_dec(v_start_4468_);
lean_dec_ref(v_revArgs_4467_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4472_, lean_object* v_beginIdx_4473_, lean_object* v_endIdx_4474_, lean_object* v_revArgs_4475_){
_start:
{
lean_object* v___x_4476_; 
v___x_4476_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4475_, v_beginIdx_4473_, v_f_4472_, v_endIdx_4474_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4477_, lean_object* v_beginIdx_4478_, lean_object* v_endIdx_4479_, lean_object* v_revArgs_4480_){
_start:
{
lean_object* v_res_4481_; 
v_res_4481_ = l_Lean_Expr_mkAppRevRange(v_f_4477_, v_beginIdx_4478_, v_endIdx_4479_, v_revArgs_4480_);
lean_dec_ref(v_revArgs_4480_);
lean_dec(v_beginIdx_4478_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4482_, uint8_t v_useZeta_4483_, uint8_t v_preserveMData_4484_, lean_object* v_sz_4485_, lean_object* v_e_4486_, lean_object* v_i_4487_){
_start:
{
switch(lean_obj_tag(v_e_4486_))
{
case 6:
{
lean_object* v_body_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; uint8_t v___x_4496_; 
v_body_4493_ = lean_ctor_get(v_e_4486_, 2);
lean_inc_ref(v_body_4493_);
lean_dec_ref_known(v_e_4486_, 3);
v___x_4494_ = lean_unsigned_to_nat(1u);
v___x_4495_ = lean_nat_add(v_i_4487_, v___x_4494_);
lean_dec(v_i_4487_);
v___x_4496_ = lean_nat_dec_lt(v___x_4495_, v_sz_4485_);
if (v___x_4496_ == 0)
{
lean_object* v___x_4497_; 
lean_dec(v___x_4495_);
v___x_4497_ = lean_expr_instantiate(v_body_4493_, v_revArgs_4482_);
lean_dec_ref(v_body_4493_);
return v___x_4497_;
}
else
{
v_e_4486_ = v_body_4493_;
v_i_4487_ = v___x_4495_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4483_ == 0)
{
goto v___jp_4488_;
}
else
{
lean_object* v_value_4499_; lean_object* v_body_4500_; uint8_t v___x_4501_; 
v_value_4499_ = lean_ctor_get(v_e_4486_, 2);
v_body_4500_ = lean_ctor_get(v_e_4486_, 3);
v___x_4501_ = lean_nat_dec_lt(v_i_4487_, v_sz_4485_);
if (v___x_4501_ == 0)
{
goto v___jp_4488_;
}
else
{
lean_object* v___x_4502_; 
lean_inc_ref(v_body_4500_);
lean_inc_ref(v_value_4499_);
lean_dec_ref_known(v_e_4486_, 4);
v___x_4502_ = lean_expr_instantiate1(v_body_4500_, v_value_4499_);
lean_dec_ref(v_value_4499_);
lean_dec_ref(v_body_4500_);
v_e_4486_ = v___x_4502_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4484_ == 0)
{
lean_object* v_expr_4504_; 
v_expr_4504_ = lean_ctor_get(v_e_4486_, 1);
lean_inc_ref(v_expr_4504_);
lean_dec_ref_known(v_e_4486_, 2);
v_e_4486_ = v_expr_4504_;
goto _start;
}
else
{
goto v___jp_4488_;
}
}
default: 
{
goto v___jp_4488_;
}
}
v___jp_4488_:
{
lean_object* v_n_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v_n_4489_ = lean_nat_sub(v_sz_4485_, v_i_4487_);
lean_dec(v_i_4487_);
v___x_4490_ = lean_expr_instantiate_range(v_e_4486_, v_n_4489_, v_sz_4485_, v_revArgs_4482_);
lean_dec_ref(v_e_4486_);
v___x_4491_ = lean_unsigned_to_nat(0u);
v___x_4492_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4482_, v___x_4491_, v___x_4490_, v_n_4489_);
return v___x_4492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4506_, lean_object* v_useZeta_4507_, lean_object* v_preserveMData_4508_, lean_object* v_sz_4509_, lean_object* v_e_4510_, lean_object* v_i_4511_){
_start:
{
uint8_t v_useZeta_boxed_4512_; uint8_t v_preserveMData_boxed_4513_; lean_object* v_res_4514_; 
v_useZeta_boxed_4512_ = lean_unbox(v_useZeta_4507_);
v_preserveMData_boxed_4513_ = lean_unbox(v_preserveMData_4508_);
v_res_4514_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4506_, v_useZeta_boxed_4512_, v_preserveMData_boxed_4513_, v_sz_4509_, v_e_4510_, v_i_4511_);
lean_dec(v_sz_4509_);
lean_dec_ref(v_revArgs_4506_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4515_, lean_object* v_revArgs_4516_, uint8_t v_useZeta_4517_, uint8_t v_preserveMData_4518_){
_start:
{
lean_object* v_sz_4519_; lean_object* v___x_4520_; uint8_t v___x_4521_; 
v_sz_4519_ = lean_array_get_size(v_revArgs_4516_);
v___x_4520_ = lean_unsigned_to_nat(0u);
v___x_4521_ = lean_nat_dec_eq(v_sz_4519_, v___x_4520_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; 
v___x_4522_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4516_, v_useZeta_4517_, v_preserveMData_4518_, v_sz_4519_, v_f_4515_, v___x_4520_);
return v___x_4522_;
}
else
{
return v_f_4515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4523_, lean_object* v_revArgs_4524_, lean_object* v_useZeta_4525_, lean_object* v_preserveMData_4526_){
_start:
{
uint8_t v_useZeta_boxed_4527_; uint8_t v_preserveMData_boxed_4528_; lean_object* v_res_4529_; 
v_useZeta_boxed_4527_ = lean_unbox(v_useZeta_4525_);
v_preserveMData_boxed_4528_ = lean_unbox(v_preserveMData_4526_);
v_res_4529_ = l_Lean_Expr_betaRev(v_f_4523_, v_revArgs_4524_, v_useZeta_boxed_4527_, v_preserveMData_boxed_4528_);
lean_dec_ref(v_revArgs_4524_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4530_, lean_object* v_args_4531_){
_start:
{
lean_object* v___x_4532_; uint8_t v___x_4533_; lean_object* v___x_4534_; 
v___x_4532_ = l_Array_reverse___redArg(v_args_4531_);
v___x_4533_ = 0;
v___x_4534_ = l_Lean_Expr_betaRev(v_f_4530_, v___x_4532_, v___x_4533_, v___x_4533_);
lean_dec_ref(v___x_4532_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4535_){
_start:
{
switch(lean_obj_tag(v_x_4535_))
{
case 6:
{
lean_object* v_body_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; 
v_body_4536_ = lean_ctor_get(v_x_4535_, 2);
v___x_4537_ = l_Lean_Expr_getNumHeadLambdas(v_body_4536_);
v___x_4538_ = lean_unsigned_to_nat(1u);
v___x_4539_ = lean_nat_add(v___x_4537_, v___x_4538_);
lean_dec(v___x_4537_);
return v___x_4539_;
}
case 10:
{
lean_object* v_expr_4540_; 
v_expr_4540_ = lean_ctor_get(v_x_4535_, 1);
v_x_4535_ = v_expr_4540_;
goto _start;
}
default: 
{
lean_object* v___x_4542_; 
v___x_4542_ = lean_unsigned_to_nat(0u);
return v___x_4542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_Expr_getNumHeadLambdas(v_x_4543_);
lean_dec_ref(v_x_4543_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object* v_x_4545_){
_start:
{
switch(lean_obj_tag(v_x_4545_))
{
case 6:
{
lean_object* v_body_4546_; 
v_body_4546_ = lean_ctor_get(v_x_4545_, 2);
v_x_4545_ = v_body_4546_;
goto _start;
}
case 10:
{
lean_object* v_expr_4548_; 
v_expr_4548_ = lean_ctor_get(v_x_4545_, 1);
v_x_4545_ = v_expr_4548_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_4545_);
return v_x_4545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object* v_x_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l_Lean_Expr_getLambdaBody(v_x_4550_);
lean_dec_ref(v_x_4550_);
return v_res_4551_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4552_, lean_object* v_x_4553_){
_start:
{
switch(lean_obj_tag(v_x_4553_))
{
case 6:
{
uint8_t v___x_4554_; 
v___x_4554_ = 1;
return v___x_4554_;
}
case 8:
{
if (v_useZeta_4552_ == 0)
{
return v_useZeta_4552_;
}
else
{
lean_object* v_body_4555_; 
v_body_4555_ = lean_ctor_get(v_x_4553_, 3);
v_x_4553_ = v_body_4555_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4557_; 
v_expr_4557_ = lean_ctor_get(v_x_4553_, 1);
v_x_4553_ = v_expr_4557_;
goto _start;
}
default: 
{
uint8_t v___x_4559_; 
v___x_4559_ = 0;
return v___x_4559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4560_, lean_object* v_x_4561_){
_start:
{
uint8_t v_useZeta_boxed_4562_; uint8_t v_res_4563_; lean_object* v_r_4564_; 
v_useZeta_boxed_4562_ = lean_unbox(v_useZeta_4560_);
v_res_4563_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4562_, v_x_4561_);
lean_dec_ref(v_x_4561_);
v_r_4564_ = lean_box(v_res_4563_);
return v_r_4564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4565_){
_start:
{
lean_object* v_f_4566_; uint8_t v___x_4567_; uint8_t v___x_4568_; 
v_f_4566_ = l_Lean_Expr_getAppFn(v_e_4565_);
v___x_4567_ = 0;
v___x_4568_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4567_, v_f_4566_);
if (v___x_4568_ == 0)
{
lean_dec_ref(v_f_4566_);
return v_e_4565_;
}
else
{
lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4569_ = l_Lean_Expr_getAppNumArgs(v_e_4565_);
v___x_4570_ = lean_mk_empty_array_with_capacity(v___x_4569_);
lean_dec(v___x_4569_);
v___x_4571_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4565_, v___x_4570_);
v___x_4572_ = l_Lean_Expr_betaRev(v_f_4566_, v___x_4571_, v___x_4567_, v___x_4567_);
lean_dec_ref(v___x_4571_);
return v___x_4572_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4573_, uint8_t v_useZeta_4574_){
_start:
{
uint8_t v___x_4575_; 
v___x_4575_ = l_Lean_Expr_isApp(v_e_4573_);
if (v___x_4575_ == 0)
{
return v___x_4575_;
}
else
{
lean_object* v___x_4576_; uint8_t v___x_4577_; 
v___x_4576_ = l_Lean_Expr_getAppFn(v_e_4573_);
v___x_4577_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4574_, v___x_4576_);
lean_dec_ref(v___x_4576_);
return v___x_4577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4578_, lean_object* v_useZeta_4579_){
_start:
{
uint8_t v_useZeta_boxed_4580_; uint8_t v_res_4581_; lean_object* v_r_4582_; 
v_useZeta_boxed_4580_ = lean_unbox(v_useZeta_4579_);
v_res_4581_ = l_Lean_Expr_isHeadBetaTarget(v_e_4578_, v_useZeta_boxed_4580_);
lean_dec_ref(v_e_4578_);
v_r_4582_ = lean_box(v_res_4581_);
return v_r_4582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4583_, lean_object* v_x_4584_, lean_object* v_x_4585_){
_start:
{
lean_object* v_f_4587_; 
if (lean_obj_tag(v_x_4583_) == 5)
{
lean_object* v_arg_4591_; 
v_arg_4591_ = lean_ctor_get(v_x_4583_, 1);
if (lean_obj_tag(v_arg_4591_) == 0)
{
lean_object* v_fn_4592_; lean_object* v_deBruijnIndex_4593_; lean_object* v_zero_4594_; uint8_t v_isZero_4595_; 
v_fn_4592_ = lean_ctor_get(v_x_4583_, 0);
v_deBruijnIndex_4593_ = lean_ctor_get(v_arg_4591_, 0);
v_zero_4594_ = lean_unsigned_to_nat(0u);
v_isZero_4595_ = lean_nat_dec_eq(v_x_4584_, v_zero_4594_);
if (v_isZero_4595_ == 1)
{
lean_dec(v_x_4585_);
lean_dec(v_x_4584_);
v_f_4587_ = v_x_4583_;
goto v___jp_4586_;
}
else
{
uint8_t v___x_4596_; 
lean_inc(v_deBruijnIndex_4593_);
lean_inc_ref(v_fn_4592_);
lean_dec_ref_known(v_x_4583_, 2);
v___x_4596_ = lean_nat_dec_eq(v_deBruijnIndex_4593_, v_x_4585_);
lean_dec(v_deBruijnIndex_4593_);
if (v___x_4596_ == 0)
{
lean_object* v___x_4597_; 
lean_dec_ref(v_fn_4592_);
lean_dec(v_x_4585_);
lean_dec(v_x_4584_);
v___x_4597_ = lean_box(0);
return v___x_4597_;
}
else
{
lean_object* v_one_4598_; lean_object* v_n_4599_; lean_object* v___x_4600_; 
v_one_4598_ = lean_unsigned_to_nat(1u);
v_n_4599_ = lean_nat_sub(v_x_4584_, v_one_4598_);
lean_dec(v_x_4584_);
v___x_4600_ = lean_nat_add(v_x_4585_, v_one_4598_);
lean_dec(v_x_4585_);
v_x_4583_ = v_fn_4592_;
v_x_4584_ = v_n_4599_;
v_x_4585_ = v___x_4600_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4602_; uint8_t v_isZero_4603_; 
lean_dec(v_x_4585_);
v_zero_4602_ = lean_unsigned_to_nat(0u);
v_isZero_4603_ = lean_nat_dec_eq(v_x_4584_, v_zero_4602_);
lean_dec(v_x_4584_);
if (v_isZero_4603_ == 1)
{
v_f_4587_ = v_x_4583_;
goto v___jp_4586_;
}
else
{
lean_object* v___x_4604_; 
lean_dec_ref_known(v_x_4583_, 2);
v___x_4604_ = lean_box(0);
return v___x_4604_;
}
}
}
else
{
lean_object* v_zero_4605_; uint8_t v_isZero_4606_; 
lean_dec(v_x_4585_);
v_zero_4605_ = lean_unsigned_to_nat(0u);
v_isZero_4606_ = lean_nat_dec_eq(v_x_4584_, v_zero_4605_);
lean_dec(v_x_4584_);
if (v_isZero_4606_ == 1)
{
v_f_4587_ = v_x_4583_;
goto v___jp_4586_;
}
else
{
lean_object* v___x_4607_; 
lean_dec_ref(v_x_4583_);
v___x_4607_ = lean_box(0);
return v___x_4607_;
}
}
v___jp_4586_:
{
uint8_t v___x_4588_; 
v___x_4588_ = l_Lean_Expr_hasLooseBVars(v_f_4587_);
if (v___x_4588_ == 0)
{
lean_object* v___x_4589_; 
v___x_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4589_, 0, v_f_4587_);
return v___x_4589_;
}
else
{
lean_object* v___x_4590_; 
lean_dec_ref(v_f_4587_);
v___x_4590_ = lean_box(0);
return v___x_4590_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4608_, lean_object* v_x_4609_){
_start:
{
if (lean_obj_tag(v_x_4608_) == 6)
{
lean_object* v_body_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v_body_4610_ = lean_ctor_get(v_x_4608_, 2);
lean_inc_ref(v_body_4610_);
lean_dec_ref_known(v_x_4608_, 3);
v___x_4611_ = lean_unsigned_to_nat(1u);
v___x_4612_ = lean_nat_add(v_x_4609_, v___x_4611_);
lean_dec(v_x_4609_);
v_x_4608_ = v_body_4610_;
v_x_4609_ = v___x_4612_;
goto _start;
}
else
{
lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4614_ = lean_unsigned_to_nat(0u);
v___x_4615_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4608_, v_x_4609_, v___x_4614_);
return v___x_4615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4616_){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4617_ = lean_unsigned_to_nat(0u);
v___x_4618_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4616_, v___x_4617_);
return v___x_4618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4619_){
_start:
{
if (lean_obj_tag(v_x_4619_) == 6)
{
lean_object* v_body_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v_body_4620_ = lean_ctor_get(v_x_4619_, 2);
lean_inc_ref(v_body_4620_);
lean_dec_ref_known(v_x_4619_, 3);
v___x_4621_ = lean_unsigned_to_nat(1u);
v___x_4622_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4620_, v___x_4621_);
return v___x_4622_;
}
else
{
lean_object* v___x_4623_; 
lean_dec_ref(v_x_4619_);
v___x_4623_ = lean_box(0);
return v___x_4623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4627_){
_start:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; uint8_t v___x_4630_; 
v___x_4628_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4629_ = lean_unsigned_to_nat(2u);
v___x_4630_ = l_Lean_Expr_isAppOfArity(v_e_4627_, v___x_4628_, v___x_4629_);
if (v___x_4630_ == 0)
{
lean_object* v___x_4631_; 
v___x_4631_ = lean_box(0);
return v___x_4631_;
}
else
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = l_Lean_Expr_appArg_x21(v_e_4627_);
v___x_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4632_);
return v___x_4633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4634_);
lean_dec_ref(v_e_4634_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4639_){
_start:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; uint8_t v___x_4642_; 
v___x_4640_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4646_);
lean_dec_ref(v_e_4646_);
return v_res_4647_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOutParam(lean_object* v_e_4651_){
_start:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; uint8_t v___x_4654_; 
v___x_4652_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4653_ = lean_unsigned_to_nat(1u);
v___x_4654_ = l_Lean_Expr_isAppOfArity(v_e_4651_, v___x_4652_, v___x_4653_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4655_){
_start:
{
uint8_t v_res_4656_; lean_object* v_r_4657_; 
v_res_4656_ = l_Lean_Expr_isOutParam(v_e_4655_);
lean_dec_ref(v_e_4655_);
v_r_4657_ = lean_box(v_res_4656_);
return v_r_4657_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4661_){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; uint8_t v___x_4664_; 
v___x_4662_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4663_ = lean_unsigned_to_nat(1u);
v___x_4664_ = l_Lean_Expr_isAppOfArity(v_e_4661_, v___x_4662_, v___x_4663_);
return v___x_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4665_){
_start:
{
uint8_t v_res_4666_; lean_object* v_r_4667_; 
v_res_4666_ = l_Lean_Expr_isSemiOutParam(v_e_4665_);
lean_dec_ref(v_e_4665_);
v_r_4667_ = lean_box(v_res_4666_);
return v_r_4667_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4668_){
_start:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; uint8_t v___x_4671_; 
v___x_4669_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4670_ = lean_unsigned_to_nat(2u);
v___x_4671_ = l_Lean_Expr_isAppOfArity(v_e_4668_, v___x_4669_, v___x_4670_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4672_){
_start:
{
uint8_t v_res_4673_; lean_object* v_r_4674_; 
v_res_4673_ = l_Lean_Expr_isOptParam(v_e_4672_);
lean_dec_ref(v_e_4672_);
v_r_4674_ = lean_box(v_res_4673_);
return v_r_4674_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4675_){
_start:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; uint8_t v___x_4678_; 
v___x_4676_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4677_ = lean_unsigned_to_nat(2u);
v___x_4678_ = l_Lean_Expr_isAppOfArity(v_e_4675_, v___x_4676_, v___x_4677_);
return v___x_4678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4679_){
_start:
{
uint8_t v_res_4680_; lean_object* v_r_4681_; 
v_res_4680_ = l_Lean_Expr_isAutoParam(v_e_4679_);
lean_dec_ref(v_e_4679_);
v_r_4681_ = lean_box(v_res_4680_);
return v_r_4681_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4682_){
_start:
{
lean_object* v___x_4683_; 
v___x_4683_ = l_Lean_Expr_getAppFn(v_e_4682_);
if (lean_obj_tag(v___x_4683_) == 4)
{
lean_object* v_declName_4684_; uint8_t v___y_4686_; lean_object* v___x_4691_; uint8_t v___x_4692_; 
v_declName_4684_ = lean_ctor_get(v___x_4683_, 0);
lean_inc(v_declName_4684_);
lean_dec_ref_known(v___x_4683_, 2);
v___x_4691_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4692_ = lean_name_eq(v_declName_4684_, v___x_4691_);
if (v___x_4692_ == 0)
{
lean_object* v___x_4693_; uint8_t v___x_4694_; 
v___x_4693_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4694_ = lean_name_eq(v_declName_4684_, v___x_4693_);
v___y_4686_ = v___x_4694_;
goto v___jp_4685_;
}
else
{
v___y_4686_ = v___x_4692_;
goto v___jp_4685_;
}
v___jp_4685_:
{
if (v___y_4686_ == 0)
{
lean_object* v___x_4687_; uint8_t v___x_4688_; 
v___x_4687_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4688_ = lean_name_eq(v_declName_4684_, v___x_4687_);
if (v___x_4688_ == 0)
{
lean_object* v___x_4689_; uint8_t v___x_4690_; 
v___x_4689_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4690_ = lean_name_eq(v_declName_4684_, v___x_4689_);
lean_dec(v_declName_4684_);
return v___x_4690_;
}
else
{
lean_dec(v_declName_4684_);
return v___x_4688_;
}
}
else
{
lean_dec(v_declName_4684_);
return v___y_4686_;
}
}
}
else
{
uint8_t v___x_4695_; 
lean_dec_ref(v___x_4683_);
v___x_4695_ = 0;
return v___x_4695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4696_){
_start:
{
uint8_t v_res_4697_; lean_object* v_r_4698_; 
v_res_4697_ = l_Lean_Expr_isTypeAnnotation(v_e_4696_);
lean_dec_ref(v_e_4696_);
v_r_4698_ = lean_box(v_res_4697_);
return v_r_4698_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4699_){
_start:
{
uint8_t v___y_4701_; uint8_t v___y_4705_; uint8_t v___x_4711_; 
v___x_4711_ = l_Lean_Expr_isOptParam(v_e_4699_);
if (v___x_4711_ == 0)
{
uint8_t v___x_4712_; 
v___x_4712_ = l_Lean_Expr_isAutoParam(v_e_4699_);
v___y_4705_ = v___x_4712_;
goto v___jp_4704_;
}
else
{
v___y_4705_ = v___x_4711_;
goto v___jp_4704_;
}
v___jp_4700_:
{
if (v___y_4701_ == 0)
{
return v_e_4699_;
}
else
{
lean_object* v___x_4702_; 
v___x_4702_ = l_Lean_Expr_appArg_x21(v_e_4699_);
lean_dec_ref(v_e_4699_);
v_e_4699_ = v___x_4702_;
goto _start;
}
}
v___jp_4704_:
{
if (v___y_4705_ == 0)
{
uint8_t v___x_4706_; 
v___x_4706_ = l_Lean_Expr_isOutParam(v_e_4699_);
if (v___x_4706_ == 0)
{
uint8_t v___x_4707_; 
v___x_4707_ = l_Lean_Expr_isSemiOutParam(v_e_4699_);
v___y_4701_ = v___x_4707_;
goto v___jp_4700_;
}
else
{
v___y_4701_ = v___x_4706_;
goto v___jp_4700_;
}
}
else
{
lean_object* v___x_4708_; lean_object* v___x_4709_; 
v___x_4708_ = l_Lean_Expr_appFn_x21(v_e_4699_);
lean_dec_ref(v_e_4699_);
v___x_4709_ = l_Lean_Expr_appArg_x21(v___x_4708_);
lean_dec_ref(v___x_4708_);
v_e_4699_ = v___x_4709_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4713_){
_start:
{
lean_object* v___x_4714_; lean_object* v_e_x27_4715_; uint8_t v___x_4716_; 
v___x_4714_ = l_Lean_Expr_consumeMData(v_e_4713_);
v_e_x27_4715_ = lean_expr_consume_type_annotations(v___x_4714_);
v___x_4716_ = lean_expr_eqv(v_e_x27_4715_, v_e_4713_);
if (v___x_4716_ == 0)
{
lean_dec_ref(v_e_4713_);
v_e_4713_ = v_e_x27_4715_;
goto _start;
}
else
{
lean_dec_ref(v_e_x27_4715_);
return v_e_4713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4718_){
_start:
{
lean_object* v_fn_4719_; lean_object* v___x_4720_; 
v_fn_4719_ = lean_ctor_get(v_e_4718_, 0);
lean_inc_ref(v_fn_4719_);
lean_dec_ref(v_e_4718_);
v___x_4720_ = l_Lean_Expr_cleanupAnnotations(v_fn_4719_);
return v___x_4720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* v_e_4721_, lean_object* v_h_4722_){
_start:
{
lean_object* v___x_4723_; 
v___x_4723_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4721_);
return v___x_4723_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4727_){
_start:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; uint8_t v___x_4730_; 
v___x_4728_ = l_Lean_Expr_cleanupAnnotations(v_e_4727_);
v___x_4729_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4730_ = l_Lean_Expr_isConstOf(v___x_4728_, v___x_4729_);
lean_dec_ref(v___x_4728_);
return v___x_4730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4731_){
_start:
{
uint8_t v_res_4732_; lean_object* v_r_4733_; 
v_res_4732_ = l_Lean_Expr_isFalse(v_e_4731_);
v_r_4733_ = lean_box(v_res_4732_);
return v_r_4733_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4737_){
_start:
{
lean_object* v___x_4738_; lean_object* v___x_4739_; uint8_t v___x_4740_; 
v___x_4738_ = l_Lean_Expr_cleanupAnnotations(v_e_4737_);
v___x_4739_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4740_ = l_Lean_Expr_isConstOf(v___x_4738_, v___x_4739_);
lean_dec_ref(v___x_4738_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4741_){
_start:
{
uint8_t v_res_4742_; lean_object* v_r_4743_; 
v_res_4742_ = l_Lean_Expr_isTrue(v_e_4741_);
v_r_4743_ = lean_box(v_res_4742_);
return v_r_4743_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object* v_e_4748_){
_start:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; uint8_t v___x_4751_; 
v___x_4749_ = l_Lean_Expr_cleanupAnnotations(v_e_4748_);
v___x_4750_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_4751_ = l_Lean_Expr_isConstOf(v___x_4749_, v___x_4750_);
lean_dec_ref(v___x_4749_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object* v_e_4752_){
_start:
{
uint8_t v_res_4753_; lean_object* v_r_4754_; 
v_res_4753_ = l_Lean_Expr_isBoolFalse(v_e_4752_);
v_r_4754_ = lean_box(v_res_4753_);
return v_r_4754_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object* v_e_4758_){
_start:
{
lean_object* v___x_4759_; lean_object* v___x_4760_; uint8_t v___x_4761_; 
v___x_4759_ = l_Lean_Expr_cleanupAnnotations(v_e_4758_);
v___x_4760_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_4761_ = l_Lean_Expr_isConstOf(v___x_4759_, v___x_4760_);
lean_dec_ref(v___x_4759_);
return v___x_4761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object* v_e_4762_){
_start:
{
uint8_t v_res_4763_; lean_object* v_r_4764_; 
v_res_4763_ = l_Lean_Expr_isBoolTrue(v_e_4762_);
v_r_4764_ = lean_box(v_res_4763_);
return v_r_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* v_x_4765_){
_start:
{
switch(lean_obj_tag(v_x_4765_))
{
case 10:
{
lean_object* v_expr_4766_; 
v_expr_4766_ = lean_ctor_get(v_x_4765_, 1);
lean_inc_ref(v_expr_4766_);
lean_dec_ref_known(v_x_4765_, 2);
v_x_4765_ = v_expr_4766_;
goto _start;
}
case 7:
{
lean_object* v_body_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v_body_4768_ = lean_ctor_get(v_x_4765_, 2);
lean_inc_ref(v_body_4768_);
lean_dec_ref_known(v_x_4765_, 3);
v___x_4769_ = l_Lean_Expr_getForallArity(v_body_4768_);
v___x_4770_ = lean_unsigned_to_nat(1u);
v___x_4771_ = lean_nat_add(v___x_4769_, v___x_4770_);
lean_dec(v___x_4769_);
return v___x_4771_;
}
default: 
{
uint8_t v___x_4772_; uint8_t v___x_4773_; 
v___x_4772_ = 0;
v___x_4773_ = l_Lean_Expr_isHeadBetaTarget(v_x_4765_, v___x_4772_);
if (v___x_4773_ == 0)
{
lean_object* v_e_x27_4774_; uint8_t v___x_4775_; 
lean_inc_ref(v_x_4765_);
v_e_x27_4774_ = l_Lean_Expr_cleanupAnnotations(v_x_4765_);
v___x_4775_ = lean_expr_eqv(v_x_4765_, v_e_x27_4774_);
lean_dec_ref(v_x_4765_);
if (v___x_4775_ == 0)
{
v_x_4765_ = v_e_x27_4774_;
goto _start;
}
else
{
if (v___x_4773_ == 0)
{
lean_object* v___x_4777_; 
lean_dec_ref(v_e_x27_4774_);
v___x_4777_ = lean_unsigned_to_nat(0u);
return v___x_4777_;
}
else
{
v_x_4765_ = v_e_x27_4774_;
goto _start;
}
}
}
else
{
lean_object* v___x_4779_; 
v___x_4779_ = l_Lean_Expr_headBeta(v_x_4765_);
v_x_4765_ = v___x_4779_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4781_){
_start:
{
lean_object* v___x_4782_; uint8_t v___x_4783_; 
v___x_4782_ = l_Lean_Expr_cleanupAnnotations(v_e_4781_);
v___x_4783_ = l_Lean_Expr_isApp(v___x_4782_);
if (v___x_4783_ == 0)
{
lean_object* v___x_4784_; 
lean_dec_ref(v___x_4782_);
v___x_4784_ = lean_box(0);
return v___x_4784_;
}
else
{
lean_object* v___x_4785_; uint8_t v___x_4786_; 
v___x_4785_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4782_);
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
lean_object* v_arg_4788_; lean_object* v___x_4789_; uint8_t v___x_4790_; 
v_arg_4788_ = lean_ctor_get(v___x_4785_, 1);
lean_inc_ref(v_arg_4788_);
v___x_4789_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4785_);
v___x_4790_ = l_Lean_Expr_isApp(v___x_4789_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; 
lean_dec_ref(v___x_4789_);
lean_dec_ref(v_arg_4788_);
v___x_4791_ = lean_box(0);
return v___x_4791_;
}
else
{
lean_object* v___x_4792_; lean_object* v___x_4793_; uint8_t v___x_4794_; 
v___x_4792_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4789_);
v___x_4793_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4794_ = l_Lean_Expr_isConstOf(v___x_4792_, v___x_4793_);
lean_dec_ref(v___x_4792_);
if (v___x_4794_ == 0)
{
lean_object* v___x_4795_; 
lean_dec_ref(v_arg_4788_);
v___x_4795_ = lean_box(0);
return v___x_4795_;
}
else
{
if (lean_obj_tag(v_arg_4788_) == 9)
{
lean_object* v_a_4796_; 
v_a_4796_ = lean_ctor_get(v_arg_4788_, 0);
lean_inc_ref(v_a_4796_);
lean_dec_ref_known(v_arg_4788_, 1);
if (lean_obj_tag(v_a_4796_) == 0)
{
lean_object* v_val_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4804_; 
v_val_4797_ = lean_ctor_get(v_a_4796_, 0);
v_isSharedCheck_4804_ = !lean_is_exclusive(v_a_4796_);
if (v_isSharedCheck_4804_ == 0)
{
v___x_4799_ = v_a_4796_;
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_val_4797_);
lean_dec(v_a_4796_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4802_; 
if (v_isShared_4800_ == 0)
{
lean_ctor_set_tag(v___x_4799_, 1);
v___x_4802_ = v___x_4799_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v_val_4797_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
}
else
{
lean_object* v___x_4805_; 
lean_dec_ref(v_a_4796_);
v___x_4805_ = lean_box(0);
return v___x_4805_;
}
}
else
{
lean_object* v___x_4806_; 
lean_dec_ref(v_arg_4788_);
v___x_4806_ = lean_box(0);
return v___x_4806_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4812_){
_start:
{
lean_object* v___x_4825_; uint8_t v___x_4826_; 
lean_inc_ref(v_e_4812_);
v___x_4825_ = l_Lean_Expr_cleanupAnnotations(v_e_4812_);
v___x_4826_ = l_Lean_Expr_isApp(v___x_4825_);
if (v___x_4826_ == 0)
{
lean_dec_ref(v___x_4825_);
goto v___jp_4813_;
}
else
{
lean_object* v_arg_4827_; lean_object* v___x_4828_; uint8_t v___x_4829_; 
v_arg_4827_ = lean_ctor_get(v___x_4825_, 1);
lean_inc_ref(v_arg_4827_);
v___x_4828_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4825_);
v___x_4829_ = l_Lean_Expr_isApp(v___x_4828_);
if (v___x_4829_ == 0)
{
lean_dec_ref(v___x_4828_);
lean_dec_ref(v_arg_4827_);
goto v___jp_4813_;
}
else
{
lean_object* v___x_4830_; uint8_t v___x_4831_; 
v___x_4830_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4828_);
v___x_4831_ = l_Lean_Expr_isApp(v___x_4830_);
if (v___x_4831_ == 0)
{
lean_dec_ref(v___x_4830_);
lean_dec_ref(v_arg_4827_);
goto v___jp_4813_;
}
else
{
lean_object* v___x_4832_; lean_object* v___x_4833_; uint8_t v___x_4834_; 
v___x_4832_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4830_);
v___x_4833_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4834_ = l_Lean_Expr_isConstOf(v___x_4832_, v___x_4833_);
lean_dec_ref(v___x_4832_);
if (v___x_4834_ == 0)
{
lean_dec_ref(v_arg_4827_);
goto v___jp_4813_;
}
else
{
lean_object* v___x_4835_; 
lean_dec_ref(v_e_4812_);
v___x_4835_ = l_Lean_Expr_nat_x3f(v_arg_4827_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v___x_4836_; 
v___x_4836_ = lean_box(0);
return v___x_4836_;
}
else
{
lean_object* v_val_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4849_; 
v_val_4837_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4839_ = v___x_4835_;
v_isShared_4840_ = v_isSharedCheck_4849_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_val_4837_);
lean_dec(v___x_4835_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4849_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4841_; uint8_t v___x_4842_; 
v___x_4841_ = lean_unsigned_to_nat(0u);
v___x_4842_ = lean_nat_dec_eq(v_val_4837_, v___x_4841_);
if (v___x_4842_ == 0)
{
lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4846_; 
v___x_4843_ = lean_nat_to_int(v_val_4837_);
v___x_4844_ = lean_int_neg(v___x_4843_);
lean_dec(v___x_4843_);
if (v_isShared_4840_ == 0)
{
lean_ctor_set(v___x_4839_, 0, v___x_4844_);
v___x_4846_ = v___x_4839_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v___x_4844_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
else
{
lean_object* v___x_4848_; 
lean_del_object(v___x_4839_);
lean_dec(v_val_4837_);
v___x_4848_ = lean_box(0);
return v___x_4848_;
}
}
}
}
}
}
}
v___jp_4813_:
{
lean_object* v___x_4814_; 
v___x_4814_ = l_Lean_Expr_nat_x3f(v_e_4812_);
if (lean_obj_tag(v___x_4814_) == 0)
{
lean_object* v___x_4815_; 
v___x_4815_ = lean_box(0);
return v___x_4815_;
}
else
{
lean_object* v_val_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4824_; 
v_val_4816_ = lean_ctor_get(v___x_4814_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4814_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4818_ = v___x_4814_;
v_isShared_4819_ = v_isSharedCheck_4824_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_val_4816_);
lean_dec(v___x_4814_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4824_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4820_; lean_object* v___x_4822_; 
v___x_4820_ = lean_nat_to_int(v_val_4816_);
if (v_isShared_4819_ == 0)
{
lean_ctor_set(v___x_4818_, 0, v___x_4820_);
v___x_4822_ = v___x_4818_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v___x_4820_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4850_, lean_object* v_e_4851_){
_start:
{
uint8_t v___x_4852_; lean_object* v_d_4854_; lean_object* v_b_4855_; 
v___x_4852_ = l_Lean_Expr_hasFVar(v_e_4851_);
if (v___x_4852_ == 0)
{
lean_dec_ref(v_e_4851_);
lean_dec_ref(v_p_4850_);
return v___x_4852_;
}
else
{
switch(lean_obj_tag(v_e_4851_))
{
case 7:
{
lean_object* v_binderType_4858_; lean_object* v_body_4859_; 
v_binderType_4858_ = lean_ctor_get(v_e_4851_, 1);
lean_inc_ref(v_binderType_4858_);
v_body_4859_ = lean_ctor_get(v_e_4851_, 2);
lean_inc_ref(v_body_4859_);
lean_dec_ref_known(v_e_4851_, 3);
v_d_4854_ = v_binderType_4858_;
v_b_4855_ = v_body_4859_;
goto v___jp_4853_;
}
case 6:
{
lean_object* v_binderType_4860_; lean_object* v_body_4861_; 
v_binderType_4860_ = lean_ctor_get(v_e_4851_, 1);
lean_inc_ref(v_binderType_4860_);
v_body_4861_ = lean_ctor_get(v_e_4851_, 2);
lean_inc_ref(v_body_4861_);
lean_dec_ref_known(v_e_4851_, 3);
v_d_4854_ = v_binderType_4860_;
v_b_4855_ = v_body_4861_;
goto v___jp_4853_;
}
case 10:
{
lean_object* v_expr_4862_; 
v_expr_4862_ = lean_ctor_get(v_e_4851_, 1);
lean_inc_ref(v_expr_4862_);
lean_dec_ref_known(v_e_4851_, 2);
v_e_4851_ = v_expr_4862_;
goto _start;
}
case 8:
{
lean_object* v_type_4864_; lean_object* v_value_4865_; lean_object* v_body_4866_; uint8_t v___x_4867_; 
v_type_4864_ = lean_ctor_get(v_e_4851_, 1);
lean_inc_ref(v_type_4864_);
v_value_4865_ = lean_ctor_get(v_e_4851_, 2);
lean_inc_ref(v_value_4865_);
v_body_4866_ = lean_ctor_get(v_e_4851_, 3);
lean_inc_ref(v_body_4866_);
lean_dec_ref_known(v_e_4851_, 4);
lean_inc_ref(v_p_4850_);
v___x_4867_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4850_, v_type_4864_);
if (v___x_4867_ == 0)
{
uint8_t v___x_4868_; 
lean_inc_ref(v_p_4850_);
v___x_4868_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4850_, v_value_4865_);
if (v___x_4868_ == 0)
{
v_e_4851_ = v_body_4866_;
goto _start;
}
else
{
lean_dec_ref(v_body_4866_);
lean_dec_ref(v_p_4850_);
return v___x_4852_;
}
}
else
{
lean_dec_ref(v_body_4866_);
lean_dec_ref(v_value_4865_);
lean_dec_ref(v_p_4850_);
return v___x_4852_;
}
}
case 5:
{
lean_object* v_fn_4870_; lean_object* v_arg_4871_; uint8_t v___x_4872_; 
v_fn_4870_ = lean_ctor_get(v_e_4851_, 0);
lean_inc_ref(v_fn_4870_);
v_arg_4871_ = lean_ctor_get(v_e_4851_, 1);
lean_inc_ref(v_arg_4871_);
lean_dec_ref_known(v_e_4851_, 2);
lean_inc_ref(v_p_4850_);
v___x_4872_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4850_, v_fn_4870_);
if (v___x_4872_ == 0)
{
v_e_4851_ = v_arg_4871_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4871_);
lean_dec_ref(v_p_4850_);
return v___x_4852_;
}
}
case 11:
{
lean_object* v_struct_4874_; 
v_struct_4874_ = lean_ctor_get(v_e_4851_, 2);
lean_inc_ref(v_struct_4874_);
lean_dec_ref_known(v_e_4851_, 3);
v_e_4851_ = v_struct_4874_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4876_; lean_object* v___x_4877_; uint8_t v___x_4878_; 
v_fvarId_4876_ = lean_ctor_get(v_e_4851_, 0);
lean_inc(v_fvarId_4876_);
lean_dec_ref_known(v_e_4851_, 1);
v___x_4877_ = lean_apply_1(v_p_4850_, v_fvarId_4876_);
v___x_4878_ = lean_unbox(v___x_4877_);
return v___x_4878_;
}
default: 
{
uint8_t v___x_4879_; 
lean_dec_ref(v_e_4851_);
lean_dec_ref(v_p_4850_);
v___x_4879_ = 0;
return v___x_4879_;
}
}
}
v___jp_4853_:
{
uint8_t v___x_4856_; 
lean_inc_ref(v_p_4850_);
v___x_4856_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4850_, v_d_4854_);
if (v___x_4856_ == 0)
{
v_e_4851_ = v_b_4855_;
goto _start;
}
else
{
lean_dec_ref(v_b_4855_);
lean_dec_ref(v_p_4850_);
return v___x_4852_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_4880_, lean_object* v_e_4881_){
_start:
{
uint8_t v_res_4882_; lean_object* v_r_4883_; 
v_res_4882_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4880_, v_e_4881_);
v_r_4883_ = lean_box(v_res_4882_);
return v_r_4883_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_4884_, lean_object* v_p_4885_){
_start:
{
uint8_t v___x_4886_; 
v___x_4886_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4885_, v_e_4884_);
return v___x_4886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_4887_, lean_object* v_p_4888_){
_start:
{
uint8_t v_res_4889_; lean_object* v_r_4890_; 
v_res_4889_ = l_Lean_Expr_hasAnyFVar(v_e_4887_, v_p_4888_);
v_r_4890_ = lean_box(v_res_4889_);
return v_r_4890_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_4891_, lean_object* v_e_4892_){
_start:
{
uint8_t v___x_4893_; lean_object* v_d_4895_; lean_object* v_b_4896_; 
v___x_4893_ = l_Lean_Expr_hasFVar(v_e_4892_);
if (v___x_4893_ == 0)
{
return v___x_4893_;
}
else
{
switch(lean_obj_tag(v_e_4892_))
{
case 7:
{
lean_object* v_binderType_4899_; lean_object* v_body_4900_; 
v_binderType_4899_ = lean_ctor_get(v_e_4892_, 1);
v_body_4900_ = lean_ctor_get(v_e_4892_, 2);
v_d_4895_ = v_binderType_4899_;
v_b_4896_ = v_body_4900_;
goto v___jp_4894_;
}
case 6:
{
lean_object* v_binderType_4901_; lean_object* v_body_4902_; 
v_binderType_4901_ = lean_ctor_get(v_e_4892_, 1);
v_body_4902_ = lean_ctor_get(v_e_4892_, 2);
v_d_4895_ = v_binderType_4901_;
v_b_4896_ = v_body_4902_;
goto v___jp_4894_;
}
case 10:
{
lean_object* v_expr_4903_; 
v_expr_4903_ = lean_ctor_get(v_e_4892_, 1);
v_e_4892_ = v_expr_4903_;
goto _start;
}
case 8:
{
lean_object* v_type_4905_; lean_object* v_value_4906_; lean_object* v_body_4907_; uint8_t v___x_4908_; 
v_type_4905_ = lean_ctor_get(v_e_4892_, 1);
v_value_4906_ = lean_ctor_get(v_e_4892_, 2);
v_body_4907_ = lean_ctor_get(v_e_4892_, 3);
v___x_4908_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4891_, v_type_4905_);
if (v___x_4908_ == 0)
{
uint8_t v___x_4909_; 
v___x_4909_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4891_, v_value_4906_);
if (v___x_4909_ == 0)
{
v_e_4892_ = v_body_4907_;
goto _start;
}
else
{
return v___x_4893_;
}
}
else
{
return v___x_4893_;
}
}
case 5:
{
lean_object* v_fn_4911_; lean_object* v_arg_4912_; uint8_t v___x_4913_; 
v_fn_4911_ = lean_ctor_get(v_e_4892_, 0);
v_arg_4912_ = lean_ctor_get(v_e_4892_, 1);
v___x_4913_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4891_, v_fn_4911_);
if (v___x_4913_ == 0)
{
v_e_4892_ = v_arg_4912_;
goto _start;
}
else
{
return v___x_4893_;
}
}
case 11:
{
lean_object* v_struct_4915_; 
v_struct_4915_ = lean_ctor_get(v_e_4892_, 2);
v_e_4892_ = v_struct_4915_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4917_; uint8_t v___x_4918_; 
v_fvarId_4917_ = lean_ctor_get(v_e_4892_, 0);
v___x_4918_ = lean_name_eq(v_fvarId_4917_, v_fvarId_4891_);
return v___x_4918_;
}
default: 
{
uint8_t v___x_4919_; 
v___x_4919_ = 0;
return v___x_4919_;
}
}
}
v___jp_4894_:
{
uint8_t v___x_4897_; 
v___x_4897_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4891_, v_d_4895_);
if (v___x_4897_ == 0)
{
v_e_4892_ = v_b_4896_;
goto _start;
}
else
{
return v___x_4893_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_4920_, lean_object* v_e_4921_){
_start:
{
uint8_t v_res_4922_; lean_object* v_r_4923_; 
v_res_4922_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4920_, v_e_4921_);
lean_dec_ref(v_e_4921_);
lean_dec(v_fvarId_4920_);
v_r_4923_ = lean_box(v_res_4922_);
return v_r_4923_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_4924_, lean_object* v_fvarId_4925_){
_start:
{
uint8_t v___x_4926_; 
v___x_4926_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4925_, v_e_4924_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_4927_, lean_object* v_fvarId_4928_){
_start:
{
uint8_t v_res_4929_; lean_object* v_r_4930_; 
v_res_4929_ = l_Lean_Expr_containsFVar(v_e_4927_, v_fvarId_4928_);
lean_dec(v_fvarId_4928_);
lean_dec_ref(v_e_4927_);
v_r_4930_ = lean_box(v_res_4929_);
return v_r_4930_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(lean_object* v_p_4931_, lean_object* v_e_4932_){
_start:
{
uint8_t v___x_4933_; lean_object* v_d_4935_; lean_object* v_b_4936_; 
v___x_4933_ = l_Lean_Expr_hasExprMVar(v_e_4932_);
if (v___x_4933_ == 0)
{
lean_dec_ref(v_e_4932_);
lean_dec_ref(v_p_4931_);
return v___x_4933_;
}
else
{
switch(lean_obj_tag(v_e_4932_))
{
case 7:
{
lean_object* v_binderType_4939_; lean_object* v_body_4940_; 
v_binderType_4939_ = lean_ctor_get(v_e_4932_, 1);
lean_inc_ref(v_binderType_4939_);
v_body_4940_ = lean_ctor_get(v_e_4932_, 2);
lean_inc_ref(v_body_4940_);
lean_dec_ref_known(v_e_4932_, 3);
v_d_4935_ = v_binderType_4939_;
v_b_4936_ = v_body_4940_;
goto v___jp_4934_;
}
case 6:
{
lean_object* v_binderType_4941_; lean_object* v_body_4942_; 
v_binderType_4941_ = lean_ctor_get(v_e_4932_, 1);
lean_inc_ref(v_binderType_4941_);
v_body_4942_ = lean_ctor_get(v_e_4932_, 2);
lean_inc_ref(v_body_4942_);
lean_dec_ref_known(v_e_4932_, 3);
v_d_4935_ = v_binderType_4941_;
v_b_4936_ = v_body_4942_;
goto v___jp_4934_;
}
case 10:
{
lean_object* v_expr_4943_; 
v_expr_4943_ = lean_ctor_get(v_e_4932_, 1);
lean_inc_ref(v_expr_4943_);
lean_dec_ref_known(v_e_4932_, 2);
v_e_4932_ = v_expr_4943_;
goto _start;
}
case 8:
{
lean_object* v_type_4945_; lean_object* v_value_4946_; lean_object* v_body_4947_; uint8_t v___x_4948_; 
v_type_4945_ = lean_ctor_get(v_e_4932_, 1);
lean_inc_ref(v_type_4945_);
v_value_4946_ = lean_ctor_get(v_e_4932_, 2);
lean_inc_ref(v_value_4946_);
v_body_4947_ = lean_ctor_get(v_e_4932_, 3);
lean_inc_ref(v_body_4947_);
lean_dec_ref_known(v_e_4932_, 4);
lean_inc_ref(v_p_4931_);
v___x_4948_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4931_, v_type_4945_);
if (v___x_4948_ == 0)
{
uint8_t v___x_4949_; 
lean_inc_ref(v_p_4931_);
v___x_4949_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4931_, v_value_4946_);
if (v___x_4949_ == 0)
{
v_e_4932_ = v_body_4947_;
goto _start;
}
else
{
lean_dec_ref(v_body_4947_);
lean_dec_ref(v_p_4931_);
return v___x_4933_;
}
}
else
{
lean_dec_ref(v_body_4947_);
lean_dec_ref(v_value_4946_);
lean_dec_ref(v_p_4931_);
return v___x_4933_;
}
}
case 5:
{
lean_object* v_fn_4951_; lean_object* v_arg_4952_; uint8_t v___x_4953_; 
v_fn_4951_ = lean_ctor_get(v_e_4932_, 0);
lean_inc_ref(v_fn_4951_);
v_arg_4952_ = lean_ctor_get(v_e_4932_, 1);
lean_inc_ref(v_arg_4952_);
lean_dec_ref_known(v_e_4932_, 2);
lean_inc_ref(v_p_4931_);
v___x_4953_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4931_, v_fn_4951_);
if (v___x_4953_ == 0)
{
v_e_4932_ = v_arg_4952_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4952_);
lean_dec_ref(v_p_4931_);
return v___x_4933_;
}
}
case 11:
{
lean_object* v_struct_4955_; 
v_struct_4955_ = lean_ctor_get(v_e_4932_, 2);
lean_inc_ref(v_struct_4955_);
lean_dec_ref_known(v_e_4932_, 3);
v_e_4932_ = v_struct_4955_;
goto _start;
}
case 2:
{
lean_object* v_mvarId_4957_; lean_object* v___x_4958_; uint8_t v___x_4959_; 
v_mvarId_4957_ = lean_ctor_get(v_e_4932_, 0);
lean_inc(v_mvarId_4957_);
lean_dec_ref_known(v_e_4932_, 1);
v___x_4958_ = lean_apply_1(v_p_4931_, v_mvarId_4957_);
v___x_4959_ = lean_unbox(v___x_4958_);
return v___x_4959_;
}
default: 
{
uint8_t v___x_4960_; 
lean_dec_ref(v_e_4932_);
lean_dec_ref(v_p_4931_);
v___x_4960_ = 0;
return v___x_4960_;
}
}
}
v___jp_4934_:
{
uint8_t v___x_4937_; 
lean_inc_ref(v_p_4931_);
v___x_4937_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4931_, v_d_4935_);
if (v___x_4937_ == 0)
{
v_e_4932_ = v_b_4936_;
goto _start;
}
else
{
lean_dec_ref(v_b_4936_);
lean_dec_ref(v_p_4931_);
return v___x_4933_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___boxed(lean_object* v_p_4961_, lean_object* v_e_4962_){
_start:
{
uint8_t v_res_4963_; lean_object* v_r_4964_; 
v_res_4963_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4961_, v_e_4962_);
v_r_4964_ = lean_box(v_res_4963_);
return v_r_4964_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyMVar(lean_object* v_e_4965_, lean_object* v_p_4966_){
_start:
{
uint8_t v___x_4967_; 
v___x_4967_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4966_, v_e_4965_);
return v___x_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyMVar___boxed(lean_object* v_e_4968_, lean_object* v_p_4969_){
_start:
{
uint8_t v_res_4970_; lean_object* v_r_4971_; 
v_res_4970_ = l_Lean_Expr_hasAnyMVar(v_e_4968_, v_p_4969_);
v_r_4971_ = lean_box(v_res_4970_);
return v_r_4971_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(lean_object* v_mvarId_4972_, lean_object* v_e_4973_){
_start:
{
uint8_t v___x_4974_; lean_object* v_d_4976_; lean_object* v_b_4977_; 
v___x_4974_ = l_Lean_Expr_hasExprMVar(v_e_4973_);
if (v___x_4974_ == 0)
{
return v___x_4974_;
}
else
{
switch(lean_obj_tag(v_e_4973_))
{
case 7:
{
lean_object* v_binderType_4980_; lean_object* v_body_4981_; 
v_binderType_4980_ = lean_ctor_get(v_e_4973_, 1);
v_body_4981_ = lean_ctor_get(v_e_4973_, 2);
v_d_4976_ = v_binderType_4980_;
v_b_4977_ = v_body_4981_;
goto v___jp_4975_;
}
case 6:
{
lean_object* v_binderType_4982_; lean_object* v_body_4983_; 
v_binderType_4982_ = lean_ctor_get(v_e_4973_, 1);
v_body_4983_ = lean_ctor_get(v_e_4973_, 2);
v_d_4976_ = v_binderType_4982_;
v_b_4977_ = v_body_4983_;
goto v___jp_4975_;
}
case 10:
{
lean_object* v_expr_4984_; 
v_expr_4984_ = lean_ctor_get(v_e_4973_, 1);
v_e_4973_ = v_expr_4984_;
goto _start;
}
case 8:
{
lean_object* v_type_4986_; lean_object* v_value_4987_; lean_object* v_body_4988_; uint8_t v___x_4989_; 
v_type_4986_ = lean_ctor_get(v_e_4973_, 1);
v_value_4987_ = lean_ctor_get(v_e_4973_, 2);
v_body_4988_ = lean_ctor_get(v_e_4973_, 3);
v___x_4989_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4972_, v_type_4986_);
if (v___x_4989_ == 0)
{
uint8_t v___x_4990_; 
v___x_4990_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4972_, v_value_4987_);
if (v___x_4990_ == 0)
{
v_e_4973_ = v_body_4988_;
goto _start;
}
else
{
return v___x_4974_;
}
}
else
{
return v___x_4974_;
}
}
case 5:
{
lean_object* v_fn_4992_; lean_object* v_arg_4993_; uint8_t v___x_4994_; 
v_fn_4992_ = lean_ctor_get(v_e_4973_, 0);
v_arg_4993_ = lean_ctor_get(v_e_4973_, 1);
v___x_4994_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4972_, v_fn_4992_);
if (v___x_4994_ == 0)
{
v_e_4973_ = v_arg_4993_;
goto _start;
}
else
{
return v___x_4974_;
}
}
case 11:
{
lean_object* v_struct_4996_; 
v_struct_4996_ = lean_ctor_get(v_e_4973_, 2);
v_e_4973_ = v_struct_4996_;
goto _start;
}
case 2:
{
lean_object* v_mvarId_4998_; uint8_t v___x_4999_; 
v_mvarId_4998_ = lean_ctor_get(v_e_4973_, 0);
v___x_4999_ = lean_name_eq(v_mvarId_4998_, v_mvarId_4972_);
return v___x_4999_;
}
default: 
{
uint8_t v___x_5000_; 
v___x_5000_ = 0;
return v___x_5000_;
}
}
}
v___jp_4975_:
{
uint8_t v___x_4978_; 
v___x_4978_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4972_, v_d_4976_);
if (v___x_4978_ == 0)
{
v_e_4973_ = v_b_4977_;
goto _start;
}
else
{
return v___x_4974_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0___boxed(lean_object* v_mvarId_5001_, lean_object* v_e_5002_){
_start:
{
uint8_t v_res_5003_; lean_object* v_r_5004_; 
v_res_5003_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5001_, v_e_5002_);
lean_dec_ref(v_e_5002_);
lean_dec(v_mvarId_5001_);
v_r_5004_ = lean_box(v_res_5003_);
return v_r_5004_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsMVar(lean_object* v_e_5005_, lean_object* v_mvarId_5006_){
_start:
{
uint8_t v___x_5007_; 
v___x_5007_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5006_, v_e_5005_);
return v___x_5007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsMVar___boxed(lean_object* v_e_5008_, lean_object* v_mvarId_5009_){
_start:
{
uint8_t v_res_5010_; lean_object* v_r_5011_; 
v_res_5010_ = l_Lean_Expr_containsMVar(v_e_5008_, v_mvarId_5009_);
lean_dec(v_mvarId_5009_);
lean_dec_ref(v_e_5008_);
v_r_5011_ = lean_box(v_res_5010_);
return v_r_5011_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; 
v___x_5013_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_5014_ = lean_unsigned_to_nat(18u);
v___x_5015_ = lean_unsigned_to_nat(1864u);
v___x_5016_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_5017_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5018_ = l_mkPanicMessageWithDecl(v___x_5017_, v___x_5016_, v___x_5015_, v___x_5014_, v___x_5013_);
return v___x_5018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_5019_, lean_object* v_newFn_5020_, lean_object* v_newArg_5021_){
_start:
{
if (lean_obj_tag(v_e_5019_) == 5)
{
lean_object* v_fn_5022_; lean_object* v_arg_5023_; size_t v___x_5024_; size_t v___x_5025_; uint8_t v___x_5026_; 
v_fn_5022_ = lean_ctor_get(v_e_5019_, 0);
v_arg_5023_ = lean_ctor_get(v_e_5019_, 1);
v___x_5024_ = lean_ptr_addr(v_fn_5022_);
v___x_5025_ = lean_ptr_addr(v_newFn_5020_);
v___x_5026_ = lean_usize_dec_eq(v___x_5024_, v___x_5025_);
if (v___x_5026_ == 0)
{
lean_object* v___x_5027_; 
v___x_5027_ = l_Lean_Expr_app___override(v_newFn_5020_, v_newArg_5021_);
return v___x_5027_;
}
else
{
size_t v___x_5028_; size_t v___x_5029_; uint8_t v___x_5030_; 
v___x_5028_ = lean_ptr_addr(v_arg_5023_);
v___x_5029_ = lean_ptr_addr(v_newArg_5021_);
v___x_5030_ = lean_usize_dec_eq(v___x_5028_, v___x_5029_);
if (v___x_5030_ == 0)
{
lean_object* v___x_5031_; 
v___x_5031_ = l_Lean_Expr_app___override(v_newFn_5020_, v_newArg_5021_);
return v___x_5031_;
}
else
{
lean_dec_ref(v_newArg_5021_);
lean_dec_ref(v_newFn_5020_);
lean_inc_ref(v_e_5019_);
return v_e_5019_;
}
}
}
else
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
lean_dec_ref(v_newArg_5021_);
lean_dec_ref(v_newFn_5020_);
v___x_5032_ = l_Lean_instInhabitedExpr;
v___x_5033_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_5034_ = l_panic___redArg(v___x_5032_, v___x_5033_);
return v___x_5034_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_5035_, lean_object* v_newFn_5036_, lean_object* v_newArg_5037_){
_start:
{
lean_object* v_res_5038_; 
v_res_5038_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_5035_, v_newFn_5036_, v_newArg_5037_);
lean_dec_ref(v_e_5035_);
return v_res_5038_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
v___x_5040_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_5041_ = lean_unsigned_to_nat(20u);
v___x_5042_ = lean_unsigned_to_nat(1875u);
v___x_5043_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_5044_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5045_ = l_mkPanicMessageWithDecl(v___x_5044_, v___x_5043_, v___x_5042_, v___x_5041_, v___x_5040_);
return v___x_5045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_5046_, lean_object* v_fvarIdNew_5047_){
_start:
{
if (lean_obj_tag(v_e_5046_) == 1)
{
lean_object* v_fvarId_5048_; uint8_t v___x_5049_; 
v_fvarId_5048_ = lean_ctor_get(v_e_5046_, 0);
v___x_5049_ = lean_name_eq(v_fvarId_5048_, v_fvarIdNew_5047_);
if (v___x_5049_ == 0)
{
lean_object* v___x_5050_; 
v___x_5050_ = l_Lean_Expr_fvar___override(v_fvarIdNew_5047_);
return v___x_5050_;
}
else
{
lean_dec(v_fvarIdNew_5047_);
lean_inc_ref(v_e_5046_);
return v_e_5046_;
}
}
else
{
lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
lean_dec(v_fvarIdNew_5047_);
v___x_5051_ = l_Lean_instInhabitedExpr;
v___x_5052_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_5053_ = l_panic___redArg(v___x_5051_, v___x_5052_);
return v___x_5053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_5054_, lean_object* v_fvarIdNew_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l_Lean_Expr_updateFVar_x21(v_e_5054_, v_fvarIdNew_5055_);
lean_dec_ref(v_e_5054_);
return v_res_5056_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
v___x_5058_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_5059_ = lean_unsigned_to_nat(18u);
v___x_5060_ = lean_unsigned_to_nat(1880u);
v___x_5061_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_5062_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5063_ = l_mkPanicMessageWithDecl(v___x_5062_, v___x_5061_, v___x_5060_, v___x_5059_, v___x_5058_);
return v___x_5063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_5064_, lean_object* v_newLevels_5065_){
_start:
{
if (lean_obj_tag(v_e_5064_) == 4)
{
lean_object* v_declName_5066_; lean_object* v_us_5067_; uint8_t v___x_5068_; 
v_declName_5066_ = lean_ctor_get(v_e_5064_, 0);
v_us_5067_ = lean_ctor_get(v_e_5064_, 1);
v___x_5068_ = l_ptrEqList___redArg(v_us_5067_, v_newLevels_5065_);
if (v___x_5068_ == 0)
{
lean_object* v___x_5069_; 
lean_inc(v_declName_5066_);
lean_dec_ref_known(v_e_5064_, 2);
v___x_5069_ = l_Lean_Expr_const___override(v_declName_5066_, v_newLevels_5065_);
return v___x_5069_;
}
else
{
lean_dec(v_newLevels_5065_);
return v_e_5064_;
}
}
else
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; 
lean_dec(v_newLevels_5065_);
lean_dec_ref(v_e_5064_);
v___x_5070_ = l_Lean_instInhabitedExpr;
v___x_5071_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_5072_ = l_panic___redArg(v___x_5070_, v___x_5071_);
return v___x_5072_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; 
v___x_5075_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_5076_ = lean_unsigned_to_nat(14u);
v___x_5077_ = lean_unsigned_to_nat(1891u);
v___x_5078_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_5079_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5080_ = l_mkPanicMessageWithDecl(v___x_5079_, v___x_5078_, v___x_5077_, v___x_5076_, v___x_5075_);
return v___x_5080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_5081_, lean_object* v_u_x27_5082_){
_start:
{
if (lean_obj_tag(v_e_5081_) == 3)
{
lean_object* v_u_5083_; size_t v___x_5084_; size_t v___x_5085_; uint8_t v___x_5086_; 
v_u_5083_ = lean_ctor_get(v_e_5081_, 0);
v___x_5084_ = lean_ptr_addr(v_u_5083_);
v___x_5085_ = lean_ptr_addr(v_u_x27_5082_);
v___x_5086_ = lean_usize_dec_eq(v___x_5084_, v___x_5085_);
if (v___x_5086_ == 0)
{
lean_object* v___x_5087_; 
v___x_5087_ = l_Lean_Expr_sort___override(v_u_x27_5082_);
return v___x_5087_;
}
else
{
lean_dec(v_u_x27_5082_);
lean_inc_ref(v_e_5081_);
return v_e_5081_;
}
}
else
{
lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; 
lean_dec(v_u_x27_5082_);
v___x_5088_ = l_Lean_instInhabitedExpr;
v___x_5089_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_5090_ = l_panic___redArg(v___x_5088_, v___x_5089_);
return v___x_5090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_5091_, lean_object* v_u_x27_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_5091_, v_u_x27_5092_);
lean_dec_ref(v_e_5091_);
return v_res_5093_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; 
v___x_5096_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_5097_ = lean_unsigned_to_nat(17u);
v___x_5098_ = lean_unsigned_to_nat(1902u);
v___x_5099_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_5100_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5101_ = l_mkPanicMessageWithDecl(v___x_5100_, v___x_5099_, v___x_5098_, v___x_5097_, v___x_5096_);
return v___x_5101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_5102_, lean_object* v_newExpr_5103_){
_start:
{
if (lean_obj_tag(v_e_5102_) == 10)
{
lean_object* v_data_5104_; lean_object* v_expr_5105_; size_t v___x_5106_; size_t v___x_5107_; uint8_t v___x_5108_; 
v_data_5104_ = lean_ctor_get(v_e_5102_, 0);
v_expr_5105_ = lean_ctor_get(v_e_5102_, 1);
v___x_5106_ = lean_ptr_addr(v_expr_5105_);
v___x_5107_ = lean_ptr_addr(v_newExpr_5103_);
v___x_5108_ = lean_usize_dec_eq(v___x_5106_, v___x_5107_);
if (v___x_5108_ == 0)
{
lean_object* v___x_5109_; 
lean_inc(v_data_5104_);
lean_dec_ref_known(v_e_5102_, 2);
v___x_5109_ = l_Lean_Expr_mdata___override(v_data_5104_, v_newExpr_5103_);
return v___x_5109_;
}
else
{
lean_dec_ref(v_newExpr_5103_);
return v_e_5102_;
}
}
else
{
lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; 
lean_dec_ref(v_newExpr_5103_);
lean_dec_ref(v_e_5102_);
v___x_5110_ = l_Lean_instInhabitedExpr;
v___x_5111_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_5112_ = l_panic___redArg(v___x_5110_, v___x_5111_);
return v___x_5112_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5115_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_5116_ = lean_unsigned_to_nat(18u);
v___x_5117_ = lean_unsigned_to_nat(1913u);
v___x_5118_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_5119_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5120_ = l_mkPanicMessageWithDecl(v___x_5119_, v___x_5118_, v___x_5117_, v___x_5116_, v___x_5115_);
return v___x_5120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_5121_, lean_object* v_newExpr_5122_){
_start:
{
if (lean_obj_tag(v_e_5121_) == 11)
{
lean_object* v_typeName_5123_; lean_object* v_idx_5124_; lean_object* v_struct_5125_; size_t v___x_5126_; size_t v___x_5127_; uint8_t v___x_5128_; 
v_typeName_5123_ = lean_ctor_get(v_e_5121_, 0);
v_idx_5124_ = lean_ctor_get(v_e_5121_, 1);
v_struct_5125_ = lean_ctor_get(v_e_5121_, 2);
v___x_5126_ = lean_ptr_addr(v_struct_5125_);
v___x_5127_ = lean_ptr_addr(v_newExpr_5122_);
v___x_5128_ = lean_usize_dec_eq(v___x_5126_, v___x_5127_);
if (v___x_5128_ == 0)
{
lean_object* v___x_5129_; 
lean_inc(v_idx_5124_);
lean_inc(v_typeName_5123_);
lean_dec_ref_known(v_e_5121_, 3);
v___x_5129_ = l_Lean_Expr_proj___override(v_typeName_5123_, v_idx_5124_, v_newExpr_5122_);
return v___x_5129_;
}
else
{
lean_dec_ref(v_newExpr_5122_);
return v_e_5121_;
}
}
else
{
lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; 
lean_dec_ref(v_newExpr_5122_);
lean_dec_ref(v_e_5121_);
v___x_5130_ = l_Lean_instInhabitedExpr;
v___x_5131_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_5132_ = l_panic___redArg(v___x_5130_, v___x_5131_);
return v___x_5132_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; 
v___x_5135_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5136_ = lean_unsigned_to_nat(23u);
v___x_5137_ = lean_unsigned_to_nat(1928u);
v___x_5138_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_5139_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5140_ = l_mkPanicMessageWithDecl(v___x_5139_, v___x_5138_, v___x_5137_, v___x_5136_, v___x_5135_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_5141_, uint8_t v_newBinfo_5142_, lean_object* v_newDomain_5143_, lean_object* v_newBody_5144_){
_start:
{
if (lean_obj_tag(v_e_5141_) == 7)
{
lean_object* v_binderName_5145_; lean_object* v_binderType_5146_; lean_object* v_body_5147_; uint8_t v_binderInfo_5148_; size_t v___x_5149_; size_t v___x_5150_; uint8_t v___x_5151_; 
v_binderName_5145_ = lean_ctor_get(v_e_5141_, 0);
v_binderType_5146_ = lean_ctor_get(v_e_5141_, 1);
v_body_5147_ = lean_ctor_get(v_e_5141_, 2);
v_binderInfo_5148_ = lean_ctor_get_uint8(v_e_5141_, sizeof(void*)*3 + 8);
v___x_5149_ = lean_ptr_addr(v_binderType_5146_);
v___x_5150_ = lean_ptr_addr(v_newDomain_5143_);
v___x_5151_ = lean_usize_dec_eq(v___x_5149_, v___x_5150_);
if (v___x_5151_ == 0)
{
lean_object* v___x_5152_; 
lean_inc(v_binderName_5145_);
lean_dec_ref_known(v_e_5141_, 3);
v___x_5152_ = l_Lean_Expr_forallE___override(v_binderName_5145_, v_newDomain_5143_, v_newBody_5144_, v_newBinfo_5142_);
return v___x_5152_;
}
else
{
size_t v___x_5153_; size_t v___x_5154_; uint8_t v___x_5155_; 
v___x_5153_ = lean_ptr_addr(v_body_5147_);
v___x_5154_ = lean_ptr_addr(v_newBody_5144_);
v___x_5155_ = lean_usize_dec_eq(v___x_5153_, v___x_5154_);
if (v___x_5155_ == 0)
{
lean_object* v___x_5156_; 
lean_inc(v_binderName_5145_);
lean_dec_ref_known(v_e_5141_, 3);
v___x_5156_ = l_Lean_Expr_forallE___override(v_binderName_5145_, v_newDomain_5143_, v_newBody_5144_, v_newBinfo_5142_);
return v___x_5156_;
}
else
{
uint8_t v___x_5157_; 
v___x_5157_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5148_, v_newBinfo_5142_);
if (v___x_5157_ == 0)
{
lean_object* v___x_5158_; 
lean_inc(v_binderName_5145_);
lean_dec_ref_known(v_e_5141_, 3);
v___x_5158_ = l_Lean_Expr_forallE___override(v_binderName_5145_, v_newDomain_5143_, v_newBody_5144_, v_newBinfo_5142_);
return v___x_5158_;
}
else
{
lean_dec_ref(v_newBody_5144_);
lean_dec_ref(v_newDomain_5143_);
return v_e_5141_;
}
}
}
}
else
{
lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; 
lean_dec_ref(v_newBody_5144_);
lean_dec_ref(v_newDomain_5143_);
lean_dec_ref(v_e_5141_);
v___x_5159_ = l_Lean_instInhabitedExpr;
v___x_5160_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_5161_ = l_panic___redArg(v___x_5159_, v___x_5160_);
return v___x_5161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_5162_, lean_object* v_newBinfo_5163_, lean_object* v_newDomain_5164_, lean_object* v_newBody_5165_){
_start:
{
uint8_t v_newBinfo_boxed_5166_; lean_object* v_res_5167_; 
v_newBinfo_boxed_5166_ = lean_unbox(v_newBinfo_5163_);
v_res_5167_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5162_, v_newBinfo_boxed_5166_, v_newDomain_5164_, v_newBody_5165_);
return v_res_5167_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; 
v___x_5169_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5170_ = lean_unsigned_to_nat(24u);
v___x_5171_ = lean_unsigned_to_nat(1939u);
v___x_5172_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_5173_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5174_ = l_mkPanicMessageWithDecl(v___x_5173_, v___x_5172_, v___x_5171_, v___x_5170_, v___x_5169_);
return v___x_5174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_5175_, lean_object* v_newDomain_5176_, lean_object* v_newBody_5177_){
_start:
{
if (lean_obj_tag(v_e_5175_) == 7)
{
lean_object* v_binderName_5178_; lean_object* v_binderType_5179_; lean_object* v_body_5180_; uint8_t v_binderInfo_5181_; size_t v___x_5182_; size_t v___x_5183_; uint8_t v___x_5184_; 
v_binderName_5178_ = lean_ctor_get(v_e_5175_, 0);
v_binderType_5179_ = lean_ctor_get(v_e_5175_, 1);
v_body_5180_ = lean_ctor_get(v_e_5175_, 2);
v_binderInfo_5181_ = lean_ctor_get_uint8(v_e_5175_, sizeof(void*)*3 + 8);
v___x_5182_ = lean_ptr_addr(v_binderType_5179_);
v___x_5183_ = lean_ptr_addr(v_newDomain_5176_);
v___x_5184_ = lean_usize_dec_eq(v___x_5182_, v___x_5183_);
if (v___x_5184_ == 0)
{
lean_object* v___x_5185_; 
lean_inc(v_binderName_5178_);
lean_dec_ref_known(v_e_5175_, 3);
v___x_5185_ = l_Lean_Expr_forallE___override(v_binderName_5178_, v_newDomain_5176_, v_newBody_5177_, v_binderInfo_5181_);
return v___x_5185_;
}
else
{
size_t v___x_5186_; size_t v___x_5187_; uint8_t v___x_5188_; 
v___x_5186_ = lean_ptr_addr(v_body_5180_);
v___x_5187_ = lean_ptr_addr(v_newBody_5177_);
v___x_5188_ = lean_usize_dec_eq(v___x_5186_, v___x_5187_);
if (v___x_5188_ == 0)
{
lean_object* v___x_5189_; 
lean_inc(v_binderName_5178_);
lean_dec_ref_known(v_e_5175_, 3);
v___x_5189_ = l_Lean_Expr_forallE___override(v_binderName_5178_, v_newDomain_5176_, v_newBody_5177_, v_binderInfo_5181_);
return v___x_5189_;
}
else
{
uint8_t v___x_5190_; 
v___x_5190_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5181_, v_binderInfo_5181_);
if (v___x_5190_ == 0)
{
lean_object* v___x_5191_; 
lean_inc(v_binderName_5178_);
lean_dec_ref_known(v_e_5175_, 3);
v___x_5191_ = l_Lean_Expr_forallE___override(v_binderName_5178_, v_newDomain_5176_, v_newBody_5177_, v_binderInfo_5181_);
return v___x_5191_;
}
else
{
lean_dec_ref(v_newBody_5177_);
lean_dec_ref(v_newDomain_5176_);
return v_e_5175_;
}
}
}
}
else
{
lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; 
lean_dec_ref(v_newBody_5177_);
lean_dec_ref(v_newDomain_5176_);
lean_dec_ref(v_e_5175_);
v___x_5192_ = l_Lean_instInhabitedExpr;
v___x_5193_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_5194_ = l_panic___redArg(v___x_5192_, v___x_5193_);
return v___x_5194_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; 
v___x_5197_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5198_ = lean_unsigned_to_nat(19u);
v___x_5199_ = lean_unsigned_to_nat(1948u);
v___x_5200_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_5201_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5202_ = l_mkPanicMessageWithDecl(v___x_5201_, v___x_5200_, v___x_5199_, v___x_5198_, v___x_5197_);
return v___x_5202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_5203_, uint8_t v_newBinfo_5204_, lean_object* v_newDomain_5205_, lean_object* v_newBody_5206_){
_start:
{
if (lean_obj_tag(v_e_5203_) == 6)
{
lean_object* v_binderName_5207_; lean_object* v_binderType_5208_; lean_object* v_body_5209_; uint8_t v_binderInfo_5210_; size_t v___x_5211_; size_t v___x_5212_; uint8_t v___x_5213_; 
v_binderName_5207_ = lean_ctor_get(v_e_5203_, 0);
v_binderType_5208_ = lean_ctor_get(v_e_5203_, 1);
v_body_5209_ = lean_ctor_get(v_e_5203_, 2);
v_binderInfo_5210_ = lean_ctor_get_uint8(v_e_5203_, sizeof(void*)*3 + 8);
v___x_5211_ = lean_ptr_addr(v_binderType_5208_);
v___x_5212_ = lean_ptr_addr(v_newDomain_5205_);
v___x_5213_ = lean_usize_dec_eq(v___x_5211_, v___x_5212_);
if (v___x_5213_ == 0)
{
lean_object* v___x_5214_; 
lean_inc(v_binderName_5207_);
lean_dec_ref_known(v_e_5203_, 3);
v___x_5214_ = l_Lean_Expr_lam___override(v_binderName_5207_, v_newDomain_5205_, v_newBody_5206_, v_newBinfo_5204_);
return v___x_5214_;
}
else
{
size_t v___x_5215_; size_t v___x_5216_; uint8_t v___x_5217_; 
v___x_5215_ = lean_ptr_addr(v_body_5209_);
v___x_5216_ = lean_ptr_addr(v_newBody_5206_);
v___x_5217_ = lean_usize_dec_eq(v___x_5215_, v___x_5216_);
if (v___x_5217_ == 0)
{
lean_object* v___x_5218_; 
lean_inc(v_binderName_5207_);
lean_dec_ref_known(v_e_5203_, 3);
v___x_5218_ = l_Lean_Expr_lam___override(v_binderName_5207_, v_newDomain_5205_, v_newBody_5206_, v_newBinfo_5204_);
return v___x_5218_;
}
else
{
uint8_t v___x_5219_; 
v___x_5219_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5210_, v_newBinfo_5204_);
if (v___x_5219_ == 0)
{
lean_object* v___x_5220_; 
lean_inc(v_binderName_5207_);
lean_dec_ref_known(v_e_5203_, 3);
v___x_5220_ = l_Lean_Expr_lam___override(v_binderName_5207_, v_newDomain_5205_, v_newBody_5206_, v_newBinfo_5204_);
return v___x_5220_;
}
else
{
lean_dec_ref(v_newBody_5206_);
lean_dec_ref(v_newDomain_5205_);
return v_e_5203_;
}
}
}
}
else
{
lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; 
lean_dec_ref(v_newBody_5206_);
lean_dec_ref(v_newDomain_5205_);
lean_dec_ref(v_e_5203_);
v___x_5221_ = l_Lean_instInhabitedExpr;
v___x_5222_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_5223_ = l_panic___redArg(v___x_5221_, v___x_5222_);
return v___x_5223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_5224_, lean_object* v_newBinfo_5225_, lean_object* v_newDomain_5226_, lean_object* v_newBody_5227_){
_start:
{
uint8_t v_newBinfo_boxed_5228_; lean_object* v_res_5229_; 
v_newBinfo_boxed_5228_ = lean_unbox(v_newBinfo_5225_);
v_res_5229_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5224_, v_newBinfo_boxed_5228_, v_newDomain_5226_, v_newBody_5227_);
return v_res_5229_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
v___x_5231_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5232_ = lean_unsigned_to_nat(20u);
v___x_5233_ = lean_unsigned_to_nat(1959u);
v___x_5234_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5235_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5236_ = l_mkPanicMessageWithDecl(v___x_5235_, v___x_5234_, v___x_5233_, v___x_5232_, v___x_5231_);
return v___x_5236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5237_, lean_object* v_newDomain_5238_, lean_object* v_newBody_5239_){
_start:
{
if (lean_obj_tag(v_e_5237_) == 6)
{
lean_object* v_binderName_5240_; lean_object* v_binderType_5241_; lean_object* v_body_5242_; uint8_t v_binderInfo_5243_; size_t v___x_5244_; size_t v___x_5245_; uint8_t v___x_5246_; 
v_binderName_5240_ = lean_ctor_get(v_e_5237_, 0);
v_binderType_5241_ = lean_ctor_get(v_e_5237_, 1);
v_body_5242_ = lean_ctor_get(v_e_5237_, 2);
v_binderInfo_5243_ = lean_ctor_get_uint8(v_e_5237_, sizeof(void*)*3 + 8);
v___x_5244_ = lean_ptr_addr(v_binderType_5241_);
v___x_5245_ = lean_ptr_addr(v_newDomain_5238_);
v___x_5246_ = lean_usize_dec_eq(v___x_5244_, v___x_5245_);
if (v___x_5246_ == 0)
{
lean_object* v___x_5247_; 
lean_inc(v_binderName_5240_);
lean_dec_ref_known(v_e_5237_, 3);
v___x_5247_ = l_Lean_Expr_lam___override(v_binderName_5240_, v_newDomain_5238_, v_newBody_5239_, v_binderInfo_5243_);
return v___x_5247_;
}
else
{
size_t v___x_5248_; size_t v___x_5249_; uint8_t v___x_5250_; 
v___x_5248_ = lean_ptr_addr(v_body_5242_);
v___x_5249_ = lean_ptr_addr(v_newBody_5239_);
v___x_5250_ = lean_usize_dec_eq(v___x_5248_, v___x_5249_);
if (v___x_5250_ == 0)
{
lean_object* v___x_5251_; 
lean_inc(v_binderName_5240_);
lean_dec_ref_known(v_e_5237_, 3);
v___x_5251_ = l_Lean_Expr_lam___override(v_binderName_5240_, v_newDomain_5238_, v_newBody_5239_, v_binderInfo_5243_);
return v___x_5251_;
}
else
{
uint8_t v___x_5252_; 
v___x_5252_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5243_, v_binderInfo_5243_);
if (v___x_5252_ == 0)
{
lean_object* v___x_5253_; 
lean_inc(v_binderName_5240_);
lean_dec_ref_known(v_e_5237_, 3);
v___x_5253_ = l_Lean_Expr_lam___override(v_binderName_5240_, v_newDomain_5238_, v_newBody_5239_, v_binderInfo_5243_);
return v___x_5253_;
}
else
{
lean_dec_ref(v_newBody_5239_);
lean_dec_ref(v_newDomain_5238_);
return v_e_5237_;
}
}
}
}
else
{
lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; 
lean_dec_ref(v_newBody_5239_);
lean_dec_ref(v_newDomain_5238_);
lean_dec_ref(v_e_5237_);
v___x_5254_ = l_Lean_instInhabitedExpr;
v___x_5255_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5256_ = l_panic___redArg(v___x_5254_, v___x_5255_);
return v___x_5256_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; 
v___x_5258_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5259_ = lean_unsigned_to_nat(22u);
v___x_5260_ = lean_unsigned_to_nat(1968u);
v___x_5261_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5262_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5263_ = l_mkPanicMessageWithDecl(v___x_5262_, v___x_5261_, v___x_5260_, v___x_5259_, v___x_5258_);
return v___x_5263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5264_, lean_object* v_newType_5265_, lean_object* v_newVal_5266_, lean_object* v_newBody_5267_, uint8_t v_newNondep_5268_){
_start:
{
if (lean_obj_tag(v_e_5264_) == 8)
{
lean_object* v_declName_5269_; lean_object* v_type_5270_; lean_object* v_value_5271_; lean_object* v_body_5272_; uint8_t v_nondep_5273_; size_t v___x_5274_; size_t v___x_5275_; uint8_t v___x_5276_; 
v_declName_5269_ = lean_ctor_get(v_e_5264_, 0);
v_type_5270_ = lean_ctor_get(v_e_5264_, 1);
v_value_5271_ = lean_ctor_get(v_e_5264_, 2);
v_body_5272_ = lean_ctor_get(v_e_5264_, 3);
v_nondep_5273_ = lean_ctor_get_uint8(v_e_5264_, sizeof(void*)*4 + 8);
v___x_5274_ = lean_ptr_addr(v_type_5270_);
v___x_5275_ = lean_ptr_addr(v_newType_5265_);
v___x_5276_ = lean_usize_dec_eq(v___x_5274_, v___x_5275_);
if (v___x_5276_ == 0)
{
lean_object* v___x_5277_; 
lean_inc(v_declName_5269_);
lean_dec_ref_known(v_e_5264_, 4);
v___x_5277_ = l_Lean_Expr_letE___override(v_declName_5269_, v_newType_5265_, v_newVal_5266_, v_newBody_5267_, v_newNondep_5268_);
return v___x_5277_;
}
else
{
size_t v___x_5278_; size_t v___x_5279_; uint8_t v___x_5280_; 
v___x_5278_ = lean_ptr_addr(v_value_5271_);
v___x_5279_ = lean_ptr_addr(v_newVal_5266_);
v___x_5280_ = lean_usize_dec_eq(v___x_5278_, v___x_5279_);
if (v___x_5280_ == 0)
{
lean_object* v___x_5281_; 
lean_inc(v_declName_5269_);
lean_dec_ref_known(v_e_5264_, 4);
v___x_5281_ = l_Lean_Expr_letE___override(v_declName_5269_, v_newType_5265_, v_newVal_5266_, v_newBody_5267_, v_newNondep_5268_);
return v___x_5281_;
}
else
{
size_t v___x_5282_; size_t v___x_5283_; uint8_t v___x_5284_; 
v___x_5282_ = lean_ptr_addr(v_body_5272_);
v___x_5283_ = lean_ptr_addr(v_newBody_5267_);
v___x_5284_ = lean_usize_dec_eq(v___x_5282_, v___x_5283_);
if (v___x_5284_ == 0)
{
lean_object* v___x_5285_; 
lean_inc(v_declName_5269_);
lean_dec_ref_known(v_e_5264_, 4);
v___x_5285_ = l_Lean_Expr_letE___override(v_declName_5269_, v_newType_5265_, v_newVal_5266_, v_newBody_5267_, v_newNondep_5268_);
return v___x_5285_;
}
else
{
if (v_newNondep_5268_ == 0)
{
if (v_nondep_5273_ == 0)
{
lean_dec_ref(v_newBody_5267_);
lean_dec_ref(v_newVal_5266_);
lean_dec_ref(v_newType_5265_);
return v_e_5264_;
}
else
{
lean_object* v___x_5286_; 
lean_inc(v_declName_5269_);
lean_dec_ref_known(v_e_5264_, 4);
v___x_5286_ = l_Lean_Expr_letE___override(v_declName_5269_, v_newType_5265_, v_newVal_5266_, v_newBody_5267_, v_newNondep_5268_);
return v___x_5286_;
}
}
else
{
if (v_nondep_5273_ == 0)
{
lean_object* v___x_5287_; 
lean_inc(v_declName_5269_);
lean_dec_ref_known(v_e_5264_, 4);
v___x_5287_ = l_Lean_Expr_letE___override(v_declName_5269_, v_newType_5265_, v_newVal_5266_, v_newBody_5267_, v_newNondep_5268_);
return v___x_5287_;
}
else
{
lean_dec_ref(v_newBody_5267_);
lean_dec_ref(v_newVal_5266_);
lean_dec_ref(v_newType_5265_);
return v_e_5264_;
}
}
}
}
}
}
else
{
lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; 
lean_dec_ref(v_newBody_5267_);
lean_dec_ref(v_newVal_5266_);
lean_dec_ref(v_newType_5265_);
lean_dec_ref(v_e_5264_);
v___x_5288_ = l_Lean_instInhabitedExpr;
v___x_5289_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5290_ = l_panic___redArg(v___x_5288_, v___x_5289_);
return v___x_5290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5291_, lean_object* v_newType_5292_, lean_object* v_newVal_5293_, lean_object* v_newBody_5294_, lean_object* v_newNondep_5295_){
_start:
{
uint8_t v_newNondep_boxed_5296_; lean_object* v_res_5297_; 
v_newNondep_boxed_5296_ = lean_unbox(v_newNondep_5295_);
v_res_5297_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5291_, v_newType_5292_, v_newVal_5293_, v_newBody_5294_, v_newNondep_boxed_5296_);
return v_res_5297_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; 
v___x_5299_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5300_ = lean_unsigned_to_nat(27u);
v___x_5301_ = lean_unsigned_to_nat(1981u);
v___x_5302_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5303_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5304_ = l_mkPanicMessageWithDecl(v___x_5303_, v___x_5302_, v___x_5301_, v___x_5300_, v___x_5299_);
return v___x_5304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5305_, lean_object* v_newType_5306_, lean_object* v_newVal_5307_, lean_object* v_newBody_5308_){
_start:
{
if (lean_obj_tag(v_e_5305_) == 8)
{
lean_object* v_declName_5309_; lean_object* v_type_5310_; lean_object* v_value_5311_; lean_object* v_body_5312_; uint8_t v_nondep_5313_; size_t v___x_5314_; size_t v___x_5315_; uint8_t v___x_5316_; 
v_declName_5309_ = lean_ctor_get(v_e_5305_, 0);
v_type_5310_ = lean_ctor_get(v_e_5305_, 1);
v_value_5311_ = lean_ctor_get(v_e_5305_, 2);
v_body_5312_ = lean_ctor_get(v_e_5305_, 3);
v_nondep_5313_ = lean_ctor_get_uint8(v_e_5305_, sizeof(void*)*4 + 8);
v___x_5314_ = lean_ptr_addr(v_type_5310_);
v___x_5315_ = lean_ptr_addr(v_newType_5306_);
v___x_5316_ = lean_usize_dec_eq(v___x_5314_, v___x_5315_);
if (v___x_5316_ == 0)
{
lean_object* v___x_5317_; 
lean_inc(v_declName_5309_);
lean_dec_ref_known(v_e_5305_, 4);
v___x_5317_ = l_Lean_Expr_letE___override(v_declName_5309_, v_newType_5306_, v_newVal_5307_, v_newBody_5308_, v_nondep_5313_);
return v___x_5317_;
}
else
{
size_t v___x_5318_; size_t v___x_5319_; uint8_t v___x_5320_; 
v___x_5318_ = lean_ptr_addr(v_value_5311_);
v___x_5319_ = lean_ptr_addr(v_newVal_5307_);
v___x_5320_ = lean_usize_dec_eq(v___x_5318_, v___x_5319_);
if (v___x_5320_ == 0)
{
lean_object* v___x_5321_; 
lean_inc(v_declName_5309_);
lean_dec_ref_known(v_e_5305_, 4);
v___x_5321_ = l_Lean_Expr_letE___override(v_declName_5309_, v_newType_5306_, v_newVal_5307_, v_newBody_5308_, v_nondep_5313_);
return v___x_5321_;
}
else
{
size_t v___x_5322_; size_t v___x_5323_; uint8_t v___x_5324_; 
v___x_5322_ = lean_ptr_addr(v_body_5312_);
v___x_5323_ = lean_ptr_addr(v_newBody_5308_);
v___x_5324_ = lean_usize_dec_eq(v___x_5322_, v___x_5323_);
if (v___x_5324_ == 0)
{
lean_object* v___x_5325_; 
lean_inc(v_declName_5309_);
lean_dec_ref_known(v_e_5305_, 4);
v___x_5325_ = l_Lean_Expr_letE___override(v_declName_5309_, v_newType_5306_, v_newVal_5307_, v_newBody_5308_, v_nondep_5313_);
return v___x_5325_;
}
else
{
lean_dec_ref(v_newBody_5308_);
lean_dec_ref(v_newVal_5307_);
lean_dec_ref(v_newType_5306_);
return v_e_5305_;
}
}
}
}
else
{
lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; 
lean_dec_ref(v_newBody_5308_);
lean_dec_ref(v_newVal_5307_);
lean_dec_ref(v_newType_5306_);
lean_dec_ref(v_e_5305_);
v___x_5326_ = l_Lean_instInhabitedExpr;
v___x_5327_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5328_ = l_panic___redArg(v___x_5326_, v___x_5327_);
return v___x_5328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5329_, lean_object* v_x_5330_){
_start:
{
if (lean_obj_tag(v_x_5329_) == 5)
{
lean_object* v_fn_5331_; lean_object* v_arg_5332_; lean_object* v___x_5333_; size_t v___x_5334_; size_t v___x_5335_; uint8_t v___x_5336_; 
v_fn_5331_ = lean_ctor_get(v_x_5329_, 0);
v_arg_5332_ = lean_ctor_get(v_x_5329_, 1);
lean_inc_ref(v_fn_5331_);
v___x_5333_ = l_Lean_Expr_updateFn(v_fn_5331_, v_x_5330_);
v___x_5334_ = lean_ptr_addr(v_fn_5331_);
v___x_5335_ = lean_ptr_addr(v___x_5333_);
v___x_5336_ = lean_usize_dec_eq(v___x_5334_, v___x_5335_);
if (v___x_5336_ == 0)
{
lean_object* v___x_5337_; 
lean_inc_ref(v_arg_5332_);
lean_dec_ref_known(v_x_5329_, 2);
v___x_5337_ = l_Lean_Expr_app___override(v___x_5333_, v_arg_5332_);
return v___x_5337_;
}
else
{
size_t v___x_5338_; uint8_t v___x_5339_; 
v___x_5338_ = lean_ptr_addr(v_arg_5332_);
v___x_5339_ = lean_usize_dec_eq(v___x_5338_, v___x_5338_);
if (v___x_5339_ == 0)
{
lean_object* v___x_5340_; 
lean_inc_ref(v_arg_5332_);
lean_dec_ref_known(v_x_5329_, 2);
v___x_5340_ = l_Lean_Expr_app___override(v___x_5333_, v_arg_5332_);
return v___x_5340_;
}
else
{
lean_dec_ref(v___x_5333_);
return v_x_5329_;
}
}
}
else
{
lean_dec_ref(v_x_5329_);
lean_inc_ref(v_x_5330_);
return v_x_5330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5341_, lean_object* v_x_5342_){
_start:
{
lean_object* v_res_5343_; 
v_res_5343_ = l_Lean_Expr_updateFn(v_x_5341_, v_x_5342_);
lean_dec_ref(v_x_5342_);
return v_res_5343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5344_){
_start:
{
if (lean_obj_tag(v_e_5344_) == 6)
{
lean_object* v_binderName_5345_; lean_object* v_binderType_5346_; lean_object* v_body_5347_; uint8_t v_binderInfo_5348_; lean_object* v_b_x27_5349_; 
v_binderName_5345_ = lean_ctor_get(v_e_5344_, 0);
v_binderType_5346_ = lean_ctor_get(v_e_5344_, 1);
v_body_5347_ = lean_ctor_get(v_e_5344_, 2);
v_binderInfo_5348_ = lean_ctor_get_uint8(v_e_5344_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5347_);
v_b_x27_5349_ = l_Lean_Expr_eta(v_body_5347_);
if (lean_obj_tag(v_b_x27_5349_) == 5)
{
lean_object* v_arg_5360_; 
v_arg_5360_ = lean_ctor_get(v_b_x27_5349_, 1);
if (lean_obj_tag(v_arg_5360_) == 0)
{
lean_object* v_fn_5361_; lean_object* v_deBruijnIndex_5362_; lean_object* v___x_5363_; uint8_t v___x_5364_; 
v_fn_5361_ = lean_ctor_get(v_b_x27_5349_, 0);
v_deBruijnIndex_5362_ = lean_ctor_get(v_arg_5360_, 0);
v___x_5363_ = lean_unsigned_to_nat(0u);
v___x_5364_ = lean_nat_dec_eq(v_deBruijnIndex_5362_, v___x_5363_);
if (v___x_5364_ == 0)
{
goto v___jp_5350_;
}
else
{
uint8_t v___x_5365_; 
v___x_5365_ = lean_expr_has_loose_bvar(v_fn_5361_, v___x_5363_);
if (v___x_5365_ == 0)
{
lean_object* v___x_5366_; lean_object* v___x_5367_; 
lean_inc_ref(v_fn_5361_);
lean_dec_ref_known(v_b_x27_5349_, 2);
lean_dec_ref_known(v_e_5344_, 3);
v___x_5366_ = lean_unsigned_to_nat(1u);
v___x_5367_ = lean_expr_lower_loose_bvars(v_fn_5361_, v___x_5366_, v___x_5366_);
lean_dec_ref(v_fn_5361_);
return v___x_5367_;
}
else
{
size_t v___x_5368_; uint8_t v___x_5369_; 
v___x_5368_ = lean_ptr_addr(v_binderType_5346_);
v___x_5369_ = lean_usize_dec_eq(v___x_5368_, v___x_5368_);
if (v___x_5369_ == 0)
{
lean_object* v___x_5370_; 
lean_inc_ref(v_binderType_5346_);
lean_inc(v_binderName_5345_);
lean_dec_ref_known(v_e_5344_, 3);
v___x_5370_ = l_Lean_Expr_lam___override(v_binderName_5345_, v_binderType_5346_, v_b_x27_5349_, v_binderInfo_5348_);
return v___x_5370_;
}
else
{
size_t v___x_5371_; size_t v___x_5372_; uint8_t v___x_5373_; 
v___x_5371_ = lean_ptr_addr(v_body_5347_);
v___x_5372_ = lean_ptr_addr(v_b_x27_5349_);
v___x_5373_ = lean_usize_dec_eq(v___x_5371_, v___x_5372_);
if (v___x_5373_ == 0)
{
lean_object* v___x_5374_; 
lean_inc_ref(v_binderType_5346_);
lean_inc(v_binderName_5345_);
lean_dec_ref_known(v_e_5344_, 3);
v___x_5374_ = l_Lean_Expr_lam___override(v_binderName_5345_, v_binderType_5346_, v_b_x27_5349_, v_binderInfo_5348_);
return v___x_5374_;
}
else
{
uint8_t v___x_5375_; 
v___x_5375_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5348_, v_binderInfo_5348_);
if (v___x_5375_ == 0)
{
lean_object* v___x_5376_; 
lean_inc_ref(v_binderType_5346_);
lean_inc(v_binderName_5345_);
lean_dec_ref_known(v_e_5344_, 3);
v___x_5376_ = l_Lean_Expr_lam___override(v_binderName_5345_, v_binderType_5346_, v_b_x27_5349_, v_binderInfo_5348_);
return v___x_5376_;
}
else
{
lean_dec_ref_known(v_b_x27_5349_, 2);
return v_e_5344_;
}
}
}
}
}
}
else
{
goto v___jp_5350_;
}
}
else
{
goto v___jp_5350_;
}
v___jp_5350_:
{
size_t v___x_5351_; uint8_t v___x_5352_; 
v___x_5351_ = lean_ptr_addr(v_binderType_5346_);
v___x_5352_ = lean_usize_dec_eq(v___x_5351_, v___x_5351_);
if (v___x_5352_ == 0)
{
lean_object* v___x_5353_; 
lean_inc_ref(v_binderType_5346_);
lean_inc(v_binderName_5345_);
lean_dec_ref_known(v_e_5344_, 3);
v___x_5353_ = l_Lean_Expr_lam___override(v_binderName_5345_, v_binderType_5346_, v_b_x27_5349_, v_binderInfo_5348_);
return v___x_5353_;
}
else
{
size_t v___x_5354_; size_t v___x_5355_; uint8_t v___x_5356_; 
v___x_5354_ = lean_ptr_addr(v_body_5347_);
v___x_5355_ = lean_ptr_addr(v_b_x27_5349_);
v___x_5356_ = lean_usize_dec_eq(v___x_5354_, v___x_5355_);
if (v___x_5356_ == 0)
{
lean_object* v___x_5357_; 
lean_inc_ref(v_binderType_5346_);
lean_inc(v_binderName_5345_);
lean_dec_ref_known(v_e_5344_, 3);
v___x_5357_ = l_Lean_Expr_lam___override(v_binderName_5345_, v_binderType_5346_, v_b_x27_5349_, v_binderInfo_5348_);
return v___x_5357_;
}
else
{
uint8_t v___x_5358_; 
v___x_5358_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5348_, v_binderInfo_5348_);
if (v___x_5358_ == 0)
{
lean_object* v___x_5359_; 
lean_inc_ref(v_binderType_5346_);
lean_inc(v_binderName_5345_);
lean_dec_ref_known(v_e_5344_, 3);
v___x_5359_ = l_Lean_Expr_lam___override(v_binderName_5345_, v_binderType_5346_, v_b_x27_5349_, v_binderInfo_5348_);
return v___x_5359_;
}
else
{
lean_dec_ref(v_b_x27_5349_);
return v_e_5344_;
}
}
}
}
}
else
{
return v_e_5344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5377_, lean_object* v_optionName_5378_, lean_object* v_inst_5379_, lean_object* v_val_5380_){
_start:
{
lean_object* v_toDataValue_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; 
v_toDataValue_5381_ = lean_ctor_get(v_inst_5379_, 0);
lean_inc_ref(v_toDataValue_5381_);
lean_dec_ref(v_inst_5379_);
v___x_5382_ = lean_box(0);
v___x_5383_ = lean_apply_1(v_toDataValue_5381_, v_val_5380_);
v___x_5384_ = l_Lean_KVMap_insert(v___x_5382_, v_optionName_5378_, v___x_5383_);
v___x_5385_ = l_Lean_Expr_mdata___override(v___x_5384_, v_e_5377_);
return v___x_5385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5386_, lean_object* v_e_5387_, lean_object* v_optionName_5388_, lean_object* v_inst_5389_, lean_object* v_val_5390_){
_start:
{
lean_object* v___x_5391_; 
v___x_5391_ = l_Lean_Expr_setOption___redArg(v_e_5387_, v_optionName_5388_, v_inst_5389_, v_val_5390_);
return v___x_5391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5392_, lean_object* v_optionName_5393_, uint8_t v_val_5394_){
_start:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; 
v___x_5395_ = lean_box(0);
v___x_5396_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5396_, 0, v_val_5394_);
v___x_5397_ = l_Lean_KVMap_insert(v___x_5395_, v_optionName_5393_, v___x_5396_);
v___x_5398_ = l_Lean_Expr_mdata___override(v___x_5397_, v_e_5392_);
return v___x_5398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5399_, lean_object* v_optionName_5400_, lean_object* v_val_5401_){
_start:
{
uint8_t v_val_boxed_5402_; lean_object* v_res_5403_; 
v_val_boxed_5402_ = lean_unbox(v_val_5401_);
v_res_5403_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5399_, v_optionName_5400_, v_val_boxed_5402_);
return v_res_5403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5409_, uint8_t v_flag_5410_){
_start:
{
lean_object* v___x_5411_; lean_object* v___x_5412_; 
v___x_5411_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5412_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5409_, v___x_5411_, v_flag_5410_);
return v___x_5412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5413_, lean_object* v_flag_5414_){
_start:
{
uint8_t v_flag_boxed_5415_; lean_object* v_res_5416_; 
v_flag_boxed_5415_ = lean_unbox(v_flag_5414_);
v_res_5416_ = l_Lean_Expr_setPPExplicit(v_e_5413_, v_flag_boxed_5415_);
return v_res_5416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5421_, uint8_t v_flag_5422_){
_start:
{
lean_object* v___x_5423_; lean_object* v___x_5424_; 
v___x_5423_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5424_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5421_, v___x_5423_, v_flag_5422_);
return v___x_5424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5425_, lean_object* v_flag_5426_){
_start:
{
uint8_t v_flag_boxed_5427_; lean_object* v_res_5428_; 
v_flag_boxed_5427_ = lean_unbox(v_flag_5426_);
v_res_5428_ = l_Lean_Expr_setPPUniverses(v_e_5425_, v_flag_boxed_5427_);
return v_res_5428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5433_, uint8_t v_flag_5434_){
_start:
{
lean_object* v___x_5435_; lean_object* v___x_5436_; 
v___x_5435_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5436_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5433_, v___x_5435_, v_flag_5434_);
return v___x_5436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5437_, lean_object* v_flag_5438_){
_start:
{
uint8_t v_flag_boxed_5439_; lean_object* v_res_5440_; 
v_flag_boxed_5439_ = lean_unbox(v_flag_5438_);
v_res_5440_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5437_, v_flag_boxed_5439_);
return v_res_5440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5445_, uint8_t v_flag_5446_){
_start:
{
lean_object* v___x_5447_; lean_object* v___x_5448_; 
v___x_5447_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5448_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5445_, v___x_5447_, v_flag_5446_);
return v___x_5448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5449_, lean_object* v_flag_5450_){
_start:
{
uint8_t v_flag_boxed_5451_; lean_object* v_res_5452_; 
v_flag_boxed_5451_ = lean_unbox(v_flag_5450_);
v_res_5452_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5449_, v_flag_boxed_5451_);
return v_res_5452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5457_, uint8_t v_flag_5458_){
_start:
{
lean_object* v___x_5459_; lean_object* v___x_5460_; 
v___x_5459_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5460_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5457_, v___x_5459_, v_flag_5458_);
return v___x_5460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5461_, lean_object* v_flag_5462_){
_start:
{
uint8_t v_flag_boxed_5463_; lean_object* v_res_5464_; 
v_flag_boxed_5463_ = lean_unbox(v_flag_5462_);
v_res_5464_ = l_Lean_Expr_setPPNumericTypes(v_e_5461_, v_flag_boxed_5463_);
return v_res_5464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5465_, size_t v_i_5466_, lean_object* v_bs_5467_){
_start:
{
uint8_t v___x_5468_; 
v___x_5468_ = lean_usize_dec_lt(v_i_5466_, v_sz_5465_);
if (v___x_5468_ == 0)
{
return v_bs_5467_;
}
else
{
uint8_t v___x_5469_; lean_object* v_v_5470_; lean_object* v___x_5471_; lean_object* v_bs_x27_5472_; lean_object* v___x_5473_; size_t v___x_5474_; size_t v___x_5475_; lean_object* v___x_5476_; 
v___x_5469_ = 0;
v_v_5470_ = lean_array_uget(v_bs_5467_, v_i_5466_);
v___x_5471_ = lean_unsigned_to_nat(0u);
v_bs_x27_5472_ = lean_array_uset(v_bs_5467_, v_i_5466_, v___x_5471_);
v___x_5473_ = l_Lean_Expr_setPPExplicit(v_v_5470_, v___x_5469_);
v___x_5474_ = ((size_t)1ULL);
v___x_5475_ = lean_usize_add(v_i_5466_, v___x_5474_);
v___x_5476_ = lean_array_uset(v_bs_x27_5472_, v_i_5466_, v___x_5473_);
v_i_5466_ = v___x_5475_;
v_bs_5467_ = v___x_5476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5478_, lean_object* v_i_5479_, lean_object* v_bs_5480_){
_start:
{
size_t v_sz_boxed_5481_; size_t v_i_boxed_5482_; lean_object* v_res_5483_; 
v_sz_boxed_5481_ = lean_unbox_usize(v_sz_5478_);
lean_dec(v_sz_5478_);
v_i_boxed_5482_ = lean_unbox_usize(v_i_5479_);
lean_dec(v_i_5479_);
v_res_5483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5481_, v_i_boxed_5482_, v_bs_5480_);
return v_res_5483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5484_){
_start:
{
if (lean_obj_tag(v_e_5484_) == 5)
{
lean_object* v___x_5485_; uint8_t v___x_5486_; lean_object* v_f_5487_; lean_object* v_dummy_5488_; lean_object* v_nargs_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; size_t v_sz_5494_; size_t v___x_5495_; lean_object* v_args_5496_; lean_object* v___x_5497_; uint8_t v___x_5498_; lean_object* v___x_5499_; 
v___x_5485_ = l_Lean_Expr_getAppFn(v_e_5484_);
v___x_5486_ = 0;
v_f_5487_ = l_Lean_Expr_setPPExplicit(v___x_5485_, v___x_5486_);
v_dummy_5488_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5489_ = l_Lean_Expr_getAppNumArgs(v_e_5484_);
lean_inc(v_nargs_5489_);
v___x_5490_ = lean_mk_array(v_nargs_5489_, v_dummy_5488_);
v___x_5491_ = lean_unsigned_to_nat(1u);
v___x_5492_ = lean_nat_sub(v_nargs_5489_, v___x_5491_);
lean_dec(v_nargs_5489_);
v___x_5493_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5484_, v___x_5490_, v___x_5492_);
v_sz_5494_ = lean_array_size(v___x_5493_);
v___x_5495_ = ((size_t)0ULL);
v_args_5496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5494_, v___x_5495_, v___x_5493_);
v___x_5497_ = l_Lean_mkAppN(v_f_5487_, v_args_5496_);
lean_dec_ref(v_args_5496_);
v___x_5498_ = 1;
v___x_5499_ = l_Lean_Expr_setPPExplicit(v___x_5497_, v___x_5498_);
return v___x_5499_;
}
else
{
return v_e_5484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5500_, size_t v_i_5501_, lean_object* v_bs_5502_){
_start:
{
uint8_t v___x_5503_; 
v___x_5503_ = lean_usize_dec_lt(v_i_5501_, v_sz_5500_);
if (v___x_5503_ == 0)
{
return v_bs_5502_;
}
else
{
lean_object* v_v_5504_; lean_object* v___x_5505_; lean_object* v_bs_x27_5506_; lean_object* v___y_5508_; uint8_t v___x_5513_; 
v_v_5504_ = lean_array_uget(v_bs_5502_, v_i_5501_);
v___x_5505_ = lean_unsigned_to_nat(0u);
v_bs_x27_5506_ = lean_array_uset(v_bs_5502_, v_i_5501_, v___x_5505_);
v___x_5513_ = l_Lean_Expr_hasMVar(v_v_5504_);
if (v___x_5513_ == 0)
{
lean_object* v___x_5514_; 
v___x_5514_ = l_Lean_Expr_setPPExplicit(v_v_5504_, v___x_5513_);
v___y_5508_ = v___x_5514_;
goto v___jp_5507_;
}
else
{
v___y_5508_ = v_v_5504_;
goto v___jp_5507_;
}
v___jp_5507_:
{
size_t v___x_5509_; size_t v___x_5510_; lean_object* v___x_5511_; 
v___x_5509_ = ((size_t)1ULL);
v___x_5510_ = lean_usize_add(v_i_5501_, v___x_5509_);
v___x_5511_ = lean_array_uset(v_bs_x27_5506_, v_i_5501_, v___y_5508_);
v_i_5501_ = v___x_5510_;
v_bs_5502_ = v___x_5511_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5515_, lean_object* v_i_5516_, lean_object* v_bs_5517_){
_start:
{
size_t v_sz_boxed_5518_; size_t v_i_boxed_5519_; lean_object* v_res_5520_; 
v_sz_boxed_5518_ = lean_unbox_usize(v_sz_5515_);
lean_dec(v_sz_5515_);
v_i_boxed_5519_ = lean_unbox_usize(v_i_5516_);
lean_dec(v_i_5516_);
v_res_5520_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5518_, v_i_boxed_5519_, v_bs_5517_);
return v_res_5520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5521_){
_start:
{
if (lean_obj_tag(v_e_5521_) == 5)
{
lean_object* v___x_5522_; uint8_t v___x_5523_; lean_object* v_f_5524_; lean_object* v_dummy_5525_; lean_object* v_nargs_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; size_t v_sz_5531_; size_t v___x_5532_; lean_object* v_args_5533_; lean_object* v___x_5534_; uint8_t v___x_5535_; lean_object* v___x_5536_; 
v___x_5522_ = l_Lean_Expr_getAppFn(v_e_5521_);
v___x_5523_ = 0;
v_f_5524_ = l_Lean_Expr_setPPExplicit(v___x_5522_, v___x_5523_);
v_dummy_5525_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5526_ = l_Lean_Expr_getAppNumArgs(v_e_5521_);
lean_inc(v_nargs_5526_);
v___x_5527_ = lean_mk_array(v_nargs_5526_, v_dummy_5525_);
v___x_5528_ = lean_unsigned_to_nat(1u);
v___x_5529_ = lean_nat_sub(v_nargs_5526_, v___x_5528_);
lean_dec(v_nargs_5526_);
v___x_5530_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5521_, v___x_5527_, v___x_5529_);
v_sz_5531_ = lean_array_size(v___x_5530_);
v___x_5532_ = ((size_t)0ULL);
v_args_5533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5531_, v___x_5532_, v___x_5530_);
v___x_5534_ = l_Lean_mkAppN(v_f_5524_, v_args_5533_);
lean_dec_ref(v_args_5533_);
v___x_5535_ = 1;
v___x_5536_ = l_Lean_Expr_setPPExplicit(v___x_5534_, v___x_5535_);
return v___x_5536_;
}
else
{
return v_e_5521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5537_, lean_object* v_body_5538_, lean_object* v_x_5539_){
_start:
{
lean_object* v___x_5540_; 
v___x_5540_ = lean_apply_1(v_f_5537_, v_body_5538_);
return v___x_5540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5541_, lean_object* v_binderType_5542_, lean_object* v_x_5543_){
_start:
{
lean_object* v___x_5544_; 
v___x_5544_ = lean_apply_1(v_f_5541_, v_binderType_5542_);
return v___x_5544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5545_, lean_object* v_value_5546_, lean_object* v_x_5547_){
_start:
{
lean_object* v___x_5548_; 
v___x_5548_ = lean_apply_1(v_f_5545_, v_value_5546_);
return v___x_5548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5549_, lean_object* v_type_5550_, lean_object* v_x_5551_){
_start:
{
lean_object* v___x_5552_; 
v___x_5552_ = lean_apply_1(v_f_5549_, v_type_5550_);
return v___x_5552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5553_, lean_object* v_arg_5554_, lean_object* v_x_5555_){
_start:
{
lean_object* v___x_5556_; 
v___x_5556_ = lean_apply_1(v_f_5553_, v_arg_5554_);
return v___x_5556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5557_, lean_object* v_fn_5558_, lean_object* v_x_5559_){
_start:
{
lean_object* v___x_5560_; 
v___x_5560_ = lean_apply_1(v_f_5557_, v_fn_5558_);
return v___x_5560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5561_, lean_object* v_f_5562_, lean_object* v_x_5563_){
_start:
{
switch(lean_obj_tag(v_x_5563_))
{
case 7:
{
lean_object* v_toPure_5564_; lean_object* v_toSeq_5565_; lean_object* v_binderType_5566_; lean_object* v_body_5567_; lean_object* v___f_5568_; lean_object* v___f_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; 
v_toPure_5564_ = lean_ctor_get(v_inst_5561_, 1);
lean_inc(v_toPure_5564_);
v_toSeq_5565_ = lean_ctor_get(v_inst_5561_, 2);
lean_inc_n(v_toSeq_5565_, 2);
lean_dec_ref(v_inst_5561_);
v_binderType_5566_ = lean_ctor_get(v_x_5563_, 1);
v_body_5567_ = lean_ctor_get(v_x_5563_, 2);
lean_inc_ref(v_body_5567_);
lean_inc(v_f_5562_);
v___f_5568_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5568_, 0, v_f_5562_);
lean_closure_set(v___f_5568_, 1, v_body_5567_);
lean_inc_ref(v_binderType_5566_);
v___f_5569_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5569_, 0, v_f_5562_);
lean_closure_set(v___f_5569_, 1, v_binderType_5566_);
v___x_5570_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5570_, 0, v_x_5563_);
v___x_5571_ = lean_apply_2(v_toPure_5564_, lean_box(0), v___x_5570_);
v___x_5572_ = lean_apply_4(v_toSeq_5565_, lean_box(0), lean_box(0), v___x_5571_, v___f_5569_);
v___x_5573_ = lean_apply_4(v_toSeq_5565_, lean_box(0), lean_box(0), v___x_5572_, v___f_5568_);
return v___x_5573_;
}
case 6:
{
lean_object* v_toPure_5574_; lean_object* v_toSeq_5575_; lean_object* v_binderType_5576_; lean_object* v_body_5577_; lean_object* v___f_5578_; lean_object* v___f_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; 
v_toPure_5574_ = lean_ctor_get(v_inst_5561_, 1);
lean_inc(v_toPure_5574_);
v_toSeq_5575_ = lean_ctor_get(v_inst_5561_, 2);
lean_inc_n(v_toSeq_5575_, 2);
lean_dec_ref(v_inst_5561_);
v_binderType_5576_ = lean_ctor_get(v_x_5563_, 1);
v_body_5577_ = lean_ctor_get(v_x_5563_, 2);
lean_inc_ref(v_body_5577_);
lean_inc(v_f_5562_);
v___f_5578_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5578_, 0, v_f_5562_);
lean_closure_set(v___f_5578_, 1, v_body_5577_);
lean_inc_ref(v_binderType_5576_);
v___f_5579_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5579_, 0, v_f_5562_);
lean_closure_set(v___f_5579_, 1, v_binderType_5576_);
v___x_5580_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5580_, 0, v_x_5563_);
v___x_5581_ = lean_apply_2(v_toPure_5574_, lean_box(0), v___x_5580_);
v___x_5582_ = lean_apply_4(v_toSeq_5575_, lean_box(0), lean_box(0), v___x_5581_, v___f_5579_);
v___x_5583_ = lean_apply_4(v_toSeq_5575_, lean_box(0), lean_box(0), v___x_5582_, v___f_5578_);
return v___x_5583_;
}
case 10:
{
lean_object* v_toFunctor_5584_; lean_object* v_expr_5585_; lean_object* v_map_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; 
v_toFunctor_5584_ = lean_ctor_get(v_inst_5561_, 0);
lean_inc_ref(v_toFunctor_5584_);
lean_dec_ref(v_inst_5561_);
v_expr_5585_ = lean_ctor_get(v_x_5563_, 1);
lean_inc_ref(v_expr_5585_);
v_map_5586_ = lean_ctor_get(v_toFunctor_5584_, 0);
lean_inc(v_map_5586_);
lean_dec_ref(v_toFunctor_5584_);
v___x_5587_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5587_, 0, v_x_5563_);
v___x_5588_ = lean_apply_1(v_f_5562_, v_expr_5585_);
v___x_5589_ = lean_apply_4(v_map_5586_, lean_box(0), lean_box(0), v___x_5587_, v___x_5588_);
return v___x_5589_;
}
case 8:
{
lean_object* v_toPure_5590_; lean_object* v_toSeq_5591_; lean_object* v_type_5592_; lean_object* v_value_5593_; lean_object* v_body_5594_; lean_object* v___f_5595_; lean_object* v___f_5596_; lean_object* v___f_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; 
v_toPure_5590_ = lean_ctor_get(v_inst_5561_, 1);
lean_inc(v_toPure_5590_);
v_toSeq_5591_ = lean_ctor_get(v_inst_5561_, 2);
lean_inc_n(v_toSeq_5591_, 3);
lean_dec_ref(v_inst_5561_);
v_type_5592_ = lean_ctor_get(v_x_5563_, 1);
v_value_5593_ = lean_ctor_get(v_x_5563_, 2);
v_body_5594_ = lean_ctor_get(v_x_5563_, 3);
lean_inc_ref(v_body_5594_);
lean_inc_n(v_f_5562_, 2);
v___f_5595_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5595_, 0, v_f_5562_);
lean_closure_set(v___f_5595_, 1, v_body_5594_);
lean_inc_ref(v_value_5593_);
v___f_5596_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5596_, 0, v_f_5562_);
lean_closure_set(v___f_5596_, 1, v_value_5593_);
lean_inc_ref(v_type_5592_);
v___f_5597_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5597_, 0, v_f_5562_);
lean_closure_set(v___f_5597_, 1, v_type_5592_);
v___x_5598_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5598_, 0, v_x_5563_);
v___x_5599_ = lean_apply_2(v_toPure_5590_, lean_box(0), v___x_5598_);
v___x_5600_ = lean_apply_4(v_toSeq_5591_, lean_box(0), lean_box(0), v___x_5599_, v___f_5597_);
v___x_5601_ = lean_apply_4(v_toSeq_5591_, lean_box(0), lean_box(0), v___x_5600_, v___f_5596_);
v___x_5602_ = lean_apply_4(v_toSeq_5591_, lean_box(0), lean_box(0), v___x_5601_, v___f_5595_);
return v___x_5602_;
}
case 5:
{
lean_object* v_toPure_5603_; lean_object* v_toSeq_5604_; lean_object* v_fn_5605_; lean_object* v_arg_5606_; lean_object* v___f_5607_; lean_object* v___f_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; 
v_toPure_5603_ = lean_ctor_get(v_inst_5561_, 1);
lean_inc(v_toPure_5603_);
v_toSeq_5604_ = lean_ctor_get(v_inst_5561_, 2);
lean_inc_n(v_toSeq_5604_, 2);
lean_dec_ref(v_inst_5561_);
v_fn_5605_ = lean_ctor_get(v_x_5563_, 0);
v_arg_5606_ = lean_ctor_get(v_x_5563_, 1);
lean_inc_ref(v_arg_5606_);
lean_inc(v_f_5562_);
v___f_5607_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5607_, 0, v_f_5562_);
lean_closure_set(v___f_5607_, 1, v_arg_5606_);
lean_inc_ref(v_fn_5605_);
v___f_5608_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5608_, 0, v_f_5562_);
lean_closure_set(v___f_5608_, 1, v_fn_5605_);
v___x_5609_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5609_, 0, v_x_5563_);
v___x_5610_ = lean_apply_2(v_toPure_5603_, lean_box(0), v___x_5609_);
v___x_5611_ = lean_apply_4(v_toSeq_5604_, lean_box(0), lean_box(0), v___x_5610_, v___f_5608_);
v___x_5612_ = lean_apply_4(v_toSeq_5604_, lean_box(0), lean_box(0), v___x_5611_, v___f_5607_);
return v___x_5612_;
}
case 11:
{
lean_object* v_toFunctor_5613_; lean_object* v_struct_5614_; lean_object* v_map_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; 
v_toFunctor_5613_ = lean_ctor_get(v_inst_5561_, 0);
lean_inc_ref(v_toFunctor_5613_);
lean_dec_ref(v_inst_5561_);
v_struct_5614_ = lean_ctor_get(v_x_5563_, 2);
lean_inc_ref(v_struct_5614_);
v_map_5615_ = lean_ctor_get(v_toFunctor_5613_, 0);
lean_inc(v_map_5615_);
lean_dec_ref(v_toFunctor_5613_);
v___x_5616_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5616_, 0, v_x_5563_);
v___x_5617_ = lean_apply_1(v_f_5562_, v_struct_5614_);
v___x_5618_ = lean_apply_4(v_map_5615_, lean_box(0), lean_box(0), v___x_5616_, v___x_5617_);
return v___x_5618_;
}
default: 
{
lean_object* v_toPure_5619_; lean_object* v___x_5620_; 
lean_dec(v_f_5562_);
v_toPure_5619_ = lean_ctor_get(v_inst_5561_, 1);
lean_inc(v_toPure_5619_);
lean_dec_ref(v_inst_5561_);
v___x_5620_ = lean_apply_2(v_toPure_5619_, lean_box(0), v_x_5563_);
return v___x_5620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5621_, lean_object* v_inst_5622_, lean_object* v_f_5623_, lean_object* v_x_5624_){
_start:
{
lean_object* v___x_5625_; 
v___x_5625_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5622_, v_f_5623_, v_x_5624_);
return v___x_5625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5626_){
_start:
{
lean_object* v_snd_5627_; 
v_snd_5627_ = lean_ctor_get(v_self_5626_, 1);
lean_inc(v_snd_5627_);
return v_snd_5627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5628_){
_start:
{
lean_object* v_res_5629_; 
v_res_5629_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5628_);
lean_dec_ref(v_self_5628_);
return v_res_5629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5630_, lean_object* v_snd_5631_){
_start:
{
lean_object* v___x_5632_; 
v___x_5632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5632_, 0, v_e_x27_5630_);
lean_ctor_set(v___x_5632_, 1, v_snd_5631_);
return v___x_5632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5633_, lean_object* v_map_5634_, lean_object* v_e_x27_5635_, lean_object* v_a_5636_){
_start:
{
lean_object* v___f_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; 
lean_inc_ref(v_e_x27_5635_);
v___f_5637_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5637_, 0, v_e_x27_5635_);
v___x_5638_ = lean_apply_2(v_f_5633_, v_a_5636_, v_e_x27_5635_);
v___x_5639_ = lean_apply_4(v_map_5634_, lean_box(0), lean_box(0), v___f_5637_, v___x_5638_);
return v___x_5639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5641_, lean_object* v_f_5642_, lean_object* v_init_5643_, lean_object* v_e_5644_){
_start:
{
lean_object* v_toApplicative_5645_; lean_object* v_toFunctor_5646_; lean_object* v___x_5648_; uint8_t v_isShared_5649_; uint8_t v_isSharedCheck_5673_; 
v_toApplicative_5645_ = lean_ctor_get(v_inst_5641_, 0);
lean_inc_ref(v_toApplicative_5645_);
v_toFunctor_5646_ = lean_ctor_get(v_toApplicative_5645_, 0);
v_isSharedCheck_5673_ = !lean_is_exclusive(v_toApplicative_5645_);
if (v_isSharedCheck_5673_ == 0)
{
lean_object* v_unused_5674_; lean_object* v_unused_5675_; lean_object* v_unused_5676_; lean_object* v_unused_5677_; 
v_unused_5674_ = lean_ctor_get(v_toApplicative_5645_, 4);
lean_dec(v_unused_5674_);
v_unused_5675_ = lean_ctor_get(v_toApplicative_5645_, 3);
lean_dec(v_unused_5675_);
v_unused_5676_ = lean_ctor_get(v_toApplicative_5645_, 2);
lean_dec(v_unused_5676_);
v_unused_5677_ = lean_ctor_get(v_toApplicative_5645_, 1);
lean_dec(v_unused_5677_);
v___x_5648_ = v_toApplicative_5645_;
v_isShared_5649_ = v_isSharedCheck_5673_;
goto v_resetjp_5647_;
}
else
{
lean_inc(v_toFunctor_5646_);
lean_dec(v_toApplicative_5645_);
v___x_5648_ = lean_box(0);
v_isShared_5649_ = v_isSharedCheck_5673_;
goto v_resetjp_5647_;
}
v_resetjp_5647_:
{
lean_object* v_map_5650_; lean_object* v___x_5652_; uint8_t v_isShared_5653_; uint8_t v_isSharedCheck_5671_; 
v_map_5650_ = lean_ctor_get(v_toFunctor_5646_, 0);
v_isSharedCheck_5671_ = !lean_is_exclusive(v_toFunctor_5646_);
if (v_isSharedCheck_5671_ == 0)
{
lean_object* v_unused_5672_; 
v_unused_5672_ = lean_ctor_get(v_toFunctor_5646_, 1);
lean_dec(v_unused_5672_);
v___x_5652_ = v_toFunctor_5646_;
v_isShared_5653_ = v_isSharedCheck_5671_;
goto v_resetjp_5651_;
}
else
{
lean_inc(v_map_5650_);
lean_dec(v_toFunctor_5646_);
v___x_5652_ = lean_box(0);
v_isShared_5653_ = v_isSharedCheck_5671_;
goto v_resetjp_5651_;
}
v_resetjp_5651_:
{
lean_object* v___f_5654_; lean_object* v___f_5655_; lean_object* v___f_5656_; lean_object* v___f_5657_; lean_object* v___f_5658_; lean_object* v___f_5659_; lean_object* v___x_5660_; lean_object* v___x_5662_; 
v___f_5654_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5650_);
v___f_5655_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5655_, 0, v_f_5642_);
lean_closure_set(v___f_5655_, 1, v_map_5650_);
lean_inc_ref_n(v_inst_5641_, 5);
v___f_5656_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5656_, 0, v_inst_5641_);
v___f_5657_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5657_, 0, v_inst_5641_);
v___f_5658_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5658_, 0, v_inst_5641_);
v___f_5659_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5659_, 0, v_inst_5641_);
v___x_5660_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5660_, 0, lean_box(0));
lean_closure_set(v___x_5660_, 1, lean_box(0));
lean_closure_set(v___x_5660_, 2, v_inst_5641_);
if (v_isShared_5653_ == 0)
{
lean_ctor_set(v___x_5652_, 1, v___f_5656_);
lean_ctor_set(v___x_5652_, 0, v___x_5660_);
v___x_5662_ = v___x_5652_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v___x_5660_);
lean_ctor_set(v_reuseFailAlloc_5670_, 1, v___f_5656_);
v___x_5662_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
lean_object* v___x_5663_; lean_object* v___x_5665_; 
v___x_5663_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5663_, 0, lean_box(0));
lean_closure_set(v___x_5663_, 1, lean_box(0));
lean_closure_set(v___x_5663_, 2, v_inst_5641_);
if (v_isShared_5649_ == 0)
{
lean_ctor_set(v___x_5648_, 4, v___f_5659_);
lean_ctor_set(v___x_5648_, 3, v___f_5658_);
lean_ctor_set(v___x_5648_, 2, v___f_5657_);
lean_ctor_set(v___x_5648_, 1, v___x_5663_);
lean_ctor_set(v___x_5648_, 0, v___x_5662_);
v___x_5665_ = v___x_5648_;
goto v_reusejp_5664_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v___x_5662_);
lean_ctor_set(v_reuseFailAlloc_5669_, 1, v___x_5663_);
lean_ctor_set(v_reuseFailAlloc_5669_, 2, v___f_5657_);
lean_ctor_set(v_reuseFailAlloc_5669_, 3, v___f_5658_);
lean_ctor_set(v_reuseFailAlloc_5669_, 4, v___f_5659_);
v___x_5665_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5664_;
}
v_reusejp_5664_:
{
lean_object* v___x_30__overap_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; 
v___x_30__overap_5666_ = l_Lean_Expr_traverseChildren___redArg(v___x_5665_, v___f_5655_, v_e_5644_);
v___x_5667_ = lean_apply_1(v___x_30__overap_5666_, v_init_5643_);
v___x_5668_ = lean_apply_4(v_map_5650_, lean_box(0), lean_box(0), v___f_5654_, v___x_5667_);
return v___x_5668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5678_, lean_object* v_m_5679_, lean_object* v_inst_5680_, lean_object* v_f_5681_, lean_object* v_init_5682_, lean_object* v_e_5683_){
_start:
{
lean_object* v___x_5684_; 
v___x_5684_ = l_Lean_Expr_foldlM___redArg(v_inst_5680_, v_f_5681_, v_init_5682_, v_e_5683_);
return v___x_5684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5685_){
_start:
{
lean_object* v_d_5687_; lean_object* v_b_5688_; 
switch(lean_obj_tag(v_x_5685_))
{
case 5:
{
lean_object* v_fn_5694_; lean_object* v_arg_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; 
v_fn_5694_ = lean_ctor_get(v_x_5685_, 0);
v_arg_5695_ = lean_ctor_get(v_x_5685_, 1);
v___x_5696_ = lean_unsigned_to_nat(1u);
v___x_5697_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5694_);
v___x_5698_ = lean_nat_add(v___x_5696_, v___x_5697_);
lean_dec(v___x_5697_);
v___x_5699_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5695_);
v___x_5700_ = lean_nat_add(v___x_5698_, v___x_5699_);
lean_dec(v___x_5699_);
lean_dec(v___x_5698_);
return v___x_5700_;
}
case 6:
{
lean_object* v_binderType_5701_; lean_object* v_body_5702_; 
v_binderType_5701_ = lean_ctor_get(v_x_5685_, 1);
v_body_5702_ = lean_ctor_get(v_x_5685_, 2);
v_d_5687_ = v_binderType_5701_;
v_b_5688_ = v_body_5702_;
goto v___jp_5686_;
}
case 7:
{
lean_object* v_binderType_5703_; lean_object* v_body_5704_; 
v_binderType_5703_ = lean_ctor_get(v_x_5685_, 1);
v_body_5704_ = lean_ctor_get(v_x_5685_, 2);
v_d_5687_ = v_binderType_5703_;
v_b_5688_ = v_body_5704_;
goto v___jp_5686_;
}
case 8:
{
lean_object* v_type_5705_; lean_object* v_value_5706_; lean_object* v_body_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; 
v_type_5705_ = lean_ctor_get(v_x_5685_, 1);
v_value_5706_ = lean_ctor_get(v_x_5685_, 2);
v_body_5707_ = lean_ctor_get(v_x_5685_, 3);
v___x_5708_ = lean_unsigned_to_nat(1u);
v___x_5709_ = l_Lean_Expr_sizeWithoutSharing(v_type_5705_);
v___x_5710_ = lean_nat_add(v___x_5708_, v___x_5709_);
lean_dec(v___x_5709_);
v___x_5711_ = l_Lean_Expr_sizeWithoutSharing(v_value_5706_);
v___x_5712_ = lean_nat_add(v___x_5710_, v___x_5711_);
lean_dec(v___x_5711_);
lean_dec(v___x_5710_);
v___x_5713_ = l_Lean_Expr_sizeWithoutSharing(v_body_5707_);
v___x_5714_ = lean_nat_add(v___x_5712_, v___x_5713_);
lean_dec(v___x_5713_);
lean_dec(v___x_5712_);
return v___x_5714_;
}
case 10:
{
lean_object* v_expr_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; 
v_expr_5715_ = lean_ctor_get(v_x_5685_, 1);
v___x_5716_ = lean_unsigned_to_nat(1u);
v___x_5717_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5715_);
v___x_5718_ = lean_nat_add(v___x_5716_, v___x_5717_);
lean_dec(v___x_5717_);
return v___x_5718_;
}
case 11:
{
lean_object* v_struct_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; 
v_struct_5719_ = lean_ctor_get(v_x_5685_, 2);
v___x_5720_ = lean_unsigned_to_nat(1u);
v___x_5721_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5719_);
v___x_5722_ = lean_nat_add(v___x_5720_, v___x_5721_);
lean_dec(v___x_5721_);
return v___x_5722_;
}
default: 
{
lean_object* v___x_5723_; 
v___x_5723_ = lean_unsigned_to_nat(1u);
return v___x_5723_;
}
}
v___jp_5686_:
{
lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; 
v___x_5689_ = lean_unsigned_to_nat(1u);
v___x_5690_ = l_Lean_Expr_sizeWithoutSharing(v_d_5687_);
v___x_5691_ = lean_nat_add(v___x_5689_, v___x_5690_);
lean_dec(v___x_5690_);
v___x_5692_ = l_Lean_Expr_sizeWithoutSharing(v_b_5688_);
v___x_5693_ = lean_nat_add(v___x_5691_, v___x_5692_);
lean_dec(v___x_5692_);
lean_dec(v___x_5691_);
return v___x_5693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5724_){
_start:
{
lean_object* v_res_5725_; 
v_res_5725_ = l_Lean_Expr_sizeWithoutSharing(v_x_5724_);
lean_dec_ref(v_x_5724_);
return v_res_5725_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5728_, lean_object* v_e_5729_){
_start:
{
lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; 
v___x_5730_ = l_Lean_KVMap_empty;
v___x_5731_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5732_ = l_Lean_KVMap_insert(v___x_5730_, v_kind_5728_, v___x_5731_);
v___x_5733_ = l_Lean_Expr_mdata___override(v___x_5732_, v_e_5729_);
return v___x_5733_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5734_, lean_object* v_e_5735_){
_start:
{
if (lean_obj_tag(v_e_5735_) == 10)
{
lean_object* v_data_5736_; lean_object* v_expr_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; uint8_t v___x_5740_; 
v_data_5736_ = lean_ctor_get(v_e_5735_, 0);
v_expr_5737_ = lean_ctor_get(v_e_5735_, 1);
v___x_5738_ = l_Lean_KVMap_size(v_data_5736_);
v___x_5739_ = lean_unsigned_to_nat(1u);
v___x_5740_ = lean_nat_dec_eq(v___x_5738_, v___x_5739_);
lean_dec(v___x_5738_);
if (v___x_5740_ == 0)
{
lean_object* v___x_5741_; 
v___x_5741_ = lean_box(0);
return v___x_5741_;
}
else
{
uint8_t v___x_5742_; uint8_t v___x_5743_; 
v___x_5742_ = 0;
v___x_5743_ = l_Lean_KVMap_getBool(v_data_5736_, v_kind_5734_, v___x_5742_);
if (v___x_5743_ == 0)
{
lean_object* v___x_5744_; 
v___x_5744_ = lean_box(0);
return v___x_5744_;
}
else
{
lean_object* v___x_5745_; 
lean_inc_ref(v_expr_5737_);
v___x_5745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5745_, 0, v_expr_5737_);
return v___x_5745_;
}
}
}
else
{
lean_object* v___x_5746_; 
v___x_5746_ = lean_box(0);
return v___x_5746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* v_kind_5747_, lean_object* v_e_5748_){
_start:
{
lean_object* v_res_5749_; 
v_res_5749_ = l_Lean_annotation_x3f(v_kind_5747_, v_e_5748_);
lean_dec_ref(v_e_5748_);
lean_dec(v_kind_5747_);
return v_res_5749_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* v_e_5753_){
_start:
{
lean_object* v___x_5754_; lean_object* v___x_5755_; 
v___x_5754_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5755_ = l_Lean_mkAnnotation(v___x_5754_, v_e_5753_);
return v___x_5755_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* v_e_5756_){
_start:
{
lean_object* v___x_5757_; lean_object* v___x_5758_; 
v___x_5757_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5758_ = l_Lean_annotation_x3f(v___x_5757_, v_e_5756_);
return v___x_5758_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* v_e_5759_){
_start:
{
lean_object* v_res_5760_; 
v_res_5760_ = l_Lean_inaccessible_x3f(v_e_5759_);
lean_dec_ref(v_e_5759_);
return v_res_5760_;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* v_p_5765_){
_start:
{
if (lean_obj_tag(v_p_5765_) == 10)
{
lean_object* v_data_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; 
v_data_5766_ = lean_ctor_get(v_p_5765_, 0);
v___x_5767_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5768_ = l_Lean_KVMap_find(v_data_5766_, v___x_5767_);
if (lean_obj_tag(v___x_5768_) == 1)
{
lean_object* v_val_5769_; lean_object* v___x_5771_; uint8_t v_isShared_5772_; uint8_t v_isSharedCheck_5780_; 
v_val_5769_ = lean_ctor_get(v___x_5768_, 0);
v_isSharedCheck_5780_ = !lean_is_exclusive(v___x_5768_);
if (v_isSharedCheck_5780_ == 0)
{
v___x_5771_ = v___x_5768_;
v_isShared_5772_ = v_isSharedCheck_5780_;
goto v_resetjp_5770_;
}
else
{
lean_inc(v_val_5769_);
lean_dec(v___x_5768_);
v___x_5771_ = lean_box(0);
v_isShared_5772_ = v_isSharedCheck_5780_;
goto v_resetjp_5770_;
}
v_resetjp_5770_:
{
if (lean_obj_tag(v_val_5769_) == 5)
{
lean_object* v_v_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5777_; 
v_v_5773_ = lean_ctor_get(v_val_5769_, 0);
lean_inc(v_v_5773_);
lean_dec_ref_known(v_val_5769_, 1);
v___x_5774_ = l_Lean_Expr_mdataExpr_x21(v_p_5765_);
v___x_5775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5775_, 0, v_v_5773_);
lean_ctor_set(v___x_5775_, 1, v___x_5774_);
if (v_isShared_5772_ == 0)
{
lean_ctor_set(v___x_5771_, 0, v___x_5775_);
v___x_5777_ = v___x_5771_;
goto v_reusejp_5776_;
}
else
{
lean_object* v_reuseFailAlloc_5778_; 
v_reuseFailAlloc_5778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5778_, 0, v___x_5775_);
v___x_5777_ = v_reuseFailAlloc_5778_;
goto v_reusejp_5776_;
}
v_reusejp_5776_:
{
return v___x_5777_;
}
}
else
{
lean_object* v___x_5779_; 
lean_del_object(v___x_5771_);
lean_dec(v_val_5769_);
v___x_5779_ = lean_box(0);
return v___x_5779_;
}
}
}
else
{
lean_object* v___x_5781_; 
lean_dec(v___x_5768_);
v___x_5781_ = lean_box(0);
return v___x_5781_;
}
}
else
{
lean_object* v___x_5782_; 
v___x_5782_ = lean_box(0);
return v___x_5782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* v_p_5783_){
_start:
{
lean_object* v_res_5784_; 
v_res_5784_ = l_Lean_patternWithRef_x3f(v_p_5783_);
lean_dec_ref(v_p_5783_);
return v_res_5784_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object* v_p_5785_){
_start:
{
lean_object* v___x_5786_; 
v___x_5786_ = l_Lean_patternWithRef_x3f(v_p_5785_);
if (lean_obj_tag(v___x_5786_) == 0)
{
uint8_t v___x_5787_; 
v___x_5787_ = 0;
return v___x_5787_;
}
else
{
uint8_t v___x_5788_; 
lean_dec_ref_known(v___x_5786_, 1);
v___x_5788_ = 1;
return v___x_5788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* v_p_5789_){
_start:
{
uint8_t v_res_5790_; lean_object* v_r_5791_; 
v_res_5790_ = l_Lean_isPatternWithRef(v_p_5789_);
lean_dec_ref(v_p_5789_);
v_r_5791_ = lean_box(v_res_5790_);
return v_r_5791_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* v_p_5792_, lean_object* v_stx_5793_){
_start:
{
lean_object* v___x_5794_; 
v___x_5794_ = l_Lean_patternWithRef_x3f(v_p_5792_);
if (lean_obj_tag(v___x_5794_) == 0)
{
lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; 
v___x_5795_ = l_Lean_KVMap_empty;
v___x_5796_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5797_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_5797_, 0, v_stx_5793_);
v___x_5798_ = l_Lean_KVMap_insert(v___x_5795_, v___x_5796_, v___x_5797_);
v___x_5799_ = l_Lean_Expr_mdata___override(v___x_5798_, v_p_5792_);
return v___x_5799_;
}
else
{
lean_dec_ref_known(v___x_5794_, 1);
lean_dec(v_stx_5793_);
return v_p_5792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* v_e_5800_){
_start:
{
lean_object* v___x_5801_; 
v___x_5801_ = l_Lean_inaccessible_x3f(v_e_5800_);
if (lean_obj_tag(v___x_5801_) == 1)
{
return v___x_5801_;
}
else
{
lean_object* v___x_5802_; 
lean_dec(v___x_5801_);
v___x_5802_ = l_Lean_patternWithRef_x3f(v_e_5800_);
if (lean_obj_tag(v___x_5802_) == 1)
{
lean_object* v_val_5803_; lean_object* v___x_5805_; uint8_t v_isShared_5806_; uint8_t v_isSharedCheck_5811_; 
v_val_5803_ = lean_ctor_get(v___x_5802_, 0);
v_isSharedCheck_5811_ = !lean_is_exclusive(v___x_5802_);
if (v_isSharedCheck_5811_ == 0)
{
v___x_5805_ = v___x_5802_;
v_isShared_5806_ = v_isSharedCheck_5811_;
goto v_resetjp_5804_;
}
else
{
lean_inc(v_val_5803_);
lean_dec(v___x_5802_);
v___x_5805_ = lean_box(0);
v_isShared_5806_ = v_isSharedCheck_5811_;
goto v_resetjp_5804_;
}
v_resetjp_5804_:
{
lean_object* v_snd_5807_; lean_object* v___x_5809_; 
v_snd_5807_ = lean_ctor_get(v_val_5803_, 1);
lean_inc(v_snd_5807_);
lean_dec(v_val_5803_);
if (v_isShared_5806_ == 0)
{
lean_ctor_set(v___x_5805_, 0, v_snd_5807_);
v___x_5809_ = v___x_5805_;
goto v_reusejp_5808_;
}
else
{
lean_object* v_reuseFailAlloc_5810_; 
v_reuseFailAlloc_5810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5810_, 0, v_snd_5807_);
v___x_5809_ = v_reuseFailAlloc_5810_;
goto v_reusejp_5808_;
}
v_reusejp_5808_:
{
return v___x_5809_;
}
}
}
else
{
lean_object* v___x_5812_; 
lean_dec(v___x_5802_);
v___x_5812_ = lean_box(0);
return v___x_5812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* v_e_5813_){
_start:
{
lean_object* v_res_5814_; 
v_res_5814_ = l_Lean_patternAnnotation_x3f(v_e_5813_);
lean_dec_ref(v_e_5813_);
return v_res_5814_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* v_e_5818_){
_start:
{
lean_object* v___x_5819_; lean_object* v___x_5820_; 
v___x_5819_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5820_ = l_Lean_mkAnnotation(v___x_5819_, v_e_5818_);
return v___x_5820_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* v_e_5824_){
_start:
{
lean_object* v___x_5825_; lean_object* v___x_5826_; 
v___x_5825_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5826_ = l_Lean_annotation_x3f(v___x_5825_, v_e_5824_);
if (lean_obj_tag(v___x_5826_) == 0)
{
return v___x_5826_;
}
else
{
lean_object* v_val_5827_; lean_object* v___x_5829_; uint8_t v_isShared_5830_; uint8_t v_isSharedCheck_5840_; 
v_val_5827_ = lean_ctor_get(v___x_5826_, 0);
v_isSharedCheck_5840_ = !lean_is_exclusive(v___x_5826_);
if (v_isSharedCheck_5840_ == 0)
{
v___x_5829_ = v___x_5826_;
v_isShared_5830_ = v_isSharedCheck_5840_;
goto v_resetjp_5828_;
}
else
{
lean_inc(v_val_5827_);
lean_dec(v___x_5826_);
v___x_5829_ = lean_box(0);
v_isShared_5830_ = v_isSharedCheck_5840_;
goto v_resetjp_5828_;
}
v_resetjp_5828_:
{
lean_object* v___x_5831_; lean_object* v___x_5832_; uint8_t v___x_5833_; 
v___x_5831_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5832_ = lean_unsigned_to_nat(3u);
v___x_5833_ = l_Lean_Expr_isAppOfArity(v_val_5827_, v___x_5831_, v___x_5832_);
if (v___x_5833_ == 0)
{
lean_object* v___x_5834_; 
lean_del_object(v___x_5829_);
lean_dec(v_val_5827_);
v___x_5834_ = lean_box(0);
return v___x_5834_;
}
else
{
lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5838_; 
v___x_5835_ = l_Lean_Expr_appFn_x21(v_val_5827_);
lean_dec(v_val_5827_);
v___x_5836_ = l_Lean_Expr_appArg_x21(v___x_5835_);
lean_dec_ref(v___x_5835_);
if (v_isShared_5830_ == 0)
{
lean_ctor_set(v___x_5829_, 0, v___x_5836_);
v___x_5838_ = v___x_5829_;
goto v_reusejp_5837_;
}
else
{
lean_object* v_reuseFailAlloc_5839_; 
v_reuseFailAlloc_5839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5839_, 0, v___x_5836_);
v___x_5838_ = v_reuseFailAlloc_5839_;
goto v_reusejp_5837_;
}
v_reusejp_5837_:
{
return v___x_5838_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* v_e_5841_){
_start:
{
lean_object* v_res_5842_; 
v_res_5842_ = l_Lean_isLHSGoal_x3f(v_e_5841_);
lean_dec_ref(v_e_5841_);
return v_res_5842_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* v_toPure_5843_, lean_object* v_____do__lift_5844_){
_start:
{
lean_object* v___x_5845_; 
v___x_5845_ = lean_apply_2(v_toPure_5843_, lean_box(0), v_____do__lift_5844_);
return v___x_5845_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* v_inst_5846_, lean_object* v_inst_5847_){
_start:
{
lean_object* v_toApplicative_5848_; lean_object* v_toBind_5849_; lean_object* v_toPure_5850_; lean_object* v___x_5851_; lean_object* v___f_5852_; lean_object* v___x_5853_; 
v_toApplicative_5848_ = lean_ctor_get(v_inst_5846_, 0);
v_toBind_5849_ = lean_ctor_get(v_inst_5846_, 1);
lean_inc(v_toBind_5849_);
v_toPure_5850_ = lean_ctor_get(v_toApplicative_5848_, 1);
lean_inc(v_toPure_5850_);
v___x_5851_ = l_Lean_mkFreshId___redArg(v_inst_5846_, v_inst_5847_);
v___f_5852_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5852_, 0, v_toPure_5850_);
v___x_5853_ = lean_apply_4(v_toBind_5849_, lean_box(0), lean_box(0), v___x_5851_, v___f_5852_);
return v___x_5853_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* v_m_5854_, lean_object* v_inst_5855_, lean_object* v_inst_5856_){
_start:
{
lean_object* v___x_5857_; 
v___x_5857_ = l_Lean_mkFreshFVarId___redArg(v_inst_5855_, v_inst_5856_);
return v___x_5857_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* v_inst_5858_, lean_object* v_inst_5859_){
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
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* v_m_5866_, lean_object* v_inst_5867_, lean_object* v_inst_5868_){
_start:
{
lean_object* v___x_5869_; 
v___x_5869_ = l_Lean_mkFreshMVarId___redArg(v_inst_5867_, v_inst_5868_);
return v___x_5869_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* v_inst_5870_, lean_object* v_inst_5871_){
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
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* v_m_5878_, lean_object* v_inst_5879_, lean_object* v_inst_5880_){
_start:
{
lean_object* v___x_5881_; 
v___x_5881_ = l_Lean_mkFreshLMVarId___redArg(v_inst_5879_, v_inst_5880_);
return v___x_5881_;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2(void){
_start:
{
lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; 
v___x_5885_ = lean_box(0);
v___x_5886_ = ((lean_object*)(l_Lean_mkNot___closed__1));
v___x_5887_ = l_Lean_Expr_const___override(v___x_5886_, v___x_5885_);
return v___x_5887_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* v_p_5888_){
_start:
{
lean_object* v___x_5889_; lean_object* v___x_5890_; 
v___x_5889_ = lean_obj_once(&l_Lean_mkNot___closed__2, &l_Lean_mkNot___closed__2_once, _init_l_Lean_mkNot___closed__2);
v___x_5890_ = l_Lean_Expr_app___override(v___x_5889_, v_p_5888_);
return v___x_5890_;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2(void){
_start:
{
lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; 
v___x_5894_ = lean_box(0);
v___x_5895_ = ((lean_object*)(l_Lean_mkOr___closed__1));
v___x_5896_ = l_Lean_Expr_const___override(v___x_5895_, v___x_5894_);
return v___x_5896_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* v_p_5897_, lean_object* v_q_5898_){
_start:
{
lean_object* v___x_5899_; lean_object* v___x_5900_; 
v___x_5899_ = lean_obj_once(&l_Lean_mkOr___closed__2, &l_Lean_mkOr___closed__2_once, _init_l_Lean_mkOr___closed__2);
v___x_5900_ = l_Lean_mkAppB(v___x_5899_, v_p_5897_, v_q_5898_);
return v___x_5900_;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2(void){
_start:
{
lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; 
v___x_5904_ = lean_box(0);
v___x_5905_ = ((lean_object*)(l_Lean_mkAnd___closed__1));
v___x_5906_ = l_Lean_Expr_const___override(v___x_5905_, v___x_5904_);
return v___x_5906_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* v_p_5907_, lean_object* v_q_5908_){
_start:
{
lean_object* v___x_5909_; lean_object* v___x_5910_; 
v___x_5909_ = lean_obj_once(&l_Lean_mkAnd___closed__2, &l_Lean_mkAnd___closed__2_once, _init_l_Lean_mkAnd___closed__2);
v___x_5910_ = l_Lean_mkAppB(v___x_5909_, v_p_5907_, v_q_5908_);
return v___x_5910_;
}
}
static lean_object* _init_l_Lean_mkAndN___closed__0(void){
_start:
{
lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; 
v___x_5911_ = lean_box(0);
v___x_5912_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_5913_ = l_Lean_Expr_const___override(v___x_5912_, v___x_5911_);
return v___x_5913_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* v_x_5914_){
_start:
{
if (lean_obj_tag(v_x_5914_) == 0)
{
lean_object* v___x_5915_; 
v___x_5915_ = lean_obj_once(&l_Lean_mkAndN___closed__0, &l_Lean_mkAndN___closed__0_once, _init_l_Lean_mkAndN___closed__0);
return v___x_5915_;
}
else
{
lean_object* v_tail_5916_; 
v_tail_5916_ = lean_ctor_get(v_x_5914_, 1);
if (lean_obj_tag(v_tail_5916_) == 0)
{
lean_object* v_head_5917_; 
v_head_5917_ = lean_ctor_get(v_x_5914_, 0);
lean_inc(v_head_5917_);
lean_dec_ref_known(v_x_5914_, 2);
return v_head_5917_;
}
else
{
lean_object* v_head_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; 
lean_inc(v_tail_5916_);
v_head_5918_ = lean_ctor_get(v_x_5914_, 0);
lean_inc(v_head_5918_);
lean_dec_ref_known(v_x_5914_, 2);
v___x_5919_ = l_Lean_mkAndN(v_tail_5916_);
v___x_5920_ = l_Lean_mkAnd(v_head_5918_, v___x_5919_);
return v___x_5920_;
}
}
}
}
static lean_object* _init_l_Lean_mkEM___closed__3(void){
_start:
{
lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; 
v___x_5926_ = lean_box(0);
v___x_5927_ = ((lean_object*)(l_Lean_mkEM___closed__2));
v___x_5928_ = l_Lean_Expr_const___override(v___x_5927_, v___x_5926_);
return v___x_5928_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* v_p_5929_){
_start:
{
lean_object* v___x_5930_; lean_object* v___x_5931_; 
v___x_5930_ = lean_obj_once(&l_Lean_mkEM___closed__3, &l_Lean_mkEM___closed__3_once, _init_l_Lean_mkEM___closed__3);
v___x_5931_ = l_Lean_Expr_app___override(v___x_5930_, v_p_5929_);
return v___x_5931_;
}
}
static lean_object* _init_l_Lean_mkIff___closed__2(void){
_start:
{
lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; 
v___x_5935_ = lean_box(0);
v___x_5936_ = ((lean_object*)(l_Lean_mkIff___closed__1));
v___x_5937_ = l_Lean_Expr_const___override(v___x_5936_, v___x_5935_);
return v___x_5937_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* v_p_5938_, lean_object* v_q_5939_){
_start:
{
lean_object* v___x_5940_; lean_object* v___x_5941_; 
v___x_5940_ = lean_obj_once(&l_Lean_mkIff___closed__2, &l_Lean_mkIff___closed__2_once, _init_l_Lean_mkIff___closed__2);
v___x_5941_ = l_Lean_mkAppB(v___x_5940_, v_p_5938_, v_q_5939_);
return v___x_5941_;
}
}
static lean_object* _init_l_Lean_Nat_mkType(void){
_start:
{
lean_object* v___x_5942_; 
v___x_5942_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_5942_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; 
v___x_5946_ = lean_box(0);
v___x_5947_ = ((lean_object*)(l_Lean_Nat_mkInstAdd___closed__1));
v___x_5948_ = l_Lean_Expr_const___override(v___x_5947_, v___x_5946_);
return v___x_5948_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd(void){
_start:
{
lean_object* v___x_5949_; 
v___x_5949_ = lean_obj_once(&l_Lean_Nat_mkInstAdd___closed__2, &l_Lean_Nat_mkInstAdd___closed__2_once, _init_l_Lean_Nat_mkInstAdd___closed__2);
return v___x_5949_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__2(void){
_start:
{
lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; 
v___x_5953_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5954_ = ((lean_object*)(l_Lean_Nat_mkInstHAdd___closed__1));
v___x_5955_ = l_Lean_Expr_const___override(v___x_5954_, v___x_5953_);
return v___x_5955_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__3(void){
_start:
{
lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; 
v___x_5956_ = l_Lean_Nat_mkInstAdd;
v___x_5957_ = l_Lean_Nat_mkType;
v___x_5958_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_5959_ = l_Lean_mkAppB(v___x_5958_, v___x_5957_, v___x_5956_);
return v___x_5959_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd(void){
_start:
{
lean_object* v___x_5960_; 
v___x_5960_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__3, &l_Lean_Nat_mkInstHAdd___closed__3_once, _init_l_Lean_Nat_mkInstHAdd___closed__3);
return v___x_5960_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; 
v___x_5964_ = lean_box(0);
v___x_5965_ = ((lean_object*)(l_Lean_Nat_mkInstSub___closed__1));
v___x_5966_ = l_Lean_Expr_const___override(v___x_5965_, v___x_5964_);
return v___x_5966_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub(void){
_start:
{
lean_object* v___x_5967_; 
v___x_5967_ = lean_obj_once(&l_Lean_Nat_mkInstSub___closed__2, &l_Lean_Nat_mkInstSub___closed__2_once, _init_l_Lean_Nat_mkInstSub___closed__2);
return v___x_5967_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__2(void){
_start:
{
lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; 
v___x_5971_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5972_ = ((lean_object*)(l_Lean_Nat_mkInstHSub___closed__1));
v___x_5973_ = l_Lean_Expr_const___override(v___x_5972_, v___x_5971_);
return v___x_5973_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__3(void){
_start:
{
lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; 
v___x_5974_ = l_Lean_Nat_mkInstSub;
v___x_5975_ = l_Lean_Nat_mkType;
v___x_5976_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_5977_ = l_Lean_mkAppB(v___x_5976_, v___x_5975_, v___x_5974_);
return v___x_5977_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub(void){
_start:
{
lean_object* v___x_5978_; 
v___x_5978_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__3, &l_Lean_Nat_mkInstHSub___closed__3_once, _init_l_Lean_Nat_mkInstHSub___closed__3);
return v___x_5978_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; 
v___x_5982_ = lean_box(0);
v___x_5983_ = ((lean_object*)(l_Lean_Nat_mkInstMul___closed__1));
v___x_5984_ = l_Lean_Expr_const___override(v___x_5983_, v___x_5982_);
return v___x_5984_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul(void){
_start:
{
lean_object* v___x_5985_; 
v___x_5985_ = lean_obj_once(&l_Lean_Nat_mkInstMul___closed__2, &l_Lean_Nat_mkInstMul___closed__2_once, _init_l_Lean_Nat_mkInstMul___closed__2);
return v___x_5985_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__2(void){
_start:
{
lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; 
v___x_5989_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5990_ = ((lean_object*)(l_Lean_Nat_mkInstHMul___closed__1));
v___x_5991_ = l_Lean_Expr_const___override(v___x_5990_, v___x_5989_);
return v___x_5991_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; 
v___x_5992_ = l_Lean_Nat_mkInstMul;
v___x_5993_ = l_Lean_Nat_mkType;
v___x_5994_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_5995_ = l_Lean_mkAppB(v___x_5994_, v___x_5993_, v___x_5992_);
return v___x_5995_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul(void){
_start:
{
lean_object* v___x_5996_; 
v___x_5996_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__3, &l_Lean_Nat_mkInstHMul___closed__3_once, _init_l_Lean_Nat_mkInstHMul___closed__3);
return v___x_5996_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv___closed__2(void){
_start:
{
lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; 
v___x_6001_ = lean_box(0);
v___x_6002_ = ((lean_object*)(l_Lean_Nat_mkInstDiv___closed__1));
v___x_6003_ = l_Lean_Expr_const___override(v___x_6002_, v___x_6001_);
return v___x_6003_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv(void){
_start:
{
lean_object* v___x_6004_; 
v___x_6004_ = lean_obj_once(&l_Lean_Nat_mkInstDiv___closed__2, &l_Lean_Nat_mkInstDiv___closed__2_once, _init_l_Lean_Nat_mkInstDiv___closed__2);
return v___x_6004_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__2(void){
_start:
{
lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; 
v___x_6008_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6009_ = ((lean_object*)(l_Lean_Nat_mkInstHDiv___closed__1));
v___x_6010_ = l_Lean_Expr_const___override(v___x_6009_, v___x_6008_);
return v___x_6010_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__3(void){
_start:
{
lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; 
v___x_6011_ = l_Lean_Nat_mkInstDiv;
v___x_6012_ = l_Lean_Nat_mkType;
v___x_6013_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6014_ = l_Lean_mkAppB(v___x_6013_, v___x_6012_, v___x_6011_);
return v___x_6014_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv(void){
_start:
{
lean_object* v___x_6015_; 
v___x_6015_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__3, &l_Lean_Nat_mkInstHDiv___closed__3_once, _init_l_Lean_Nat_mkInstHDiv___closed__3);
return v___x_6015_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod___closed__2(void){
_start:
{
lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; 
v___x_6020_ = lean_box(0);
v___x_6021_ = ((lean_object*)(l_Lean_Nat_mkInstMod___closed__1));
v___x_6022_ = l_Lean_Expr_const___override(v___x_6021_, v___x_6020_);
return v___x_6022_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod(void){
_start:
{
lean_object* v___x_6023_; 
v___x_6023_ = lean_obj_once(&l_Lean_Nat_mkInstMod___closed__2, &l_Lean_Nat_mkInstMod___closed__2_once, _init_l_Lean_Nat_mkInstMod___closed__2);
return v___x_6023_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__2(void){
_start:
{
lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; 
v___x_6027_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6028_ = ((lean_object*)(l_Lean_Nat_mkInstHMod___closed__1));
v___x_6029_ = l_Lean_Expr_const___override(v___x_6028_, v___x_6027_);
return v___x_6029_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__3(void){
_start:
{
lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; 
v___x_6030_ = l_Lean_Nat_mkInstMod;
v___x_6031_ = l_Lean_Nat_mkType;
v___x_6032_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6033_ = l_Lean_mkAppB(v___x_6032_, v___x_6031_, v___x_6030_);
return v___x_6033_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod(void){
_start:
{
lean_object* v___x_6034_; 
v___x_6034_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__3, &l_Lean_Nat_mkInstHMod___closed__3_once, _init_l_Lean_Nat_mkInstHMod___closed__3);
return v___x_6034_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow___closed__2(void){
_start:
{
lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; 
v___x_6038_ = lean_box(0);
v___x_6039_ = ((lean_object*)(l_Lean_Nat_mkInstNatPow___closed__1));
v___x_6040_ = l_Lean_Expr_const___override(v___x_6039_, v___x_6038_);
return v___x_6040_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow(void){
_start:
{
lean_object* v___x_6041_; 
v___x_6041_ = lean_obj_once(&l_Lean_Nat_mkInstNatPow___closed__2, &l_Lean_Nat_mkInstNatPow___closed__2_once, _init_l_Lean_Nat_mkInstNatPow___closed__2);
return v___x_6041_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; 
v___x_6045_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6046_ = ((lean_object*)(l_Lean_Nat_mkInstPow___closed__1));
v___x_6047_ = l_Lean_Expr_const___override(v___x_6046_, v___x_6045_);
return v___x_6047_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__3(void){
_start:
{
lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; 
v___x_6048_ = l_Lean_Nat_mkInstNatPow;
v___x_6049_ = l_Lean_Nat_mkType;
v___x_6050_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6051_ = l_Lean_mkAppB(v___x_6050_, v___x_6049_, v___x_6048_);
return v___x_6051_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow(void){
_start:
{
lean_object* v___x_6052_; 
v___x_6052_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__3, &l_Lean_Nat_mkInstPow___closed__3_once, _init_l_Lean_Nat_mkInstPow___closed__3);
return v___x_6052_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__3(void){
_start:
{
lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; 
v___x_6059_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__2));
v___x_6060_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__1));
v___x_6061_ = l_Lean_Expr_const___override(v___x_6060_, v___x_6059_);
return v___x_6061_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__4(void){
_start:
{
lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; 
v___x_6062_ = l_Lean_Nat_mkInstPow;
v___x_6063_ = l_Lean_Nat_mkType;
v___x_6064_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6065_ = l_Lean_mkApp3(v___x_6064_, v___x_6063_, v___x_6063_, v___x_6062_);
return v___x_6065_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow(void){
_start:
{
lean_object* v___x_6066_; 
v___x_6066_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__4, &l_Lean_Nat_mkInstHPow___closed__4_once, _init_l_Lean_Nat_mkInstHPow___closed__4);
return v___x_6066_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; 
v___x_6070_ = lean_box(0);
v___x_6071_ = ((lean_object*)(l_Lean_Nat_mkInstLT___closed__1));
v___x_6072_ = l_Lean_Expr_const___override(v___x_6071_, v___x_6070_);
return v___x_6072_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT(void){
_start:
{
lean_object* v___x_6073_; 
v___x_6073_ = lean_obj_once(&l_Lean_Nat_mkInstLT___closed__2, &l_Lean_Nat_mkInstLT___closed__2_once, _init_l_Lean_Nat_mkInstLT___closed__2);
return v___x_6073_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; 
v___x_6077_ = lean_box(0);
v___x_6078_ = ((lean_object*)(l_Lean_Nat_mkInstLE___closed__1));
v___x_6079_ = l_Lean_Expr_const___override(v___x_6078_, v___x_6077_);
return v___x_6079_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE(void){
_start:
{
lean_object* v___x_6080_; 
v___x_6080_ = lean_obj_once(&l_Lean_Nat_mkInstLE___closed__2, &l_Lean_Nat_mkInstLE___closed__2_once, _init_l_Lean_Nat_mkInstLE___closed__2);
return v___x_6080_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3(void){
_start:
{
lean_object* v___x_6086_; lean_object* v___x_6087_; 
v___x_6086_ = lean_unsigned_to_nat(0u);
v___x_6087_ = l_Lean_Level_ofNat(v___x_6086_);
return v___x_6087_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4(void){
_start:
{
lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; 
v___x_6088_ = lean_box(0);
v___x_6089_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6090_, 0, v___x_6089_);
lean_ctor_set(v___x_6090_, 1, v___x_6088_);
return v___x_6090_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5(void){
_start:
{
lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; 
v___x_6091_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6092_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6092_);
lean_ctor_set(v___x_6093_, 1, v___x_6091_);
return v___x_6093_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6(void){
_start:
{
lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; 
v___x_6094_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__5, &l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5);
v___x_6095_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6095_);
lean_ctor_set(v___x_6096_, 1, v___x_6094_);
return v___x_6096_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7(void){
_start:
{
lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; 
v___x_6097_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6098_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natAddFn___closed__2));
v___x_6099_ = l_Lean_Expr_const___override(v___x_6098_, v___x_6097_);
return v___x_6099_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8(void){
_start:
{
lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; 
v___x_6100_ = l_Lean_Nat_mkInstHAdd;
v___x_6101_ = l_Lean_Nat_mkType;
v___x_6102_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6103_ = l_Lean_mkApp4(v___x_6102_, v___x_6101_, v___x_6101_, v___x_6101_, v___x_6100_);
return v___x_6103_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn(void){
_start:
{
lean_object* v___x_6104_; 
v___x_6104_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__8, &l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8);
return v___x_6104_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3(void){
_start:
{
lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; 
v___x_6110_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6111_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natSubFn___closed__2));
v___x_6112_ = l_Lean_Expr_const___override(v___x_6111_, v___x_6110_);
return v___x_6112_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4(void){
_start:
{
lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; 
v___x_6113_ = l_Lean_Nat_mkInstHSub;
v___x_6114_ = l_Lean_Nat_mkType;
v___x_6115_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6116_ = l_Lean_mkApp4(v___x_6115_, v___x_6114_, v___x_6114_, v___x_6114_, v___x_6113_);
return v___x_6116_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn(void){
_start:
{
lean_object* v___x_6117_; 
v___x_6117_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__4, &l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4);
return v___x_6117_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3(void){
_start:
{
lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; 
v___x_6123_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6124_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natMulFn___closed__2));
v___x_6125_ = l_Lean_Expr_const___override(v___x_6124_, v___x_6123_);
return v___x_6125_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4(void){
_start:
{
lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; 
v___x_6126_ = l_Lean_Nat_mkInstHMul;
v___x_6127_ = l_Lean_Nat_mkType;
v___x_6128_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6129_ = l_Lean_mkApp4(v___x_6128_, v___x_6127_, v___x_6127_, v___x_6127_, v___x_6126_);
return v___x_6129_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn(void){
_start:
{
lean_object* v___x_6130_; 
v___x_6130_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__4, &l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4);
return v___x_6130_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3(void){
_start:
{
lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; 
v___x_6136_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6137_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natPowFn___closed__2));
v___x_6138_ = l_Lean_Expr_const___override(v___x_6137_, v___x_6136_);
return v___x_6138_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4(void){
_start:
{
lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; 
v___x_6139_ = l_Lean_Nat_mkInstHPow;
v___x_6140_ = l_Lean_Nat_mkType;
v___x_6141_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6142_ = l_Lean_mkApp4(v___x_6141_, v___x_6140_, v___x_6140_, v___x_6140_, v___x_6139_);
return v___x_6142_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn(void){
_start:
{
lean_object* v___x_6143_; 
v___x_6143_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__4, &l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4);
return v___x_6143_;
}
}
static lean_object* _init_l_Lean_mkNatSucc___closed__2(void){
_start:
{
lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; 
v___x_6148_ = lean_box(0);
v___x_6149_ = ((lean_object*)(l_Lean_mkNatSucc___closed__1));
v___x_6150_ = l_Lean_Expr_const___override(v___x_6149_, v___x_6148_);
return v___x_6150_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* v_a_6151_){
_start:
{
lean_object* v___x_6152_; lean_object* v___x_6153_; 
v___x_6152_ = lean_obj_once(&l_Lean_mkNatSucc___closed__2, &l_Lean_mkNatSucc___closed__2_once, _init_l_Lean_mkNatSucc___closed__2);
v___x_6153_ = l_Lean_Expr_app___override(v___x_6152_, v_a_6151_);
return v___x_6153_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* v_a_6154_, lean_object* v_b_6155_){
_start:
{
lean_object* v___x_6156_; lean_object* v___x_6157_; 
v___x_6156_ = l___private_Lean_Expr_0__Lean_natAddFn;
v___x_6157_ = l_Lean_mkAppB(v___x_6156_, v_a_6154_, v_b_6155_);
return v___x_6157_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* v_a_6158_, lean_object* v_b_6159_){
_start:
{
lean_object* v___x_6160_; lean_object* v___x_6161_; 
v___x_6160_ = l___private_Lean_Expr_0__Lean_natSubFn;
v___x_6161_ = l_Lean_mkAppB(v___x_6160_, v_a_6158_, v_b_6159_);
return v___x_6161_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* v_a_6162_, lean_object* v_b_6163_){
_start:
{
lean_object* v___x_6164_; lean_object* v___x_6165_; 
v___x_6164_ = l___private_Lean_Expr_0__Lean_natMulFn;
v___x_6165_ = l_Lean_mkAppB(v___x_6164_, v_a_6162_, v_b_6163_);
return v___x_6165_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object* v_a_6166_, lean_object* v_b_6167_){
_start:
{
lean_object* v___x_6168_; lean_object* v___x_6169_; 
v___x_6168_ = l___private_Lean_Expr_0__Lean_natPowFn;
v___x_6169_ = l_Lean_mkAppB(v___x_6168_, v_a_6166_, v_b_6167_);
return v___x_6169_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3(void){
_start:
{
lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; 
v___x_6175_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6176_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natLEPred___closed__2));
v___x_6177_ = l_Lean_Expr_const___override(v___x_6176_, v___x_6175_);
return v___x_6177_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4(void){
_start:
{
lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; 
v___x_6178_ = l_Lean_Nat_mkInstLE;
v___x_6179_ = l_Lean_Nat_mkType;
v___x_6180_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6181_ = l_Lean_mkAppB(v___x_6180_, v___x_6179_, v___x_6178_);
return v___x_6181_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred(void){
_start:
{
lean_object* v___x_6182_; 
v___x_6182_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__4, &l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4);
return v___x_6182_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* v_a_6183_, lean_object* v_b_6184_){
_start:
{
lean_object* v___x_6185_; lean_object* v___x_6186_; 
v___x_6185_ = l___private_Lean_Expr_0__Lean_natLEPred;
v___x_6186_ = l_Lean_mkAppB(v___x_6185_, v_a_6183_, v_b_6184_);
return v___x_6186_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0(void){
_start:
{
lean_object* v___x_6187_; lean_object* v___x_6188_; 
v___x_6187_ = lean_unsigned_to_nat(1u);
v___x_6188_ = l_Lean_Level_ofNat(v___x_6187_);
return v___x_6188_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1(void){
_start:
{
lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; 
v___x_6189_ = lean_box(0);
v___x_6190_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__0, &l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0);
v___x_6191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6191_, 0, v___x_6190_);
lean_ctor_set(v___x_6191_, 1, v___x_6189_);
return v___x_6191_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2(void){
_start:
{
lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; 
v___x_6192_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__1, &l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1);
v___x_6193_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_6194_ = l_Lean_Expr_const___override(v___x_6193_, v___x_6192_);
return v___x_6194_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3(void){
_start:
{
lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; 
v___x_6195_ = l_Lean_Nat_mkType;
v___x_6196_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6197_ = l_Lean_Expr_app___override(v___x_6196_, v___x_6195_);
return v___x_6197_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred(void){
_start:
{
lean_object* v___x_6198_; 
v___x_6198_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__3, &l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3);
return v___x_6198_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* v_a_6199_, lean_object* v_b_6200_){
_start:
{
lean_object* v___x_6201_; lean_object* v___x_6202_; 
v___x_6201_ = l___private_Lean_Expr_0__Lean_natEqPred;
v___x_6202_ = l_Lean_mkAppB(v___x_6201_, v_a_6199_, v_b_6200_);
return v___x_6202_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__0(void){
_start:
{
lean_object* v___x_6203_; lean_object* v___x_6204_; 
v___x_6203_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6204_ = l_Lean_Expr_sort___override(v___x_6203_);
return v___x_6204_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__1(void){
_start:
{
lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; 
v___x_6205_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__0, &l___private_Lean_Expr_0__Lean_propEq___closed__0_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__0);
v___x_6206_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6207_ = l_Lean_Expr_app___override(v___x_6206_, v___x_6205_);
return v___x_6207_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq(void){
_start:
{
lean_object* v___x_6208_; 
v___x_6208_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__1, &l___private_Lean_Expr_0__Lean_propEq___closed__1_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__1);
return v___x_6208_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* v_a_6209_, lean_object* v_b_6210_){
_start:
{
lean_object* v___x_6211_; lean_object* v___x_6212_; 
v___x_6211_ = l___private_Lean_Expr_0__Lean_propEq;
v___x_6212_ = l_Lean_mkAppB(v___x_6211_, v_a_6209_, v_b_6210_);
return v___x_6212_;
}
}
static lean_object* _init_l_Lean_Int_mkType___closed__2(void){
_start:
{
lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; 
v___x_6216_ = lean_box(0);
v___x_6217_ = ((lean_object*)(l_Lean_Int_mkType___closed__1));
v___x_6218_ = l_Lean_Expr_const___override(v___x_6217_, v___x_6216_);
return v___x_6218_;
}
}
static lean_object* _init_l_Lean_Int_mkType(void){
_start:
{
lean_object* v___x_6219_; 
v___x_6219_ = lean_obj_once(&l_Lean_Int_mkType___closed__2, &l_Lean_Int_mkType___closed__2_once, _init_l_Lean_Int_mkType___closed__2);
return v___x_6219_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg___closed__2(void){
_start:
{
lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; 
v___x_6224_ = lean_box(0);
v___x_6225_ = ((lean_object*)(l_Lean_Int_mkInstNeg___closed__1));
v___x_6226_ = l_Lean_Expr_const___override(v___x_6225_, v___x_6224_);
return v___x_6226_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg(void){
_start:
{
lean_object* v___x_6227_; 
v___x_6227_ = lean_obj_once(&l_Lean_Int_mkInstNeg___closed__2, &l_Lean_Int_mkInstNeg___closed__2_once, _init_l_Lean_Int_mkInstNeg___closed__2);
return v___x_6227_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; 
v___x_6232_ = lean_box(0);
v___x_6233_ = ((lean_object*)(l_Lean_Int_mkInstAdd___closed__1));
v___x_6234_ = l_Lean_Expr_const___override(v___x_6233_, v___x_6232_);
return v___x_6234_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd(void){
_start:
{
lean_object* v___x_6235_; 
v___x_6235_ = lean_obj_once(&l_Lean_Int_mkInstAdd___closed__2, &l_Lean_Int_mkInstAdd___closed__2_once, _init_l_Lean_Int_mkInstAdd___closed__2);
return v___x_6235_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd___closed__0(void){
_start:
{
lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; lean_object* v___x_6239_; 
v___x_6236_ = l_Lean_Int_mkInstAdd;
v___x_6237_ = l_Lean_Int_mkType;
v___x_6238_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6239_ = l_Lean_mkAppB(v___x_6238_, v___x_6237_, v___x_6236_);
return v___x_6239_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd(void){
_start:
{
lean_object* v___x_6240_; 
v___x_6240_ = lean_obj_once(&l_Lean_Int_mkInstHAdd___closed__0, &l_Lean_Int_mkInstHAdd___closed__0_once, _init_l_Lean_Int_mkInstHAdd___closed__0);
return v___x_6240_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6245_; lean_object* v___x_6246_; lean_object* v___x_6247_; 
v___x_6245_ = lean_box(0);
v___x_6246_ = ((lean_object*)(l_Lean_Int_mkInstSub___closed__1));
v___x_6247_ = l_Lean_Expr_const___override(v___x_6246_, v___x_6245_);
return v___x_6247_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub(void){
_start:
{
lean_object* v___x_6248_; 
v___x_6248_ = lean_obj_once(&l_Lean_Int_mkInstSub___closed__2, &l_Lean_Int_mkInstSub___closed__2_once, _init_l_Lean_Int_mkInstSub___closed__2);
return v___x_6248_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub___closed__0(void){
_start:
{
lean_object* v___x_6249_; lean_object* v___x_6250_; lean_object* v___x_6251_; lean_object* v___x_6252_; 
v___x_6249_ = l_Lean_Int_mkInstSub;
v___x_6250_ = l_Lean_Int_mkType;
v___x_6251_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6252_ = l_Lean_mkAppB(v___x_6251_, v___x_6250_, v___x_6249_);
return v___x_6252_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub(void){
_start:
{
lean_object* v___x_6253_; 
v___x_6253_ = lean_obj_once(&l_Lean_Int_mkInstHSub___closed__0, &l_Lean_Int_mkInstHSub___closed__0_once, _init_l_Lean_Int_mkInstHSub___closed__0);
return v___x_6253_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6258_; lean_object* v___x_6259_; lean_object* v___x_6260_; 
v___x_6258_ = lean_box(0);
v___x_6259_ = ((lean_object*)(l_Lean_Int_mkInstMul___closed__1));
v___x_6260_ = l_Lean_Expr_const___override(v___x_6259_, v___x_6258_);
return v___x_6260_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul(void){
_start:
{
lean_object* v___x_6261_; 
v___x_6261_ = lean_obj_once(&l_Lean_Int_mkInstMul___closed__2, &l_Lean_Int_mkInstMul___closed__2_once, _init_l_Lean_Int_mkInstMul___closed__2);
return v___x_6261_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul___closed__0(void){
_start:
{
lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; 
v___x_6262_ = l_Lean_Int_mkInstMul;
v___x_6263_ = l_Lean_Int_mkType;
v___x_6264_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6265_ = l_Lean_mkAppB(v___x_6264_, v___x_6263_, v___x_6262_);
return v___x_6265_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul(void){
_start:
{
lean_object* v___x_6266_; 
v___x_6266_ = lean_obj_once(&l_Lean_Int_mkInstHMul___closed__0, &l_Lean_Int_mkInstHMul___closed__0_once, _init_l_Lean_Int_mkInstHMul___closed__0);
return v___x_6266_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv___closed__1(void){
_start:
{
lean_object* v___x_6270_; lean_object* v___x_6271_; lean_object* v___x_6272_; 
v___x_6270_ = lean_box(0);
v___x_6271_ = ((lean_object*)(l_Lean_Int_mkInstDiv___closed__0));
v___x_6272_ = l_Lean_Expr_const___override(v___x_6271_, v___x_6270_);
return v___x_6272_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv(void){
_start:
{
lean_object* v___x_6273_; 
v___x_6273_ = lean_obj_once(&l_Lean_Int_mkInstDiv___closed__1, &l_Lean_Int_mkInstDiv___closed__1_once, _init_l_Lean_Int_mkInstDiv___closed__1);
return v___x_6273_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv___closed__0(void){
_start:
{
lean_object* v___x_6274_; lean_object* v___x_6275_; lean_object* v___x_6276_; lean_object* v___x_6277_; 
v___x_6274_ = l_Lean_Int_mkInstDiv;
v___x_6275_ = l_Lean_Int_mkType;
v___x_6276_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6277_ = l_Lean_mkAppB(v___x_6276_, v___x_6275_, v___x_6274_);
return v___x_6277_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv(void){
_start:
{
lean_object* v___x_6278_; 
v___x_6278_ = lean_obj_once(&l_Lean_Int_mkInstHDiv___closed__0, &l_Lean_Int_mkInstHDiv___closed__0_once, _init_l_Lean_Int_mkInstHDiv___closed__0);
return v___x_6278_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod___closed__1(void){
_start:
{
lean_object* v___x_6282_; lean_object* v___x_6283_; lean_object* v___x_6284_; 
v___x_6282_ = lean_box(0);
v___x_6283_ = ((lean_object*)(l_Lean_Int_mkInstMod___closed__0));
v___x_6284_ = l_Lean_Expr_const___override(v___x_6283_, v___x_6282_);
return v___x_6284_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod(void){
_start:
{
lean_object* v___x_6285_; 
v___x_6285_ = lean_obj_once(&l_Lean_Int_mkInstMod___closed__1, &l_Lean_Int_mkInstMod___closed__1_once, _init_l_Lean_Int_mkInstMod___closed__1);
return v___x_6285_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod___closed__0(void){
_start:
{
lean_object* v___x_6286_; lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; 
v___x_6286_ = l_Lean_Int_mkInstMod;
v___x_6287_ = l_Lean_Int_mkType;
v___x_6288_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6289_ = l_Lean_mkAppB(v___x_6288_, v___x_6287_, v___x_6286_);
return v___x_6289_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod(void){
_start:
{
lean_object* v___x_6290_; 
v___x_6290_ = lean_obj_once(&l_Lean_Int_mkInstHMod___closed__0, &l_Lean_Int_mkInstHMod___closed__0_once, _init_l_Lean_Int_mkInstHMod___closed__0);
return v___x_6290_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; 
v___x_6295_ = lean_box(0);
v___x_6296_ = ((lean_object*)(l_Lean_Int_mkInstPow___closed__1));
v___x_6297_ = l_Lean_Expr_const___override(v___x_6296_, v___x_6295_);
return v___x_6297_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow(void){
_start:
{
lean_object* v___x_6298_; 
v___x_6298_ = lean_obj_once(&l_Lean_Int_mkInstPow___closed__2, &l_Lean_Int_mkInstPow___closed__2_once, _init_l_Lean_Int_mkInstPow___closed__2);
return v___x_6298_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat___closed__0(void){
_start:
{
lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; 
v___x_6299_ = l_Lean_Int_mkInstPow;
v___x_6300_ = l_Lean_Int_mkType;
v___x_6301_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6302_ = l_Lean_mkAppB(v___x_6301_, v___x_6300_, v___x_6299_);
return v___x_6302_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat(void){
_start:
{
lean_object* v___x_6303_; 
v___x_6303_ = lean_obj_once(&l_Lean_Int_mkInstPowNat___closed__0, &l_Lean_Int_mkInstPowNat___closed__0_once, _init_l_Lean_Int_mkInstPowNat___closed__0);
return v___x_6303_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow___closed__0(void){
_start:
{
lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; lean_object* v___x_6307_; lean_object* v___x_6308_; 
v___x_6304_ = l_Lean_Int_mkInstPowNat;
v___x_6305_ = l_Lean_Nat_mkType;
v___x_6306_ = l_Lean_Int_mkType;
v___x_6307_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6308_ = l_Lean_mkApp3(v___x_6307_, v___x_6306_, v___x_6305_, v___x_6304_);
return v___x_6308_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow(void){
_start:
{
lean_object* v___x_6309_; 
v___x_6309_ = lean_obj_once(&l_Lean_Int_mkInstHPow___closed__0, &l_Lean_Int_mkInstHPow___closed__0_once, _init_l_Lean_Int_mkInstHPow___closed__0);
return v___x_6309_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6314_; lean_object* v___x_6315_; lean_object* v___x_6316_; 
v___x_6314_ = lean_box(0);
v___x_6315_ = ((lean_object*)(l_Lean_Int_mkInstLT___closed__1));
v___x_6316_ = l_Lean_Expr_const___override(v___x_6315_, v___x_6314_);
return v___x_6316_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT(void){
_start:
{
lean_object* v___x_6317_; 
v___x_6317_ = lean_obj_once(&l_Lean_Int_mkInstLT___closed__2, &l_Lean_Int_mkInstLT___closed__2_once, _init_l_Lean_Int_mkInstLT___closed__2);
return v___x_6317_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6322_; lean_object* v___x_6323_; lean_object* v___x_6324_; 
v___x_6322_ = lean_box(0);
v___x_6323_ = ((lean_object*)(l_Lean_Int_mkInstLE___closed__1));
v___x_6324_ = l_Lean_Expr_const___override(v___x_6323_, v___x_6322_);
return v___x_6324_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE(void){
_start:
{
lean_object* v___x_6325_; 
v___x_6325_ = lean_obj_once(&l_Lean_Int_mkInstLE___closed__2, &l_Lean_Int_mkInstLE___closed__2_once, _init_l_Lean_Int_mkInstLE___closed__2);
return v___x_6325_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast___closed__2(void){
_start:
{
lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; 
v___x_6329_ = lean_box(0);
v___x_6330_ = ((lean_object*)(l_Lean_Int_mkInstNatCast___closed__1));
v___x_6331_ = l_Lean_Expr_const___override(v___x_6330_, v___x_6329_);
return v___x_6331_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast(void){
_start:
{
lean_object* v___x_6332_; 
v___x_6332_ = lean_obj_once(&l_Lean_Int_mkInstNatCast___closed__2, &l_Lean_Int_mkInstNatCast___closed__2_once, _init_l_Lean_Int_mkInstNatCast___closed__2);
return v___x_6332_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0(void){
_start:
{
lean_object* v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; 
v___x_6333_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6334_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_6335_ = l_Lean_Expr_const___override(v___x_6334_, v___x_6333_);
return v___x_6335_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1(void){
_start:
{
lean_object* v___x_6336_; lean_object* v___x_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; 
v___x_6336_ = l_Lean_Int_mkInstNeg;
v___x_6337_ = l_Lean_Int_mkType;
v___x_6338_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__0, &l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0);
v___x_6339_ = l_Lean_mkAppB(v___x_6338_, v___x_6337_, v___x_6336_);
return v___x_6339_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn(void){
_start:
{
lean_object* v___x_6340_; 
v___x_6340_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__1, &l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1);
return v___x_6340_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0(void){
_start:
{
lean_object* v___x_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; lean_object* v___x_6344_; 
v___x_6341_ = l_Lean_Int_mkInstHAdd;
v___x_6342_ = l_Lean_Int_mkType;
v___x_6343_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6344_ = l_Lean_mkApp4(v___x_6343_, v___x_6342_, v___x_6342_, v___x_6342_, v___x_6341_);
return v___x_6344_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn(void){
_start:
{
lean_object* v___x_6345_; 
v___x_6345_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intAddFn___closed__0, &l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0);
return v___x_6345_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0(void){
_start:
{
lean_object* v___x_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; lean_object* v___x_6349_; 
v___x_6346_ = l_Lean_Int_mkInstHSub;
v___x_6347_ = l_Lean_Int_mkType;
v___x_6348_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6349_ = l_Lean_mkApp4(v___x_6348_, v___x_6347_, v___x_6347_, v___x_6347_, v___x_6346_);
return v___x_6349_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn(void){
_start:
{
lean_object* v___x_6350_; 
v___x_6350_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intSubFn___closed__0, &l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0);
return v___x_6350_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0(void){
_start:
{
lean_object* v___x_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; 
v___x_6351_ = l_Lean_Int_mkInstHMul;
v___x_6352_ = l_Lean_Int_mkType;
v___x_6353_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6354_ = l_Lean_mkApp4(v___x_6353_, v___x_6352_, v___x_6352_, v___x_6352_, v___x_6351_);
return v___x_6354_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn(void){
_start:
{
lean_object* v___x_6355_; 
v___x_6355_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intMulFn___closed__0, &l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0);
return v___x_6355_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3(void){
_start:
{
lean_object* v___x_6361_; lean_object* v___x_6362_; lean_object* v___x_6363_; 
v___x_6361_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6362_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intDivFn___closed__2));
v___x_6363_ = l_Lean_Expr_const___override(v___x_6362_, v___x_6361_);
return v___x_6363_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4(void){
_start:
{
lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; 
v___x_6364_ = l_Lean_Int_mkInstHDiv;
v___x_6365_ = l_Lean_Int_mkType;
v___x_6366_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__3, &l___private_Lean_Expr_0__Lean_intDivFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3);
v___x_6367_ = l_Lean_mkApp4(v___x_6366_, v___x_6365_, v___x_6365_, v___x_6365_, v___x_6364_);
return v___x_6367_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn(void){
_start:
{
lean_object* v___x_6368_; 
v___x_6368_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__4, &l___private_Lean_Expr_0__Lean_intDivFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4);
return v___x_6368_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3(void){
_start:
{
lean_object* v___x_6374_; lean_object* v___x_6375_; lean_object* v___x_6376_; 
v___x_6374_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6375_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intModFn___closed__2));
v___x_6376_ = l_Lean_Expr_const___override(v___x_6375_, v___x_6374_);
return v___x_6376_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4(void){
_start:
{
lean_object* v___x_6377_; lean_object* v___x_6378_; lean_object* v___x_6379_; lean_object* v___x_6380_; 
v___x_6377_ = l_Lean_Int_mkInstHMod;
v___x_6378_ = l_Lean_Int_mkType;
v___x_6379_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__3, &l___private_Lean_Expr_0__Lean_intModFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3);
v___x_6380_ = l_Lean_mkApp4(v___x_6379_, v___x_6378_, v___x_6378_, v___x_6378_, v___x_6377_);
return v___x_6380_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn(void){
_start:
{
lean_object* v___x_6381_; 
v___x_6381_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__4, &l___private_Lean_Expr_0__Lean_intModFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4);
return v___x_6381_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0(void){
_start:
{
lean_object* v___x_6382_; lean_object* v___x_6383_; lean_object* v___x_6384_; lean_object* v___x_6385_; lean_object* v___x_6386_; 
v___x_6382_ = l_Lean_Int_mkInstHPow;
v___x_6383_ = l_Lean_Nat_mkType;
v___x_6384_ = l_Lean_Int_mkType;
v___x_6385_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6386_ = l_Lean_mkApp4(v___x_6385_, v___x_6384_, v___x_6383_, v___x_6384_, v___x_6382_);
return v___x_6386_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn(void){
_start:
{
lean_object* v___x_6387_; 
v___x_6387_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0, &l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0);
return v___x_6387_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3(void){
_start:
{
lean_object* v___x_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; 
v___x_6393_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6394_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2));
v___x_6395_ = l_Lean_Expr_const___override(v___x_6394_, v___x_6393_);
return v___x_6395_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4(void){
_start:
{
lean_object* v___x_6396_; lean_object* v___x_6397_; lean_object* v___x_6398_; lean_object* v___x_6399_; 
v___x_6396_ = l_Lean_Int_mkInstNatCast;
v___x_6397_ = l_Lean_Int_mkType;
v___x_6398_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3);
v___x_6399_ = l_Lean_mkAppB(v___x_6398_, v___x_6397_, v___x_6396_);
return v___x_6399_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn(void){
_start:
{
lean_object* v___x_6400_; 
v___x_6400_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4);
return v___x_6400_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* v_a_6401_){
_start:
{
lean_object* v___x_6402_; lean_object* v___x_6403_; 
v___x_6402_ = l___private_Lean_Expr_0__Lean_intNegFn;
v___x_6403_ = l_Lean_Expr_app___override(v___x_6402_, v_a_6401_);
return v___x_6403_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* v_a_6404_, lean_object* v_b_6405_){
_start:
{
lean_object* v___x_6406_; lean_object* v___x_6407_; 
v___x_6406_ = l___private_Lean_Expr_0__Lean_intAddFn;
v___x_6407_ = l_Lean_mkAppB(v___x_6406_, v_a_6404_, v_b_6405_);
return v___x_6407_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* v_a_6408_, lean_object* v_b_6409_){
_start:
{
lean_object* v___x_6410_; lean_object* v___x_6411_; 
v___x_6410_ = l___private_Lean_Expr_0__Lean_intSubFn;
v___x_6411_ = l_Lean_mkAppB(v___x_6410_, v_a_6408_, v_b_6409_);
return v___x_6411_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* v_a_6412_, lean_object* v_b_6413_){
_start:
{
lean_object* v___x_6414_; lean_object* v___x_6415_; 
v___x_6414_ = l___private_Lean_Expr_0__Lean_intMulFn;
v___x_6415_ = l_Lean_mkAppB(v___x_6414_, v_a_6412_, v_b_6413_);
return v___x_6415_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* v_a_6416_, lean_object* v_b_6417_){
_start:
{
lean_object* v___x_6418_; lean_object* v___x_6419_; 
v___x_6418_ = l___private_Lean_Expr_0__Lean_intDivFn;
v___x_6419_ = l_Lean_mkAppB(v___x_6418_, v_a_6416_, v_b_6417_);
return v___x_6419_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* v_a_6420_, lean_object* v_b_6421_){
_start:
{
lean_object* v___x_6422_; lean_object* v___x_6423_; 
v___x_6422_ = l___private_Lean_Expr_0__Lean_intModFn;
v___x_6423_ = l_Lean_mkAppB(v___x_6422_, v_a_6420_, v_b_6421_);
return v___x_6423_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* v_a_6424_){
_start:
{
lean_object* v___x_6425_; lean_object* v___x_6426_; 
v___x_6425_ = l___private_Lean_Expr_0__Lean_intNatCastFn;
v___x_6426_ = l_Lean_Expr_app___override(v___x_6425_, v_a_6424_);
return v___x_6426_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object* v_a_6427_, lean_object* v_b_6428_){
_start:
{
lean_object* v___x_6429_; lean_object* v___x_6430_; 
v___x_6429_ = l___private_Lean_Expr_0__Lean_intPowNatFn;
v___x_6430_ = l_Lean_mkAppB(v___x_6429_, v_a_6427_, v_b_6428_);
return v___x_6430_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0(void){
_start:
{
lean_object* v___x_6431_; lean_object* v___x_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; 
v___x_6431_ = l_Lean_Int_mkInstLE;
v___x_6432_ = l_Lean_Int_mkType;
v___x_6433_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6434_ = l_Lean_mkAppB(v___x_6433_, v___x_6432_, v___x_6431_);
return v___x_6434_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred(void){
_start:
{
lean_object* v___x_6435_; 
v___x_6435_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLEPred___closed__0, &l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0);
return v___x_6435_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* v_a_6436_, lean_object* v_b_6437_){
_start:
{
lean_object* v___x_6438_; lean_object* v___x_6439_; 
v___x_6438_ = l___private_Lean_Expr_0__Lean_intLEPred;
v___x_6439_ = l_Lean_mkAppB(v___x_6438_, v_a_6436_, v_b_6437_);
return v___x_6439_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3(void){
_start:
{
lean_object* v___x_6445_; lean_object* v___x_6446_; lean_object* v___x_6447_; 
v___x_6445_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6446_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intLTPred___closed__2));
v___x_6447_ = l_Lean_Expr_const___override(v___x_6446_, v___x_6445_);
return v___x_6447_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4(void){
_start:
{
lean_object* v___x_6448_; lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; 
v___x_6448_ = l_Lean_Int_mkInstLT;
v___x_6449_ = l_Lean_Int_mkType;
v___x_6450_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__3, &l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3);
v___x_6451_ = l_Lean_mkAppB(v___x_6450_, v___x_6449_, v___x_6448_);
return v___x_6451_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred(void){
_start:
{
lean_object* v___x_6452_; 
v___x_6452_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__4, &l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4);
return v___x_6452_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object* v_a_6453_, lean_object* v_b_6454_){
_start:
{
lean_object* v___x_6455_; lean_object* v___x_6456_; 
v___x_6455_ = l___private_Lean_Expr_0__Lean_intLTPred;
v___x_6456_ = l_Lean_mkAppB(v___x_6455_, v_a_6453_, v_b_6454_);
return v___x_6456_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0(void){
_start:
{
lean_object* v___x_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; 
v___x_6457_ = l_Lean_Int_mkType;
v___x_6458_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6459_ = l_Lean_Expr_app___override(v___x_6458_, v___x_6457_);
return v___x_6459_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred(void){
_start:
{
lean_object* v___x_6460_; 
v___x_6460_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intEqPred___closed__0, &l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0);
return v___x_6460_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* v_a_6461_, lean_object* v_b_6462_){
_start:
{
lean_object* v___x_6463_; lean_object* v___x_6464_; 
v___x_6463_ = l___private_Lean_Expr_0__Lean_intEqPred;
v___x_6464_ = l_Lean_mkAppB(v___x_6463_, v_a_6461_, v_b_6462_);
return v___x_6464_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__3(void){
_start:
{
lean_object* v___x_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; 
v___x_6470_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6471_ = ((lean_object*)(l_Lean_mkIntDvd___closed__2));
v___x_6472_ = l_Lean_Expr_const___override(v___x_6471_, v___x_6470_);
return v___x_6472_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__6(void){
_start:
{
lean_object* v___x_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; 
v___x_6477_ = lean_box(0);
v___x_6478_ = ((lean_object*)(l_Lean_mkIntDvd___closed__5));
v___x_6479_ = l_Lean_Expr_const___override(v___x_6478_, v___x_6477_);
return v___x_6479_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* v_a_6480_, lean_object* v_b_6481_){
_start:
{
lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; lean_object* v___x_6485_; 
v___x_6482_ = lean_obj_once(&l_Lean_mkIntDvd___closed__3, &l_Lean_mkIntDvd___closed__3_once, _init_l_Lean_mkIntDvd___closed__3);
v___x_6483_ = l_Lean_Int_mkType;
v___x_6484_ = lean_obj_once(&l_Lean_mkIntDvd___closed__6, &l_Lean_mkIntDvd___closed__6_once, _init_l_Lean_mkIntDvd___closed__6);
v___x_6485_ = l_Lean_mkApp4(v___x_6482_, v___x_6483_, v___x_6484_, v_a_6480_, v_b_6481_);
return v___x_6485_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__2(void){
_start:
{
lean_object* v___x_6489_; lean_object* v___x_6490_; lean_object* v___x_6491_; 
v___x_6489_ = lean_box(0);
v___x_6490_ = ((lean_object*)(l_Lean_mkIntLit___closed__1));
v___x_6491_ = l_Lean_Expr_const___override(v___x_6490_, v___x_6489_);
return v___x_6491_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__3(void){
_start:
{
lean_object* v___x_6492_; lean_object* v___x_6493_; 
v___x_6492_ = lean_unsigned_to_nat(0u);
v___x_6493_ = lean_nat_to_int(v___x_6492_);
return v___x_6493_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* v_n_6494_){
_start:
{
lean_object* v___x_6495_; lean_object* v_r_6496_; lean_object* v___x_6497_; lean_object* v___x_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; lean_object* v_r_6501_; lean_object* v___x_6502_; uint8_t v___x_6503_; 
v___x_6495_ = lean_nat_abs(v_n_6494_);
v_r_6496_ = l_Lean_mkRawNatLit(v___x_6495_);
v___x_6497_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_6498_ = l_Lean_Int_mkType;
v___x_6499_ = lean_obj_once(&l_Lean_mkIntLit___closed__2, &l_Lean_mkIntLit___closed__2_once, _init_l_Lean_mkIntLit___closed__2);
lean_inc_ref(v_r_6496_);
v___x_6500_ = l_Lean_Expr_app___override(v___x_6499_, v_r_6496_);
v_r_6501_ = l_Lean_mkApp3(v___x_6497_, v___x_6498_, v_r_6496_, v___x_6500_);
v___x_6502_ = lean_obj_once(&l_Lean_mkIntLit___closed__3, &l_Lean_mkIntLit___closed__3_once, _init_l_Lean_mkIntLit___closed__3);
v___x_6503_ = lean_int_dec_lt(v_n_6494_, v___x_6502_);
if (v___x_6503_ == 0)
{
return v_r_6501_;
}
else
{
lean_object* v___x_6504_; 
v___x_6504_ = l_Lean_mkIntNeg(v_r_6501_);
return v___x_6504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* v_n_6505_){
_start:
{
lean_object* v_res_6506_; 
v_res_6506_ = l_Lean_mkIntLit(v_n_6505_);
lean_dec(v_n_6505_);
return v_res_6506_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6511_; lean_object* v___x_6512_; 
v___x_6511_ = lean_box(0);
v___x_6512_ = l_Lean_Level_succ___override(v___x_6511_);
return v___x_6512_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; 
v___x_6513_ = lean_box(0);
v___x_6514_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__2, &l_Lean_reflBoolTrue___closed__2_once, _init_l_Lean_reflBoolTrue___closed__2);
v___x_6515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6515_, 0, v___x_6514_);
lean_ctor_set(v___x_6515_, 1, v___x_6513_);
return v___x_6515_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6516_; lean_object* v___x_6517_; lean_object* v___x_6518_; 
v___x_6516_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__3, &l_Lean_reflBoolTrue___closed__3_once, _init_l_Lean_reflBoolTrue___closed__3);
v___x_6517_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__1));
v___x_6518_ = l_Lean_Expr_const___override(v___x_6517_, v___x_6516_);
return v___x_6518_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__6(void){
_start:
{
lean_object* v___x_6521_; lean_object* v___x_6522_; lean_object* v___x_6523_; 
v___x_6521_ = lean_box(0);
v___x_6522_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__5));
v___x_6523_ = l_Lean_Expr_const___override(v___x_6522_, v___x_6521_);
return v___x_6523_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__7(void){
_start:
{
lean_object* v___x_6524_; lean_object* v___x_6525_; lean_object* v___x_6526_; 
v___x_6524_ = lean_box(0);
v___x_6525_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_6526_ = l_Lean_Expr_const___override(v___x_6525_, v___x_6524_);
return v___x_6526_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__8(void){
_start:
{
lean_object* v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; 
v___x_6527_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6528_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6529_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6530_ = l_Lean_mkAppB(v___x_6529_, v___x_6528_, v___x_6527_);
return v___x_6530_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue(void){
_start:
{
lean_object* v___x_6531_; 
v___x_6531_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__8, &l_Lean_reflBoolTrue___closed__8_once, _init_l_Lean_reflBoolTrue___closed__8);
return v___x_6531_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6532_; lean_object* v___x_6533_; lean_object* v___x_6534_; 
v___x_6532_ = lean_box(0);
v___x_6533_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_6534_ = l_Lean_Expr_const___override(v___x_6533_, v___x_6532_);
return v___x_6534_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6535_; lean_object* v___x_6536_; lean_object* v___x_6537_; lean_object* v___x_6538_; 
v___x_6535_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6536_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6537_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6538_ = l_Lean_mkAppB(v___x_6537_, v___x_6536_, v___x_6535_);
return v___x_6538_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse(void){
_start:
{
lean_object* v___x_6539_; 
v___x_6539_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
return v___x_6539_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; 
v___x_6543_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6544_ = ((lean_object*)(l_Lean_eagerReflBoolTrue___closed__1));
v___x_6545_ = l_Lean_Expr_const___override(v___x_6544_, v___x_6543_);
return v___x_6545_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; 
v___x_6546_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6547_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6548_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6549_ = l_Lean_mkApp3(v___x_6548_, v___x_6547_, v___x_6546_, v___x_6546_);
return v___x_6549_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; lean_object* v___x_6553_; 
v___x_6550_ = l_Lean_reflBoolTrue;
v___x_6551_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__3, &l_Lean_eagerReflBoolTrue___closed__3_once, _init_l_Lean_eagerReflBoolTrue___closed__3);
v___x_6552_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6553_ = l_Lean_mkAppB(v___x_6552_, v___x_6551_, v___x_6550_);
return v___x_6553_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue(void){
_start:
{
lean_object* v___x_6554_; 
v___x_6554_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__4, &l_Lean_eagerReflBoolTrue___closed__4_once, _init_l_Lean_eagerReflBoolTrue___closed__4);
return v___x_6554_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6555_; lean_object* v___x_6556_; lean_object* v___x_6557_; lean_object* v___x_6558_; 
v___x_6555_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6556_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6557_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6558_ = l_Lean_mkApp3(v___x_6557_, v___x_6556_, v___x_6555_, v___x_6555_);
return v___x_6558_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; lean_object* v___x_6562_; 
v___x_6559_ = l_Lean_reflBoolFalse;
v___x_6560_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__0, &l_Lean_eagerReflBoolFalse___closed__0_once, _init_l_Lean_eagerReflBoolFalse___closed__0);
v___x_6561_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6562_ = l_Lean_mkAppB(v___x_6561_, v___x_6560_, v___x_6559_);
return v___x_6562_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse(void){
_start:
{
lean_object* v___x_6563_; 
v___x_6563_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__1, &l_Lean_eagerReflBoolFalse___closed__1_once, _init_l_Lean_eagerReflBoolFalse___closed__1);
return v___x_6563_;
}
}
static lean_object* _init_l_Lean_Expr_replaceFn___closed__2(void){
_start:
{
lean_object* v___x_6566_; lean_object* v___x_6567_; lean_object* v___x_6568_; lean_object* v___x_6569_; lean_object* v___x_6570_; lean_object* v___x_6571_; 
v___x_6566_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__1));
v___x_6567_ = lean_unsigned_to_nat(9u);
v___x_6568_ = lean_unsigned_to_nat(2458u);
v___x_6569_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__0));
v___x_6570_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_6571_ = l_mkPanicMessageWithDecl(v___x_6570_, v___x_6569_, v___x_6568_, v___x_6567_, v___x_6566_);
return v___x_6571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object* v_e_6572_, lean_object* v_declName_6573_){
_start:
{
switch(lean_obj_tag(v_e_6572_))
{
case 5:
{
lean_object* v_fn_6574_; lean_object* v_arg_6575_; lean_object* v___x_6576_; lean_object* v___x_6577_; 
v_fn_6574_ = lean_ctor_get(v_e_6572_, 0);
lean_inc_ref(v_fn_6574_);
v_arg_6575_ = lean_ctor_get(v_e_6572_, 1);
lean_inc_ref(v_arg_6575_);
lean_dec_ref_known(v_e_6572_, 2);
v___x_6576_ = l_Lean_Expr_replaceFn(v_fn_6574_, v_declName_6573_);
v___x_6577_ = l_Lean_Expr_app___override(v___x_6576_, v_arg_6575_);
return v___x_6577_;
}
case 4:
{
lean_object* v_us_6578_; lean_object* v___x_6579_; 
v_us_6578_ = lean_ctor_get(v_e_6572_, 1);
lean_inc(v_us_6578_);
lean_dec_ref_known(v_e_6572_, 2);
v___x_6579_ = l_Lean_Expr_const___override(v_declName_6573_, v_us_6578_);
return v___x_6579_;
}
default: 
{
lean_object* v___x_6580_; lean_object* v___x_6581_; 
lean_dec(v_declName_6573_);
lean_dec_ref(v_e_6572_);
v___x_6580_ = lean_obj_once(&l_Lean_Expr_replaceFn___closed__2, &l_Lean_Expr_replaceFn___closed__2_once, _init_l_Lean_Expr_replaceFn___closed__2);
v___x_6581_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_6580_);
return v___x_6581_;
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
