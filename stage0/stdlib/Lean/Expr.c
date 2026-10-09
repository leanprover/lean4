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
uint8_t l_Lean_instBEqLiteral_beq(lean_object* v_x_43_, lean_object* v_x_44_){
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
LEAN_EXPORT void l_Lean_instBEqLiteral_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_43_ = stack[0].m_obj;
lean_object* v_x_44_ = stack[1].m_obj;
uint8_t v_res_53_;
v_res_53_ = l_Lean_instBEqLiteral_beq(v_x_43_, v_x_44_);
stack->m_num = v_res_53_;
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
uint64_t l_Lean_Literal_hash(lean_object* v_x_125_){
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
LEAN_EXPORT void l_Lean_Literal_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_125_ = stack[0].m_obj;
uint64_t v_res_130_;
v_res_130_ = l_Lean_Literal_hash(v_x_125_);
stack->m_num = v_res_130_;
}
LEAN_EXPORT lean_object* l_Lean_Literal_hash___boxed(lean_object* v_x_131_){
_start:
{
uint64_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Lean_Literal_hash(v_x_131_);
lean_dec_ref(v_x_131_);
v_r_133_ = lean_box_uint64(v_res_132_);
return v_r_133_;
}
}
uint8_t l_Lean_Literal_lt(lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v_val_138_; lean_object* v_val_139_; uint8_t v___x_140_; 
v_val_138_ = lean_ctor_get(v_x_136_, 0);
v_val_139_ = lean_ctor_get(v_x_137_, 0);
v___x_140_ = lean_nat_dec_lt(v_val_138_, v_val_139_);
return v___x_140_;
}
else
{
uint8_t v___x_141_; 
v___x_141_ = 1;
return v___x_141_;
}
}
else
{
if (lean_obj_tag(v_x_137_) == 1)
{
lean_object* v_val_142_; lean_object* v_val_143_; uint8_t v___x_144_; 
v_val_142_ = lean_ctor_get(v_x_136_, 0);
v_val_143_ = lean_ctor_get(v_x_137_, 0);
v___x_144_ = lean_string_dec_lt(v_val_142_, v_val_143_);
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
}
}
LEAN_EXPORT void l_Lean_Literal_lt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_136_ = stack[0].m_obj;
lean_object* v_x_137_ = stack[1].m_obj;
uint8_t v_res_146_;
v_res_146_ = l_Lean_Literal_lt(v_x_136_, v_x_137_);
stack->m_num = v_res_146_;
}
LEAN_EXPORT lean_object* l_Lean_Literal_lt___boxed(lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Lean_Literal_lt(v_x_147_, v_x_148_);
lean_dec_ref(v_x_148_);
lean_dec_ref(v_x_147_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
static lean_object* _init_l_Lean_instLTLiteral(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_box(0);
return v___x_151_;
}
}
uint8_t l_Lean_instDecidableLtLiteral(lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = l_Lean_Literal_lt(v_a_152_, v_b_153_);
return v___x_154_;
}
}
LEAN_EXPORT void l_Lean_instDecidableLtLiteral_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_152_ = stack[0].m_obj;
lean_object* v_b_153_ = stack[1].m_obj;
uint8_t v_res_155_;
v_res_155_ = l_Lean_instDecidableLtLiteral(v_a_152_, v_b_153_);
stack->m_num = v_res_155_;
}
LEAN_EXPORT lean_object* l_Lean_instDecidableLtLiteral___boxed(lean_object* v_a_156_, lean_object* v_b_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Lean_instDecidableLtLiteral(v_a_156_, v_b_157_);
lean_dec_ref(v_b_157_);
lean_dec_ref(v_a_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
lean_object* l_Lean_BinderInfo_ctorIdx___impl(uint8_t v_x_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_box(v_x_160_);
v___x_162_ = lean_obj_tag_nat(v___x_161_);
lean_dec(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT void l_Lean_BinderInfo_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_160_ = stack[0].m_num;
lean_object* v_res_163_;
v_res_163_ = l_Lean_BinderInfo_ctorIdx___impl(v_x_160_);
stack->m_obj
 = v_res_163_;
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx___impl___boxed(lean_object* v_x_164_){
_start:
{
uint8_t v_x_4__boxed_165_; lean_object* v_res_166_; 
v_x_4__boxed_165_ = lean_unbox(v_x_164_);
v_res_166_ = l_Lean_BinderInfo_ctorIdx___impl(v_x_4__boxed_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg(lean_object* v_k_167_){
_start:
{
lean_inc(v_k_167_);
return v_k_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg___boxed(lean_object* v_k_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_BinderInfo_ctorElim___redArg(v_k_168_);
lean_dec(v_k_168_);
return v_res_169_;
}
}
lean_object* l_Lean_BinderInfo_ctorElim(lean_object* v_motive_170_, lean_object* v_ctorIdx_171_, uint8_t v_t_172_, lean_object* v_h_173_, lean_object* v_k_174_){
_start:
{
lean_inc(v_k_174_);
return v_k_174_;
}
}
LEAN_EXPORT void l_Lean_BinderInfo_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_171_ = stack[1].m_obj;
uint8_t v_t_172_ = stack[2].m_num;
lean_object* v_k_174_ = stack[4].m_obj;
lean_object* v_res_175_;
v_res_175_ = l_Lean_BinderInfo_ctorElim(lean_box(0), v_ctorIdx_171_, v_t_172_, lean_box(0), v_k_174_);
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___boxed(lean_object* v_motive_176_, lean_object* v_ctorIdx_177_, lean_object* v_t_178_, lean_object* v_h_179_, lean_object* v_k_180_){
_start:
{
uint8_t v_t_boxed_181_; lean_object* v_res_182_; 
v_t_boxed_181_ = lean_unbox(v_t_178_);
v_res_182_ = l_Lean_BinderInfo_ctorElim(v_motive_176_, v_ctorIdx_177_, v_t_boxed_181_, v_h_179_, v_k_180_);
lean_dec(v_k_180_);
lean_dec(v_ctorIdx_177_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg(lean_object* v_default_183_){
_start:
{
lean_inc(v_default_183_);
return v_default_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg___boxed(lean_object* v_default_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_BinderInfo_default_elim___redArg(v_default_184_);
lean_dec(v_default_184_);
return v_res_185_;
}
}
lean_object* l_Lean_BinderInfo_default_elim(lean_object* v_motive_186_, uint8_t v_t_187_, lean_object* v_h_188_, lean_object* v_default_189_){
_start:
{
lean_inc(v_default_189_);
return v_default_189_;
}
}
LEAN_EXPORT void l_Lean_BinderInfo_default_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_187_ = stack[1].m_num;
lean_object* v_default_189_ = stack[3].m_obj;
lean_object* v_res_190_;
v_res_190_ = l_Lean_BinderInfo_default_elim(lean_box(0), v_t_187_, lean_box(0), v_default_189_);
stack->m_obj
 = v_res_190_;
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___boxed(lean_object* v_motive_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_default_194_){
_start:
{
uint8_t v_t_boxed_195_; lean_object* v_res_196_; 
v_t_boxed_195_ = lean_unbox(v_t_192_);
v_res_196_ = l_Lean_BinderInfo_default_elim(v_motive_191_, v_t_boxed_195_, v_h_193_, v_default_194_);
lean_dec(v_default_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg(lean_object* v_implicit_197_){
_start:
{
lean_inc(v_implicit_197_);
return v_implicit_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg___boxed(lean_object* v_implicit_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_BinderInfo_implicit_elim___redArg(v_implicit_198_);
lean_dec(v_implicit_198_);
return v_res_199_;
}
}
lean_object* l_Lean_BinderInfo_implicit_elim(lean_object* v_motive_200_, uint8_t v_t_201_, lean_object* v_h_202_, lean_object* v_implicit_203_){
_start:
{
lean_inc(v_implicit_203_);
return v_implicit_203_;
}
}
LEAN_EXPORT void l_Lean_BinderInfo_implicit_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_201_ = stack[1].m_num;
lean_object* v_implicit_203_ = stack[3].m_obj;
lean_object* v_res_204_;
v_res_204_ = l_Lean_BinderInfo_implicit_elim(lean_box(0), v_t_201_, lean_box(0), v_implicit_203_);
stack->m_obj
 = v_res_204_;
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
lean_object* l_Lean_BinderInfo_strictImplicit_elim(lean_object* v_motive_214_, uint8_t v_t_215_, lean_object* v_h_216_, lean_object* v_strictImplicit_217_){
_start:
{
lean_inc(v_strictImplicit_217_);
return v_strictImplicit_217_;
}
}
LEAN_EXPORT void l_Lean_BinderInfo_strictImplicit_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_215_ = stack[1].m_num;
lean_object* v_strictImplicit_217_ = stack[3].m_obj;
lean_object* v_res_218_;
v_res_218_ = l_Lean_BinderInfo_strictImplicit_elim(lean_box(0), v_t_215_, lean_box(0), v_strictImplicit_217_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___boxed(lean_object* v_motive_219_, lean_object* v_t_220_, lean_object* v_h_221_, lean_object* v_strictImplicit_222_){
_start:
{
uint8_t v_t_boxed_223_; lean_object* v_res_224_; 
v_t_boxed_223_ = lean_unbox(v_t_220_);
v_res_224_ = l_Lean_BinderInfo_strictImplicit_elim(v_motive_219_, v_t_boxed_223_, v_h_221_, v_strictImplicit_222_);
lean_dec(v_strictImplicit_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg(lean_object* v_instImplicit_225_){
_start:
{
lean_inc(v_instImplicit_225_);
return v_instImplicit_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg___boxed(lean_object* v_instImplicit_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_BinderInfo_instImplicit_elim___redArg(v_instImplicit_226_);
lean_dec(v_instImplicit_226_);
return v_res_227_;
}
}
lean_object* l_Lean_BinderInfo_instImplicit_elim(lean_object* v_motive_228_, uint8_t v_t_229_, lean_object* v_h_230_, lean_object* v_instImplicit_231_){
_start:
{
lean_inc(v_instImplicit_231_);
return v_instImplicit_231_;
}
}
LEAN_EXPORT void l_Lean_BinderInfo_instImplicit_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_229_ = stack[1].m_num;
lean_object* v_instImplicit_231_ = stack[3].m_obj;
lean_object* v_res_232_;
v_res_232_ = l_Lean_BinderInfo_instImplicit_elim(lean_box(0), v_t_229_, lean_box(0), v_instImplicit_231_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___boxed(lean_object* v_motive_233_, lean_object* v_t_234_, lean_object* v_h_235_, lean_object* v_instImplicit_236_){
_start:
{
uint8_t v_t_boxed_237_; lean_object* v_res_238_; 
v_t_boxed_237_ = lean_unbox(v_t_234_);
v_res_238_ = l_Lean_BinderInfo_instImplicit_elim(v_motive_233_, v_t_boxed_237_, v_h_235_, v_instImplicit_236_);
lean_dec(v_instImplicit_236_);
return v_res_238_;
}
}
static uint8_t _init_l_Lean_instInhabitedBinderInfo_default(void){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = 0;
return v___x_239_;
}
}
static uint8_t _init_l_Lean_instInhabitedBinderInfo(void){
_start:
{
uint8_t v___x_240_; 
v___x_240_ = 0;
return v___x_240_;
}
}
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t v_x_241_, uint8_t v_y_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_243_ = lean_box(v_x_241_);
v___x_244_ = lean_obj_tag_nat(v___x_243_);
lean_dec(v___x_243_);
v___x_245_ = lean_box(v_y_242_);
v___x_246_ = lean_obj_tag_nat(v___x_245_);
lean_dec(v___x_245_);
v___x_247_ = lean_nat_dec_eq(v___x_244_, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT void l_Lean_instBEqBinderInfo_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_241_ = stack[0].m_num;
uint8_t v_y_242_ = stack[1].m_num;
uint8_t v_res_248_;
v_res_248_ = l_Lean_instBEqBinderInfo_beq(v_x_241_, v_y_242_);
stack->m_num = v_res_248_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqBinderInfo_beq___boxed(lean_object* v_x_249_, lean_object* v_y_250_){
_start:
{
uint8_t v_x_24__boxed_251_; uint8_t v_y_25__boxed_252_; uint8_t v_res_253_; lean_object* v_r_254_; 
v_x_24__boxed_251_ = lean_unbox(v_x_249_);
v_y_25__boxed_252_ = lean_unbox(v_y_250_);
v_res_253_ = l_Lean_instBEqBinderInfo_beq(v_x_24__boxed_251_, v_y_25__boxed_252_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
lean_object* l_Lean_instReprBinderInfo_repr(uint8_t v_x_269_, lean_object* v_prec_270_){
_start:
{
lean_object* v___y_272_; lean_object* v___y_279_; lean_object* v___y_286_; lean_object* v___y_293_; 
switch(v_x_269_)
{
case 0:
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(1024u);
v___x_300_ = lean_nat_dec_le(v___x_299_, v_prec_270_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_272_ = v___x_301_;
goto v___jp_271_;
}
else
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_272_ = v___x_302_;
goto v___jp_271_;
}
}
case 1:
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(1024u);
v___x_304_ = lean_nat_dec_le(v___x_303_, v_prec_270_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_279_ = v___x_305_;
goto v___jp_278_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_279_ = v___x_306_;
goto v___jp_278_;
}
}
case 2:
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(1024u);
v___x_308_ = lean_nat_dec_le(v___x_307_, v_prec_270_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
v___x_309_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_286_ = v___x_309_;
goto v___jp_285_;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_286_ = v___x_310_;
goto v___jp_285_;
}
}
default: 
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(1024u);
v___x_312_ = lean_nat_dec_le(v___x_311_, v_prec_270_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
v___x_313_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_293_ = v___x_313_;
goto v___jp_292_;
}
else
{
lean_object* v___x_314_; 
v___x_314_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_293_ = v___x_314_;
goto v___jp_292_;
}
}
}
v___jp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_273_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__1));
lean_inc(v___y_272_);
v___x_274_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_274_, 0, v___y_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = 0;
v___x_276_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_276_, 0, v___x_274_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*1, v___x_275_);
v___x_277_ = l_Repr_addAppParen(v___x_276_, v_prec_270_);
return v___x_277_;
}
v___jp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_280_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__3));
lean_inc(v___y_279_);
v___x_281_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_281_, 0, v___y_279_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = 0;
v___x_283_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*1, v___x_282_);
v___x_284_ = l_Repr_addAppParen(v___x_283_, v_prec_270_);
return v___x_284_;
}
v___jp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_287_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__5));
lean_inc(v___y_286_);
v___x_288_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_288_, 0, v___y_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = 0;
v___x_290_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*1, v___x_289_);
v___x_291_ = l_Repr_addAppParen(v___x_290_, v_prec_270_);
return v___x_291_;
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_294_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__7));
lean_inc(v___y_293_);
v___x_295_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_295_, 0, v___y_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = 0;
v___x_297_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set_uint8(v___x_297_, sizeof(void*)*1, v___x_296_);
v___x_298_ = l_Repr_addAppParen(v___x_297_, v_prec_270_);
return v___x_298_;
}
}
}
LEAN_EXPORT void l_Lean_instReprBinderInfo_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_269_ = stack[0].m_num;
lean_object* v_prec_270_ = stack[1].m_obj;
lean_object* v_res_315_;
v_res_315_ = l_Lean_instReprBinderInfo_repr(v_x_269_, v_prec_270_);
stack->m_obj
 = v_res_315_;
}
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr___boxed(lean_object* v_x_316_, lean_object* v_prec_317_){
_start:
{
uint8_t v_x_221__boxed_318_; lean_object* v_res_319_; 
v_x_221__boxed_318_ = lean_unbox(v_x_316_);
v_res_319_ = l_Lean_instReprBinderInfo_repr(v_x_221__boxed_318_, v_prec_317_);
lean_dec(v_prec_317_);
return v_res_319_;
}
}
uint64_t l_Lean_BinderInfo_hash(uint8_t v_x_322_){
_start:
{
switch(v_x_322_)
{
case 0:
{
uint64_t v___x_323_; 
v___x_323_ = 947ULL;
return v___x_323_;
}
case 1:
{
uint64_t v___x_324_; 
v___x_324_ = 1019ULL;
return v___x_324_;
}
case 2:
{
uint64_t v___x_325_; 
v___x_325_ = 1087ULL;
return v___x_325_;
}
default: 
{
uint64_t v___x_326_; 
v___x_326_ = 1153ULL;
return v___x_326_;
}
}
}
}
LEAN_EXPORT void l_Lean_BinderInfo_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_322_ = stack[0].m_num;
uint64_t v_res_327_;
v_res_327_ = l_Lean_BinderInfo_hash(v_x_322_);
stack->m_num = v_res_327_;
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_hash___boxed(lean_object* v_x_328_){
_start:
{
uint8_t v_x_52__boxed_329_; uint64_t v_res_330_; lean_object* v_r_331_; 
v_x_52__boxed_329_ = lean_unbox(v_x_328_);
v_res_330_ = l_Lean_BinderInfo_hash(v_x_52__boxed_329_);
v_r_331_ = lean_box_uint64(v_res_330_);
return v_r_331_;
}
}
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t v_x_332_){
_start:
{
switch(v_x_332_)
{
case 1:
{
uint8_t v___x_333_; 
v___x_333_ = 0;
return v___x_333_;
}
case 2:
{
uint8_t v___x_334_; 
v___x_334_ = 0;
return v___x_334_;
}
case 3:
{
uint8_t v___x_335_; 
v___x_335_ = 0;
return v___x_335_;
}
default: 
{
uint8_t v___x_336_; 
v___x_336_ = 1;
return v___x_336_;
}
}
}
}
LEAN_EXPORT void l_Lean_BinderInfo_isExplicit_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_332_ = stack[0].m_num;
uint8_t v_res_337_;
v_res_337_ = l_Lean_BinderInfo_isExplicit(v_x_332_);
stack->m_num = v_res_337_;
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object* v_x_338_){
_start:
{
uint8_t v_x_27__boxed_339_; uint8_t v_res_340_; lean_object* v_r_341_; 
v_x_27__boxed_339_ = lean_unbox(v_x_338_);
v_res_340_ = l_Lean_BinderInfo_isExplicit(v_x_27__boxed_339_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t v_x_344_){
_start:
{
if (v_x_344_ == 3)
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
LEAN_EXPORT void l_Lean_BinderInfo_isInstImplicit_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_344_ = stack[0].m_num;
uint8_t v_res_347_;
v_res_347_ = l_Lean_BinderInfo_isInstImplicit(v_x_344_);
stack->m_num = v_res_347_;
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object* v_x_348_){
_start:
{
uint8_t v_x_17__boxed_349_; uint8_t v_res_350_; lean_object* v_r_351_; 
v_x_17__boxed_349_ = lean_unbox(v_x_348_);
v_res_350_ = l_Lean_BinderInfo_isInstImplicit(v_x_17__boxed_349_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
uint8_t l_Lean_BinderInfo_isImplicit(uint8_t v_x_352_){
_start:
{
if (v_x_352_ == 1)
{
uint8_t v___x_353_; 
v___x_353_ = 1;
return v___x_353_;
}
else
{
uint8_t v___x_354_; 
v___x_354_ = 0;
return v___x_354_;
}
}
}
LEAN_EXPORT void l_Lean_BinderInfo_isImplicit_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_352_ = stack[0].m_num;
uint8_t v_res_355_;
v_res_355_ = l_Lean_BinderInfo_isImplicit(v_x_352_);
stack->m_num = v_res_355_;
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isImplicit___boxed(lean_object* v_x_356_){
_start:
{
uint8_t v_x_17__boxed_357_; uint8_t v_res_358_; lean_object* v_r_359_; 
v_x_17__boxed_357_ = lean_unbox(v_x_356_);
v_res_358_ = l_Lean_BinderInfo_isImplicit(v_x_17__boxed_357_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
uint8_t l_Lean_BinderInfo_isStrictImplicit(uint8_t v_x_360_){
_start:
{
if (v_x_360_ == 2)
{
uint8_t v___x_361_; 
v___x_361_ = 1;
return v___x_361_;
}
else
{
uint8_t v___x_362_; 
v___x_362_ = 0;
return v___x_362_;
}
}
}
LEAN_EXPORT void l_Lean_BinderInfo_isStrictImplicit_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_360_ = stack[0].m_num;
uint8_t v_res_363_;
v_res_363_ = l_Lean_BinderInfo_isStrictImplicit(v_x_360_);
stack->m_num = v_res_363_;
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isStrictImplicit___boxed(lean_object* v_x_364_){
_start:
{
uint8_t v_x_17__boxed_365_; uint8_t v_res_366_; lean_object* v_r_367_; 
v_x_17__boxed_365_ = lean_unbox(v_x_364_);
v_res_366_ = l_Lean_BinderInfo_isStrictImplicit(v_x_17__boxed_365_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
static lean_object* _init_l_Lean_MData_empty(void){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_box(0);
return v___x_368_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1___aux__1(void){
_start:
{
uint64_t v___x_369_; 
v___x_369_ = 0ULL;
return v___x_369_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1(void){
_start:
{
uint64_t v___x_370_; 
v___x_370_ = 0ULL;
return v___x_370_;
}
}
uint64_t l_Lean_Expr_Data_hash(uint64_t v_c_371_){
_start:
{
uint32_t v___x_372_; uint64_t v___x_373_; 
v___x_372_ = lean_uint64_to_uint32(v_c_371_);
v___x_373_ = lean_uint32_to_uint64(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT void l_Lean_Expr_Data_hash_0interp(lean_interpreter_value* stack)
{
uint64_t v_c_371_ = stack[0].m_num;
uint64_t v_res_374_;
v_res_374_ = l_Lean_Expr_Data_hash(v_c_371_);
stack->m_num = v_res_374_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object* v_c_375_){
_start:
{
uint64_t v_c_boxed_376_; uint64_t v_res_377_; lean_object* v_r_378_; 
v_c_boxed_376_ = lean_unbox_uint64(v_c_375_);
lean_dec_ref(v_c_375_);
v_res_377_ = l_Lean_Expr_Data_hash(v_c_boxed_376_);
v_r_378_ = lean_box_uint64(v_res_377_);
return v_r_378_;
}
}
uint8_t l_Lean_Expr_Data_approxDepth(uint64_t v_c_381_){
_start:
{
uint64_t v___x_382_; uint64_t v___x_383_; uint64_t v___x_384_; uint64_t v___x_385_; uint8_t v___x_386_; 
v___x_382_ = 32ULL;
v___x_383_ = lean_uint64_shift_right(v_c_381_, v___x_382_);
v___x_384_ = 255ULL;
v___x_385_ = lean_uint64_land(v___x_383_, v___x_384_);
v___x_386_ = lean_uint64_to_uint8(v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT void l_Lean_Expr_Data_approxDepth_0interp(lean_interpreter_value* stack)
{
uint64_t v_c_381_ = stack[0].m_num;
uint8_t v_res_387_;
v_res_387_ = l_Lean_Expr_Data_approxDepth(v_c_381_);
stack->m_num = v_res_387_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object* v_c_388_){
_start:
{
uint64_t v_c_boxed_389_; uint8_t v_res_390_; lean_object* v_r_391_; 
v_c_boxed_389_ = lean_unbox_uint64(v_c_388_);
lean_dec_ref(v_c_388_);
v_res_390_ = l_Lean_Expr_Data_approxDepth(v_c_boxed_389_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t v_c_392_){
_start:
{
uint64_t v___x_393_; uint64_t v___x_394_; uint32_t v___x_395_; 
v___x_393_ = 44ULL;
v___x_394_ = lean_uint64_shift_right(v_c_392_, v___x_393_);
v___x_395_ = lean_uint64_to_uint32(v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT void l_Lean_Expr_Data_looseBVarRange_0interp(lean_interpreter_value* stack)
{
uint64_t v_c_392_ = stack[0].m_num;
uint32_t v_res_396_;
v_res_396_ = l_Lean_Expr_Data_looseBVarRange(v_c_392_);
stack->m_num = v_res_396_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object* v_c_397_){
_start:
{
uint64_t v_c_boxed_398_; uint32_t v_res_399_; lean_object* v_r_400_; 
v_c_boxed_398_ = lean_unbox_uint64(v_c_397_);
lean_dec_ref(v_c_397_);
v_res_399_ = l_Lean_Expr_Data_looseBVarRange(v_c_boxed_398_);
v_r_400_ = lean_box_uint32(v_res_399_);
return v_r_400_;
}
}
uint8_t l_Lean_Expr_Data_hasFVar(uint64_t v_c_401_){
_start:
{
uint64_t v___x_402_; uint64_t v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint8_t v___x_406_; 
v___x_402_ = 40ULL;
v___x_403_ = lean_uint64_shift_right(v_c_401_, v___x_402_);
v___x_404_ = 1ULL;
v___x_405_ = lean_uint64_land(v___x_403_, v___x_404_);
v___x_406_ = lean_uint64_dec_eq(v___x_405_, v___x_404_);
return v___x_406_;
}
}
LEAN_EXPORT void l_Lean_Expr_Data_hasFVar_0interp(lean_interpreter_value* stack)
{
uint64_t v_c_401_ = stack[0].m_num;
uint8_t v_res_407_;
v_res_407_ = l_Lean_Expr_Data_hasFVar(v_c_401_);
stack->m_num = v_res_407_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object* v_c_408_){
_start:
{
uint64_t v_c_boxed_409_; uint8_t v_res_410_; lean_object* v_r_411_; 
v_c_boxed_409_ = lean_unbox_uint64(v_c_408_);
lean_dec_ref(v_c_408_);
v_res_410_ = l_Lean_Expr_Data_hasFVar(v_c_boxed_409_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t v_c_412_){
_start:
{
uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; uint8_t v___x_417_; 
v___x_413_ = 41ULL;
v___x_414_ = lean_uint64_shift_right(v_c_412_, v___x_413_);
v___x_415_ = 1ULL;
v___x_416_ = lean_uint64_land(v___x_414_, v___x_415_);
v___x_417_ = lean_uint64_dec_eq(v___x_416_, v___x_415_);
return v___x_417_;
}
}
LEAN_EXPORT void l_Lean_Expr_Data_hasExprMVar_0interp(lean_interpreter_value* stack)
{
uint64_t v_c_412_ = stack[0].m_num;
uint8_t v_res_418_;
v_res_418_ = l_Lean_Expr_Data_hasExprMVar(v_c_412_);
stack->m_num = v_res_418_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object* v_c_419_){
_start:
{
uint64_t v_c_boxed_420_; uint8_t v_res_421_; lean_object* v_r_422_; 
v_c_boxed_420_ = lean_unbox_uint64(v_c_419_);
lean_dec_ref(v_c_419_);
v_res_421_ = l_Lean_Expr_Data_hasExprMVar(v_c_boxed_420_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t v_c_423_){
_start:
{
uint64_t v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v___x_427_; uint8_t v___x_428_; 
v___x_424_ = 42ULL;
v___x_425_ = lean_uint64_shift_right(v_c_423_, v___x_424_);
v___x_426_ = 1ULL;
v___x_427_ = lean_uint64_land(v___x_425_, v___x_426_);
v___x_428_ = lean_uint64_dec_eq(v___x_427_, v___x_426_);
return v___x_428_;
}
}
LEAN_EXPORT void l_Lean_Expr_Data_hasLevelMVar_0interp(lean_interpreter_value* stack)
{
uint64_t v_c_423_ = stack[0].m_num;
uint8_t v_res_429_;
v_res_429_ = l_Lean_Expr_Data_hasLevelMVar(v_c_423_);
stack->m_num = v_res_429_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object* v_c_430_){
_start:
{
uint64_t v_c_boxed_431_; uint8_t v_res_432_; lean_object* v_r_433_; 
v_c_boxed_431_ = lean_unbox_uint64(v_c_430_);
lean_dec_ref(v_c_430_);
v_res_432_ = l_Lean_Expr_Data_hasLevelMVar(v_c_boxed_431_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t v_c_434_){
_start:
{
uint64_t v___x_435_; uint64_t v___x_436_; uint64_t v___x_437_; uint64_t v___x_438_; uint8_t v___x_439_; 
v___x_435_ = 43ULL;
v___x_436_ = lean_uint64_shift_right(v_c_434_, v___x_435_);
v___x_437_ = 1ULL;
v___x_438_ = lean_uint64_land(v___x_436_, v___x_437_);
v___x_439_ = lean_uint64_dec_eq(v___x_438_, v___x_437_);
return v___x_439_;
}
}
LEAN_EXPORT void l_Lean_Expr_Data_hasLevelParam_0interp(lean_interpreter_value* stack)
{
uint64_t v_c_434_ = stack[0].m_num;
uint8_t v_res_440_;
v_res_440_ = l_Lean_Expr_Data_hasLevelParam(v_c_434_);
stack->m_num = v_res_440_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object* v_c_441_){
_start:
{
uint64_t v_c_boxed_442_; uint8_t v_res_443_; lean_object* v_r_444_; 
v_c_boxed_442_ = lean_unbox_uint64(v_c_441_);
lean_dec_ref(v_c_441_);
v_res_443_ = l_Lean_Expr_Data_hasLevelParam(v_c_boxed_442_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT void l_Lean_BinderInfo_toUInt64_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_00___x40___internal___hyg_445_ = stack[0].m_num;
uint64_t v_res_446_;
v_res_446_ = lean_uint8_to_uint64(v_a_00___x40___internal___hyg_445_);
stack->m_num = v_res_446_;
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_447_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_448_; uint64_t v_res_449_; lean_object* v_r_450_; 
v_a_00___x40___internal___hyg_1__boxed_448_ = lean_unbox(v_a_00___x40___internal___hyg_447_);
v_res_449_ = lean_uint8_to_uint64(v_a_00___x40___internal___hyg_1__boxed_448_);
v_r_450_ = lean_box_uint64(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT void l_Lean_Expr_mkData_0interp(lean_interpreter_value* stack)
{
uint64_t v_h_451_ = stack[0].m_num;
lean_object* v_looseBVarRange_452_ = stack[1].m_obj;
uint32_t v_approxDepth_453_ = stack[2].m_num;
uint8_t v_hasFVar_454_ = stack[3].m_num;
uint8_t v_hasExprMVar_455_ = stack[4].m_num;
uint8_t v_hasLevelMVar_456_ = stack[5].m_num;
uint8_t v_hasLevelParam_457_ = stack[6].m_num;
uint64_t v_res_458_;
v_res_458_ = lean_expr_mk_data(v_h_451_, v_looseBVarRange_452_, v_approxDepth_453_, v_hasFVar_454_, v_hasExprMVar_455_, v_hasLevelMVar_456_, v_hasLevelParam_457_);
stack->m_num = v_res_458_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object* v_h_459_, lean_object* v_looseBVarRange_460_, lean_object* v_approxDepth_461_, lean_object* v_hasFVar_462_, lean_object* v_hasExprMVar_463_, lean_object* v_hasLevelMVar_464_, lean_object* v_hasLevelParam_465_){
_start:
{
uint64_t v_h_boxed_466_; uint32_t v_approxDepth_boxed_467_; uint8_t v_hasFVar_boxed_468_; uint8_t v_hasExprMVar_boxed_469_; uint8_t v_hasLevelMVar_boxed_470_; uint8_t v_hasLevelParam_boxed_471_; uint64_t v_res_472_; lean_object* v_r_473_; 
v_h_boxed_466_ = lean_unbox_uint64(v_h_459_);
lean_dec_ref(v_h_459_);
v_approxDepth_boxed_467_ = lean_unbox_uint32(v_approxDepth_461_);
lean_dec(v_approxDepth_461_);
v_hasFVar_boxed_468_ = lean_unbox(v_hasFVar_462_);
v_hasExprMVar_boxed_469_ = lean_unbox(v_hasExprMVar_463_);
v_hasLevelMVar_boxed_470_ = lean_unbox(v_hasLevelMVar_464_);
v_hasLevelParam_boxed_471_ = lean_unbox(v_hasLevelParam_465_);
v_res_472_ = lean_expr_mk_data(v_h_boxed_466_, v_looseBVarRange_460_, v_approxDepth_boxed_467_, v_hasFVar_boxed_468_, v_hasExprMVar_boxed_469_, v_hasLevelMVar_boxed_470_, v_hasLevelParam_boxed_471_);
v_r_473_ = lean_box_uint64(v_res_472_);
return v_r_473_;
}
}
LEAN_EXPORT void l_Lean_Expr_mkAppData_0interp(lean_interpreter_value* stack)
{
uint64_t v_fData_474_ = stack[0].m_num;
uint64_t v_aData_475_ = stack[1].m_num;
uint64_t v_res_476_;
v_res_476_ = lean_expr_mk_app_data(v_fData_474_, v_aData_475_);
stack->m_num = v_res_476_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object* v_fData_477_, lean_object* v_aData_478_){
_start:
{
uint64_t v_fData_boxed_479_; uint64_t v_aData_boxed_480_; uint64_t v_res_481_; lean_object* v_r_482_; 
v_fData_boxed_479_ = lean_unbox_uint64(v_fData_477_);
lean_dec_ref(v_fData_477_);
v_aData_boxed_480_ = lean_unbox_uint64(v_aData_478_);
lean_dec_ref(v_aData_478_);
v_res_481_ = lean_expr_mk_app_data(v_fData_boxed_479_, v_aData_boxed_480_);
v_r_482_ = lean_box_uint64(v_res_481_);
return v_r_482_;
}
}
uint64_t l_Lean_Expr_mkDataForBinder(uint64_t v_h_483_, lean_object* v_looseBVarRange_484_, uint32_t v_approxDepth_485_, uint8_t v_hasFVar_486_, uint8_t v_hasExprMVar_487_, uint8_t v_hasLevelMVar_488_, uint8_t v_hasLevelParam_489_){
_start:
{
uint64_t v___x_490_; 
v___x_490_ = lean_expr_mk_data(v_h_483_, v_looseBVarRange_484_, v_approxDepth_485_, v_hasFVar_486_, v_hasExprMVar_487_, v_hasLevelMVar_488_, v_hasLevelParam_489_);
return v___x_490_;
}
}
LEAN_EXPORT void l_Lean_Expr_mkDataForBinder_0interp(lean_interpreter_value* stack)
{
uint64_t v_h_483_ = stack[0].m_num;
lean_object* v_looseBVarRange_484_ = stack[1].m_obj;
uint32_t v_approxDepth_485_ = stack[2].m_num;
uint8_t v_hasFVar_486_ = stack[3].m_num;
uint8_t v_hasExprMVar_487_ = stack[4].m_num;
uint8_t v_hasLevelMVar_488_ = stack[5].m_num;
uint8_t v_hasLevelParam_489_ = stack[6].m_num;
uint64_t v_res_491_;
v_res_491_ = l_Lean_Expr_mkDataForBinder(v_h_483_, v_looseBVarRange_484_, v_approxDepth_485_, v_hasFVar_486_, v_hasExprMVar_487_, v_hasLevelMVar_488_, v_hasLevelParam_489_);
stack->m_num = v_res_491_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object* v_h_492_, lean_object* v_looseBVarRange_493_, lean_object* v_approxDepth_494_, lean_object* v_hasFVar_495_, lean_object* v_hasExprMVar_496_, lean_object* v_hasLevelMVar_497_, lean_object* v_hasLevelParam_498_){
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
v_res_505_ = l_Lean_Expr_mkDataForBinder(v_h_boxed_499_, v_looseBVarRange_493_, v_approxDepth_boxed_500_, v_hasFVar_boxed_501_, v_hasExprMVar_boxed_502_, v_hasLevelMVar_boxed_503_, v_hasLevelParam_boxed_504_);
v_r_506_ = lean_box_uint64(v_res_505_);
return v_r_506_;
}
}
uint64_t l_Lean_Expr_mkDataForLet(uint64_t v_h_507_, lean_object* v_looseBVarRange_508_, uint32_t v_approxDepth_509_, uint8_t v_hasFVar_510_, uint8_t v_hasExprMVar_511_, uint8_t v_hasLevelMVar_512_, uint8_t v_hasLevelParam_513_){
_start:
{
uint64_t v___x_514_; 
v___x_514_ = lean_expr_mk_data(v_h_507_, v_looseBVarRange_508_, v_approxDepth_509_, v_hasFVar_510_, v_hasExprMVar_511_, v_hasLevelMVar_512_, v_hasLevelParam_513_);
return v___x_514_;
}
}
LEAN_EXPORT void l_Lean_Expr_mkDataForLet_0interp(lean_interpreter_value* stack)
{
uint64_t v_h_507_ = stack[0].m_num;
lean_object* v_looseBVarRange_508_ = stack[1].m_obj;
uint32_t v_approxDepth_509_ = stack[2].m_num;
uint8_t v_hasFVar_510_ = stack[3].m_num;
uint8_t v_hasExprMVar_511_ = stack[4].m_num;
uint8_t v_hasLevelMVar_512_ = stack[5].m_num;
uint8_t v_hasLevelParam_513_ = stack[6].m_num;
uint64_t v_res_515_;
v_res_515_ = l_Lean_Expr_mkDataForLet(v_h_507_, v_looseBVarRange_508_, v_approxDepth_509_, v_hasFVar_510_, v_hasExprMVar_511_, v_hasLevelMVar_512_, v_hasLevelParam_513_);
stack->m_num = v_res_515_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object* v_h_516_, lean_object* v_looseBVarRange_517_, lean_object* v_approxDepth_518_, lean_object* v_hasFVar_519_, lean_object* v_hasExprMVar_520_, lean_object* v_hasLevelMVar_521_, lean_object* v_hasLevelParam_522_){
_start:
{
uint64_t v_h_boxed_523_; uint32_t v_approxDepth_boxed_524_; uint8_t v_hasFVar_boxed_525_; uint8_t v_hasExprMVar_boxed_526_; uint8_t v_hasLevelMVar_boxed_527_; uint8_t v_hasLevelParam_boxed_528_; uint64_t v_res_529_; lean_object* v_r_530_; 
v_h_boxed_523_ = lean_unbox_uint64(v_h_516_);
lean_dec_ref(v_h_516_);
v_approxDepth_boxed_524_ = lean_unbox_uint32(v_approxDepth_518_);
lean_dec(v_approxDepth_518_);
v_hasFVar_boxed_525_ = lean_unbox(v_hasFVar_519_);
v_hasExprMVar_boxed_526_ = lean_unbox(v_hasExprMVar_520_);
v_hasLevelMVar_boxed_527_ = lean_unbox(v_hasLevelMVar_521_);
v_hasLevelParam_boxed_528_ = lean_unbox(v_hasLevelParam_522_);
v_res_529_ = l_Lean_Expr_mkDataForLet(v_h_boxed_523_, v_looseBVarRange_517_, v_approxDepth_boxed_524_, v_hasFVar_boxed_525_, v_hasExprMVar_boxed_526_, v_hasLevelMVar_boxed_527_, v_hasLevelParam_boxed_528_);
v_r_530_ = lean_box_uint64(v_res_529_);
return v_r_530_;
}
}
lean_object* l_Lean_instReprData__1___lam__0(uint64_t v_v_540_, lean_object* v_prec_541_){
_start:
{
lean_object* v_r_543_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v_r_553_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v_r_566_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v_r_579_; lean_object* v_r_586_; lean_object* v___x_597_; uint64_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v_r_601_; uint32_t v___x_602_; uint32_t v___x_603_; uint8_t v___x_604_; 
v___x_597_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__7));
v___x_598_ = l_Lean_Expr_Data_hash(v_v_540_);
v___x_599_ = lean_uint64_to_nat(v___x_598_);
v___x_600_ = l_Nat_reprFast(v___x_599_);
v_r_601_ = lean_string_append(v___x_597_, v___x_600_);
lean_dec_ref(v___x_600_);
v___x_602_ = l_Lean_Expr_Data_looseBVarRange(v_v_540_);
v___x_603_ = 0;
v___x_604_ = lean_uint32_dec_eq(v___x_602_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_r_611_; 
v___x_605_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__8));
v___x_606_ = lean_string_append(v_r_601_, v___x_605_);
v___x_607_ = lean_uint32_to_nat(v___x_602_);
v___x_608_ = l_Nat_reprFast(v___x_607_);
v___x_609_ = lean_string_append(v___x_606_, v___x_608_);
lean_dec_ref(v___x_608_);
v___x_610_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_611_ = lean_string_append(v___x_609_, v___x_610_);
v_r_586_ = v_r_611_;
goto v___jp_585_;
}
else
{
v_r_586_ = v_r_601_;
goto v___jp_585_;
}
v___jp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_544_, 0, v_r_543_);
v___x_545_ = l_Repr_addAppParen(v___x_544_, v_prec_541_);
return v___x_545_;
}
v___jp_546_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v_r_551_; 
v___x_549_ = lean_string_append(v___y_547_, v___y_548_);
v___x_550_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_551_ = lean_string_append(v___x_549_, v___x_550_);
v_r_543_ = v_r_551_;
goto v___jp_542_;
}
v___jp_552_:
{
uint8_t v___x_554_; 
v___x_554_ = l_Lean_Expr_Data_hasLevelMVar(v_v_540_);
if (v___x_554_ == 0)
{
v_r_543_ = v_r_553_;
goto v___jp_542_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
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
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v_r_564_; 
v___x_562_ = lean_string_append(v___y_560_, v___y_561_);
v___x_563_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_564_ = lean_string_append(v___x_562_, v___x_563_);
v_r_553_ = v_r_564_;
goto v___jp_552_;
}
v___jp_565_:
{
uint8_t v___x_567_; 
v___x_567_ = l_Lean_Expr_Data_hasExprMVar(v_v_540_);
if (v___x_567_ == 0)
{
v_r_553_ = v_r_566_;
goto v___jp_552_;
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__4));
v___x_569_ = lean_string_append(v_r_566_, v___x_568_);
if (v___x_567_ == 0)
{
lean_object* v___x_570_; 
v___x_570_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_560_ = v___x_569_;
v___y_561_ = v___x_570_;
goto v___jp_559_;
}
else
{
lean_object* v___x_571_; 
v___x_571_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_560_ = v___x_569_;
v___y_561_ = v___x_571_;
goto v___jp_559_;
}
}
}
v___jp_572_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v_r_577_; 
v___x_575_ = lean_string_append(v___y_573_, v___y_574_);
v___x_576_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_577_ = lean_string_append(v___x_575_, v___x_576_);
v_r_566_ = v_r_577_;
goto v___jp_565_;
}
v___jp_578_:
{
uint8_t v___x_580_; 
v___x_580_ = l_Lean_Expr_Data_hasFVar(v_v_540_);
if (v___x_580_ == 0)
{
v_r_566_ = v_r_579_;
goto v___jp_565_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__5));
v___x_582_ = lean_string_append(v_r_579_, v___x_581_);
if (v___x_580_ == 0)
{
lean_object* v___x_583_; 
v___x_583_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_573_ = v___x_582_;
v___y_574_ = v___x_583_;
goto v___jp_572_;
}
else
{
lean_object* v___x_584_; 
v___x_584_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_573_ = v___x_582_;
v___y_574_ = v___x_584_;
goto v___jp_572_;
}
}
}
v___jp_585_:
{
uint8_t v___x_587_; uint8_t v___x_588_; uint8_t v___x_589_; 
v___x_587_ = l_Lean_Expr_Data_approxDepth(v_v_540_);
v___x_588_ = 0;
v___x_589_ = lean_uint8_dec_eq(v___x_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v_r_596_; 
v___x_590_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__6));
v___x_591_ = lean_string_append(v_r_586_, v___x_590_);
v___x_592_ = lean_uint8_to_nat(v___x_587_);
v___x_593_ = l_Nat_reprFast(v___x_592_);
v___x_594_ = lean_string_append(v___x_591_, v___x_593_);
lean_dec_ref(v___x_593_);
v___x_595_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_596_ = lean_string_append(v___x_594_, v___x_595_);
v_r_579_ = v_r_596_;
goto v___jp_578_;
}
else
{
v_r_579_ = v_r_586_;
goto v___jp_578_;
}
}
}
}
LEAN_EXPORT void l_Lean_instReprData__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_v_540_ = stack[0].m_num;
lean_object* v_prec_541_ = stack[1].m_obj;
lean_object* v_res_612_;
v_res_612_ = l_Lean_instReprData__1___lam__0(v_v_540_, v_prec_541_);
stack->m_obj
 = v_res_612_;
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0___boxed(lean_object* v_v_613_, lean_object* v_prec_614_){
_start:
{
uint64_t v_v_boxed_615_; lean_object* v_res_616_; 
v_v_boxed_615_ = lean_unbox_uint64(v_v_613_);
lean_dec_ref(v_v_613_);
v_res_616_ = l_Lean_instReprData__1___lam__0(v_v_boxed_615_, v_prec_614_);
lean_dec(v_prec_614_);
return v_res_616_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId_default(void){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = lean_box(0);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId(void){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lean_box(0);
return v___x_620_;
}
}
uint8_t l_Lean_instBEqFVarId_beq(lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_name_eq(v_x_621_, v_x_622_);
return v___x_623_;
}
}
LEAN_EXPORT void l_Lean_instBEqFVarId_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_621_ = stack[0].m_obj;
lean_object* v_x_622_ = stack[1].m_obj;
uint8_t v_res_624_;
v_res_624_ = l_Lean_instBEqFVarId_beq(v_x_621_, v_x_622_);
stack->m_num = v_res_624_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
uint8_t v_res_627_; lean_object* v_r_628_; 
v_res_627_ = l_Lean_instBEqFVarId_beq(v_x_625_, v_x_626_);
lean_dec(v_x_626_);
lean_dec(v_x_625_);
v_r_628_ = lean_box(v_res_627_);
return v_r_628_;
}
}
uint64_t l_Lean_instHashableFVarId_hash(lean_object* v_x_631_){
_start:
{
uint64_t v___x_632_; 
v___x_632_ = 0ULL;
if (lean_obj_tag(v_x_631_) == 0)
{
uint64_t v___x_633_; 
v___x_633_ = 8934034000889494153ULL;
return v___x_633_;
}
else
{
uint64_t v_hash_634_; uint64_t v___x_635_; 
v_hash_634_ = lean_ctor_get_uint64(v_x_631_, sizeof(void*)*2);
v___x_635_ = lean_uint64_mix_hash(v___x_632_, v_hash_634_);
return v___x_635_;
}
}
}
LEAN_EXPORT void l_Lean_instHashableFVarId_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_631_ = stack[0].m_obj;
uint64_t v_res_636_;
v_res_636_ = l_Lean_instHashableFVarId_hash(v_x_631_);
stack->m_num = v_res_636_;
}
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object* v_x_637_){
_start:
{
uint64_t v_res_638_; lean_object* v_r_639_; 
v_res_638_ = l_Lean_instHashableFVarId_hash(v_x_637_);
lean_dec(v_x_637_);
v_r_639_ = lean_box_uint64(v_res_638_);
return v_r_639_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = lean_box(1);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet(void){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = lean_box(1);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = lean_box(1);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet(void){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = lean_box(1);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___aux__1(lean_object* v_e_649_){
_start:
{
lean_object* v___f_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___f_650_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_651_ = lean_box(1);
lean_inc(v_e_649_);
v___x_652_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___f_650_, v_e_649_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_box(0);
v___x_654_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_650_, v_e_649_, v___x_653_, v___x_651_);
return v___x_654_;
}
else
{
lean_dec(v_e_649_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object* v_k_655_, lean_object* v_v_656_, lean_object* v_t_657_){
_start:
{
if (lean_obj_tag(v_t_657_) == 0)
{
lean_object* v_size_658_; lean_object* v_k_659_; lean_object* v_v_660_; lean_object* v_l_661_; lean_object* v_r_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_942_; 
v_size_658_ = lean_ctor_get(v_t_657_, 0);
v_k_659_ = lean_ctor_get(v_t_657_, 1);
v_v_660_ = lean_ctor_get(v_t_657_, 2);
v_l_661_ = lean_ctor_get(v_t_657_, 3);
v_r_662_ = lean_ctor_get(v_t_657_, 4);
v_isSharedCheck_942_ = !lean_is_exclusive(v_t_657_);
if (v_isSharedCheck_942_ == 0)
{
v___x_664_ = v_t_657_;
v_isShared_665_ = v_isSharedCheck_942_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_r_662_);
lean_inc(v_l_661_);
lean_inc(v_v_660_);
lean_inc(v_k_659_);
lean_inc(v_size_658_);
lean_dec(v_t_657_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_942_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
uint8_t v___x_666_; 
v___x_666_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_655_, v_k_659_);
switch(v___x_666_)
{
case 0:
{
lean_object* v_impl_667_; lean_object* v___x_668_; 
lean_dec(v_size_658_);
v_impl_667_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_655_, v_v_656_, v_l_661_);
v___x_668_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_662_) == 0)
{
lean_object* v_size_669_; lean_object* v_size_670_; lean_object* v_k_671_; lean_object* v_v_672_; lean_object* v_l_673_; lean_object* v_r_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_size_669_ = lean_ctor_get(v_r_662_, 0);
v_size_670_ = lean_ctor_get(v_impl_667_, 0);
v_k_671_ = lean_ctor_get(v_impl_667_, 1);
v_v_672_ = lean_ctor_get(v_impl_667_, 2);
v_l_673_ = lean_ctor_get(v_impl_667_, 3);
v_r_674_ = lean_ctor_get(v_impl_667_, 4);
lean_inc(v_r_674_);
v___x_675_ = lean_unsigned_to_nat(3u);
v___x_676_ = lean_nat_mul(v___x_675_, v_size_669_);
v___x_677_ = lean_nat_dec_lt(v___x_676_, v_size_670_);
lean_dec(v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
lean_dec(v_r_674_);
v___x_678_ = lean_nat_add(v___x_668_, v_size_670_);
v___x_679_ = lean_nat_add(v___x_678_, v_size_669_);
lean_dec(v___x_678_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 3, v_impl_667_);
lean_ctor_set(v___x_664_, 0, v___x_679_);
v___x_681_ = v___x_664_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_impl_667_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_r_662_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
else
{
lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_748_; 
lean_inc(v_l_673_);
lean_inc(v_v_672_);
lean_inc(v_k_671_);
lean_inc(v_size_670_);
v_isSharedCheck_748_ = !lean_is_exclusive(v_impl_667_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; lean_object* v_unused_750_; lean_object* v_unused_751_; lean_object* v_unused_752_; lean_object* v_unused_753_; 
v_unused_749_ = lean_ctor_get(v_impl_667_, 4);
lean_dec(v_unused_749_);
v_unused_750_ = lean_ctor_get(v_impl_667_, 3);
lean_dec(v_unused_750_);
v_unused_751_ = lean_ctor_get(v_impl_667_, 2);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_impl_667_, 1);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_impl_667_, 0);
lean_dec(v_unused_753_);
v___x_684_ = v_impl_667_;
v_isShared_685_ = v_isSharedCheck_748_;
goto v_resetjp_683_;
}
else
{
lean_dec(v_impl_667_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_748_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v_size_686_; lean_object* v_size_687_; lean_object* v_k_688_; lean_object* v_v_689_; lean_object* v_l_690_; lean_object* v_r_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_size_686_ = lean_ctor_get(v_l_673_, 0);
v_size_687_ = lean_ctor_get(v_r_674_, 0);
v_k_688_ = lean_ctor_get(v_r_674_, 1);
v_v_689_ = lean_ctor_get(v_r_674_, 2);
v_l_690_ = lean_ctor_get(v_r_674_, 3);
v_r_691_ = lean_ctor_get(v_r_674_, 4);
v___x_692_ = lean_unsigned_to_nat(2u);
v___x_693_ = lean_nat_mul(v___x_692_, v_size_686_);
v___x_694_ = lean_nat_dec_lt(v_size_687_, v___x_693_);
lean_dec(v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_723_; 
lean_inc(v_r_691_);
lean_inc(v_l_690_);
lean_inc(v_v_689_);
lean_inc(v_k_688_);
v_isSharedCheck_723_ = !lean_is_exclusive(v_r_674_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; lean_object* v_unused_725_; lean_object* v_unused_726_; lean_object* v_unused_727_; lean_object* v_unused_728_; 
v_unused_724_ = lean_ctor_get(v_r_674_, 4);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v_r_674_, 3);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_r_674_, 2);
lean_dec(v_unused_726_);
v_unused_727_ = lean_ctor_get(v_r_674_, 1);
lean_dec(v_unused_727_);
v_unused_728_ = lean_ctor_get(v_r_674_, 0);
lean_dec(v_unused_728_);
v___x_696_ = v_r_674_;
v_isShared_697_ = v_isSharedCheck_723_;
goto v_resetjp_695_;
}
else
{
lean_dec(v_r_674_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_723_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___x_711_; lean_object* v___y_713_; 
v___x_698_ = lean_nat_add(v___x_668_, v_size_670_);
lean_dec(v_size_670_);
v___x_699_ = lean_nat_add(v___x_698_, v_size_669_);
lean_dec(v___x_698_);
v___x_711_ = lean_nat_add(v___x_668_, v_size_686_);
if (lean_obj_tag(v_l_690_) == 0)
{
lean_object* v_size_721_; 
v_size_721_ = lean_ctor_get(v_l_690_, 0);
lean_inc(v_size_721_);
v___y_713_ = v_size_721_;
goto v___jp_712_;
}
else
{
lean_object* v___x_722_; 
v___x_722_ = lean_unsigned_to_nat(0u);
v___y_713_ = v___x_722_;
goto v___jp_712_;
}
v___jp_700_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_nat_add(v___y_701_, v___y_703_);
lean_dec(v___y_703_);
lean_dec(v___y_701_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 4, v_r_662_);
lean_ctor_set(v___x_696_, 3, v_r_691_);
lean_ctor_set(v___x_696_, 2, v_v_660_);
lean_ctor_set(v___x_696_, 1, v_k_659_);
lean_ctor_set(v___x_696_, 0, v___x_704_);
v___x_706_ = v___x_696_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_r_691_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v_r_662_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 4, v___x_706_);
lean_ctor_set(v___x_684_, 3, v___y_702_);
lean_ctor_set(v___x_684_, 2, v_v_689_);
lean_ctor_set(v___x_684_, 1, v_k_688_);
lean_ctor_set(v___x_684_, 0, v___x_699_);
v___x_708_ = v___x_684_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_k_688_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v_v_689_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v___y_702_);
lean_ctor_set(v_reuseFailAlloc_709_, 4, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
v___jp_712_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_nat_add(v___x_711_, v___y_713_);
lean_dec(v___y_713_);
lean_dec(v___x_711_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v_l_690_);
lean_ctor_set(v___x_664_, 3, v_l_673_);
lean_ctor_set(v___x_664_, 2, v_v_672_);
lean_ctor_set(v___x_664_, 1, v_k_671_);
lean_ctor_set(v___x_664_, 0, v___x_714_);
v___x_716_ = v___x_664_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_k_671_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_v_672_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v_l_673_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v_l_690_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_717_; 
v___x_717_ = lean_nat_add(v___x_668_, v_size_669_);
if (lean_obj_tag(v_r_691_) == 0)
{
lean_object* v_size_718_; 
v_size_718_ = lean_ctor_get(v_r_691_, 0);
lean_inc(v_size_718_);
v___y_701_ = v___x_717_;
v___y_702_ = v___x_716_;
v___y_703_ = v_size_718_;
goto v___jp_700_;
}
else
{
lean_object* v___x_719_; 
v___x_719_ = lean_unsigned_to_nat(0u);
v___y_701_ = v___x_717_;
v___y_702_ = v___x_716_;
v___y_703_ = v___x_719_;
goto v___jp_700_;
}
}
}
}
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
lean_del_object(v___x_664_);
v___x_729_ = lean_nat_add(v___x_668_, v_size_670_);
lean_dec(v_size_670_);
v___x_730_ = lean_nat_add(v___x_729_, v_size_669_);
lean_dec(v___x_729_);
v___x_731_ = lean_nat_add(v___x_668_, v_size_669_);
v___x_732_ = lean_nat_add(v___x_731_, v_size_687_);
lean_dec(v___x_731_);
lean_inc_ref(v_r_662_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 4, v_r_662_);
lean_ctor_set(v___x_684_, 3, v_r_674_);
lean_ctor_set(v___x_684_, 2, v_v_660_);
lean_ctor_set(v___x_684_, 1, v_k_659_);
lean_ctor_set(v___x_684_, 0, v___x_732_);
v___x_734_ = v___x_684_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_r_674_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_r_662_);
v___x_734_ = v_reuseFailAlloc_747_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
v_isSharedCheck_741_ = !lean_is_exclusive(v_r_662_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; lean_object* v_unused_743_; lean_object* v_unused_744_; lean_object* v_unused_745_; lean_object* v_unused_746_; 
v_unused_742_ = lean_ctor_get(v_r_662_, 4);
lean_dec(v_unused_742_);
v_unused_743_ = lean_ctor_get(v_r_662_, 3);
lean_dec(v_unused_743_);
v_unused_744_ = lean_ctor_get(v_r_662_, 2);
lean_dec(v_unused_744_);
v_unused_745_ = lean_ctor_get(v_r_662_, 1);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v_r_662_, 0);
lean_dec(v_unused_746_);
v___x_736_ = v_r_662_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_dec(v_r_662_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 4, v___x_734_);
lean_ctor_set(v___x_736_, 3, v_l_673_);
lean_ctor_set(v___x_736_, 2, v_v_672_);
lean_ctor_set(v___x_736_, 1, v_k_671_);
lean_ctor_set(v___x_736_, 0, v___x_730_);
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_k_671_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_v_672_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v_l_673_);
lean_ctor_set(v_reuseFailAlloc_740_, 4, v___x_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_754_; 
v_l_754_ = lean_ctor_get(v_impl_667_, 3);
if (lean_obj_tag(v_l_754_) == 0)
{
lean_object* v_r_755_; lean_object* v_k_756_; lean_object* v_v_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_768_; 
lean_inc_ref(v_l_754_);
v_r_755_ = lean_ctor_get(v_impl_667_, 4);
v_k_756_ = lean_ctor_get(v_impl_667_, 1);
v_v_757_ = lean_ctor_get(v_impl_667_, 2);
v_isSharedCheck_768_ = !lean_is_exclusive(v_impl_667_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; lean_object* v_unused_770_; 
v_unused_769_ = lean_ctor_get(v_impl_667_, 3);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_impl_667_, 0);
lean_dec(v_unused_770_);
v___x_759_ = v_impl_667_;
v_isShared_760_ = v_isSharedCheck_768_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_r_755_);
lean_inc(v_v_757_);
lean_inc(v_k_756_);
lean_dec(v_impl_667_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_768_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_755_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 3, v_r_755_);
lean_ctor_set(v___x_759_, 2, v_v_660_);
lean_ctor_set(v___x_759_, 1, v_k_659_);
lean_ctor_set(v___x_759_, 0, v___x_668_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_r_755_);
lean_ctor_set(v_reuseFailAlloc_767_, 4, v_r_755_);
v___x_763_ = v_reuseFailAlloc_767_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_765_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v___x_763_);
lean_ctor_set(v___x_664_, 3, v_l_754_);
lean_ctor_set(v___x_664_, 2, v_v_757_);
lean_ctor_set(v___x_664_, 1, v_k_756_);
lean_ctor_set(v___x_664_, 0, v___x_761_);
v___x_765_ = v___x_664_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_k_756_);
lean_ctor_set(v_reuseFailAlloc_766_, 2, v_v_757_);
lean_ctor_set(v_reuseFailAlloc_766_, 3, v_l_754_);
lean_ctor_set(v_reuseFailAlloc_766_, 4, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v_r_771_; 
v_r_771_ = lean_ctor_get(v_impl_667_, 4);
lean_inc(v_r_771_);
if (lean_obj_tag(v_r_771_) == 0)
{
lean_object* v_k_772_; lean_object* v_v_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_796_; 
lean_inc(v_l_754_);
v_k_772_ = lean_ctor_get(v_impl_667_, 1);
v_v_773_ = lean_ctor_get(v_impl_667_, 2);
v_isSharedCheck_796_ = !lean_is_exclusive(v_impl_667_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; lean_object* v_unused_798_; lean_object* v_unused_799_; 
v_unused_797_ = lean_ctor_get(v_impl_667_, 4);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_impl_667_, 3);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_impl_667_, 0);
lean_dec(v_unused_799_);
v___x_775_ = v_impl_667_;
v_isShared_776_ = v_isSharedCheck_796_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_v_773_);
lean_inc(v_k_772_);
lean_dec(v_impl_667_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_796_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_k_777_; lean_object* v_v_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_792_; 
v_k_777_ = lean_ctor_get(v_r_771_, 1);
v_v_778_ = lean_ctor_get(v_r_771_, 2);
v_isSharedCheck_792_ = !lean_is_exclusive(v_r_771_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; lean_object* v_unused_794_; lean_object* v_unused_795_; 
v_unused_793_ = lean_ctor_get(v_r_771_, 4);
lean_dec(v_unused_793_);
v_unused_794_ = lean_ctor_get(v_r_771_, 3);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_r_771_, 0);
lean_dec(v_unused_795_);
v___x_780_ = v_r_771_;
v_isShared_781_ = v_isSharedCheck_792_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_v_778_);
lean_inc(v_k_777_);
lean_dec(v_r_771_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_792_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_unsigned_to_nat(3u);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 4, v_l_754_);
lean_ctor_set(v___x_780_, 3, v_l_754_);
lean_ctor_set(v___x_780_, 2, v_v_773_);
lean_ctor_set(v___x_780_, 1, v_k_772_);
lean_ctor_set(v___x_780_, 0, v___x_668_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_k_772_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_v_773_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_l_754_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_l_754_);
v___x_784_ = v_reuseFailAlloc_791_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_786_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 4, v_l_754_);
lean_ctor_set(v___x_775_, 2, v_v_660_);
lean_ctor_set(v___x_775_, 1, v_k_659_);
lean_ctor_set(v___x_775_, 0, v___x_668_);
v___x_786_ = v___x_775_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_790_, 3, v_l_754_);
lean_ctor_set(v_reuseFailAlloc_790_, 4, v_l_754_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v___x_786_);
lean_ctor_set(v___x_664_, 3, v___x_784_);
lean_ctor_set(v___x_664_, 2, v_v_778_);
lean_ctor_set(v___x_664_, 1, v_k_777_);
lean_ctor_set(v___x_664_, 0, v___x_782_);
v___x_788_ = v___x_664_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_k_777_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_v_778_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_789_, 4, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
else
{
lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_800_ = lean_unsigned_to_nat(2u);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v_r_771_);
lean_ctor_set(v___x_664_, 3, v_impl_667_);
lean_ctor_set(v___x_664_, 0, v___x_800_);
v___x_802_ = v___x_664_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_803_, 3, v_impl_667_);
lean_ctor_set(v_reuseFailAlloc_803_, 4, v_r_771_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
case 1:
{
lean_object* v___x_805_; 
lean_dec(v_v_660_);
lean_dec(v_k_659_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 2, v_v_656_);
lean_ctor_set(v___x_664_, 1, v_k_655_);
v___x_805_ = v___x_664_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_size_658_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_k_655_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_v_656_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v_l_661_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v_r_662_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
default: 
{
lean_object* v_impl_807_; lean_object* v___x_808_; 
lean_dec(v_size_658_);
v_impl_807_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_655_, v_v_656_, v_r_662_);
v___x_808_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_661_) == 0)
{
lean_object* v_size_809_; lean_object* v_size_810_; lean_object* v_k_811_; lean_object* v_v_812_; lean_object* v_l_813_; lean_object* v_r_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_size_809_ = lean_ctor_get(v_l_661_, 0);
v_size_810_ = lean_ctor_get(v_impl_807_, 0);
v_k_811_ = lean_ctor_get(v_impl_807_, 1);
v_v_812_ = lean_ctor_get(v_impl_807_, 2);
v_l_813_ = lean_ctor_get(v_impl_807_, 3);
lean_inc(v_l_813_);
v_r_814_ = lean_ctor_get(v_impl_807_, 4);
v___x_815_ = lean_unsigned_to_nat(3u);
v___x_816_ = lean_nat_mul(v___x_815_, v_size_809_);
v___x_817_ = lean_nat_dec_lt(v___x_816_, v_size_810_);
lean_dec(v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
lean_dec(v_l_813_);
v___x_818_ = lean_nat_add(v___x_808_, v_size_809_);
v___x_819_ = lean_nat_add(v___x_818_, v_size_810_);
lean_dec(v___x_818_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v_impl_807_);
lean_ctor_set(v___x_664_, 0, v___x_819_);
v___x_821_ = v___x_664_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v_l_661_);
lean_ctor_set(v_reuseFailAlloc_822_, 4, v_impl_807_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_886_; 
lean_inc(v_r_814_);
lean_inc(v_v_812_);
lean_inc(v_k_811_);
lean_inc(v_size_810_);
v_isSharedCheck_886_ = !lean_is_exclusive(v_impl_807_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; lean_object* v_unused_888_; lean_object* v_unused_889_; lean_object* v_unused_890_; lean_object* v_unused_891_; 
v_unused_887_ = lean_ctor_get(v_impl_807_, 4);
lean_dec(v_unused_887_);
v_unused_888_ = lean_ctor_get(v_impl_807_, 3);
lean_dec(v_unused_888_);
v_unused_889_ = lean_ctor_get(v_impl_807_, 2);
lean_dec(v_unused_889_);
v_unused_890_ = lean_ctor_get(v_impl_807_, 1);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_impl_807_, 0);
lean_dec(v_unused_891_);
v___x_824_ = v_impl_807_;
v_isShared_825_ = v_isSharedCheck_886_;
goto v_resetjp_823_;
}
else
{
lean_dec(v_impl_807_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_886_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_size_826_; lean_object* v_k_827_; lean_object* v_v_828_; lean_object* v_l_829_; lean_object* v_r_830_; lean_object* v_size_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_size_826_ = lean_ctor_get(v_l_813_, 0);
v_k_827_ = lean_ctor_get(v_l_813_, 1);
v_v_828_ = lean_ctor_get(v_l_813_, 2);
v_l_829_ = lean_ctor_get(v_l_813_, 3);
v_r_830_ = lean_ctor_get(v_l_813_, 4);
v_size_831_ = lean_ctor_get(v_r_814_, 0);
v___x_832_ = lean_unsigned_to_nat(2u);
v___x_833_ = lean_nat_mul(v___x_832_, v_size_831_);
v___x_834_ = lean_nat_dec_lt(v_size_826_, v___x_833_);
lean_dec(v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_862_; 
lean_inc(v_r_830_);
lean_inc(v_l_829_);
lean_inc(v_v_828_);
lean_inc(v_k_827_);
v_isSharedCheck_862_ = !lean_is_exclusive(v_l_813_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; lean_object* v_unused_864_; lean_object* v_unused_865_; lean_object* v_unused_866_; lean_object* v_unused_867_; 
v_unused_863_ = lean_ctor_get(v_l_813_, 4);
lean_dec(v_unused_863_);
v_unused_864_ = lean_ctor_get(v_l_813_, 3);
lean_dec(v_unused_864_);
v_unused_865_ = lean_ctor_get(v_l_813_, 2);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_l_813_, 1);
lean_dec(v_unused_866_);
v_unused_867_ = lean_ctor_get(v_l_813_, 0);
lean_dec(v_unused_867_);
v___x_836_ = v_l_813_;
v_isShared_837_ = v_isSharedCheck_862_;
goto v_resetjp_835_;
}
else
{
lean_dec(v_l_813_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_862_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_852_; 
v___x_838_ = lean_nat_add(v___x_808_, v_size_809_);
v___x_839_ = lean_nat_add(v___x_838_, v_size_810_);
lean_dec(v_size_810_);
if (lean_obj_tag(v_l_829_) == 0)
{
lean_object* v_size_860_; 
v_size_860_ = lean_ctor_get(v_l_829_, 0);
lean_inc(v_size_860_);
v___y_852_ = v_size_860_;
goto v___jp_851_;
}
else
{
lean_object* v___x_861_; 
v___x_861_ = lean_unsigned_to_nat(0u);
v___y_852_ = v___x_861_;
goto v___jp_851_;
}
v___jp_840_:
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = lean_nat_add(v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec(v___y_842_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 4, v_r_814_);
lean_ctor_set(v___x_836_, 3, v_r_830_);
lean_ctor_set(v___x_836_, 2, v_v_812_);
lean_ctor_set(v___x_836_, 1, v_k_811_);
lean_ctor_set(v___x_836_, 0, v___x_844_);
v___x_846_ = v___x_836_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_k_811_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_v_812_);
lean_ctor_set(v_reuseFailAlloc_850_, 3, v_r_830_);
lean_ctor_set(v_reuseFailAlloc_850_, 4, v_r_814_);
v___x_846_ = v_reuseFailAlloc_850_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_848_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 4, v___x_846_);
lean_ctor_set(v___x_824_, 3, v___y_841_);
lean_ctor_set(v___x_824_, 2, v_v_828_);
lean_ctor_set(v___x_824_, 1, v_k_827_);
lean_ctor_set(v___x_824_, 0, v___x_839_);
v___x_848_ = v___x_824_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_k_827_);
lean_ctor_set(v_reuseFailAlloc_849_, 2, v_v_828_);
lean_ctor_set(v_reuseFailAlloc_849_, 3, v___y_841_);
lean_ctor_set(v_reuseFailAlloc_849_, 4, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
v___jp_851_:
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = lean_nat_add(v___x_838_, v___y_852_);
lean_dec(v___y_852_);
lean_dec(v___x_838_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v_l_829_);
lean_ctor_set(v___x_664_, 0, v___x_853_);
v___x_855_ = v___x_664_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_859_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_859_, 3, v_l_661_);
lean_ctor_set(v_reuseFailAlloc_859_, 4, v_l_829_);
v___x_855_ = v_reuseFailAlloc_859_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; 
v___x_856_ = lean_nat_add(v___x_808_, v_size_831_);
if (lean_obj_tag(v_r_830_) == 0)
{
lean_object* v_size_857_; 
v_size_857_ = lean_ctor_get(v_r_830_, 0);
lean_inc(v_size_857_);
v___y_841_ = v___x_855_;
v___y_842_ = v___x_856_;
v___y_843_ = v_size_857_;
goto v___jp_840_;
}
else
{
lean_object* v___x_858_; 
v___x_858_ = lean_unsigned_to_nat(0u);
v___y_841_ = v___x_855_;
v___y_842_ = v___x_856_;
v___y_843_ = v___x_858_;
goto v___jp_840_;
}
}
}
}
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
lean_del_object(v___x_664_);
v___x_868_ = lean_nat_add(v___x_808_, v_size_809_);
v___x_869_ = lean_nat_add(v___x_868_, v_size_810_);
lean_dec(v_size_810_);
v___x_870_ = lean_nat_add(v___x_868_, v_size_826_);
lean_dec(v___x_868_);
lean_inc_ref(v_l_661_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 4, v_l_813_);
lean_ctor_set(v___x_824_, 3, v_l_661_);
lean_ctor_set(v___x_824_, 2, v_v_660_);
lean_ctor_set(v___x_824_, 1, v_k_659_);
lean_ctor_set(v___x_824_, 0, v___x_870_);
v___x_872_ = v___x_824_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_885_, 3, v_l_661_);
lean_ctor_set(v_reuseFailAlloc_885_, 4, v_l_813_);
v___x_872_ = v_reuseFailAlloc_885_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v_isSharedCheck_879_ = !lean_is_exclusive(v_l_661_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; lean_object* v_unused_881_; lean_object* v_unused_882_; lean_object* v_unused_883_; lean_object* v_unused_884_; 
v_unused_880_ = lean_ctor_get(v_l_661_, 4);
lean_dec(v_unused_880_);
v_unused_881_ = lean_ctor_get(v_l_661_, 3);
lean_dec(v_unused_881_);
v_unused_882_ = lean_ctor_get(v_l_661_, 2);
lean_dec(v_unused_882_);
v_unused_883_ = lean_ctor_get(v_l_661_, 1);
lean_dec(v_unused_883_);
v_unused_884_ = lean_ctor_get(v_l_661_, 0);
lean_dec(v_unused_884_);
v___x_874_ = v_l_661_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_dec(v_l_661_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 4, v_r_814_);
lean_ctor_set(v___x_874_, 3, v___x_872_);
lean_ctor_set(v___x_874_, 2, v_v_812_);
lean_ctor_set(v___x_874_, 1, v_k_811_);
lean_ctor_set(v___x_874_, 0, v___x_869_);
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_k_811_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_v_812_);
lean_ctor_set(v_reuseFailAlloc_878_, 3, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_878_, 4, v_r_814_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_892_; 
v_l_892_ = lean_ctor_get(v_impl_807_, 3);
lean_inc(v_l_892_);
if (lean_obj_tag(v_l_892_) == 0)
{
lean_object* v_r_893_; lean_object* v_k_894_; lean_object* v_v_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_918_; 
v_r_893_ = lean_ctor_get(v_impl_807_, 4);
v_k_894_ = lean_ctor_get(v_impl_807_, 1);
v_v_895_ = lean_ctor_get(v_impl_807_, 2);
v_isSharedCheck_918_ = !lean_is_exclusive(v_impl_807_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; lean_object* v_unused_920_; 
v_unused_919_ = lean_ctor_get(v_impl_807_, 3);
lean_dec(v_unused_919_);
v_unused_920_ = lean_ctor_get(v_impl_807_, 0);
lean_dec(v_unused_920_);
v___x_897_ = v_impl_807_;
v_isShared_898_ = v_isSharedCheck_918_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_r_893_);
lean_inc(v_v_895_);
lean_inc(v_k_894_);
lean_dec(v_impl_807_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_918_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_k_899_; lean_object* v_v_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_914_; 
v_k_899_ = lean_ctor_get(v_l_892_, 1);
v_v_900_ = lean_ctor_get(v_l_892_, 2);
v_isSharedCheck_914_ = !lean_is_exclusive(v_l_892_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; lean_object* v_unused_916_; lean_object* v_unused_917_; 
v_unused_915_ = lean_ctor_get(v_l_892_, 4);
lean_dec(v_unused_915_);
v_unused_916_ = lean_ctor_get(v_l_892_, 3);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_l_892_, 0);
lean_dec(v_unused_917_);
v___x_902_ = v_l_892_;
v_isShared_903_ = v_isSharedCheck_914_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_v_900_);
lean_inc(v_k_899_);
lean_dec(v_l_892_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_914_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_893_, 2);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_r_893_);
lean_ctor_set(v___x_902_, 3, v_r_893_);
lean_ctor_set(v___x_902_, 2, v_v_660_);
lean_ctor_set(v___x_902_, 1, v_k_659_);
lean_ctor_set(v___x_902_, 0, v___x_808_);
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_r_893_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_r_893_);
v___x_906_ = v_reuseFailAlloc_913_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_908_; 
lean_inc(v_r_893_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 3, v_r_893_);
lean_ctor_set(v___x_897_, 0, v___x_808_);
v___x_908_ = v___x_897_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_k_894_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_v_895_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v_r_893_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v_r_893_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v___x_908_);
lean_ctor_set(v___x_664_, 3, v___x_906_);
lean_ctor_set(v___x_664_, 2, v_v_900_);
lean_ctor_set(v___x_664_, 1, v_k_899_);
lean_ctor_set(v___x_664_, 0, v___x_904_);
v___x_910_ = v___x_664_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_k_899_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_v_900_);
lean_ctor_set(v_reuseFailAlloc_911_, 3, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_911_, 4, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
}
else
{
lean_object* v_r_921_; 
v_r_921_ = lean_ctor_get(v_impl_807_, 4);
lean_inc(v_r_921_);
if (lean_obj_tag(v_r_921_) == 0)
{
lean_object* v_k_922_; lean_object* v_v_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_934_; 
v_k_922_ = lean_ctor_get(v_impl_807_, 1);
v_v_923_ = lean_ctor_get(v_impl_807_, 2);
v_isSharedCheck_934_ = !lean_is_exclusive(v_impl_807_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; lean_object* v_unused_936_; lean_object* v_unused_937_; 
v_unused_935_ = lean_ctor_get(v_impl_807_, 4);
lean_dec(v_unused_935_);
v_unused_936_ = lean_ctor_get(v_impl_807_, 3);
lean_dec(v_unused_936_);
v_unused_937_ = lean_ctor_get(v_impl_807_, 0);
lean_dec(v_unused_937_);
v___x_925_ = v_impl_807_;
v_isShared_926_ = v_isSharedCheck_934_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_v_923_);
lean_inc(v_k_922_);
lean_dec(v_impl_807_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_934_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_927_ = lean_unsigned_to_nat(3u);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 4, v_l_892_);
lean_ctor_set(v___x_925_, 2, v_v_660_);
lean_ctor_set(v___x_925_, 1, v_k_659_);
lean_ctor_set(v___x_925_, 0, v___x_808_);
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v_l_892_);
lean_ctor_set(v_reuseFailAlloc_933_, 4, v_l_892_);
v___x_929_ = v_reuseFailAlloc_933_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_931_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v_r_921_);
lean_ctor_set(v___x_664_, 3, v___x_929_);
lean_ctor_set(v___x_664_, 2, v_v_923_);
lean_ctor_set(v___x_664_, 1, v_k_922_);
lean_ctor_set(v___x_664_, 0, v___x_927_);
v___x_931_ = v___x_664_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_k_922_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_v_923_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v_r_921_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_938_ = lean_unsigned_to_nat(2u);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v_impl_807_);
lean_ctor_set(v___x_664_, 3, v_r_921_);
lean_ctor_set(v___x_664_, 0, v___x_938_);
v___x_940_ = v___x_664_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_r_921_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_impl_807_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
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
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_k_655_);
lean_ctor_set(v___x_944_, 2, v_v_656_);
lean_ctor_set(v___x_944_, 3, v_t_657_);
lean_ctor_set(v___x_944_, 4, v_t_657_);
return v___x_944_;
}
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(lean_object* v_k_945_, lean_object* v_t_946_){
_start:
{
if (lean_obj_tag(v_t_946_) == 0)
{
lean_object* v_k_947_; lean_object* v_l_948_; lean_object* v_r_949_; uint8_t v___x_950_; 
v_k_947_ = lean_ctor_get(v_t_946_, 1);
v_l_948_ = lean_ctor_get(v_t_946_, 3);
v_r_949_ = lean_ctor_get(v_t_946_, 4);
v___x_950_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_945_, v_k_947_);
switch(v___x_950_)
{
case 0:
{
v_t_946_ = v_l_948_;
goto _start;
}
case 1:
{
uint8_t v___x_952_; 
v___x_952_ = 1;
return v___x_952_;
}
default: 
{
v_t_946_ = v_r_949_;
goto _start;
}
}
}
else
{
uint8_t v___x_954_; 
v___x_954_ = 0;
return v___x_954_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_945_ = stack[0].m_obj;
lean_object* v_t_946_ = stack[1].m_obj;
uint8_t v_res_955_;
v_res_955_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_945_, v_t_946_);
stack->m_num = v_res_955_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg___boxed(lean_object* v_k_956_, lean_object* v_t_957_){
_start:
{
uint8_t v_res_958_; lean_object* v_r_959_; 
v_res_958_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_956_, v_t_957_);
lean_dec(v_t_957_);
lean_dec(v_k_956_);
v_r_959_ = lean_box(v_res_958_);
return v_r_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object* v___y_960_){
_start:
{
lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_961_ = lean_box(1);
v___x_962_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v___y_960_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_box(0);
v___x_964_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___y_960_, v___x_963_, v___x_961_);
return v___x_964_;
}
else
{
lean_dec(v___y_960_);
return v___x_961_;
}
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(lean_object* v_00_u03b2_967_, lean_object* v_k_968_, lean_object* v_t_969_){
_start:
{
uint8_t v___x_970_; 
v___x_970_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_968_, v_t_969_);
return v___x_970_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_968_ = stack[1].m_obj;
lean_object* v_t_969_ = stack[2].m_obj;
uint8_t v_res_971_;
v_res_971_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(lean_box(0), v_k_968_, v_t_969_);
stack->m_num = v_res_971_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___boxed(lean_object* v_00_u03b2_972_, lean_object* v_k_973_, lean_object* v_t_974_){
_start:
{
uint8_t v_res_975_; lean_object* v_r_976_; 
v_res_975_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(v_00_u03b2_972_, v_k_973_, v_t_974_);
lean_dec(v_t_974_);
lean_dec(v_k_973_);
v_r_976_ = lean_box(v_res_975_);
return v_r_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1(lean_object* v_00_u03b2_977_, lean_object* v_k_978_, lean_object* v_v_979_, lean_object* v_t_980_, lean_object* v_hl_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_978_, v_v_979_, v_t_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_983_, lean_object* v_a_984_, lean_object* v_b_985_, lean_object* v_c_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = lean_apply_2(v_f_983_, v_a_984_, v_c_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_988_, lean_object* v_____do__lift_989_){
_start:
{
lean_object* v_a_990_; lean_object* v___x_991_; 
v_a_990_ = lean_ctor_get(v_____do__lift_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref(v_____do__lift_989_);
v___x_991_ = lean_apply_2(v_toPure_988_, lean_box(0), v_a_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg(lean_object* v_inst_992_, lean_object* v_m_993_, lean_object* v_init_994_, lean_object* v_f_995_){
_start:
{
lean_object* v_toApplicative_996_; lean_object* v_toBind_997_; lean_object* v_toPure_998_; lean_object* v___f_999_; lean_object* v___x_1000_; lean_object* v___f_1001_; lean_object* v___x_1002_; 
v_toApplicative_996_ = lean_ctor_get(v_inst_992_, 0);
v_toBind_997_ = lean_ctor_get(v_inst_992_, 1);
lean_inc(v_toBind_997_);
v_toPure_998_ = lean_ctor_get(v_toApplicative_996_, 1);
lean_inc(v_toPure_998_);
v___f_999_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_999_, 0, v_f_995_);
v___x_1000_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_992_, v___f_999_, v_init_994_, v_m_993_);
v___f_1001_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1001_, 0, v_toPure_998_);
v___x_1002_ = lean_apply_4(v_toBind_997_, lean_box(0), lean_box(0), v___x_1000_, v___f_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1(lean_object* v_m_1003_, lean_object* v_inst_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_m_1006_, lean_object* v_init_1007_, lean_object* v_f_1008_){
_start:
{
lean_object* v_toApplicative_1009_; lean_object* v_toBind_1010_; lean_object* v_toPure_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; lean_object* v___f_1014_; lean_object* v___x_1015_; 
v_toApplicative_1009_ = lean_ctor_get(v_inst_1004_, 0);
v_toBind_1010_ = lean_ctor_get(v_inst_1004_, 1);
lean_inc(v_toBind_1010_);
v_toPure_1011_ = lean_ctor_get(v_toApplicative_1009_, 1);
lean_inc(v_toPure_1011_);
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1012_, 0, v_f_1008_);
v___x_1013_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1004_, v___f_1012_, v_init_1007_, v_m_1006_);
v___f_1014_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1014_, 0, v_toPure_1011_);
v___x_1015_ = lean_apply_4(v_toBind_1010_, lean_box(0), lean_box(0), v___x_1013_, v___f_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___redArg(lean_object* v_inst_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1017_, 0, lean_box(0));
lean_closure_set(v___x_1017_, 1, v_inst_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad(lean_object* v_m_1018_, lean_object* v_inst_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1020_, 0, lean_box(0));
lean_closure_set(v___x_1020_, 1, v_inst_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object* v_s_1021_, lean_object* v_fvarId_1022_){
_start:
{
uint8_t v___x_1023_; 
v___x_1023_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_fvarId_1022_, v_s_1021_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_box(0);
v___x_1025_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1022_, v___x_1024_, v_s_1021_);
return v___x_1025_;
}
else
{
lean_dec(v_fvarId_1022_);
return v_s_1021_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(lean_object* v_init_1026_, lean_object* v_x_1027_){
_start:
{
if (lean_obj_tag(v_x_1027_) == 0)
{
lean_object* v_k_1028_; lean_object* v_l_1029_; lean_object* v_r_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_k_1028_ = lean_ctor_get(v_x_1027_, 1);
lean_inc(v_k_1028_);
v_l_1029_ = lean_ctor_get(v_x_1027_, 3);
lean_inc(v_l_1029_);
v_r_1030_ = lean_ctor_get(v_x_1027_, 4);
lean_inc(v_r_1030_);
lean_dec_ref_known(v_x_1027_, 5);
v___x_1031_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_1026_, v_l_1029_);
v___x_1032_ = l_Lean_FVarIdSet_insert(v___x_1031_, v_k_1028_);
v_init_1026_ = v___x_1032_;
v_x_1027_ = v_r_1030_;
goto _start;
}
else
{
return v_init_1026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_union(lean_object* v_vs_u2081_1034_, lean_object* v_vs_u2082_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_vs_u2082_1035_, v_vs_u2081_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0(lean_object* v_init_1037_, lean_object* v_t_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_1037_, v_t_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList(lean_object* v_l_1040_){
_start:
{
lean_object* v___f_1041_; lean_object* v___x_1042_; 
v___f_1041_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1042_ = l_Std_TreeSet_ofList___redArg(v_l_1040_, v___f_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList___boxed(lean_object* v_l_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_FVarIdSet_ofList(v_l_1043_);
lean_dec(v_l_1043_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object* v_l_1045_){
_start:
{
lean_object* v___f_1046_; lean_object* v___x_1047_; 
v___f_1046_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1047_ = l_Std_TreeSet_ofArray___redArg(v_l_1045_, v___f_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object* v_l_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_FVarIdSet_ofArray(v_l_1048_);
lean_dec_ref(v_l_1048_);
return v_res_1049_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = lean_box(0);
v___x_1051_ = lean_unsigned_to_nat(16u);
v___x_1052_ = lean_mk_array(v___x_1051_, v___x_1050_);
return v___x_1052_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0);
v___x_1054_ = lean_unsigned_to_nat(0u);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v___x_1053_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet(void){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet(void){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object* v_s_1060_, lean_object* v_fvarId_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1061_, v_a_1062_, v_s_1060_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object* v_00_u03b1_1064_, lean_object* v_s_1065_, lean_object* v_fvarId_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1066_, v_a_1067_, v_s_1065_);
return v___x_1068_;
}
}
lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_box(1);
return v___x_1070_;
}
}
LEAN_EXPORT void l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1071_;
v_res_1071_ = l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg();
stack->m_obj
 = v_res_1071_;
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg();
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1(lean_object* v_00_u03b1_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_box(1);
return v___x_1075_;
}
}
lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg(){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_box(1);
return v___x_1077_;
}
}
LEAN_EXPORT void l_Lean_instEmptyCollectionFVarIdMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1078_;
v_res_1078_ = l_Lean_instEmptyCollectionFVarIdMap___redArg();
stack->m_obj
 = v_res_1078_;
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg___boxed(lean_object* v___dummy_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_instEmptyCollectionFVarIdMap___redArg();
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* v_00_u03b1_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_box(1);
return v___x_1082_;
}
}
lean_object* l_Lean_instInhabitedFVarIdMap___redArg(){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_box(1);
return v___x_1084_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedFVarIdMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1085_;
v_res_1085_ = l_Lean_instInhabitedFVarIdMap___redArg();
stack->m_obj
 = v_res_1085_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg___boxed(lean_object* v___dummy_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_instInhabitedFVarIdMap___redArg();
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* v_00_u03b1_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_box(1);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId_default(void){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_box(0);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId(void){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_box(0);
return v___x_1091_;
}
}
uint8_t l_Lean_instBEqMVarId_beq(lean_object* v_x_1092_, lean_object* v_x_1093_){
_start:
{
uint8_t v___x_1094_; 
v___x_1094_ = lean_name_eq(v_x_1092_, v_x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT void l_Lean_instBEqMVarId_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1092_ = stack[0].m_obj;
lean_object* v_x_1093_ = stack[1].m_obj;
uint8_t v_res_1095_;
v_res_1095_ = l_Lean_instBEqMVarId_beq(v_x_1092_, v_x_1093_);
stack->m_num = v_res_1095_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
uint8_t v_res_1098_; lean_object* v_r_1099_; 
v_res_1098_ = l_Lean_instBEqMVarId_beq(v_x_1096_, v_x_1097_);
lean_dec(v_x_1097_);
lean_dec(v_x_1096_);
v_r_1099_ = lean_box(v_res_1098_);
return v_r_1099_;
}
}
uint64_t l_Lean_instHashableMVarId_hash(lean_object* v_x_1102_){
_start:
{
uint64_t v___x_1103_; 
v___x_1103_ = 0ULL;
if (lean_obj_tag(v_x_1102_) == 0)
{
uint64_t v___x_1104_; 
v___x_1104_ = 8934034000889494153ULL;
return v___x_1104_;
}
else
{
uint64_t v_hash_1105_; uint64_t v___x_1106_; 
v_hash_1105_ = lean_ctor_get_uint64(v_x_1102_, sizeof(void*)*2);
v___x_1106_ = lean_uint64_mix_hash(v___x_1103_, v_hash_1105_);
return v___x_1106_;
}
}
}
LEAN_EXPORT void l_Lean_instHashableMVarId_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1102_ = stack[0].m_obj;
uint64_t v_res_1107_;
v_res_1107_ = l_Lean_instHashableMVarId_hash(v_x_1102_);
stack->m_num = v_res_1107_;
}
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object* v_x_1108_){
_start:
{
uint64_t v_res_1109_; lean_object* v_r_1110_; 
v_res_1109_ = l_Lean_instHashableMVarId_hash(v_x_1108_);
lean_dec(v_x_1108_);
v_r_1110_ = lean_box_uint64(v_res_1109_);
return v_r_1110_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_box(1);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet(void){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_box(1);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_box(1);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet(void){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_box(1);
return v___x_1117_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object* v_k_1118_, lean_object* v_t_1119_){
_start:
{
if (lean_obj_tag(v_t_1119_) == 0)
{
lean_object* v_k_1120_; lean_object* v_l_1121_; lean_object* v_r_1122_; uint8_t v___x_1123_; 
v_k_1120_ = lean_ctor_get(v_t_1119_, 1);
v_l_1121_ = lean_ctor_get(v_t_1119_, 3);
v_r_1122_ = lean_ctor_get(v_t_1119_, 4);
v___x_1123_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1118_, v_k_1120_);
switch(v___x_1123_)
{
case 0:
{
v_t_1119_ = v_l_1121_;
goto _start;
}
case 1:
{
uint8_t v___x_1125_; 
v___x_1125_ = 1;
return v___x_1125_;
}
default: 
{
v_t_1119_ = v_r_1122_;
goto _start;
}
}
}
else
{
uint8_t v___x_1127_; 
v___x_1127_ = 0;
return v___x_1127_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1118_ = stack[0].m_obj;
lean_object* v_t_1119_ = stack[1].m_obj;
uint8_t v_res_1128_;
v_res_1128_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1118_, v_t_1119_);
stack->m_num = v_res_1128_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object* v_k_1129_, lean_object* v_t_1130_){
_start:
{
uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1129_, v_t_1130_);
lean_dec(v_t_1130_);
lean_dec(v_k_1129_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object* v_k_1133_, lean_object* v_v_1134_, lean_object* v_t_1135_){
_start:
{
if (lean_obj_tag(v_t_1135_) == 0)
{
lean_object* v_size_1136_; lean_object* v_k_1137_; lean_object* v_v_1138_; lean_object* v_l_1139_; lean_object* v_r_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1420_; 
v_size_1136_ = lean_ctor_get(v_t_1135_, 0);
v_k_1137_ = lean_ctor_get(v_t_1135_, 1);
v_v_1138_ = lean_ctor_get(v_t_1135_, 2);
v_l_1139_ = lean_ctor_get(v_t_1135_, 3);
v_r_1140_ = lean_ctor_get(v_t_1135_, 4);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_t_1135_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1142_ = v_t_1135_;
v_isShared_1143_ = v_isSharedCheck_1420_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_r_1140_);
lean_inc(v_l_1139_);
lean_inc(v_v_1138_);
lean_inc(v_k_1137_);
lean_inc(v_size_1136_);
lean_dec(v_t_1135_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1420_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
uint8_t v___x_1144_; 
v___x_1144_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1133_, v_k_1137_);
switch(v___x_1144_)
{
case 0:
{
lean_object* v_impl_1145_; lean_object* v___x_1146_; 
lean_dec(v_size_1136_);
v_impl_1145_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1133_, v_v_1134_, v_l_1139_);
v___x_1146_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1140_) == 0)
{
lean_object* v_size_1147_; lean_object* v_size_1148_; lean_object* v_k_1149_; lean_object* v_v_1150_; lean_object* v_l_1151_; lean_object* v_r_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v_size_1147_ = lean_ctor_get(v_r_1140_, 0);
v_size_1148_ = lean_ctor_get(v_impl_1145_, 0);
v_k_1149_ = lean_ctor_get(v_impl_1145_, 1);
v_v_1150_ = lean_ctor_get(v_impl_1145_, 2);
v_l_1151_ = lean_ctor_get(v_impl_1145_, 3);
v_r_1152_ = lean_ctor_get(v_impl_1145_, 4);
lean_inc(v_r_1152_);
v___x_1153_ = lean_unsigned_to_nat(3u);
v___x_1154_ = lean_nat_mul(v___x_1153_, v_size_1147_);
v___x_1155_ = lean_nat_dec_lt(v___x_1154_, v_size_1148_);
lean_dec(v___x_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
lean_dec(v_r_1152_);
v___x_1156_ = lean_nat_add(v___x_1146_, v_size_1148_);
v___x_1157_ = lean_nat_add(v___x_1156_, v_size_1147_);
lean_dec(v___x_1156_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 3, v_impl_1145_);
lean_ctor_set(v___x_1142_, 0, v___x_1157_);
v___x_1159_ = v___x_1142_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_k_1137_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_v_1138_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v_impl_1145_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v_r_1140_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
else
{
lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1226_; 
lean_inc(v_l_1151_);
lean_inc(v_v_1150_);
lean_inc(v_k_1149_);
lean_inc(v_size_1148_);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_impl_1145_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; lean_object* v_unused_1228_; lean_object* v_unused_1229_; lean_object* v_unused_1230_; lean_object* v_unused_1231_; 
v_unused_1227_ = lean_ctor_get(v_impl_1145_, 4);
lean_dec(v_unused_1227_);
v_unused_1228_ = lean_ctor_get(v_impl_1145_, 3);
lean_dec(v_unused_1228_);
v_unused_1229_ = lean_ctor_get(v_impl_1145_, 2);
lean_dec(v_unused_1229_);
v_unused_1230_ = lean_ctor_get(v_impl_1145_, 1);
lean_dec(v_unused_1230_);
v_unused_1231_ = lean_ctor_get(v_impl_1145_, 0);
lean_dec(v_unused_1231_);
v___x_1162_ = v_impl_1145_;
v_isShared_1163_ = v_isSharedCheck_1226_;
goto v_resetjp_1161_;
}
else
{
lean_dec(v_impl_1145_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1226_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v_size_1164_; lean_object* v_size_1165_; lean_object* v_k_1166_; lean_object* v_v_1167_; lean_object* v_l_1168_; lean_object* v_r_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_size_1164_ = lean_ctor_get(v_l_1151_, 0);
v_size_1165_ = lean_ctor_get(v_r_1152_, 0);
v_k_1166_ = lean_ctor_get(v_r_1152_, 1);
v_v_1167_ = lean_ctor_get(v_r_1152_, 2);
v_l_1168_ = lean_ctor_get(v_r_1152_, 3);
v_r_1169_ = lean_ctor_get(v_r_1152_, 4);
v___x_1170_ = lean_unsigned_to_nat(2u);
v___x_1171_ = lean_nat_mul(v___x_1170_, v_size_1164_);
v___x_1172_ = lean_nat_dec_lt(v_size_1165_, v___x_1171_);
lean_dec(v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1201_; 
lean_inc(v_r_1169_);
lean_inc(v_l_1168_);
lean_inc(v_v_1167_);
lean_inc(v_k_1166_);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_r_1152_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; lean_object* v_unused_1203_; lean_object* v_unused_1204_; lean_object* v_unused_1205_; lean_object* v_unused_1206_; 
v_unused_1202_ = lean_ctor_get(v_r_1152_, 4);
lean_dec(v_unused_1202_);
v_unused_1203_ = lean_ctor_get(v_r_1152_, 3);
lean_dec(v_unused_1203_);
v_unused_1204_ = lean_ctor_get(v_r_1152_, 2);
lean_dec(v_unused_1204_);
v_unused_1205_ = lean_ctor_get(v_r_1152_, 1);
lean_dec(v_unused_1205_);
v_unused_1206_ = lean_ctor_get(v_r_1152_, 0);
lean_dec(v_unused_1206_);
v___x_1174_ = v_r_1152_;
v_isShared_1175_ = v_isSharedCheck_1201_;
goto v_resetjp_1173_;
}
else
{
lean_dec(v_r_1152_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1201_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___x_1189_; lean_object* v___y_1191_; 
v___x_1176_ = lean_nat_add(v___x_1146_, v_size_1148_);
lean_dec(v_size_1148_);
v___x_1177_ = lean_nat_add(v___x_1176_, v_size_1147_);
lean_dec(v___x_1176_);
v___x_1189_ = lean_nat_add(v___x_1146_, v_size_1164_);
if (lean_obj_tag(v_l_1168_) == 0)
{
lean_object* v_size_1199_; 
v_size_1199_ = lean_ctor_get(v_l_1168_, 0);
lean_inc(v_size_1199_);
v___y_1191_ = v_size_1199_;
goto v___jp_1190_;
}
else
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_unsigned_to_nat(0u);
v___y_1191_ = v___x_1200_;
goto v___jp_1190_;
}
v___jp_1178_:
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1182_ = lean_nat_add(v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec(v___y_1180_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 4, v_r_1140_);
lean_ctor_set(v___x_1174_, 3, v_r_1169_);
lean_ctor_set(v___x_1174_, 2, v_v_1138_);
lean_ctor_set(v___x_1174_, 1, v_k_1137_);
lean_ctor_set(v___x_1174_, 0, v___x_1182_);
v___x_1184_ = v___x_1174_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_k_1137_);
lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_v_1138_);
lean_ctor_set(v_reuseFailAlloc_1188_, 3, v_r_1169_);
lean_ctor_set(v_reuseFailAlloc_1188_, 4, v_r_1140_);
v___x_1184_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1186_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 4, v___x_1184_);
lean_ctor_set(v___x_1162_, 3, v___y_1179_);
lean_ctor_set(v___x_1162_, 2, v_v_1167_);
lean_ctor_set(v___x_1162_, 1, v_k_1166_);
lean_ctor_set(v___x_1162_, 0, v___x_1177_);
v___x_1186_ = v___x_1162_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_k_1166_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_v_1167_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v___y_1179_);
lean_ctor_set(v_reuseFailAlloc_1187_, 4, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
v___jp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_nat_add(v___x_1189_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec(v___x_1189_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 4, v_l_1168_);
lean_ctor_set(v___x_1142_, 3, v_l_1151_);
lean_ctor_set(v___x_1142_, 2, v_v_1150_);
lean_ctor_set(v___x_1142_, 1, v_k_1149_);
lean_ctor_set(v___x_1142_, 0, v___x_1192_);
v___x_1194_ = v___x_1142_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_k_1149_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v_v_1150_);
lean_ctor_set(v_reuseFailAlloc_1198_, 3, v_l_1151_);
lean_ctor_set(v_reuseFailAlloc_1198_, 4, v_l_1168_);
v___x_1194_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_nat_add(v___x_1146_, v_size_1147_);
if (lean_obj_tag(v_r_1169_) == 0)
{
lean_object* v_size_1196_; 
v_size_1196_ = lean_ctor_get(v_r_1169_, 0);
lean_inc(v_size_1196_);
v___y_1179_ = v___x_1194_;
v___y_1180_ = v___x_1195_;
v___y_1181_ = v_size_1196_;
goto v___jp_1178_;
}
else
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_unsigned_to_nat(0u);
v___y_1179_ = v___x_1194_;
v___y_1180_ = v___x_1195_;
v___y_1181_ = v___x_1197_;
goto v___jp_1178_;
}
}
}
}
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
lean_del_object(v___x_1142_);
v___x_1207_ = lean_nat_add(v___x_1146_, v_size_1148_);
lean_dec(v_size_1148_);
v___x_1208_ = lean_nat_add(v___x_1207_, v_size_1147_);
lean_dec(v___x_1207_);
v___x_1209_ = lean_nat_add(v___x_1146_, v_size_1147_);
v___x_1210_ = lean_nat_add(v___x_1209_, v_size_1165_);
lean_dec(v___x_1209_);
lean_inc_ref(v_r_1140_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 4, v_r_1140_);
lean_ctor_set(v___x_1162_, 3, v_r_1152_);
lean_ctor_set(v___x_1162_, 2, v_v_1138_);
lean_ctor_set(v___x_1162_, 1, v_k_1137_);
lean_ctor_set(v___x_1162_, 0, v___x_1210_);
v___x_1212_ = v___x_1162_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_k_1137_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_v_1138_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_r_1152_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_r_1140_);
v___x_1212_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
v_isSharedCheck_1219_ = !lean_is_exclusive(v_r_1140_);
if (v_isSharedCheck_1219_ == 0)
{
lean_object* v_unused_1220_; lean_object* v_unused_1221_; lean_object* v_unused_1222_; lean_object* v_unused_1223_; lean_object* v_unused_1224_; 
v_unused_1220_ = lean_ctor_get(v_r_1140_, 4);
lean_dec(v_unused_1220_);
v_unused_1221_ = lean_ctor_get(v_r_1140_, 3);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_r_1140_, 2);
lean_dec(v_unused_1222_);
v_unused_1223_ = lean_ctor_get(v_r_1140_, 1);
lean_dec(v_unused_1223_);
v_unused_1224_ = lean_ctor_get(v_r_1140_, 0);
lean_dec(v_unused_1224_);
v___x_1214_ = v_r_1140_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_dec(v_r_1140_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 4, v___x_1212_);
lean_ctor_set(v___x_1214_, 3, v_l_1151_);
lean_ctor_set(v___x_1214_, 2, v_v_1150_);
lean_ctor_set(v___x_1214_, 1, v_k_1149_);
lean_ctor_set(v___x_1214_, 0, v___x_1208_);
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_k_1149_);
lean_ctor_set(v_reuseFailAlloc_1218_, 2, v_v_1150_);
lean_ctor_set(v_reuseFailAlloc_1218_, 3, v_l_1151_);
lean_ctor_set(v_reuseFailAlloc_1218_, 4, v___x_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1232_; 
v_l_1232_ = lean_ctor_get(v_impl_1145_, 3);
if (lean_obj_tag(v_l_1232_) == 0)
{
lean_object* v_r_1233_; lean_object* v_k_1234_; lean_object* v_v_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1246_; 
lean_inc_ref(v_l_1232_);
v_r_1233_ = lean_ctor_get(v_impl_1145_, 4);
v_k_1234_ = lean_ctor_get(v_impl_1145_, 1);
v_v_1235_ = lean_ctor_get(v_impl_1145_, 2);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_impl_1145_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; lean_object* v_unused_1248_; 
v_unused_1247_ = lean_ctor_get(v_impl_1145_, 3);
lean_dec(v_unused_1247_);
v_unused_1248_ = lean_ctor_get(v_impl_1145_, 0);
lean_dec(v_unused_1248_);
v___x_1237_ = v_impl_1145_;
v_isShared_1238_ = v_isSharedCheck_1246_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_r_1233_);
lean_inc(v_v_1235_);
lean_inc(v_k_1234_);
lean_dec(v_impl_1145_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1246_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1239_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1233_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 3, v_r_1233_);
lean_ctor_set(v___x_1237_, 2, v_v_1138_);
lean_ctor_set(v___x_1237_, 1, v_k_1137_);
lean_ctor_set(v___x_1237_, 0, v___x_1146_);
v___x_1241_ = v___x_1237_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_k_1137_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_v_1138_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_r_1233_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v_r_1233_);
v___x_1241_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1243_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 4, v___x_1241_);
lean_ctor_set(v___x_1142_, 3, v_l_1232_);
lean_ctor_set(v___x_1142_, 2, v_v_1235_);
lean_ctor_set(v___x_1142_, 1, v_k_1234_);
lean_ctor_set(v___x_1142_, 0, v___x_1239_);
v___x_1243_ = v___x_1142_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_k_1234_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_v_1235_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v_l_1232_);
lean_ctor_set(v_reuseFailAlloc_1244_, 4, v___x_1241_);
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
else
{
lean_object* v_r_1249_; 
v_r_1249_ = lean_ctor_get(v_impl_1145_, 4);
lean_inc(v_r_1249_);
if (lean_obj_tag(v_r_1249_) == 0)
{
lean_object* v_k_1250_; lean_object* v_v_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1274_; 
lean_inc(v_l_1232_);
v_k_1250_ = lean_ctor_get(v_impl_1145_, 1);
v_v_1251_ = lean_ctor_get(v_impl_1145_, 2);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_impl_1145_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; lean_object* v_unused_1276_; lean_object* v_unused_1277_; 
v_unused_1275_ = lean_ctor_get(v_impl_1145_, 4);
lean_dec(v_unused_1275_);
v_unused_1276_ = lean_ctor_get(v_impl_1145_, 3);
lean_dec(v_unused_1276_);
v_unused_1277_ = lean_ctor_get(v_impl_1145_, 0);
lean_dec(v_unused_1277_);
v___x_1253_ = v_impl_1145_;
v_isShared_1254_ = v_isSharedCheck_1274_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_v_1251_);
lean_inc(v_k_1250_);
lean_dec(v_impl_1145_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1274_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v_k_1255_; lean_object* v_v_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1270_; 
v_k_1255_ = lean_ctor_get(v_r_1249_, 1);
v_v_1256_ = lean_ctor_get(v_r_1249_, 2);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_r_1249_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; lean_object* v_unused_1272_; lean_object* v_unused_1273_; 
v_unused_1271_ = lean_ctor_get(v_r_1249_, 4);
lean_dec(v_unused_1271_);
v_unused_1272_ = lean_ctor_get(v_r_1249_, 3);
lean_dec(v_unused_1272_);
v_unused_1273_ = lean_ctor_get(v_r_1249_, 0);
lean_dec(v_unused_1273_);
v___x_1258_ = v_r_1249_;
v_isShared_1259_ = v_isSharedCheck_1270_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_v_1256_);
lean_inc(v_k_1255_);
lean_dec(v_r_1249_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1270_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1260_ = lean_unsigned_to_nat(3u);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 4, v_l_1232_);
lean_ctor_set(v___x_1258_, 3, v_l_1232_);
lean_ctor_set(v___x_1258_, 2, v_v_1251_);
lean_ctor_set(v___x_1258_, 1, v_k_1250_);
lean_ctor_set(v___x_1258_, 0, v___x_1146_);
v___x_1262_ = v___x_1258_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1269_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1269_, 3, v_l_1232_);
lean_ctor_set(v_reuseFailAlloc_1269_, 4, v_l_1232_);
v___x_1262_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
lean_object* v___x_1264_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 4, v_l_1232_);
lean_ctor_set(v___x_1253_, 2, v_v_1138_);
lean_ctor_set(v___x_1253_, 1, v_k_1137_);
lean_ctor_set(v___x_1253_, 0, v___x_1146_);
v___x_1264_ = v___x_1253_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_k_1137_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_v_1138_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v_l_1232_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v_l_1232_);
v___x_1264_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1266_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 4, v___x_1264_);
lean_ctor_set(v___x_1142_, 3, v___x_1262_);
lean_ctor_set(v___x_1142_, 2, v_v_1256_);
lean_ctor_set(v___x_1142_, 1, v_k_1255_);
lean_ctor_set(v___x_1142_, 0, v___x_1260_);
v___x_1266_ = v___x_1142_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_k_1255_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_v_1256_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v___x_1262_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
}
else
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1278_ = lean_unsigned_to_nat(2u);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 4, v_r_1249_);
lean_ctor_set(v___x_1142_, 3, v_impl_1145_);
lean_ctor_set(v___x_1142_, 0, v___x_1278_);
v___x_1280_ = v___x_1142_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_k_1137_);
lean_ctor_set(v_reuseFailAlloc_1281_, 2, v_v_1138_);
lean_ctor_set(v_reuseFailAlloc_1281_, 3, v_impl_1145_);
lean_ctor_set(v_reuseFailAlloc_1281_, 4, v_r_1249_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1283_; 
lean_dec(v_v_1138_);
lean_dec(v_k_1137_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 2, v_v_1134_);
lean_ctor_set(v___x_1142_, 1, v_k_1133_);
v___x_1283_ = v___x_1142_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_size_1136_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_k_1133_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_v_1134_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_l_1139_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_r_1140_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
default: 
{
lean_object* v_impl_1285_; lean_object* v___x_1286_; 
lean_dec(v_size_1136_);
v_impl_1285_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1133_, v_v_1134_, v_r_1140_);
v___x_1286_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1139_) == 0)
{
lean_object* v_size_1287_; lean_object* v_size_1288_; lean_object* v_k_1289_; lean_object* v_v_1290_; lean_object* v_l_1291_; lean_object* v_r_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v_size_1287_ = lean_ctor_get(v_l_1139_, 0);
v_size_1288_ = lean_ctor_get(v_impl_1285_, 0);
v_k_1289_ = lean_ctor_get(v_impl_1285_, 1);
v_v_1290_ = lean_ctor_get(v_impl_1285_, 2);
v_l_1291_ = lean_ctor_get(v_impl_1285_, 3);
lean_inc(v_l_1291_);
v_r_1292_ = lean_ctor_get(v_impl_1285_, 4);
v___x_1293_ = lean_unsigned_to_nat(3u);
v___x_1294_ = lean_nat_mul(v___x_1293_, v_size_1287_);
v___x_1295_ = lean_nat_dec_lt(v___x_1294_, v_size_1288_);
lean_dec(v___x_1294_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
lean_dec(v_l_1291_);
v___x_1296_ = lean_nat_add(v___x_1286_, v_size_1287_);
v___x_1297_ = lean_nat_add(v___x_1296_, v_size_1288_);
lean_dec(v___x_1296_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 4, v_impl_1285_);
lean_ctor_set(v___x_1142_, 0, v___x_1297_);
v___x_1299_ = v___x_1142_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_k_1137_);
lean_ctor_set(v_reuseFailAlloc_1300_, 2, v_v_1138_);
lean_ctor_set(v_reuseFailAlloc_1300_, 3, v_l_1139_);
lean_ctor_set(v_reuseFailAlloc_1300_, 4, v_impl_1285_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
else
{
lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1364_; 
lean_inc(v_r_1292_);
lean_inc(v_v_1290_);
lean_inc(v_k_1289_);
lean_inc(v_size_1288_);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_impl_1285_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; lean_object* v_unused_1366_; lean_object* v_unused_1367_; lean_object* v_unused_1368_; lean_object* v_unused_1369_; 
v_unused_1365_ = lean_ctor_get(v_impl_1285_, 4);
lean_dec(v_unused_1365_);
v_unused_1366_ = lean_ctor_get(v_impl_1285_, 3);
lean_dec(v_unused_1366_);
v_unused_1367_ = lean_ctor_get(v_impl_1285_, 2);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v_impl_1285_, 1);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v_impl_1285_, 0);
lean_dec(v_unused_1369_);
v___x_1302_ = v_impl_1285_;
v_isShared_1303_ = v_isSharedCheck_1364_;
goto v_resetjp_1301_;
}
else
{
lean_dec(v_impl_1285_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1364_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v_size_1304_; lean_object* v_k_1305_; lean_object* v_v_1306_; lean_object* v_l_1307_; lean_object* v_r_1308_; lean_object* v_size_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_size_1304_ = lean_ctor_get(v_l_1291_, 0);
v_k_1305_ = lean_ctor_get(v_l_1291_, 1);
v_v_1306_ = lean_ctor_get(v_l_1291_, 2);
v_l_1307_ = lean_ctor_get(v_l_1291_, 3);
v_r_1308_ = lean_ctor_get(v_l_1291_, 4);
v_size_1309_ = lean_ctor_get(v_r_1292_, 0);
v___x_1310_ = lean_unsigned_to_nat(2u);
v___x_1311_ = lean_nat_mul(v___x_1310_, v_size_1309_);
v___x_1312_ = lean_nat_dec_lt(v_size_1304_, v___x_1311_);
lean_dec(v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1340_; 
lean_inc(v_r_1308_);
lean_inc(v_l_1307_);
lean_inc(v_v_1306_);
lean_inc(v_k_1305_);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_l_1291_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; lean_object* v_unused_1342_; lean_object* v_unused_1343_; lean_object* v_unused_1344_; lean_object* v_unused_1345_; 
v_unused_1341_ = lean_ctor_get(v_l_1291_, 4);
lean_dec(v_unused_1341_);
v_unused_1342_ = lean_ctor_get(v_l_1291_, 3);
lean_dec(v_unused_1342_);
v_unused_1343_ = lean_ctor_get(v_l_1291_, 2);
lean_dec(v_unused_1343_);
v_unused_1344_ = lean_ctor_get(v_l_1291_, 1);
lean_dec(v_unused_1344_);
v_unused_1345_ = lean_ctor_get(v_l_1291_, 0);
lean_dec(v_unused_1345_);
v___x_1314_ = v_l_1291_;
v_isShared_1315_ = v_isSharedCheck_1340_;
goto v_resetjp_1313_;
}
else
{
lean_dec(v_l_1291_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1340_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1330_; 
v___x_1316_ = lean_nat_add(v___x_1286_, v_size_1287_);
v___x_1317_ = lean_nat_add(v___x_1316_, v_size_1288_);
lean_dec(v_size_1288_);
if (lean_obj_tag(v_l_1307_) == 0)
{
lean_object* v_size_1338_; 
v_size_1338_ = lean_ctor_get(v_l_1307_, 0);
lean_inc(v_size_1338_);
v___y_1330_ = v_size_1338_;
goto v___jp_1329_;
}
else
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_unsigned_to_nat(0u);
v___y_1330_ = v___x_1339_;
goto v___jp_1329_;
}
v___jp_1318_:
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1322_ = lean_nat_add(v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec(v___y_1320_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 4, v_r_1292_);
lean_ctor_set(v___x_1314_, 3, v_r_1308_);
lean_ctor_set(v___x_1314_, 2, v_v_1290_);
lean_ctor_set(v___x_1314_, 1, v_k_1289_);
lean_ctor_set(v___x_1314_, 0, v___x_1322_);
v___x_1324_ = v___x_1314_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_k_1289_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_v_1290_);
lean_ctor_set(v_reuseFailAlloc_1328_, 3, v_r_1308_);
lean_ctor_set(v_reuseFailAlloc_1328_, 4, v_r_1292_);
v___x_1324_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1326_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 4, v___x_1324_);
lean_ctor_set(v___x_1302_, 3, v___y_1319_);
lean_ctor_set(v___x_1302_, 2, v_v_1306_);
lean_ctor_set(v___x_1302_, 1, v_k_1305_);
lean_ctor_set(v___x_1302_, 0, v___x_1317_);
v___x_1326_ = v___x_1302_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_k_1305_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_v_1306_);
lean_ctor_set(v_reuseFailAlloc_1327_, 3, v___y_1319_);
lean_ctor_set(v_reuseFailAlloc_1327_, 4, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
v___jp_1329_:
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1331_ = lean_nat_add(v___x_1316_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec(v___x_1316_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 4, v_l_1307_);
lean_ctor_set(v___x_1142_, 0, v___x_1331_);
v___x_1333_ = v___x_1142_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_k_1137_);
lean_ctor_set(v_reuseFailAlloc_1337_, 2, v_v_1138_);
lean_ctor_set(v_reuseFailAlloc_1337_, 3, v_l_1139_);
lean_ctor_set(v_reuseFailAlloc_1337_, 4, v_l_1307_);
v___x_1333_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_nat_add(v___x_1286_, v_size_1309_);
if (lean_obj_tag(v_r_1308_) == 0)
{
lean_object* v_size_1335_; 
v_size_1335_ = lean_ctor_get(v_r_1308_, 0);
lean_inc(v_size_1335_);
v___y_1319_ = v___x_1333_;
v___y_1320_ = v___x_1334_;
v___y_1321_ = v_size_1335_;
goto v___jp_1318_;
}
else
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_unsigned_to_nat(0u);
v___y_1319_ = v___x_1333_;
v___y_1320_ = v___x_1334_;
v___y_1321_ = v___x_1336_;
goto v___jp_1318_;
}
}
}
}
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
lean_del_object(v___x_1142_);
v___x_1346_ = lean_nat_add(v___x_1286_, v_size_1287_);
v___x_1347_ = lean_nat_add(v___x_1346_, v_size_1288_);
lean_dec(v_size_1288_);
v___x_1348_ = lean_nat_add(v___x_1346_, v_size_1304_);
lean_dec(v___x_1346_);
lean_inc_ref(v_l_1139_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 4, v_l_1291_);
lean_ctor_set(v___x_1302_, 3, v_l_1139_);
lean_ctor_set(v___x_1302_, 2, v_v_1138_);
lean_ctor_set(v___x_1302_, 1, v_k_1137_);
lean_ctor_set(v___x_1302_, 0, v___x_1348_);
v___x_1350_ = v___x_1302_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_k_1137_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v_v_1138_);
lean_ctor_set(v_reuseFailAlloc_1363_, 3, v_l_1139_);
lean_ctor_set(v_reuseFailAlloc_1363_, 4, v_l_1291_);
v___x_1350_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
v_isSharedCheck_1357_ = !lean_is_exclusive(v_l_1139_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; lean_object* v_unused_1359_; lean_object* v_unused_1360_; lean_object* v_unused_1361_; lean_object* v_unused_1362_; 
v_unused_1358_ = lean_ctor_get(v_l_1139_, 4);
lean_dec(v_unused_1358_);
v_unused_1359_ = lean_ctor_get(v_l_1139_, 3);
lean_dec(v_unused_1359_);
v_unused_1360_ = lean_ctor_get(v_l_1139_, 2);
lean_dec(v_unused_1360_);
v_unused_1361_ = lean_ctor_get(v_l_1139_, 1);
lean_dec(v_unused_1361_);
v_unused_1362_ = lean_ctor_get(v_l_1139_, 0);
lean_dec(v_unused_1362_);
v___x_1352_ = v_l_1139_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_dec(v_l_1139_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 4, v_r_1292_);
lean_ctor_set(v___x_1352_, 3, v___x_1350_);
lean_ctor_set(v___x_1352_, 2, v_v_1290_);
lean_ctor_set(v___x_1352_, 1, v_k_1289_);
lean_ctor_set(v___x_1352_, 0, v___x_1347_);
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_k_1289_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_v_1290_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v_r_1292_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1370_; 
v_l_1370_ = lean_ctor_get(v_impl_1285_, 3);
lean_inc(v_l_1370_);
if (lean_obj_tag(v_l_1370_) == 0)
{
lean_object* v_r_1371_; lean_object* v_k_1372_; lean_object* v_v_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1396_; 
v_r_1371_ = lean_ctor_get(v_impl_1285_, 4);
v_k_1372_ = lean_ctor_get(v_impl_1285_, 1);
v_v_1373_ = lean_ctor_get(v_impl_1285_, 2);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_impl_1285_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; lean_object* v_unused_1398_; 
v_unused_1397_ = lean_ctor_get(v_impl_1285_, 3);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v_impl_1285_, 0);
lean_dec(v_unused_1398_);
v___x_1375_ = v_impl_1285_;
v_isShared_1376_ = v_isSharedCheck_1396_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_r_1371_);
lean_inc(v_v_1373_);
lean_inc(v_k_1372_);
lean_dec(v_impl_1285_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1396_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v_k_1377_; lean_object* v_v_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1392_; 
v_k_1377_ = lean_ctor_get(v_l_1370_, 1);
v_v_1378_ = lean_ctor_get(v_l_1370_, 2);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_l_1370_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; lean_object* v_unused_1394_; lean_object* v_unused_1395_; 
v_unused_1393_ = lean_ctor_get(v_l_1370_, 4);
lean_dec(v_unused_1393_);
v_unused_1394_ = lean_ctor_get(v_l_1370_, 3);
lean_dec(v_unused_1394_);
v_unused_1395_ = lean_ctor_get(v_l_1370_, 0);
lean_dec(v_unused_1395_);
v___x_1380_ = v_l_1370_;
v_isShared_1381_ = v_isSharedCheck_1392_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_v_1378_);
lean_inc(v_k_1377_);
lean_dec(v_l_1370_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1392_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1382_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1371_, 2);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 4, v_r_1371_);
lean_ctor_set(v___x_1380_, 3, v_r_1371_);
lean_ctor_set(v___x_1380_, 2, v_v_1138_);
lean_ctor_set(v___x_1380_, 1, v_k_1137_);
lean_ctor_set(v___x_1380_, 0, v___x_1286_);
v___x_1384_ = v___x_1380_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_k_1137_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_v_1138_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_r_1371_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_r_1371_);
v___x_1384_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1386_; 
lean_inc(v_r_1371_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 3, v_r_1371_);
lean_ctor_set(v___x_1375_, 0, v___x_1286_);
v___x_1386_ = v___x_1375_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_r_1371_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_r_1371_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1388_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 4, v___x_1386_);
lean_ctor_set(v___x_1142_, 3, v___x_1384_);
lean_ctor_set(v___x_1142_, 2, v_v_1378_);
lean_ctor_set(v___x_1142_, 1, v_k_1377_);
lean_ctor_set(v___x_1142_, 0, v___x_1382_);
v___x_1388_ = v___x_1142_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_k_1377_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_v_1378_);
lean_ctor_set(v_reuseFailAlloc_1389_, 3, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1389_, 4, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
}
else
{
lean_object* v_r_1399_; 
v_r_1399_ = lean_ctor_get(v_impl_1285_, 4);
lean_inc(v_r_1399_);
if (lean_obj_tag(v_r_1399_) == 0)
{
lean_object* v_k_1400_; lean_object* v_v_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1412_; 
v_k_1400_ = lean_ctor_get(v_impl_1285_, 1);
v_v_1401_ = lean_ctor_get(v_impl_1285_, 2);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_impl_1285_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; lean_object* v_unused_1414_; lean_object* v_unused_1415_; 
v_unused_1413_ = lean_ctor_get(v_impl_1285_, 4);
lean_dec(v_unused_1413_);
v_unused_1414_ = lean_ctor_get(v_impl_1285_, 3);
lean_dec(v_unused_1414_);
v_unused_1415_ = lean_ctor_get(v_impl_1285_, 0);
lean_dec(v_unused_1415_);
v___x_1403_ = v_impl_1285_;
v_isShared_1404_ = v_isSharedCheck_1412_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_v_1401_);
lean_inc(v_k_1400_);
lean_dec(v_impl_1285_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1412_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1405_ = lean_unsigned_to_nat(3u);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 4, v_l_1370_);
lean_ctor_set(v___x_1403_, 2, v_v_1138_);
lean_ctor_set(v___x_1403_, 1, v_k_1137_);
lean_ctor_set(v___x_1403_, 0, v___x_1286_);
v___x_1407_ = v___x_1403_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_k_1137_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_v_1138_);
lean_ctor_set(v_reuseFailAlloc_1411_, 3, v_l_1370_);
lean_ctor_set(v_reuseFailAlloc_1411_, 4, v_l_1370_);
v___x_1407_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1409_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 4, v_r_1399_);
lean_ctor_set(v___x_1142_, 3, v___x_1407_);
lean_ctor_set(v___x_1142_, 2, v_v_1401_);
lean_ctor_set(v___x_1142_, 1, v_k_1400_);
lean_ctor_set(v___x_1142_, 0, v___x_1405_);
v___x_1409_ = v___x_1142_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_k_1400_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_v_1401_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_r_1399_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = lean_unsigned_to_nat(2u);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 4, v_impl_1285_);
lean_ctor_set(v___x_1142_, 3, v_r_1399_);
lean_ctor_set(v___x_1142_, 0, v___x_1416_);
v___x_1418_ = v___x_1142_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_k_1137_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_v_1138_);
lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_r_1399_);
lean_ctor_set(v_reuseFailAlloc_1419_, 4, v_impl_1285_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
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
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
lean_ctor_set(v___x_1422_, 1, v_k_1133_);
lean_ctor_set(v___x_1422_, 2, v_v_1134_);
lean_ctor_set(v___x_1422_, 3, v_t_1135_);
lean_ctor_set(v___x_1422_, 4, v_t_1135_);
return v___x_1422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object* v_s_1423_, lean_object* v_mvarId_1424_){
_start:
{
uint8_t v___x_1425_; 
v___x_1425_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_mvarId_1424_, v_s_1423_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_box(0);
v___x_1427_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1424_, v___x_1426_, v_s_1423_);
return v___x_1427_;
}
else
{
lean_dec(v_mvarId_1424_);
return v_s_1423_;
}
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object* v_00_u03b2_1428_, lean_object* v_k_1429_, lean_object* v_t_1430_){
_start:
{
uint8_t v___x_1431_; 
v___x_1431_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1429_, v_t_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1429_ = stack[1].m_obj;
lean_object* v_t_1430_ = stack[2].m_obj;
uint8_t v_res_1432_;
v_res_1432_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_box(0), v_k_1429_, v_t_1430_);
stack->m_num = v_res_1432_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object* v_00_u03b2_1433_, lean_object* v_k_1434_, lean_object* v_t_1435_){
_start:
{
uint8_t v_res_1436_; lean_object* v_r_1437_; 
v_res_1436_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(v_00_u03b2_1433_, v_k_1434_, v_t_1435_);
lean_dec(v_t_1435_);
lean_dec(v_k_1434_);
v_r_1437_ = lean_box(v_res_1436_);
return v_r_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object* v_00_u03b2_1438_, lean_object* v_k_1439_, lean_object* v_v_1440_, lean_object* v_t_1441_, lean_object* v_hl_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1439_, v_v_1440_, v_t_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object* v_l_1444_){
_start:
{
lean_object* v___f_1445_; lean_object* v___x_1446_; 
v___f_1445_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1446_ = l_Std_TreeSet_ofList___redArg(v_l_1444_, v___f_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList___boxed(lean_object* v_l_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_MVarIdSet_ofList(v_l_1447_);
lean_dec(v_l_1447_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object* v_l_1449_){
_start:
{
lean_object* v___f_1450_; lean_object* v___x_1451_; 
v___f_1450_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1451_ = l_Std_TreeSet_ofArray___redArg(v_l_1449_, v___f_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object* v_l_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_MVarIdSet_ofArray(v_l_1452_);
lean_dec_ref(v_l_1452_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1454_, lean_object* v_m_1455_, lean_object* v_init_1456_, lean_object* v_f_1457_){
_start:
{
lean_object* v_toApplicative_1458_; lean_object* v_toBind_1459_; lean_object* v_toPure_1460_; lean_object* v___f_1461_; lean_object* v___x_1462_; lean_object* v___f_1463_; lean_object* v___x_1464_; 
v_toApplicative_1458_ = lean_ctor_get(v_inst_1454_, 0);
v_toBind_1459_ = lean_ctor_get(v_inst_1454_, 1);
lean_inc(v_toBind_1459_);
v_toPure_1460_ = lean_ctor_get(v_toApplicative_1458_, 1);
lean_inc(v_toPure_1460_);
v___f_1461_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1461_, 0, v_f_1457_);
v___x_1462_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1454_, v___f_1461_, v_init_1456_, v_m_1455_);
v___f_1463_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1463_, 0, v_toPure_1460_);
v___x_1464_ = lean_apply_4(v_toBind_1459_, lean_box(0), lean_box(0), v___x_1462_, v___f_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1(lean_object* v_m_1465_, lean_object* v_inst_1466_, lean_object* v_00_u03b2_1467_, lean_object* v_m_1468_, lean_object* v_init_1469_, lean_object* v_f_1470_){
_start:
{
lean_object* v_toApplicative_1471_; lean_object* v_toBind_1472_; lean_object* v_toPure_1473_; lean_object* v___f_1474_; lean_object* v___x_1475_; lean_object* v___f_1476_; lean_object* v___x_1477_; 
v_toApplicative_1471_ = lean_ctor_get(v_inst_1466_, 0);
v_toBind_1472_ = lean_ctor_get(v_inst_1466_, 1);
lean_inc(v_toBind_1472_);
v_toPure_1473_ = lean_ctor_get(v_toApplicative_1471_, 1);
lean_inc(v_toPure_1473_);
v___f_1474_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1474_, 0, v_f_1470_);
v___x_1475_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1466_, v___f_1474_, v_init_1469_, v_m_1468_);
v___f_1476_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1476_, 0, v_toPure_1473_);
v___x_1477_ = lean_apply_4(v_toBind_1472_, lean_box(0), lean_box(0), v___x_1475_, v___f_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object* v_inst_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1479_, 0, lean_box(0));
lean_closure_set(v___x_1479_, 1, v_inst_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object* v_m_1480_, lean_object* v_inst_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1482_, 0, lean_box(0));
lean_closure_set(v___x_1482_, 1, v_inst_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object* v_s_1483_, lean_object* v_mvarId_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1484_, v_a_1485_, v_s_1483_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object* v_00_u03b1_1487_, lean_object* v_s_1488_, lean_object* v_mvarId_1489_, lean_object* v_a_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1489_, v_a_1490_, v_s_1488_);
return v___x_1491_;
}
}
lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_box(1);
return v___x_1493_;
}
}
LEAN_EXPORT void l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1494_;
v_res_1494_ = l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg();
stack->m_obj
 = v_res_1494_;
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg();
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object* v_00_u03b1_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_box(1);
return v___x_1498_;
}
}
lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg(){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_box(1);
return v___x_1500_;
}
}
LEAN_EXPORT void l_Lean_instEmptyCollectionMVarIdMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1501_;
v_res_1501_ = l_Lean_instEmptyCollectionMVarIdMap___redArg();
stack->m_obj
 = v_res_1501_;
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg___boxed(lean_object* v___dummy_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_instEmptyCollectionMVarIdMap___redArg();
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* v_00_u03b1_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_box(1);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_1506_, lean_object* v_a_1507_, lean_object* v_b_1508_, lean_object* v_c_1509_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v_a_1507_);
lean_ctor_set(v___x_1510_, 1, v_b_1508_);
v___x_1511_ = lean_apply_2(v_f_1506_, v___x_1510_, v_c_1509_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1512_, lean_object* v_m_1513_, lean_object* v_init_1514_, lean_object* v_f_1515_){
_start:
{
lean_object* v_toApplicative_1516_; lean_object* v_toBind_1517_; lean_object* v_toPure_1518_; lean_object* v___f_1519_; lean_object* v___x_1520_; lean_object* v___f_1521_; lean_object* v___x_1522_; 
v_toApplicative_1516_ = lean_ctor_get(v_inst_1512_, 0);
v_toBind_1517_ = lean_ctor_get(v_inst_1512_, 1);
lean_inc(v_toBind_1517_);
v_toPure_1518_ = lean_ctor_get(v_toApplicative_1516_, 1);
lean_inc(v_toPure_1518_);
v___f_1519_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1519_, 0, v_f_1515_);
v___x_1520_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1512_, v___f_1519_, v_init_1514_, v_m_1513_);
v___f_1521_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1521_, 0, v_toPure_1518_);
v___x_1522_ = lean_apply_4(v_toBind_1517_, lean_box(0), lean_box(0), v___x_1520_, v___f_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object* v_m_1523_, lean_object* v_00_u03b1_1524_, lean_object* v_inst_1525_, lean_object* v_00_u03b2_1526_, lean_object* v_m_1527_, lean_object* v_init_1528_, lean_object* v_f_1529_){
_start:
{
lean_object* v_toApplicative_1530_; lean_object* v_toBind_1531_; lean_object* v_toPure_1532_; lean_object* v___f_1533_; lean_object* v___x_1534_; lean_object* v___f_1535_; lean_object* v___x_1536_; 
v_toApplicative_1530_ = lean_ctor_get(v_inst_1525_, 0);
v_toBind_1531_ = lean_ctor_get(v_inst_1525_, 1);
lean_inc(v_toBind_1531_);
v_toPure_1532_ = lean_ctor_get(v_toApplicative_1530_, 1);
lean_inc(v_toPure_1532_);
v___f_1533_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1533_, 0, v_f_1529_);
v___x_1534_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1525_, v___f_1533_, v_init_1528_, v_m_1527_);
v___f_1535_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1535_, 0, v_toPure_1532_);
v___x_1536_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1534_, v___f_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object* v_inst_1537_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1538_, 0, lean_box(0));
lean_closure_set(v___x_1538_, 1, lean_box(0));
lean_closure_set(v___x_1538_, 2, v_inst_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object* v_m_1539_, lean_object* v_00_u03b1_1540_, lean_object* v_inst_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1542_, 0, lean_box(0));
lean_closure_set(v___x_1542_, 1, lean_box(0));
lean_closure_set(v___x_1542_, 2, v_inst_1541_);
return v___x_1542_;
}
}
lean_object* l_Lean_instInhabitedMVarIdMap___redArg(){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_box(1);
return v___x_1544_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedMVarIdMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1545_;
v_res_1545_ = l_Lean_instInhabitedMVarIdMap___redArg();
stack->m_obj
 = v_res_1545_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg___boxed(lean_object* v___dummy_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_instInhabitedMVarIdMap___redArg();
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* v_00_u03b1_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_box(1);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___impl(lean_object* v_x_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_obj_tag_nat(v_x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___impl___boxed(lean_object* v_x_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lean_Expr_ctorIdx___impl(v_x_1552_);
lean_dec_ref(v_x_1552_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object* v_t_1554_, lean_object* v_k_1555_){
_start:
{
switch(lean_obj_tag(v_t_1554_))
{
case 4:
{
lean_object* v_declName_1556_; lean_object* v_us_1557_; lean_object* v___x_1558_; 
v_declName_1556_ = lean_ctor_get(v_t_1554_, 0);
lean_inc(v_declName_1556_);
v_us_1557_ = lean_ctor_get(v_t_1554_, 1);
lean_inc(v_us_1557_);
lean_dec_ref_known(v_t_1554_, 2);
v___x_1558_ = lean_apply_2(v_k_1555_, v_declName_1556_, v_us_1557_);
return v___x_1558_;
}
case 5:
{
lean_object* v_fn_1559_; lean_object* v_arg_1560_; lean_object* v___x_1561_; 
v_fn_1559_ = lean_ctor_get(v_t_1554_, 0);
lean_inc_ref(v_fn_1559_);
v_arg_1560_ = lean_ctor_get(v_t_1554_, 1);
lean_inc_ref(v_arg_1560_);
lean_dec_ref_known(v_t_1554_, 2);
v___x_1561_ = lean_apply_2(v_k_1555_, v_fn_1559_, v_arg_1560_);
return v___x_1561_;
}
case 6:
{
lean_object* v_binderName_1562_; lean_object* v_binderType_1563_; lean_object* v_body_1564_; uint8_t v_binderInfo_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v_binderName_1562_ = lean_ctor_get(v_t_1554_, 0);
lean_inc(v_binderName_1562_);
v_binderType_1563_ = lean_ctor_get(v_t_1554_, 1);
lean_inc_ref(v_binderType_1563_);
v_body_1564_ = lean_ctor_get(v_t_1554_, 2);
lean_inc_ref(v_body_1564_);
v_binderInfo_1565_ = lean_ctor_get_uint8(v_t_1554_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1554_, 3);
v___x_1566_ = lean_box(v_binderInfo_1565_);
v___x_1567_ = lean_apply_4(v_k_1555_, v_binderName_1562_, v_binderType_1563_, v_body_1564_, v___x_1566_);
return v___x_1567_;
}
case 7:
{
lean_object* v_binderName_1568_; lean_object* v_binderType_1569_; lean_object* v_body_1570_; uint8_t v_binderInfo_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_binderName_1568_ = lean_ctor_get(v_t_1554_, 0);
lean_inc(v_binderName_1568_);
v_binderType_1569_ = lean_ctor_get(v_t_1554_, 1);
lean_inc_ref(v_binderType_1569_);
v_body_1570_ = lean_ctor_get(v_t_1554_, 2);
lean_inc_ref(v_body_1570_);
v_binderInfo_1571_ = lean_ctor_get_uint8(v_t_1554_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1554_, 3);
v___x_1572_ = lean_box(v_binderInfo_1571_);
v___x_1573_ = lean_apply_4(v_k_1555_, v_binderName_1568_, v_binderType_1569_, v_body_1570_, v___x_1572_);
return v___x_1573_;
}
case 8:
{
lean_object* v_declName_1574_; lean_object* v_type_1575_; lean_object* v_value_1576_; lean_object* v_body_1577_; uint8_t v_nondep_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_declName_1574_ = lean_ctor_get(v_t_1554_, 0);
lean_inc(v_declName_1574_);
v_type_1575_ = lean_ctor_get(v_t_1554_, 1);
lean_inc_ref(v_type_1575_);
v_value_1576_ = lean_ctor_get(v_t_1554_, 2);
lean_inc_ref(v_value_1576_);
v_body_1577_ = lean_ctor_get(v_t_1554_, 3);
lean_inc_ref(v_body_1577_);
v_nondep_1578_ = lean_ctor_get_uint8(v_t_1554_, sizeof(void*)*4);
lean_dec_ref_known(v_t_1554_, 4);
v___x_1579_ = lean_box(v_nondep_1578_);
v___x_1580_ = lean_apply_5(v_k_1555_, v_declName_1574_, v_type_1575_, v_value_1576_, v_body_1577_, v___x_1579_);
return v___x_1580_;
}
case 9:
{
lean_object* v_a_1581_; lean_object* v___x_1582_; 
v_a_1581_ = lean_ctor_get(v_t_1554_, 0);
lean_inc_ref(v_a_1581_);
lean_dec_ref_known(v_t_1554_, 1);
v___x_1582_ = lean_apply_1(v_k_1555_, v_a_1581_);
return v___x_1582_;
}
case 10:
{
lean_object* v_data_1583_; lean_object* v_expr_1584_; lean_object* v___x_1585_; 
v_data_1583_ = lean_ctor_get(v_t_1554_, 0);
lean_inc(v_data_1583_);
v_expr_1584_ = lean_ctor_get(v_t_1554_, 1);
lean_inc_ref(v_expr_1584_);
lean_dec_ref_known(v_t_1554_, 2);
v___x_1585_ = lean_apply_2(v_k_1555_, v_data_1583_, v_expr_1584_);
return v___x_1585_;
}
case 11:
{
lean_object* v_typeName_1586_; lean_object* v_idx_1587_; lean_object* v_struct_1588_; lean_object* v___x_1589_; 
v_typeName_1586_ = lean_ctor_get(v_t_1554_, 0);
lean_inc(v_typeName_1586_);
v_idx_1587_ = lean_ctor_get(v_t_1554_, 1);
lean_inc(v_idx_1587_);
v_struct_1588_ = lean_ctor_get(v_t_1554_, 2);
lean_inc_ref(v_struct_1588_);
lean_dec_ref_known(v_t_1554_, 3);
v___x_1589_ = lean_apply_3(v_k_1555_, v_typeName_1586_, v_idx_1587_, v_struct_1588_);
return v___x_1589_;
}
default: 
{
lean_object* v_deBruijnIndex_1590_; lean_object* v___x_1591_; 
v_deBruijnIndex_1590_ = lean_ctor_get(v_t_1554_, 0);
lean_inc(v_deBruijnIndex_1590_);
lean_dec_ref(v_t_1554_);
v___x_1591_ = lean_apply_1(v_k_1555_, v_deBruijnIndex_1590_);
return v___x_1591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object* v_motive_1592_, lean_object* v_ctorIdx_1593_, lean_object* v_t_1594_, lean_object* v_h_1595_, lean_object* v_k_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Expr_ctorElim___redArg(v_t_1594_, v_k_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object* v_motive_1598_, lean_object* v_ctorIdx_1599_, lean_object* v_t_1600_, lean_object* v_h_1601_, lean_object* v_k_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_Expr_ctorElim(v_motive_1598_, v_ctorIdx_1599_, v_t_1600_, v_h_1601_, v_k_1602_);
lean_dec(v_ctorIdx_1599_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object* v_t_1604_, lean_object* v_bvar_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Expr_ctorElim___redArg(v_t_1604_, v_bvar_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object* v_motive_1607_, lean_object* v_t_1608_, lean_object* v_h_1609_, lean_object* v_bvar_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Expr_ctorElim___redArg(v_t_1608_, v_bvar_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object* v_t_1612_, lean_object* v_fvar_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Expr_ctorElim___redArg(v_t_1612_, v_fvar_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object* v_motive_1615_, lean_object* v_t_1616_, lean_object* v_h_1617_, lean_object* v_fvar_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Expr_ctorElim___redArg(v_t_1616_, v_fvar_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object* v_t_1620_, lean_object* v_mvar_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Expr_ctorElim___redArg(v_t_1620_, v_mvar_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object* v_motive_1623_, lean_object* v_t_1624_, lean_object* v_h_1625_, lean_object* v_mvar_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Expr_ctorElim___redArg(v_t_1624_, v_mvar_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object* v_t_1628_, lean_object* v_sort_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Expr_ctorElim___redArg(v_t_1628_, v_sort_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object* v_motive_1631_, lean_object* v_t_1632_, lean_object* v_h_1633_, lean_object* v_sort_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Expr_ctorElim___redArg(v_t_1632_, v_sort_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object* v_t_1636_, lean_object* v_const_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Expr_ctorElim___redArg(v_t_1636_, v_const_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object* v_motive_1639_, lean_object* v_t_1640_, lean_object* v_h_1641_, lean_object* v_const_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Expr_ctorElim___redArg(v_t_1640_, v_const_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object* v_t_1644_, lean_object* v_app_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Expr_ctorElim___redArg(v_t_1644_, v_app_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object* v_motive_1647_, lean_object* v_t_1648_, lean_object* v_h_1649_, lean_object* v_app_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_Expr_ctorElim___redArg(v_t_1648_, v_app_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object* v_t_1652_, lean_object* v_lam_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Expr_ctorElim___redArg(v_t_1652_, v_lam_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object* v_motive_1655_, lean_object* v_t_1656_, lean_object* v_h_1657_, lean_object* v_lam_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_Expr_ctorElim___redArg(v_t_1656_, v_lam_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object* v_t_1660_, lean_object* v_forallE_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Expr_ctorElim___redArg(v_t_1660_, v_forallE_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object* v_motive_1663_, lean_object* v_t_1664_, lean_object* v_h_1665_, lean_object* v_forallE_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_Expr_ctorElim___redArg(v_t_1664_, v_forallE_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object* v_t_1668_, lean_object* v_letE_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_Expr_ctorElim___redArg(v_t_1668_, v_letE_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object* v_motive_1671_, lean_object* v_t_1672_, lean_object* v_h_1673_, lean_object* v_letE_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_Expr_ctorElim___redArg(v_t_1672_, v_letE_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object* v_t_1676_, lean_object* v_lit_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_Expr_ctorElim___redArg(v_t_1676_, v_lit_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object* v_motive_1679_, lean_object* v_t_1680_, lean_object* v_h_1681_, lean_object* v_lit_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Expr_ctorElim___redArg(v_t_1680_, v_lit_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object* v_t_1684_, lean_object* v_mdata_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_Expr_ctorElim___redArg(v_t_1684_, v_mdata_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object* v_motive_1687_, lean_object* v_t_1688_, lean_object* v_h_1689_, lean_object* v_mdata_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_Expr_ctorElim___redArg(v_t_1688_, v_mdata_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object* v_t_1692_, lean_object* v_proj_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_Expr_ctorElim___redArg(v_t_1692_, v_proj_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object* v_motive_1695_, lean_object* v_t_1696_, lean_object* v_h_1697_, lean_object* v_proj_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Expr_ctorElim___redArg(v_t_1696_, v_proj_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT void l_Lean_Expr_data_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_1700_ = stack[0].m_obj;
uint64_t v_res_1701_;
v_res_1701_ = lean_expr_data(v_a_00___x40___internal___hyg_1700_);
stack->m_num = v_res_1701_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* v_a_00___x40___internal___hyg_1702_){
_start:
{
uint64_t v_res_1703_; lean_object* v_r_1704_; 
v_res_1703_ = lean_expr_data(v_a_00___x40___internal___hyg_1702_);
lean_dec_ref(v_a_00___x40___internal___hyg_1702_);
v_r_1704_ = lean_box_uint64(v_res_1703_);
return v_r_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object* v_t_1705_, lean_object* v_bvar_1706_, lean_object* v_fvar_1707_, lean_object* v_mvar_1708_, lean_object* v_sort_1709_, lean_object* v_const_1710_, lean_object* v_app_1711_, lean_object* v_lam_1712_, lean_object* v_forallE_1713_, lean_object* v_letE_1714_, lean_object* v_lit_1715_, lean_object* v_mdata_1716_, lean_object* v_proj_1717_){
_start:
{
switch(lean_obj_tag(v_t_1705_))
{
case 0:
{
lean_object* v_deBruijnIndex_1718_; lean_object* v___x_1719_; 
lean_dec(v_proj_1717_);
lean_dec(v_mdata_1716_);
lean_dec(v_lit_1715_);
lean_dec(v_letE_1714_);
lean_dec(v_forallE_1713_);
lean_dec(v_lam_1712_);
lean_dec(v_app_1711_);
lean_dec(v_const_1710_);
lean_dec(v_sort_1709_);
lean_dec(v_mvar_1708_);
lean_dec(v_fvar_1707_);
v_deBruijnIndex_1718_ = lean_ctor_get(v_t_1705_, 0);
lean_inc(v_deBruijnIndex_1718_);
lean_dec_ref_known(v_t_1705_, 1);
v___x_1719_ = lean_apply_1(v_bvar_1706_, v_deBruijnIndex_1718_);
return v___x_1719_;
}
case 1:
{
lean_object* v_fvarId_1720_; lean_object* v___x_1721_; 
lean_dec(v_proj_1717_);
lean_dec(v_mdata_1716_);
lean_dec(v_lit_1715_);
lean_dec(v_letE_1714_);
lean_dec(v_forallE_1713_);
lean_dec(v_lam_1712_);
lean_dec(v_app_1711_);
lean_dec(v_const_1710_);
lean_dec(v_sort_1709_);
lean_dec(v_mvar_1708_);
lean_dec(v_bvar_1706_);
v_fvarId_1720_ = lean_ctor_get(v_t_1705_, 0);
lean_inc(v_fvarId_1720_);
lean_dec_ref_known(v_t_1705_, 1);
v___x_1721_ = lean_apply_1(v_fvar_1707_, v_fvarId_1720_);
return v___x_1721_;
}
case 2:
{
lean_object* v_mvarId_1722_; lean_object* v___x_1723_; 
lean_dec(v_proj_1717_);
lean_dec(v_mdata_1716_);
lean_dec(v_lit_1715_);
lean_dec(v_letE_1714_);
lean_dec(v_forallE_1713_);
lean_dec(v_lam_1712_);
lean_dec(v_app_1711_);
lean_dec(v_const_1710_);
lean_dec(v_sort_1709_);
lean_dec(v_fvar_1707_);
lean_dec(v_bvar_1706_);
v_mvarId_1722_ = lean_ctor_get(v_t_1705_, 0);
lean_inc(v_mvarId_1722_);
lean_dec_ref_known(v_t_1705_, 1);
v___x_1723_ = lean_apply_1(v_mvar_1708_, v_mvarId_1722_);
return v___x_1723_;
}
case 3:
{
lean_object* v_u_1724_; lean_object* v___x_1725_; 
lean_dec(v_proj_1717_);
lean_dec(v_mdata_1716_);
lean_dec(v_lit_1715_);
lean_dec(v_letE_1714_);
lean_dec(v_forallE_1713_);
lean_dec(v_lam_1712_);
lean_dec(v_app_1711_);
lean_dec(v_const_1710_);
lean_dec(v_mvar_1708_);
lean_dec(v_fvar_1707_);
lean_dec(v_bvar_1706_);
v_u_1724_ = lean_ctor_get(v_t_1705_, 0);
lean_inc(v_u_1724_);
lean_dec_ref_known(v_t_1705_, 1);
v___x_1725_ = lean_apply_1(v_sort_1709_, v_u_1724_);
return v___x_1725_;
}
case 4:
{
lean_object* v_declName_1726_; lean_object* v_us_1727_; lean_object* v___x_1728_; 
lean_dec(v_proj_1717_);
lean_dec(v_mdata_1716_);
lean_dec(v_lit_1715_);
lean_dec(v_letE_1714_);
lean_dec(v_forallE_1713_);
lean_dec(v_lam_1712_);
lean_dec(v_app_1711_);
lean_dec(v_sort_1709_);
lean_dec(v_mvar_1708_);
lean_dec(v_fvar_1707_);
lean_dec(v_bvar_1706_);
v_declName_1726_ = lean_ctor_get(v_t_1705_, 0);
lean_inc(v_declName_1726_);
v_us_1727_ = lean_ctor_get(v_t_1705_, 1);
lean_inc(v_us_1727_);
lean_dec_ref_known(v_t_1705_, 2);
v___x_1728_ = lean_apply_2(v_const_1710_, v_declName_1726_, v_us_1727_);
return v___x_1728_;
}
case 5:
{
lean_object* v_fn_1729_; lean_object* v_arg_1730_; lean_object* v___x_1731_; 
lean_dec(v_proj_1717_);
lean_dec(v_mdata_1716_);
lean_dec(v_lit_1715_);
lean_dec(v_letE_1714_);
lean_dec(v_forallE_1713_);
lean_dec(v_lam_1712_);
lean_dec(v_const_1710_);
lean_dec(v_sort_1709_);
lean_dec(v_mvar_1708_);
lean_dec(v_fvar_1707_);
lean_dec(v_bvar_1706_);
v_fn_1729_ = lean_ctor_get(v_t_1705_, 0);
lean_inc_ref(v_fn_1729_);
v_arg_1730_ = lean_ctor_get(v_t_1705_, 1);
lean_inc_ref(v_arg_1730_);
lean_dec_ref_known(v_t_1705_, 2);
v___x_1731_ = lean_apply_2(v_app_1711_, v_fn_1729_, v_arg_1730_);
return v___x_1731_;
}
case 6:
{
lean_object* v_binderName_1732_; lean_object* v_binderType_1733_; lean_object* v_body_1734_; uint8_t v_binderInfo_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec(v_proj_1717_);
lean_dec(v_mdata_1716_);
lean_dec(v_lit_1715_);
lean_dec(v_letE_1714_);
lean_dec(v_forallE_1713_);
lean_dec(v_app_1711_);
lean_dec(v_const_1710_);
lean_dec(v_sort_1709_);
lean_dec(v_mvar_1708_);
lean_dec(v_fvar_1707_);
lean_dec(v_bvar_1706_);
v_binderName_1732_ = lean_ctor_get(v_t_1705_, 0);
lean_inc(v_binderName_1732_);
v_binderType_1733_ = lean_ctor_get(v_t_1705_, 1);
lean_inc_ref(v_binderType_1733_);
v_body_1734_ = lean_ctor_get(v_t_1705_, 2);
lean_inc_ref(v_body_1734_);
v_binderInfo_1735_ = lean_ctor_get_uint8(v_t_1705_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1705_, 3);
v___x_1736_ = lean_box(v_binderInfo_1735_);
v___x_1737_ = lean_apply_4(v_lam_1712_, v_binderName_1732_, v_binderType_1733_, v_body_1734_, v___x_1736_);
return v___x_1737_;
}
case 7:
{
lean_object* v_binderName_1738_; lean_object* v_binderType_1739_; lean_object* v_body_1740_; uint8_t v_binderInfo_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_dec(v_proj_1717_);
lean_dec(v_mdata_1716_);
lean_dec(v_lit_1715_);
lean_dec(v_letE_1714_);
lean_dec(v_lam_1712_);
lean_dec(v_app_1711_);
lean_dec(v_const_1710_);
lean_dec(v_sort_1709_);
lean_dec(v_mvar_1708_);
lean_dec(v_fvar_1707_);
lean_dec(v_bvar_1706_);
v_binderName_1738_ = lean_ctor_get(v_t_1705_, 0);
lean_inc(v_binderName_1738_);
v_binderType_1739_ = lean_ctor_get(v_t_1705_, 1);
lean_inc_ref(v_binderType_1739_);
v_body_1740_ = lean_ctor_get(v_t_1705_, 2);
lean_inc_ref(v_body_1740_);
v_binderInfo_1741_ = lean_ctor_get_uint8(v_t_1705_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1705_, 3);
v___x_1742_ = lean_box(v_binderInfo_1741_);
v___x_1743_ = lean_apply_4(v_forallE_1713_, v_binderName_1738_, v_binderType_1739_, v_body_1740_, v___x_1742_);
return v___x_1743_;
}
case 8:
{
lean_object* v_declName_1744_; lean_object* v_type_1745_; lean_object* v_value_1746_; lean_object* v_body_1747_; uint8_t v_nondep_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec(v_proj_1717_);
lean_dec(v_mdata_1716_);
lean_dec(v_lit_1715_);
lean_dec(v_forallE_1713_);
lean_dec(v_lam_1712_);
lean_dec(v_app_1711_);
lean_dec(v_const_1710_);
lean_dec(v_sort_1709_);
lean_dec(v_mvar_1708_);
lean_dec(v_fvar_1707_);
lean_dec(v_bvar_1706_);
v_declName_1744_ = lean_ctor_get(v_t_1705_, 0);
lean_inc(v_declName_1744_);
v_type_1745_ = lean_ctor_get(v_t_1705_, 1);
lean_inc_ref(v_type_1745_);
v_value_1746_ = lean_ctor_get(v_t_1705_, 2);
lean_inc_ref(v_value_1746_);
v_body_1747_ = lean_ctor_get(v_t_1705_, 3);
lean_inc_ref(v_body_1747_);
v_nondep_1748_ = lean_ctor_get_uint8(v_t_1705_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1705_, 4);
v___x_1749_ = lean_box(v_nondep_1748_);
v___x_1750_ = lean_apply_5(v_letE_1714_, v_declName_1744_, v_type_1745_, v_value_1746_, v_body_1747_, v___x_1749_);
return v___x_1750_;
}
case 9:
{
lean_object* v_a_1751_; lean_object* v___x_1752_; 
lean_dec(v_proj_1717_);
lean_dec(v_mdata_1716_);
lean_dec(v_letE_1714_);
lean_dec(v_forallE_1713_);
lean_dec(v_lam_1712_);
lean_dec(v_app_1711_);
lean_dec(v_const_1710_);
lean_dec(v_sort_1709_);
lean_dec(v_mvar_1708_);
lean_dec(v_fvar_1707_);
lean_dec(v_bvar_1706_);
v_a_1751_ = lean_ctor_get(v_t_1705_, 0);
lean_inc_ref(v_a_1751_);
lean_dec_ref_known(v_t_1705_, 1);
v___x_1752_ = lean_apply_1(v_lit_1715_, v_a_1751_);
return v___x_1752_;
}
case 10:
{
lean_object* v_data_1753_; lean_object* v_expr_1754_; lean_object* v___x_1755_; 
lean_dec(v_proj_1717_);
lean_dec(v_lit_1715_);
lean_dec(v_letE_1714_);
lean_dec(v_forallE_1713_);
lean_dec(v_lam_1712_);
lean_dec(v_app_1711_);
lean_dec(v_const_1710_);
lean_dec(v_sort_1709_);
lean_dec(v_mvar_1708_);
lean_dec(v_fvar_1707_);
lean_dec(v_bvar_1706_);
v_data_1753_ = lean_ctor_get(v_t_1705_, 0);
lean_inc(v_data_1753_);
v_expr_1754_ = lean_ctor_get(v_t_1705_, 1);
lean_inc_ref(v_expr_1754_);
lean_dec_ref_known(v_t_1705_, 2);
v___x_1755_ = lean_apply_2(v_mdata_1716_, v_data_1753_, v_expr_1754_);
return v___x_1755_;
}
default: 
{
lean_object* v_typeName_1756_; lean_object* v_idx_1757_; lean_object* v_struct_1758_; lean_object* v___x_1759_; 
lean_dec(v_mdata_1716_);
lean_dec(v_lit_1715_);
lean_dec(v_letE_1714_);
lean_dec(v_forallE_1713_);
lean_dec(v_lam_1712_);
lean_dec(v_app_1711_);
lean_dec(v_const_1710_);
lean_dec(v_sort_1709_);
lean_dec(v_mvar_1708_);
lean_dec(v_fvar_1707_);
lean_dec(v_bvar_1706_);
v_typeName_1756_ = lean_ctor_get(v_t_1705_, 0);
lean_inc(v_typeName_1756_);
v_idx_1757_ = lean_ctor_get(v_t_1705_, 1);
lean_inc(v_idx_1757_);
v_struct_1758_ = lean_ctor_get(v_t_1705_, 2);
lean_inc_ref(v_struct_1758_);
lean_dec_ref_known(v_t_1705_, 3);
v___x_1759_ = lean_apply_3(v_proj_1717_, v_typeName_1756_, v_idx_1757_, v_struct_1758_);
return v___x_1759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* v_motive_1760_, lean_object* v_t_1761_, lean_object* v_bvar_1762_, lean_object* v_fvar_1763_, lean_object* v_mvar_1764_, lean_object* v_sort_1765_, lean_object* v_const_1766_, lean_object* v_app_1767_, lean_object* v_lam_1768_, lean_object* v_forallE_1769_, lean_object* v_letE_1770_, lean_object* v_lit_1771_, lean_object* v_mdata_1772_, lean_object* v_proj_1773_){
_start:
{
switch(lean_obj_tag(v_t_1761_))
{
case 0:
{
lean_object* v_deBruijnIndex_1774_; lean_object* v___x_1775_; 
lean_dec(v_proj_1773_);
lean_dec(v_mdata_1772_);
lean_dec(v_lit_1771_);
lean_dec(v_letE_1770_);
lean_dec(v_forallE_1769_);
lean_dec(v_lam_1768_);
lean_dec(v_app_1767_);
lean_dec(v_const_1766_);
lean_dec(v_sort_1765_);
lean_dec(v_mvar_1764_);
lean_dec(v_fvar_1763_);
v_deBruijnIndex_1774_ = lean_ctor_get(v_t_1761_, 0);
lean_inc(v_deBruijnIndex_1774_);
lean_dec_ref_known(v_t_1761_, 1);
v___x_1775_ = lean_apply_1(v_bvar_1762_, v_deBruijnIndex_1774_);
return v___x_1775_;
}
case 1:
{
lean_object* v_fvarId_1776_; lean_object* v___x_1777_; 
lean_dec(v_proj_1773_);
lean_dec(v_mdata_1772_);
lean_dec(v_lit_1771_);
lean_dec(v_letE_1770_);
lean_dec(v_forallE_1769_);
lean_dec(v_lam_1768_);
lean_dec(v_app_1767_);
lean_dec(v_const_1766_);
lean_dec(v_sort_1765_);
lean_dec(v_mvar_1764_);
lean_dec(v_bvar_1762_);
v_fvarId_1776_ = lean_ctor_get(v_t_1761_, 0);
lean_inc(v_fvarId_1776_);
lean_dec_ref_known(v_t_1761_, 1);
v___x_1777_ = lean_apply_1(v_fvar_1763_, v_fvarId_1776_);
return v___x_1777_;
}
case 2:
{
lean_object* v_mvarId_1778_; lean_object* v___x_1779_; 
lean_dec(v_proj_1773_);
lean_dec(v_mdata_1772_);
lean_dec(v_lit_1771_);
lean_dec(v_letE_1770_);
lean_dec(v_forallE_1769_);
lean_dec(v_lam_1768_);
lean_dec(v_app_1767_);
lean_dec(v_const_1766_);
lean_dec(v_sort_1765_);
lean_dec(v_fvar_1763_);
lean_dec(v_bvar_1762_);
v_mvarId_1778_ = lean_ctor_get(v_t_1761_, 0);
lean_inc(v_mvarId_1778_);
lean_dec_ref_known(v_t_1761_, 1);
v___x_1779_ = lean_apply_1(v_mvar_1764_, v_mvarId_1778_);
return v___x_1779_;
}
case 3:
{
lean_object* v_u_1780_; lean_object* v___x_1781_; 
lean_dec(v_proj_1773_);
lean_dec(v_mdata_1772_);
lean_dec(v_lit_1771_);
lean_dec(v_letE_1770_);
lean_dec(v_forallE_1769_);
lean_dec(v_lam_1768_);
lean_dec(v_app_1767_);
lean_dec(v_const_1766_);
lean_dec(v_mvar_1764_);
lean_dec(v_fvar_1763_);
lean_dec(v_bvar_1762_);
v_u_1780_ = lean_ctor_get(v_t_1761_, 0);
lean_inc(v_u_1780_);
lean_dec_ref_known(v_t_1761_, 1);
v___x_1781_ = lean_apply_1(v_sort_1765_, v_u_1780_);
return v___x_1781_;
}
case 4:
{
lean_object* v_declName_1782_; lean_object* v_us_1783_; lean_object* v___x_1784_; 
lean_dec(v_proj_1773_);
lean_dec(v_mdata_1772_);
lean_dec(v_lit_1771_);
lean_dec(v_letE_1770_);
lean_dec(v_forallE_1769_);
lean_dec(v_lam_1768_);
lean_dec(v_app_1767_);
lean_dec(v_sort_1765_);
lean_dec(v_mvar_1764_);
lean_dec(v_fvar_1763_);
lean_dec(v_bvar_1762_);
v_declName_1782_ = lean_ctor_get(v_t_1761_, 0);
lean_inc(v_declName_1782_);
v_us_1783_ = lean_ctor_get(v_t_1761_, 1);
lean_inc(v_us_1783_);
lean_dec_ref_known(v_t_1761_, 2);
v___x_1784_ = lean_apply_2(v_const_1766_, v_declName_1782_, v_us_1783_);
return v___x_1784_;
}
case 5:
{
lean_object* v_fn_1785_; lean_object* v_arg_1786_; lean_object* v___x_1787_; 
lean_dec(v_proj_1773_);
lean_dec(v_mdata_1772_);
lean_dec(v_lit_1771_);
lean_dec(v_letE_1770_);
lean_dec(v_forallE_1769_);
lean_dec(v_lam_1768_);
lean_dec(v_const_1766_);
lean_dec(v_sort_1765_);
lean_dec(v_mvar_1764_);
lean_dec(v_fvar_1763_);
lean_dec(v_bvar_1762_);
v_fn_1785_ = lean_ctor_get(v_t_1761_, 0);
lean_inc_ref(v_fn_1785_);
v_arg_1786_ = lean_ctor_get(v_t_1761_, 1);
lean_inc_ref(v_arg_1786_);
lean_dec_ref_known(v_t_1761_, 2);
v___x_1787_ = lean_apply_2(v_app_1767_, v_fn_1785_, v_arg_1786_);
return v___x_1787_;
}
case 6:
{
lean_object* v_binderName_1788_; lean_object* v_binderType_1789_; lean_object* v_body_1790_; uint8_t v_binderInfo_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_dec(v_proj_1773_);
lean_dec(v_mdata_1772_);
lean_dec(v_lit_1771_);
lean_dec(v_letE_1770_);
lean_dec(v_forallE_1769_);
lean_dec(v_app_1767_);
lean_dec(v_const_1766_);
lean_dec(v_sort_1765_);
lean_dec(v_mvar_1764_);
lean_dec(v_fvar_1763_);
lean_dec(v_bvar_1762_);
v_binderName_1788_ = lean_ctor_get(v_t_1761_, 0);
lean_inc(v_binderName_1788_);
v_binderType_1789_ = lean_ctor_get(v_t_1761_, 1);
lean_inc_ref(v_binderType_1789_);
v_body_1790_ = lean_ctor_get(v_t_1761_, 2);
lean_inc_ref(v_body_1790_);
v_binderInfo_1791_ = lean_ctor_get_uint8(v_t_1761_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1761_, 3);
v___x_1792_ = lean_box(v_binderInfo_1791_);
v___x_1793_ = lean_apply_4(v_lam_1768_, v_binderName_1788_, v_binderType_1789_, v_body_1790_, v___x_1792_);
return v___x_1793_;
}
case 7:
{
lean_object* v_binderName_1794_; lean_object* v_binderType_1795_; lean_object* v_body_1796_; uint8_t v_binderInfo_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec(v_proj_1773_);
lean_dec(v_mdata_1772_);
lean_dec(v_lit_1771_);
lean_dec(v_letE_1770_);
lean_dec(v_lam_1768_);
lean_dec(v_app_1767_);
lean_dec(v_const_1766_);
lean_dec(v_sort_1765_);
lean_dec(v_mvar_1764_);
lean_dec(v_fvar_1763_);
lean_dec(v_bvar_1762_);
v_binderName_1794_ = lean_ctor_get(v_t_1761_, 0);
lean_inc(v_binderName_1794_);
v_binderType_1795_ = lean_ctor_get(v_t_1761_, 1);
lean_inc_ref(v_binderType_1795_);
v_body_1796_ = lean_ctor_get(v_t_1761_, 2);
lean_inc_ref(v_body_1796_);
v_binderInfo_1797_ = lean_ctor_get_uint8(v_t_1761_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1761_, 3);
v___x_1798_ = lean_box(v_binderInfo_1797_);
v___x_1799_ = lean_apply_4(v_forallE_1769_, v_binderName_1794_, v_binderType_1795_, v_body_1796_, v___x_1798_);
return v___x_1799_;
}
case 8:
{
lean_object* v_declName_1800_; lean_object* v_type_1801_; lean_object* v_value_1802_; lean_object* v_body_1803_; uint8_t v_nondep_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_dec(v_proj_1773_);
lean_dec(v_mdata_1772_);
lean_dec(v_lit_1771_);
lean_dec(v_forallE_1769_);
lean_dec(v_lam_1768_);
lean_dec(v_app_1767_);
lean_dec(v_const_1766_);
lean_dec(v_sort_1765_);
lean_dec(v_mvar_1764_);
lean_dec(v_fvar_1763_);
lean_dec(v_bvar_1762_);
v_declName_1800_ = lean_ctor_get(v_t_1761_, 0);
lean_inc(v_declName_1800_);
v_type_1801_ = lean_ctor_get(v_t_1761_, 1);
lean_inc_ref(v_type_1801_);
v_value_1802_ = lean_ctor_get(v_t_1761_, 2);
lean_inc_ref(v_value_1802_);
v_body_1803_ = lean_ctor_get(v_t_1761_, 3);
lean_inc_ref(v_body_1803_);
v_nondep_1804_ = lean_ctor_get_uint8(v_t_1761_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1761_, 4);
v___x_1805_ = lean_box(v_nondep_1804_);
v___x_1806_ = lean_apply_5(v_letE_1770_, v_declName_1800_, v_type_1801_, v_value_1802_, v_body_1803_, v___x_1805_);
return v___x_1806_;
}
case 9:
{
lean_object* v_a_1807_; lean_object* v___x_1808_; 
lean_dec(v_proj_1773_);
lean_dec(v_mdata_1772_);
lean_dec(v_letE_1770_);
lean_dec(v_forallE_1769_);
lean_dec(v_lam_1768_);
lean_dec(v_app_1767_);
lean_dec(v_const_1766_);
lean_dec(v_sort_1765_);
lean_dec(v_mvar_1764_);
lean_dec(v_fvar_1763_);
lean_dec(v_bvar_1762_);
v_a_1807_ = lean_ctor_get(v_t_1761_, 0);
lean_inc_ref(v_a_1807_);
lean_dec_ref_known(v_t_1761_, 1);
v___x_1808_ = lean_apply_1(v_lit_1771_, v_a_1807_);
return v___x_1808_;
}
case 10:
{
lean_object* v_data_1809_; lean_object* v_expr_1810_; lean_object* v___x_1811_; 
lean_dec(v_proj_1773_);
lean_dec(v_lit_1771_);
lean_dec(v_letE_1770_);
lean_dec(v_forallE_1769_);
lean_dec(v_lam_1768_);
lean_dec(v_app_1767_);
lean_dec(v_const_1766_);
lean_dec(v_sort_1765_);
lean_dec(v_mvar_1764_);
lean_dec(v_fvar_1763_);
lean_dec(v_bvar_1762_);
v_data_1809_ = lean_ctor_get(v_t_1761_, 0);
lean_inc(v_data_1809_);
v_expr_1810_ = lean_ctor_get(v_t_1761_, 1);
lean_inc_ref(v_expr_1810_);
lean_dec_ref_known(v_t_1761_, 2);
v___x_1811_ = lean_apply_2(v_mdata_1772_, v_data_1809_, v_expr_1810_);
return v___x_1811_;
}
default: 
{
lean_object* v_typeName_1812_; lean_object* v_idx_1813_; lean_object* v_struct_1814_; lean_object* v___x_1815_; 
lean_dec(v_mdata_1772_);
lean_dec(v_lit_1771_);
lean_dec(v_letE_1770_);
lean_dec(v_forallE_1769_);
lean_dec(v_lam_1768_);
lean_dec(v_app_1767_);
lean_dec(v_const_1766_);
lean_dec(v_sort_1765_);
lean_dec(v_mvar_1764_);
lean_dec(v_fvar_1763_);
lean_dec(v_bvar_1762_);
v_typeName_1812_ = lean_ctor_get(v_t_1761_, 0);
lean_inc(v_typeName_1812_);
v_idx_1813_ = lean_ctor_get(v_t_1761_, 1);
lean_inc(v_idx_1813_);
v_struct_1814_ = lean_ctor_get(v_t_1761_, 2);
lean_inc_ref(v_struct_1814_);
lean_dec_ref_known(v_t_1761_, 3);
v___x_1815_ = lean_apply_3(v_proj_1773_, v_typeName_1812_, v_idx_1813_, v_struct_1814_);
return v___x_1815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* v_deBruijnIndex_1816_){
_start:
{
uint64_t v___x_1817_; uint64_t v___x_1818_; uint64_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; uint32_t v___x_1822_; uint8_t v___x_1823_; uint64_t v___x_1824_; lean_object* v___x_1825_; 
v___x_1817_ = 7ULL;
v___x_1818_ = lean_uint64_of_nat(v_deBruijnIndex_1816_);
v___x_1819_ = lean_uint64_mix_hash(v___x_1817_, v___x_1818_);
v___x_1820_ = lean_unsigned_to_nat(1u);
v___x_1821_ = lean_nat_add(v_deBruijnIndex_1816_, v___x_1820_);
v___x_1822_ = 0;
v___x_1823_ = 0;
v___x_1824_ = lean_expr_mk_data(v___x_1819_, v___x_1821_, v___x_1822_, v___x_1823_, v___x_1823_, v___x_1823_, v___x_1823_);
v___x_1825_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1825_, 0, v_deBruijnIndex_1816_);
lean_ctor_set_uint64(v___x_1825_, sizeof(void*)*1, v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* v_fvarId_1826_){
_start:
{
uint64_t v___x_1827_; uint64_t v___x_1828_; uint64_t v___x_1829_; lean_object* v___x_1830_; uint32_t v___x_1831_; uint8_t v___x_1832_; uint8_t v___x_1833_; uint64_t v___x_1834_; lean_object* v___x_1835_; 
v___x_1827_ = 13ULL;
v___x_1828_ = l_Lean_instHashableFVarId_hash(v_fvarId_1826_);
v___x_1829_ = lean_uint64_mix_hash(v___x_1827_, v___x_1828_);
v___x_1830_ = lean_unsigned_to_nat(0u);
v___x_1831_ = 0;
v___x_1832_ = 1;
v___x_1833_ = 0;
v___x_1834_ = lean_expr_mk_data(v___x_1829_, v___x_1830_, v___x_1831_, v___x_1832_, v___x_1833_, v___x_1833_, v___x_1833_);
v___x_1835_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_1835_, 0, v_fvarId_1826_);
lean_ctor_set_uint64(v___x_1835_, sizeof(void*)*1, v___x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* v_mvarId_1836_){
_start:
{
uint64_t v___x_1837_; uint64_t v___x_1838_; uint64_t v___x_1839_; lean_object* v___x_1840_; uint32_t v___x_1841_; uint8_t v___x_1842_; uint8_t v___x_1843_; uint64_t v___x_1844_; lean_object* v___x_1845_; 
v___x_1837_ = 17ULL;
v___x_1838_ = l_Lean_instHashableMVarId_hash(v_mvarId_1836_);
v___x_1839_ = lean_uint64_mix_hash(v___x_1837_, v___x_1838_);
v___x_1840_ = lean_unsigned_to_nat(0u);
v___x_1841_ = 0;
v___x_1842_ = 0;
v___x_1843_ = 1;
v___x_1844_ = lean_expr_mk_data(v___x_1839_, v___x_1840_, v___x_1841_, v___x_1842_, v___x_1843_, v___x_1842_, v___x_1842_);
v___x_1845_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_1845_, 0, v_mvarId_1836_);
lean_ctor_set_uint64(v___x_1845_, sizeof(void*)*1, v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* v_u_1846_){
_start:
{
uint64_t v___x_1847_; uint64_t v___x_1848_; uint64_t v___x_1849_; lean_object* v___x_1850_; uint32_t v___x_1851_; uint8_t v___x_1852_; uint8_t v___x_1853_; uint8_t v___x_1854_; uint64_t v___x_1855_; lean_object* v___x_1856_; 
v___x_1847_ = 11ULL;
v___x_1848_ = l_Lean_Level_hash(v_u_1846_);
v___x_1849_ = lean_uint64_mix_hash(v___x_1847_, v___x_1848_);
v___x_1850_ = lean_unsigned_to_nat(0u);
v___x_1851_ = 0;
v___x_1852_ = 0;
v___x_1853_ = l_Lean_Level_hasMVar(v_u_1846_);
v___x_1854_ = l_Lean_Level_hasParam(v_u_1846_);
v___x_1855_ = lean_expr_mk_data(v___x_1849_, v___x_1850_, v___x_1851_, v___x_1852_, v___x_1852_, v___x_1853_, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(v___x_1856_, 0, v_u_1846_);
lean_ctor_set_uint64(v___x_1856_, sizeof(void*)*1, v___x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* v_fn_1857_, lean_object* v_arg_1858_){
_start:
{
uint64_t v___x_1859_; uint64_t v___x_1860_; uint64_t v___x_1861_; lean_object* v___x_1862_; 
v___x_1859_ = lean_expr_data(v_fn_1857_);
v___x_1860_ = lean_expr_data(v_arg_1858_);
v___x_1861_ = lean_expr_mk_app_data(v___x_1859_, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(v___x_1862_, 0, v_fn_1857_);
lean_ctor_set(v___x_1862_, 1, v_arg_1858_);
lean_ctor_set_uint64(v___x_1862_, sizeof(void*)*2, v___x_1861_);
return v___x_1862_;
}
}
lean_object* l_Lean_Expr_lam___override(lean_object* v_binderName_1863_, lean_object* v_binderType_1864_, lean_object* v_body_1865_, uint8_t v_binderInfo_1866_){
_start:
{
lean_object* v___y_1868_; uint64_t v___y_1869_; uint8_t v___y_1870_; uint32_t v___y_1871_; uint8_t v___y_1872_; uint8_t v___y_1873_; uint8_t v___y_1874_; uint64_t v___x_1877_; uint8_t v___x_1878_; uint32_t v___x_1879_; uint64_t v___x_1880_; uint64_t v___y_1882_; lean_object* v___y_1883_; uint8_t v___y_1884_; uint32_t v___y_1885_; uint8_t v___y_1886_; uint8_t v___y_1887_; lean_object* v___y_1891_; uint64_t v___y_1892_; uint8_t v___y_1893_; uint32_t v___y_1894_; uint8_t v___y_1895_; uint64_t v___y_1899_; lean_object* v___y_1900_; uint32_t v___y_1901_; uint8_t v___y_1902_; uint64_t v___y_1906_; uint32_t v___y_1907_; lean_object* v___y_1908_; uint32_t v___y_1912_; uint8_t v___x_1927_; uint32_t v___x_1928_; uint8_t v___x_1929_; 
v___x_1877_ = lean_expr_data(v_binderType_1864_);
v___x_1878_ = l_Lean_Expr_Data_approxDepth(v___x_1877_);
v___x_1879_ = lean_uint8_to_uint32(v___x_1878_);
v___x_1880_ = lean_expr_data(v_body_1865_);
v___x_1927_ = l_Lean_Expr_Data_approxDepth(v___x_1880_);
v___x_1928_ = lean_uint8_to_uint32(v___x_1927_);
v___x_1929_ = lean_uint32_dec_le(v___x_1879_, v___x_1928_);
if (v___x_1929_ == 0)
{
v___y_1912_ = v___x_1879_;
goto v___jp_1911_;
}
else
{
v___y_1912_ = v___x_1928_;
goto v___jp_1911_;
}
v___jp_1867_:
{
uint64_t v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_expr_mk_data(v___y_1869_, v___y_1868_, v___y_1871_, v___y_1870_, v___y_1872_, v___y_1873_, v___y_1874_);
v___x_1876_ = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(v___x_1876_, 0, v_binderName_1863_);
lean_ctor_set(v___x_1876_, 1, v_binderType_1864_);
lean_ctor_set(v___x_1876_, 2, v_body_1865_);
lean_ctor_set_uint64(v___x_1876_, sizeof(void*)*3, v___x_1875_);
lean_ctor_set_uint8(v___x_1876_, sizeof(void*)*3 + 8, v_binderInfo_1866_);
return v___x_1876_;
}
v___jp_1881_:
{
uint8_t v___x_1888_; 
v___x_1888_ = l_Lean_Expr_Data_hasLevelParam(v___x_1877_);
if (v___x_1888_ == 0)
{
uint8_t v___x_1889_; 
v___x_1889_ = l_Lean_Expr_Data_hasLevelParam(v___x_1880_);
v___y_1868_ = v___y_1883_;
v___y_1869_ = v___y_1882_;
v___y_1870_ = v___y_1884_;
v___y_1871_ = v___y_1885_;
v___y_1872_ = v___y_1886_;
v___y_1873_ = v___y_1887_;
v___y_1874_ = v___x_1889_;
goto v___jp_1867_;
}
else
{
v___y_1868_ = v___y_1883_;
v___y_1869_ = v___y_1882_;
v___y_1870_ = v___y_1884_;
v___y_1871_ = v___y_1885_;
v___y_1872_ = v___y_1886_;
v___y_1873_ = v___y_1887_;
v___y_1874_ = v___x_1888_;
goto v___jp_1867_;
}
}
v___jp_1890_:
{
uint8_t v___x_1896_; 
v___x_1896_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1877_);
if (v___x_1896_ == 0)
{
uint8_t v___x_1897_; 
v___x_1897_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1880_);
v___y_1882_ = v___y_1892_;
v___y_1883_ = v___y_1891_;
v___y_1884_ = v___y_1893_;
v___y_1885_ = v___y_1894_;
v___y_1886_ = v___y_1895_;
v___y_1887_ = v___x_1897_;
goto v___jp_1881_;
}
else
{
v___y_1882_ = v___y_1892_;
v___y_1883_ = v___y_1891_;
v___y_1884_ = v___y_1893_;
v___y_1885_ = v___y_1894_;
v___y_1886_ = v___y_1895_;
v___y_1887_ = v___x_1896_;
goto v___jp_1881_;
}
}
v___jp_1898_:
{
uint8_t v___x_1903_; 
v___x_1903_ = l_Lean_Expr_Data_hasExprMVar(v___x_1877_);
if (v___x_1903_ == 0)
{
uint8_t v___x_1904_; 
v___x_1904_ = l_Lean_Expr_Data_hasExprMVar(v___x_1880_);
v___y_1891_ = v___y_1900_;
v___y_1892_ = v___y_1899_;
v___y_1893_ = v___y_1902_;
v___y_1894_ = v___y_1901_;
v___y_1895_ = v___x_1904_;
goto v___jp_1890_;
}
else
{
v___y_1891_ = v___y_1900_;
v___y_1892_ = v___y_1899_;
v___y_1893_ = v___y_1902_;
v___y_1894_ = v___y_1901_;
v___y_1895_ = v___x_1903_;
goto v___jp_1890_;
}
}
v___jp_1905_:
{
uint8_t v___x_1909_; 
v___x_1909_ = l_Lean_Expr_Data_hasFVar(v___x_1877_);
if (v___x_1909_ == 0)
{
uint8_t v___x_1910_; 
v___x_1910_ = l_Lean_Expr_Data_hasFVar(v___x_1880_);
v___y_1899_ = v___y_1906_;
v___y_1900_ = v___y_1908_;
v___y_1901_ = v___y_1907_;
v___y_1902_ = v___x_1910_;
goto v___jp_1898_;
}
else
{
v___y_1899_ = v___y_1906_;
v___y_1900_ = v___y_1908_;
v___y_1901_ = v___y_1907_;
v___y_1902_ = v___x_1909_;
goto v___jp_1898_;
}
}
v___jp_1911_:
{
lean_object* v___x_1913_; uint32_t v___x_1914_; uint32_t v___x_1915_; uint64_t v___x_1916_; uint64_t v___x_1917_; uint64_t v___x_1918_; uint64_t v___x_1919_; uint64_t v___x_1920_; uint32_t v___x_1921_; lean_object* v___x_1922_; uint32_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; 
v___x_1913_ = lean_unsigned_to_nat(1u);
v___x_1914_ = 1;
v___x_1915_ = lean_uint32_add(v___y_1912_, v___x_1914_);
v___x_1916_ = lean_uint32_to_uint64(v___x_1915_);
v___x_1917_ = l_Lean_Expr_Data_hash(v___x_1877_);
v___x_1918_ = l_Lean_Expr_Data_hash(v___x_1880_);
v___x_1919_ = lean_uint64_mix_hash(v___x_1917_, v___x_1918_);
v___x_1920_ = lean_uint64_mix_hash(v___x_1916_, v___x_1919_);
v___x_1921_ = l_Lean_Expr_Data_looseBVarRange(v___x_1877_);
v___x_1922_ = lean_uint32_to_nat(v___x_1921_);
v___x_1923_ = l_Lean_Expr_Data_looseBVarRange(v___x_1880_);
v___x_1924_ = lean_uint32_to_nat(v___x_1923_);
v___x_1925_ = lean_nat_sub(v___x_1924_, v___x_1913_);
lean_dec(v___x_1924_);
v___x_1926_ = lean_nat_dec_le(v___x_1922_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_dec(v___x_1925_);
v___y_1906_ = v___x_1920_;
v___y_1907_ = v___x_1915_;
v___y_1908_ = v___x_1922_;
goto v___jp_1905_;
}
else
{
lean_dec(v___x_1922_);
v___y_1906_ = v___x_1920_;
v___y_1907_ = v___x_1915_;
v___y_1908_ = v___x_1925_;
goto v___jp_1905_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_lam___override_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderName_1863_ = stack[0].m_obj;
lean_object* v_binderType_1864_ = stack[1].m_obj;
lean_object* v_body_1865_ = stack[2].m_obj;
uint8_t v_binderInfo_1866_ = stack[3].m_num;
lean_object* v_res_1930_;
v_res_1930_ = l_Lean_Expr_lam___override(v_binderName_1863_, v_binderType_1864_, v_body_1865_, v_binderInfo_1866_);
stack->m_obj
 = v_res_1930_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* v_binderName_1931_, lean_object* v_binderType_1932_, lean_object* v_body_1933_, lean_object* v_binderInfo_1934_){
_start:
{
uint8_t v_binderInfo_boxed_1935_; lean_object* v_res_1936_; 
v_binderInfo_boxed_1935_ = lean_unbox(v_binderInfo_1934_);
v_res_1936_ = l_Lean_Expr_lam___override(v_binderName_1931_, v_binderType_1932_, v_body_1933_, v_binderInfo_boxed_1935_);
return v_res_1936_;
}
}
lean_object* l_Lean_Expr_forallE___override(lean_object* v_binderName_1937_, lean_object* v_binderType_1938_, lean_object* v_body_1939_, uint8_t v_binderInfo_1940_){
_start:
{
uint8_t v___y_1942_; uint8_t v___y_1943_; lean_object* v___y_1944_; uint8_t v___y_1945_; uint64_t v___y_1946_; uint32_t v___y_1947_; uint8_t v___y_1948_; uint64_t v___x_1951_; uint8_t v___x_1952_; uint32_t v___x_1953_; uint64_t v___x_1954_; uint8_t v___y_1956_; lean_object* v___y_1957_; uint8_t v___y_1958_; uint64_t v___y_1959_; uint32_t v___y_1960_; uint8_t v___y_1961_; uint8_t v___y_1965_; lean_object* v___y_1966_; uint64_t v___y_1967_; uint32_t v___y_1968_; uint8_t v___y_1969_; lean_object* v___y_1973_; uint64_t v___y_1974_; uint32_t v___y_1975_; uint8_t v___y_1976_; uint64_t v___y_1980_; uint32_t v___y_1981_; lean_object* v___y_1982_; uint32_t v___y_1986_; uint8_t v___x_2001_; uint32_t v___x_2002_; uint8_t v___x_2003_; 
v___x_1951_ = lean_expr_data(v_binderType_1938_);
v___x_1952_ = l_Lean_Expr_Data_approxDepth(v___x_1951_);
v___x_1953_ = lean_uint8_to_uint32(v___x_1952_);
v___x_1954_ = lean_expr_data(v_body_1939_);
v___x_2001_ = l_Lean_Expr_Data_approxDepth(v___x_1954_);
v___x_2002_ = lean_uint8_to_uint32(v___x_2001_);
v___x_2003_ = lean_uint32_dec_le(v___x_1953_, v___x_2002_);
if (v___x_2003_ == 0)
{
v___y_1986_ = v___x_1953_;
goto v___jp_1985_;
}
else
{
v___y_1986_ = v___x_2002_;
goto v___jp_1985_;
}
v___jp_1941_:
{
uint64_t v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = lean_expr_mk_data(v___y_1946_, v___y_1944_, v___y_1947_, v___y_1942_, v___y_1945_, v___y_1943_, v___y_1948_);
v___x_1950_ = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(v___x_1950_, 0, v_binderName_1937_);
lean_ctor_set(v___x_1950_, 1, v_binderType_1938_);
lean_ctor_set(v___x_1950_, 2, v_body_1939_);
lean_ctor_set_uint64(v___x_1950_, sizeof(void*)*3, v___x_1949_);
lean_ctor_set_uint8(v___x_1950_, sizeof(void*)*3 + 8, v_binderInfo_1940_);
return v___x_1950_;
}
v___jp_1955_:
{
uint8_t v___x_1962_; 
v___x_1962_ = l_Lean_Expr_Data_hasLevelParam(v___x_1951_);
if (v___x_1962_ == 0)
{
uint8_t v___x_1963_; 
v___x_1963_ = l_Lean_Expr_Data_hasLevelParam(v___x_1954_);
v___y_1942_ = v___y_1956_;
v___y_1943_ = v___y_1961_;
v___y_1944_ = v___y_1957_;
v___y_1945_ = v___y_1958_;
v___y_1946_ = v___y_1959_;
v___y_1947_ = v___y_1960_;
v___y_1948_ = v___x_1963_;
goto v___jp_1941_;
}
else
{
v___y_1942_ = v___y_1956_;
v___y_1943_ = v___y_1961_;
v___y_1944_ = v___y_1957_;
v___y_1945_ = v___y_1958_;
v___y_1946_ = v___y_1959_;
v___y_1947_ = v___y_1960_;
v___y_1948_ = v___x_1962_;
goto v___jp_1941_;
}
}
v___jp_1964_:
{
uint8_t v___x_1970_; 
v___x_1970_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1951_);
if (v___x_1970_ == 0)
{
uint8_t v___x_1971_; 
v___x_1971_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1954_);
v___y_1956_ = v___y_1965_;
v___y_1957_ = v___y_1966_;
v___y_1958_ = v___y_1969_;
v___y_1959_ = v___y_1967_;
v___y_1960_ = v___y_1968_;
v___y_1961_ = v___x_1971_;
goto v___jp_1955_;
}
else
{
v___y_1956_ = v___y_1965_;
v___y_1957_ = v___y_1966_;
v___y_1958_ = v___y_1969_;
v___y_1959_ = v___y_1967_;
v___y_1960_ = v___y_1968_;
v___y_1961_ = v___x_1970_;
goto v___jp_1955_;
}
}
v___jp_1972_:
{
uint8_t v___x_1977_; 
v___x_1977_ = l_Lean_Expr_Data_hasExprMVar(v___x_1951_);
if (v___x_1977_ == 0)
{
uint8_t v___x_1978_; 
v___x_1978_ = l_Lean_Expr_Data_hasExprMVar(v___x_1954_);
v___y_1965_ = v___y_1976_;
v___y_1966_ = v___y_1973_;
v___y_1967_ = v___y_1974_;
v___y_1968_ = v___y_1975_;
v___y_1969_ = v___x_1978_;
goto v___jp_1964_;
}
else
{
v___y_1965_ = v___y_1976_;
v___y_1966_ = v___y_1973_;
v___y_1967_ = v___y_1974_;
v___y_1968_ = v___y_1975_;
v___y_1969_ = v___x_1977_;
goto v___jp_1964_;
}
}
v___jp_1979_:
{
uint8_t v___x_1983_; 
v___x_1983_ = l_Lean_Expr_Data_hasFVar(v___x_1951_);
if (v___x_1983_ == 0)
{
uint8_t v___x_1984_; 
v___x_1984_ = l_Lean_Expr_Data_hasFVar(v___x_1954_);
v___y_1973_ = v___y_1982_;
v___y_1974_ = v___y_1980_;
v___y_1975_ = v___y_1981_;
v___y_1976_ = v___x_1984_;
goto v___jp_1972_;
}
else
{
v___y_1973_ = v___y_1982_;
v___y_1974_ = v___y_1980_;
v___y_1975_ = v___y_1981_;
v___y_1976_ = v___x_1983_;
goto v___jp_1972_;
}
}
v___jp_1985_:
{
lean_object* v___x_1987_; uint32_t v___x_1988_; uint32_t v___x_1989_; uint64_t v___x_1990_; uint64_t v___x_1991_; uint64_t v___x_1992_; uint64_t v___x_1993_; uint64_t v___x_1994_; uint32_t v___x_1995_; lean_object* v___x_1996_; uint32_t v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1987_ = lean_unsigned_to_nat(1u);
v___x_1988_ = 1;
v___x_1989_ = lean_uint32_add(v___y_1986_, v___x_1988_);
v___x_1990_ = lean_uint32_to_uint64(v___x_1989_);
v___x_1991_ = l_Lean_Expr_Data_hash(v___x_1951_);
v___x_1992_ = l_Lean_Expr_Data_hash(v___x_1954_);
v___x_1993_ = lean_uint64_mix_hash(v___x_1991_, v___x_1992_);
v___x_1994_ = lean_uint64_mix_hash(v___x_1990_, v___x_1993_);
v___x_1995_ = l_Lean_Expr_Data_looseBVarRange(v___x_1951_);
v___x_1996_ = lean_uint32_to_nat(v___x_1995_);
v___x_1997_ = l_Lean_Expr_Data_looseBVarRange(v___x_1954_);
v___x_1998_ = lean_uint32_to_nat(v___x_1997_);
v___x_1999_ = lean_nat_sub(v___x_1998_, v___x_1987_);
lean_dec(v___x_1998_);
v___x_2000_ = lean_nat_dec_le(v___x_1996_, v___x_1999_);
if (v___x_2000_ == 0)
{
lean_dec(v___x_1999_);
v___y_1980_ = v___x_1994_;
v___y_1981_ = v___x_1989_;
v___y_1982_ = v___x_1996_;
goto v___jp_1979_;
}
else
{
lean_dec(v___x_1996_);
v___y_1980_ = v___x_1994_;
v___y_1981_ = v___x_1989_;
v___y_1982_ = v___x_1999_;
goto v___jp_1979_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_forallE___override_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderName_1937_ = stack[0].m_obj;
lean_object* v_binderType_1938_ = stack[1].m_obj;
lean_object* v_body_1939_ = stack[2].m_obj;
uint8_t v_binderInfo_1940_ = stack[3].m_num;
lean_object* v_res_2004_;
v_res_2004_ = l_Lean_Expr_forallE___override(v_binderName_1937_, v_binderType_1938_, v_body_1939_, v_binderInfo_1940_);
stack->m_obj
 = v_res_2004_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* v_binderName_2005_, lean_object* v_binderType_2006_, lean_object* v_body_2007_, lean_object* v_binderInfo_2008_){
_start:
{
uint8_t v_binderInfo_boxed_2009_; lean_object* v_res_2010_; 
v_binderInfo_boxed_2009_ = lean_unbox(v_binderInfo_2008_);
v_res_2010_ = l_Lean_Expr_forallE___override(v_binderName_2005_, v_binderType_2006_, v_body_2007_, v_binderInfo_boxed_2009_);
return v_res_2010_;
}
}
lean_object* l_Lean_Expr_letE___override(lean_object* v_declName_2011_, lean_object* v_type_2012_, lean_object* v_value_2013_, lean_object* v_body_2014_, uint8_t v_nondep_2015_){
_start:
{
uint64_t v___y_2017_; uint32_t v___y_2018_; uint8_t v___y_2019_; uint8_t v___y_2020_; lean_object* v___y_2021_; uint8_t v___y_2022_; uint8_t v___y_2023_; uint64_t v___y_2027_; uint32_t v___y_2028_; uint8_t v___y_2029_; uint8_t v___y_2030_; lean_object* v___y_2031_; uint8_t v___y_2032_; uint64_t v___y_2033_; uint8_t v___y_2034_; uint64_t v___x_2036_; uint8_t v___x_2037_; uint32_t v___x_2038_; uint64_t v___x_2039_; uint64_t v___y_2041_; uint32_t v___y_2042_; uint8_t v___y_2043_; uint8_t v___y_2044_; lean_object* v___y_2045_; uint64_t v___y_2046_; uint8_t v___y_2047_; uint64_t v___y_2051_; uint32_t v___y_2052_; uint8_t v___y_2053_; uint8_t v___y_2054_; lean_object* v___y_2055_; uint64_t v___y_2056_; uint8_t v___y_2057_; uint64_t v___y_2060_; uint32_t v___y_2061_; uint8_t v___y_2062_; lean_object* v___y_2063_; uint64_t v___y_2064_; uint8_t v___y_2065_; uint64_t v___y_2069_; uint32_t v___y_2070_; uint8_t v___y_2071_; lean_object* v___y_2072_; uint64_t v___y_2073_; uint8_t v___y_2074_; uint64_t v___y_2077_; uint32_t v___y_2078_; lean_object* v___y_2079_; uint64_t v___y_2080_; uint8_t v___y_2081_; uint64_t v___y_2085_; uint32_t v___y_2086_; lean_object* v___y_2087_; uint64_t v___y_2088_; uint8_t v___y_2089_; uint64_t v___y_2092_; uint32_t v___y_2093_; uint64_t v___y_2094_; lean_object* v___y_2095_; uint64_t v___y_2099_; uint32_t v___y_2100_; lean_object* v___y_2101_; uint64_t v___y_2102_; lean_object* v___y_2103_; uint64_t v___y_2109_; uint32_t v___y_2110_; uint32_t v___y_2127_; uint8_t v___x_2132_; uint32_t v___x_2133_; uint8_t v___x_2134_; 
v___x_2036_ = lean_expr_data(v_type_2012_);
v___x_2037_ = l_Lean_Expr_Data_approxDepth(v___x_2036_);
v___x_2038_ = lean_uint8_to_uint32(v___x_2037_);
v___x_2039_ = lean_expr_data(v_value_2013_);
v___x_2132_ = l_Lean_Expr_Data_approxDepth(v___x_2039_);
v___x_2133_ = lean_uint8_to_uint32(v___x_2132_);
v___x_2134_ = lean_uint32_dec_le(v___x_2038_, v___x_2133_);
if (v___x_2134_ == 0)
{
v___y_2127_ = v___x_2038_;
goto v___jp_2126_;
}
else
{
v___y_2127_ = v___x_2133_;
goto v___jp_2126_;
}
v___jp_2016_:
{
uint64_t v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_expr_mk_data(v___y_2017_, v___y_2021_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2022_, v___y_2023_);
v___x_2025_ = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(v___x_2025_, 0, v_declName_2011_);
lean_ctor_set(v___x_2025_, 1, v_type_2012_);
lean_ctor_set(v___x_2025_, 2, v_value_2013_);
lean_ctor_set(v___x_2025_, 3, v_body_2014_);
lean_ctor_set_uint64(v___x_2025_, sizeof(void*)*4, v___x_2024_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*4 + 8, v_nondep_2015_);
return v___x_2025_;
}
v___jp_2026_:
{
if (v___y_2034_ == 0)
{
uint8_t v___x_2035_; 
v___x_2035_ = l_Lean_Expr_Data_hasLevelParam(v___y_2033_);
v___y_2017_ = v___y_2027_;
v___y_2018_ = v___y_2028_;
v___y_2019_ = v___y_2029_;
v___y_2020_ = v___y_2030_;
v___y_2021_ = v___y_2031_;
v___y_2022_ = v___y_2032_;
v___y_2023_ = v___x_2035_;
goto v___jp_2016_;
}
else
{
v___y_2017_ = v___y_2027_;
v___y_2018_ = v___y_2028_;
v___y_2019_ = v___y_2029_;
v___y_2020_ = v___y_2030_;
v___y_2021_ = v___y_2031_;
v___y_2022_ = v___y_2032_;
v___y_2023_ = v___y_2034_;
goto v___jp_2016_;
}
}
v___jp_2040_:
{
uint8_t v___x_2048_; 
v___x_2048_ = l_Lean_Expr_Data_hasLevelParam(v___x_2036_);
if (v___x_2048_ == 0)
{
uint8_t v___x_2049_; 
v___x_2049_ = l_Lean_Expr_Data_hasLevelParam(v___x_2039_);
v___y_2027_ = v___y_2041_;
v___y_2028_ = v___y_2042_;
v___y_2029_ = v___y_2043_;
v___y_2030_ = v___y_2044_;
v___y_2031_ = v___y_2045_;
v___y_2032_ = v___y_2047_;
v___y_2033_ = v___y_2046_;
v___y_2034_ = v___x_2049_;
goto v___jp_2026_;
}
else
{
v___y_2027_ = v___y_2041_;
v___y_2028_ = v___y_2042_;
v___y_2029_ = v___y_2043_;
v___y_2030_ = v___y_2044_;
v___y_2031_ = v___y_2045_;
v___y_2032_ = v___y_2047_;
v___y_2033_ = v___y_2046_;
v___y_2034_ = v___x_2048_;
goto v___jp_2026_;
}
}
v___jp_2050_:
{
if (v___y_2057_ == 0)
{
uint8_t v___x_2058_; 
v___x_2058_ = l_Lean_Expr_Data_hasLevelMVar(v___y_2056_);
v___y_2041_ = v___y_2051_;
v___y_2042_ = v___y_2052_;
v___y_2043_ = v___y_2053_;
v___y_2044_ = v___y_2054_;
v___y_2045_ = v___y_2055_;
v___y_2046_ = v___y_2056_;
v___y_2047_ = v___x_2058_;
goto v___jp_2040_;
}
else
{
v___y_2041_ = v___y_2051_;
v___y_2042_ = v___y_2052_;
v___y_2043_ = v___y_2053_;
v___y_2044_ = v___y_2054_;
v___y_2045_ = v___y_2055_;
v___y_2046_ = v___y_2056_;
v___y_2047_ = v___y_2057_;
goto v___jp_2040_;
}
}
v___jp_2059_:
{
uint8_t v___x_2066_; 
v___x_2066_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2036_);
if (v___x_2066_ == 0)
{
uint8_t v___x_2067_; 
v___x_2067_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2039_);
v___y_2051_ = v___y_2060_;
v___y_2052_ = v___y_2061_;
v___y_2053_ = v___y_2062_;
v___y_2054_ = v___y_2065_;
v___y_2055_ = v___y_2063_;
v___y_2056_ = v___y_2064_;
v___y_2057_ = v___x_2067_;
goto v___jp_2050_;
}
else
{
v___y_2051_ = v___y_2060_;
v___y_2052_ = v___y_2061_;
v___y_2053_ = v___y_2062_;
v___y_2054_ = v___y_2065_;
v___y_2055_ = v___y_2063_;
v___y_2056_ = v___y_2064_;
v___y_2057_ = v___x_2066_;
goto v___jp_2050_;
}
}
v___jp_2068_:
{
if (v___y_2074_ == 0)
{
uint8_t v___x_2075_; 
v___x_2075_ = l_Lean_Expr_Data_hasExprMVar(v___y_2073_);
v___y_2060_ = v___y_2069_;
v___y_2061_ = v___y_2070_;
v___y_2062_ = v___y_2071_;
v___y_2063_ = v___y_2072_;
v___y_2064_ = v___y_2073_;
v___y_2065_ = v___x_2075_;
goto v___jp_2059_;
}
else
{
v___y_2060_ = v___y_2069_;
v___y_2061_ = v___y_2070_;
v___y_2062_ = v___y_2071_;
v___y_2063_ = v___y_2072_;
v___y_2064_ = v___y_2073_;
v___y_2065_ = v___y_2074_;
goto v___jp_2059_;
}
}
v___jp_2076_:
{
uint8_t v___x_2082_; 
v___x_2082_ = l_Lean_Expr_Data_hasExprMVar(v___x_2036_);
if (v___x_2082_ == 0)
{
uint8_t v___x_2083_; 
v___x_2083_ = l_Lean_Expr_Data_hasExprMVar(v___x_2039_);
v___y_2069_ = v___y_2077_;
v___y_2070_ = v___y_2078_;
v___y_2071_ = v___y_2081_;
v___y_2072_ = v___y_2079_;
v___y_2073_ = v___y_2080_;
v___y_2074_ = v___x_2083_;
goto v___jp_2068_;
}
else
{
v___y_2069_ = v___y_2077_;
v___y_2070_ = v___y_2078_;
v___y_2071_ = v___y_2081_;
v___y_2072_ = v___y_2079_;
v___y_2073_ = v___y_2080_;
v___y_2074_ = v___x_2082_;
goto v___jp_2068_;
}
}
v___jp_2084_:
{
if (v___y_2089_ == 0)
{
uint8_t v___x_2090_; 
v___x_2090_ = l_Lean_Expr_Data_hasFVar(v___y_2088_);
v___y_2077_ = v___y_2085_;
v___y_2078_ = v___y_2086_;
v___y_2079_ = v___y_2087_;
v___y_2080_ = v___y_2088_;
v___y_2081_ = v___x_2090_;
goto v___jp_2076_;
}
else
{
v___y_2077_ = v___y_2085_;
v___y_2078_ = v___y_2086_;
v___y_2079_ = v___y_2087_;
v___y_2080_ = v___y_2088_;
v___y_2081_ = v___y_2089_;
goto v___jp_2076_;
}
}
v___jp_2091_:
{
uint8_t v___x_2096_; 
v___x_2096_ = l_Lean_Expr_Data_hasFVar(v___x_2036_);
if (v___x_2096_ == 0)
{
uint8_t v___x_2097_; 
v___x_2097_ = l_Lean_Expr_Data_hasFVar(v___x_2039_);
v___y_2085_ = v___y_2092_;
v___y_2086_ = v___y_2093_;
v___y_2087_ = v___y_2095_;
v___y_2088_ = v___y_2094_;
v___y_2089_ = v___x_2097_;
goto v___jp_2084_;
}
else
{
v___y_2085_ = v___y_2092_;
v___y_2086_ = v___y_2093_;
v___y_2087_ = v___y_2095_;
v___y_2088_ = v___y_2094_;
v___y_2089_ = v___x_2096_;
goto v___jp_2084_;
}
}
v___jp_2098_:
{
uint32_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2104_ = l_Lean_Expr_Data_looseBVarRange(v___y_2102_);
v___x_2105_ = lean_uint32_to_nat(v___x_2104_);
v___x_2106_ = lean_nat_sub(v___x_2105_, v___y_2101_);
lean_dec(v___x_2105_);
v___x_2107_ = lean_nat_dec_le(v___y_2103_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_dec(v___x_2106_);
v___y_2092_ = v___y_2099_;
v___y_2093_ = v___y_2100_;
v___y_2094_ = v___y_2102_;
v___y_2095_ = v___y_2103_;
goto v___jp_2091_;
}
else
{
lean_dec(v___y_2103_);
v___y_2092_ = v___y_2099_;
v___y_2093_ = v___y_2100_;
v___y_2094_ = v___y_2102_;
v___y_2095_ = v___x_2106_;
goto v___jp_2091_;
}
}
v___jp_2108_:
{
lean_object* v___x_2111_; uint32_t v___x_2112_; uint32_t v___x_2113_; uint64_t v___x_2114_; uint64_t v___x_2115_; uint64_t v___x_2116_; uint64_t v___x_2117_; uint64_t v___x_2118_; uint64_t v___x_2119_; uint64_t v___x_2120_; uint32_t v___x_2121_; lean_object* v___x_2122_; uint32_t v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2111_ = lean_unsigned_to_nat(1u);
v___x_2112_ = 1;
v___x_2113_ = lean_uint32_add(v___y_2110_, v___x_2112_);
v___x_2114_ = lean_uint32_to_uint64(v___x_2113_);
v___x_2115_ = l_Lean_Expr_Data_hash(v___x_2036_);
v___x_2116_ = l_Lean_Expr_Data_hash(v___x_2039_);
v___x_2117_ = l_Lean_Expr_Data_hash(v___y_2109_);
v___x_2118_ = lean_uint64_mix_hash(v___x_2116_, v___x_2117_);
v___x_2119_ = lean_uint64_mix_hash(v___x_2115_, v___x_2118_);
v___x_2120_ = lean_uint64_mix_hash(v___x_2114_, v___x_2119_);
v___x_2121_ = l_Lean_Expr_Data_looseBVarRange(v___x_2036_);
v___x_2122_ = lean_uint32_to_nat(v___x_2121_);
v___x_2123_ = l_Lean_Expr_Data_looseBVarRange(v___x_2039_);
v___x_2124_ = lean_uint32_to_nat(v___x_2123_);
v___x_2125_ = lean_nat_dec_le(v___x_2122_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_dec(v___x_2124_);
v___y_2099_ = v___x_2120_;
v___y_2100_ = v___x_2113_;
v___y_2101_ = v___x_2111_;
v___y_2102_ = v___y_2109_;
v___y_2103_ = v___x_2122_;
goto v___jp_2098_;
}
else
{
lean_dec(v___x_2122_);
v___y_2099_ = v___x_2120_;
v___y_2100_ = v___x_2113_;
v___y_2101_ = v___x_2111_;
v___y_2102_ = v___y_2109_;
v___y_2103_ = v___x_2124_;
goto v___jp_2098_;
}
}
v___jp_2126_:
{
uint64_t v___x_2128_; uint8_t v___x_2129_; uint32_t v___x_2130_; uint8_t v___x_2131_; 
v___x_2128_ = lean_expr_data(v_body_2014_);
v___x_2129_ = l_Lean_Expr_Data_approxDepth(v___x_2128_);
v___x_2130_ = lean_uint8_to_uint32(v___x_2129_);
v___x_2131_ = lean_uint32_dec_le(v___y_2127_, v___x_2130_);
if (v___x_2131_ == 0)
{
v___y_2109_ = v___x_2128_;
v___y_2110_ = v___y_2127_;
goto v___jp_2108_;
}
else
{
v___y_2109_ = v___x_2128_;
v___y_2110_ = v___x_2130_;
goto v___jp_2108_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_letE___override_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2011_ = stack[0].m_obj;
lean_object* v_type_2012_ = stack[1].m_obj;
lean_object* v_value_2013_ = stack[2].m_obj;
lean_object* v_body_2014_ = stack[3].m_obj;
uint8_t v_nondep_2015_ = stack[4].m_num;
lean_object* v_res_2135_;
v_res_2135_ = l_Lean_Expr_letE___override(v_declName_2011_, v_type_2012_, v_value_2013_, v_body_2014_, v_nondep_2015_);
stack->m_obj
 = v_res_2135_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* v_declName_2136_, lean_object* v_type_2137_, lean_object* v_value_2138_, lean_object* v_body_2139_, lean_object* v_nondep_2140_){
_start:
{
uint8_t v_nondep_boxed_2141_; lean_object* v_res_2142_; 
v_nondep_boxed_2141_ = lean_unbox(v_nondep_2140_);
v_res_2142_ = l_Lean_Expr_letE___override(v_declName_2136_, v_type_2137_, v_value_2138_, v_body_2139_, v_nondep_boxed_2141_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* v_a_2143_){
_start:
{
uint64_t v___x_2144_; uint64_t v___x_2145_; uint64_t v___x_2146_; lean_object* v___x_2147_; uint32_t v___x_2148_; uint8_t v___x_2149_; uint64_t v___x_2150_; lean_object* v___x_2151_; 
v___x_2144_ = 3ULL;
v___x_2145_ = l_Lean_Literal_hash(v_a_2143_);
v___x_2146_ = lean_uint64_mix_hash(v___x_2144_, v___x_2145_);
v___x_2147_ = lean_unsigned_to_nat(0u);
v___x_2148_ = 0;
v___x_2149_ = 0;
v___x_2150_ = lean_expr_mk_data(v___x_2146_, v___x_2147_, v___x_2148_, v___x_2149_, v___x_2149_, v___x_2149_, v___x_2149_);
v___x_2151_ = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(v___x_2151_, 0, v_a_2143_);
lean_ctor_set_uint64(v___x_2151_, sizeof(void*)*1, v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* v_data_2152_, lean_object* v_expr_2153_){
_start:
{
uint64_t v___x_2154_; uint8_t v___x_2155_; uint32_t v___x_2156_; uint32_t v___x_2157_; uint32_t v___x_2158_; uint64_t v___x_2159_; uint64_t v___x_2160_; uint64_t v___x_2161_; uint32_t v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; uint8_t v___x_2165_; uint8_t v___x_2166_; uint8_t v___x_2167_; uint64_t v___x_2168_; lean_object* v___x_2169_; 
v___x_2154_ = lean_expr_data(v_expr_2153_);
v___x_2155_ = l_Lean_Expr_Data_approxDepth(v___x_2154_);
v___x_2156_ = lean_uint8_to_uint32(v___x_2155_);
v___x_2157_ = 1;
v___x_2158_ = lean_uint32_add(v___x_2156_, v___x_2157_);
v___x_2159_ = lean_uint32_to_uint64(v___x_2158_);
v___x_2160_ = l_Lean_Expr_Data_hash(v___x_2154_);
v___x_2161_ = lean_uint64_mix_hash(v___x_2159_, v___x_2160_);
v___x_2162_ = l_Lean_Expr_Data_looseBVarRange(v___x_2154_);
v___x_2163_ = lean_uint32_to_nat(v___x_2162_);
v___x_2164_ = l_Lean_Expr_Data_hasFVar(v___x_2154_);
v___x_2165_ = l_Lean_Expr_Data_hasExprMVar(v___x_2154_);
v___x_2166_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2154_);
v___x_2167_ = l_Lean_Expr_Data_hasLevelParam(v___x_2154_);
v___x_2168_ = lean_expr_mk_data(v___x_2161_, v___x_2163_, v___x_2158_, v___x_2164_, v___x_2165_, v___x_2166_, v___x_2167_);
v___x_2169_ = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(v___x_2169_, 0, v_data_2152_);
lean_ctor_set(v___x_2169_, 1, v_expr_2153_);
lean_ctor_set_uint64(v___x_2169_, sizeof(void*)*2, v___x_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* v_typeName_2170_, lean_object* v_idx_2171_, lean_object* v_struct_2172_){
_start:
{
uint64_t v___x_2173_; uint8_t v___x_2174_; uint32_t v___x_2175_; uint32_t v___x_2176_; uint32_t v___x_2177_; uint64_t v___x_2178_; uint64_t v___y_2180_; 
v___x_2173_ = lean_expr_data(v_struct_2172_);
v___x_2174_ = l_Lean_Expr_Data_approxDepth(v___x_2173_);
v___x_2175_ = lean_uint8_to_uint32(v___x_2174_);
v___x_2176_ = 1;
v___x_2177_ = lean_uint32_add(v___x_2175_, v___x_2176_);
v___x_2178_ = lean_uint32_to_uint64(v___x_2177_);
if (lean_obj_tag(v_typeName_2170_) == 0)
{
uint64_t v___x_2194_; 
v___x_2194_ = 1723ULL;
v___y_2180_ = v___x_2194_;
goto v___jp_2179_;
}
else
{
uint64_t v_hash_2195_; 
v_hash_2195_ = lean_ctor_get_uint64(v_typeName_2170_, sizeof(void*)*2);
v___y_2180_ = v_hash_2195_;
goto v___jp_2179_;
}
v___jp_2179_:
{
uint64_t v___x_2181_; uint64_t v___x_2182_; uint64_t v___x_2183_; uint64_t v___x_2184_; uint64_t v___x_2185_; uint32_t v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; uint8_t v___x_2189_; uint8_t v___x_2190_; uint8_t v___x_2191_; uint64_t v___x_2192_; lean_object* v___x_2193_; 
v___x_2181_ = lean_uint64_of_nat(v_idx_2171_);
v___x_2182_ = l_Lean_Expr_Data_hash(v___x_2173_);
v___x_2183_ = lean_uint64_mix_hash(v___x_2181_, v___x_2182_);
v___x_2184_ = lean_uint64_mix_hash(v___y_2180_, v___x_2183_);
v___x_2185_ = lean_uint64_mix_hash(v___x_2178_, v___x_2184_);
v___x_2186_ = l_Lean_Expr_Data_looseBVarRange(v___x_2173_);
v___x_2187_ = lean_uint32_to_nat(v___x_2186_);
v___x_2188_ = l_Lean_Expr_Data_hasFVar(v___x_2173_);
v___x_2189_ = l_Lean_Expr_Data_hasExprMVar(v___x_2173_);
v___x_2190_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2173_);
v___x_2191_ = l_Lean_Expr_Data_hasLevelParam(v___x_2173_);
v___x_2192_ = lean_expr_mk_data(v___x_2185_, v___x_2187_, v___x_2177_, v___x_2188_, v___x_2189_, v___x_2190_, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(v___x_2193_, 0, v_typeName_2170_);
lean_ctor_set(v___x_2193_, 1, v_idx_2171_);
lean_ctor_set(v___x_2193_, 2, v_struct_2172_);
lean_ctor_set_uint64(v___x_2193_, sizeof(void*)*3, v___x_2192_);
return v___x_2193_;
}
}
}
uint8_t l_List_any___at___00Lean_Expr_const___override_spec__5(lean_object* v_x_2196_){
_start:
{
if (lean_obj_tag(v_x_2196_) == 0)
{
uint8_t v___x_2197_; 
v___x_2197_ = 0;
return v___x_2197_;
}
else
{
lean_object* v_head_2198_; lean_object* v_tail_2199_; uint8_t v___x_2200_; 
v_head_2198_ = lean_ctor_get(v_x_2196_, 0);
v_tail_2199_ = lean_ctor_get(v_x_2196_, 1);
v___x_2200_ = l_Lean_Level_hasMVar(v_head_2198_);
if (v___x_2200_ == 0)
{
v_x_2196_ = v_tail_2199_;
goto _start;
}
else
{
return v___x_2200_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Expr_const___override_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2196_ = stack[0].m_obj;
uint8_t v_res_2202_;
v_res_2202_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_x_2196_);
stack->m_num = v_res_2202_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__5___boxed(lean_object* v_x_2203_){
_start:
{
uint8_t v_res_2204_; lean_object* v_r_2205_; 
v_res_2204_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_x_2203_);
lean_dec(v_x_2203_);
v_r_2205_ = lean_box(v_res_2204_);
return v_r_2205_;
}
}
uint8_t l_List_any___at___00Lean_Expr_const___override_spec__6(lean_object* v_x_2206_){
_start:
{
if (lean_obj_tag(v_x_2206_) == 0)
{
uint8_t v___x_2207_; 
v___x_2207_ = 0;
return v___x_2207_;
}
else
{
lean_object* v_head_2208_; lean_object* v_tail_2209_; uint8_t v___x_2210_; 
v_head_2208_ = lean_ctor_get(v_x_2206_, 0);
v_tail_2209_ = lean_ctor_get(v_x_2206_, 1);
v___x_2210_ = l_Lean_Level_hasParam(v_head_2208_);
if (v___x_2210_ == 0)
{
v_x_2206_ = v_tail_2209_;
goto _start;
}
else
{
return v___x_2210_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Expr_const___override_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2206_ = stack[0].m_obj;
uint8_t v_res_2212_;
v_res_2212_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_x_2206_);
stack->m_num = v_res_2212_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__6___boxed(lean_object* v_x_2213_){
_start:
{
uint8_t v_res_2214_; lean_object* v_r_2215_; 
v_res_2214_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_x_2213_);
lean_dec(v_x_2213_);
v_r_2215_ = lean_box(v_res_2214_);
return v_r_2215_;
}
}
uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t v_x_2216_, lean_object* v_x_2217_){
_start:
{
if (lean_obj_tag(v_x_2217_) == 0)
{
return v_x_2216_;
}
else
{
lean_object* v_head_2218_; lean_object* v_tail_2219_; uint64_t v___x_2220_; uint64_t v___x_2221_; 
v_head_2218_ = lean_ctor_get(v_x_2217_, 0);
v_tail_2219_ = lean_ctor_get(v_x_2217_, 1);
v___x_2220_ = l_Lean_Level_hash(v_head_2218_);
v___x_2221_ = lean_uint64_mix_hash(v_x_2216_, v___x_2220_);
v_x_2216_ = v___x_2221_;
v_x_2217_ = v_tail_2219_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_foldl___at___00Lean_Expr_const___override_spec__4_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_2216_ = stack[0].m_num;
lean_object* v_x_2217_ = stack[1].m_obj;
uint64_t v_res_2223_;
v_res_2223_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_2216_, v_x_2217_);
stack->m_num = v_res_2223_;
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object* v_x_2224_, lean_object* v_x_2225_){
_start:
{
uint64_t v_x_2062__boxed_2226_; uint64_t v_res_2227_; lean_object* v_r_2228_; 
v_x_2062__boxed_2226_ = lean_unbox_uint64(v_x_2224_);
lean_dec_ref(v_x_2224_);
v_res_2227_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_2062__boxed_2226_, v_x_2225_);
lean_dec(v_x_2225_);
v_r_2228_ = lean_box_uint64(v_res_2227_);
return v_r_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* v_declName_2229_, lean_object* v_us_2230_){
_start:
{
uint64_t v___x_2231_; uint64_t v___y_2233_; 
v___x_2231_ = 5ULL;
if (lean_obj_tag(v_declName_2229_) == 0)
{
uint64_t v___x_2245_; 
v___x_2245_ = 1723ULL;
v___y_2233_ = v___x_2245_;
goto v___jp_2232_;
}
else
{
uint64_t v_hash_2246_; 
v_hash_2246_ = lean_ctor_get_uint64(v_declName_2229_, sizeof(void*)*2);
v___y_2233_ = v_hash_2246_;
goto v___jp_2232_;
}
v___jp_2232_:
{
uint64_t v___x_2234_; uint64_t v___x_2235_; uint64_t v___x_2236_; uint64_t v___x_2237_; lean_object* v___x_2238_; uint32_t v___x_2239_; uint8_t v___x_2240_; uint8_t v___x_2241_; uint8_t v___x_2242_; uint64_t v___x_2243_; lean_object* v___x_2244_; 
v___x_2234_ = 7ULL;
v___x_2235_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v___x_2234_, v_us_2230_);
v___x_2236_ = lean_uint64_mix_hash(v___y_2233_, v___x_2235_);
v___x_2237_ = lean_uint64_mix_hash(v___x_2231_, v___x_2236_);
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = 0;
v___x_2240_ = 0;
v___x_2241_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_us_2230_);
v___x_2242_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_us_2230_);
v___x_2243_ = lean_expr_mk_data(v___x_2237_, v___x_2238_, v___x_2239_, v___x_2240_, v___x_2240_, v___x_2241_, v___x_2242_);
v___x_2244_ = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(v___x_2244_, 0, v_declName_2229_);
lean_ctor_set(v___x_2244_, 1, v_us_2230_);
lean_ctor_set_uint64(v___x_2244_, sizeof(void*)*2, v___x_2243_);
return v___x_2244_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_unsigned_to_nat(0u);
v___x_2249_ = l_Lean_instReprLevel_repr(v___y_2247_, v___x_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2250_, lean_object* v_x_2251_, lean_object* v_x_2252_){
_start:
{
if (lean_obj_tag(v_x_2252_) == 0)
{
lean_dec(v_x_2250_);
return v_x_2251_;
}
else
{
lean_object* v_head_2253_; lean_object* v_tail_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2265_; 
v_head_2253_ = lean_ctor_get(v_x_2252_, 0);
v_tail_2254_ = lean_ctor_get(v_x_2252_, 1);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_x_2252_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2256_ = v_x_2252_;
v_isShared_2257_ = v_isSharedCheck_2265_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_tail_2254_);
lean_inc(v_head_2253_);
lean_dec(v_x_2252_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2265_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
lean_inc(v_x_2250_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set_tag(v___x_2256_, 5);
lean_ctor_set(v___x_2256_, 1, v_x_2250_);
lean_ctor_set(v___x_2256_, 0, v_x_2251_);
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_x_2251_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_x_2250_);
v___x_2259_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = lean_unsigned_to_nat(0u);
v___x_2261_ = l_Lean_instReprLevel_repr(v_head_2253_, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2259_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v_x_2251_ = v___x_2262_;
v_x_2252_ = v_tail_2254_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object* v_x_2266_, lean_object* v_x_2267_, lean_object* v_x_2268_){
_start:
{
if (lean_obj_tag(v_x_2268_) == 0)
{
lean_dec(v_x_2266_);
return v_x_2267_;
}
else
{
lean_object* v_head_2269_; lean_object* v_tail_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2281_; 
v_head_2269_ = lean_ctor_get(v_x_2268_, 0);
v_tail_2270_ = lean_ctor_get(v_x_2268_, 1);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_x_2268_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2272_ = v_x_2268_;
v_isShared_2273_ = v_isSharedCheck_2281_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_tail_2270_);
lean_inc(v_head_2269_);
lean_dec(v_x_2268_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2281_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
lean_inc(v_x_2266_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set_tag(v___x_2272_, 5);
lean_ctor_set(v___x_2272_, 1, v_x_2266_);
lean_ctor_set(v___x_2272_, 0, v_x_2267_);
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_x_2267_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_x_2266_);
v___x_2275_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2276_ = lean_unsigned_to_nat(0u);
v___x_2277_ = l_Lean_instReprLevel_repr(v_head_2269_, v___x_2276_);
v___x_2278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2275_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(v_x_2266_, v___x_2278_, v_tail_2270_);
return v___x_2279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object* v_x_2282_, lean_object* v_x_2283_){
_start:
{
if (lean_obj_tag(v_x_2282_) == 0)
{
lean_object* v___x_2284_; 
lean_dec(v_x_2283_);
v___x_2284_ = lean_box(0);
return v___x_2284_;
}
else
{
lean_object* v_tail_2285_; 
v_tail_2285_ = lean_ctor_get(v_x_2282_, 1);
if (lean_obj_tag(v_tail_2285_) == 0)
{
lean_object* v_head_2286_; lean_object* v___x_2287_; 
lean_dec(v_x_2283_);
v_head_2286_ = lean_ctor_get(v_x_2282_, 0);
lean_inc(v_head_2286_);
lean_dec_ref_known(v_x_2282_, 2);
v___x_2287_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2286_);
return v___x_2287_;
}
else
{
lean_object* v_head_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_inc(v_tail_2285_);
v_head_2288_ = lean_ctor_get(v_x_2282_, 0);
lean_inc(v_head_2288_);
lean_dec_ref_known(v_x_2282_, 2);
v___x_2289_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2288_);
v___x_2290_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(v_x_2283_, v___x_2289_, v_tail_2285_);
return v___x_2290_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2));
v___x_2303_ = lean_string_length(v___x_2302_);
return v___x_2303_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7);
v___x_2305_ = lean_nat_to_int(v___x_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object* v_a_2310_){
_start:
{
if (lean_obj_tag(v_a_2310_) == 0)
{
lean_object* v___x_2311_; 
v___x_2311_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1));
return v___x_2311_;
}
else
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; lean_object* v___x_2321_; 
v___x_2312_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5));
v___x_2313_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(v_a_2310_, v___x_2312_);
v___x_2314_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8);
v___x_2315_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9));
v___x_2316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
lean_ctor_set(v___x_2316_, 1, v___x_2313_);
v___x_2317_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10));
v___x_2318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2314_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = 0;
v___x_2321_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*1, v___x_2320_);
return v___x_2321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object* v_x_2394_, lean_object* v_prec_2395_){
_start:
{
switch(lean_obj_tag(v_x_2394_))
{
case 0:
{
lean_object* v_deBruijnIndex_2396_; lean_object* v___y_2398_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
v_deBruijnIndex_2396_ = lean_ctor_get(v_x_2394_, 0);
lean_inc(v_deBruijnIndex_2396_);
lean_dec_ref_known(v_x_2394_, 1);
v___x_2407_ = lean_unsigned_to_nat(1024u);
v___x_2408_ = lean_nat_dec_le(v___x_2407_, v_prec_2395_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; 
v___x_2409_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2398_ = v___x_2409_;
goto v___jp_2397_;
}
else
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2398_ = v___x_2410_;
goto v___jp_2397_;
}
v___jp_2397_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2399_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__2));
v___x_2400_ = l_Nat_reprFast(v_deBruijnIndex_2396_);
v___x_2401_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2400_);
v___x_2402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2399_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
lean_inc(v___y_2398_);
v___x_2403_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___y_2398_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
v___x_2404_ = 0;
v___x_2405_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2405_, 0, v___x_2403_);
lean_ctor_set_uint8(v___x_2405_, sizeof(void*)*1, v___x_2404_);
v___x_2406_ = l_Repr_addAppParen(v___x_2405_, v_prec_2395_);
return v___x_2406_;
}
}
case 1:
{
lean_object* v_fvarId_2411_; lean_object* v___y_2413_; lean_object* v___x_2422_; uint8_t v___x_2423_; 
v_fvarId_2411_ = lean_ctor_get(v_x_2394_, 0);
lean_inc(v_fvarId_2411_);
lean_dec_ref_known(v_x_2394_, 1);
v___x_2422_ = lean_unsigned_to_nat(1024u);
v___x_2423_ = lean_nat_dec_le(v___x_2422_, v_prec_2395_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2413_ = v___x_2424_;
goto v___jp_2412_;
}
else
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2413_ = v___x_2425_;
goto v___jp_2412_;
}
v___jp_2412_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2414_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__5));
v___x_2415_ = lean_unsigned_to_nat(1024u);
v___x_2416_ = l_Lean_Name_reprPrec(v_fvarId_2411_, v___x_2415_);
v___x_2417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2414_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
lean_inc(v___y_2413_);
v___x_2418_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___y_2413_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = 0;
v___x_2420_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2420_, 0, v___x_2418_);
lean_ctor_set_uint8(v___x_2420_, sizeof(void*)*1, v___x_2419_);
v___x_2421_ = l_Repr_addAppParen(v___x_2420_, v_prec_2395_);
return v___x_2421_;
}
}
case 2:
{
lean_object* v_mvarId_2426_; lean_object* v___y_2428_; lean_object* v___x_2437_; uint8_t v___x_2438_; 
v_mvarId_2426_ = lean_ctor_get(v_x_2394_, 0);
lean_inc(v_mvarId_2426_);
lean_dec_ref_known(v_x_2394_, 1);
v___x_2437_ = lean_unsigned_to_nat(1024u);
v___x_2438_ = lean_nat_dec_le(v___x_2437_, v_prec_2395_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; 
v___x_2439_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2428_ = v___x_2439_;
goto v___jp_2427_;
}
else
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2428_ = v___x_2440_;
goto v___jp_2427_;
}
v___jp_2427_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2429_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__8));
v___x_2430_ = lean_unsigned_to_nat(1024u);
v___x_2431_ = l_Lean_Name_reprPrec(v_mvarId_2426_, v___x_2430_);
v___x_2432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2429_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
lean_inc(v___y_2428_);
v___x_2433_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___y_2428_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = 0;
v___x_2435_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*1, v___x_2434_);
v___x_2436_ = l_Repr_addAppParen(v___x_2435_, v_prec_2395_);
return v___x_2436_;
}
}
case 3:
{
lean_object* v_u_2441_; lean_object* v___y_2443_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
v_u_2441_ = lean_ctor_get(v_x_2394_, 0);
lean_inc(v_u_2441_);
lean_dec_ref_known(v_x_2394_, 1);
v___x_2452_ = lean_unsigned_to_nat(1024u);
v___x_2453_ = lean_nat_dec_le(v___x_2452_, v_prec_2395_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
v___x_2454_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2443_ = v___x_2454_;
goto v___jp_2442_;
}
else
{
lean_object* v___x_2455_; 
v___x_2455_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2443_ = v___x_2455_;
goto v___jp_2442_;
}
v___jp_2442_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2444_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__11));
v___x_2445_ = lean_unsigned_to_nat(1024u);
v___x_2446_ = l_Lean_instReprLevel_repr(v_u_2441_, v___x_2445_);
v___x_2447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2444_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
lean_inc(v___y_2443_);
v___x_2448_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___y_2443_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = 0;
v___x_2450_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set_uint8(v___x_2450_, sizeof(void*)*1, v___x_2449_);
v___x_2451_ = l_Repr_addAppParen(v___x_2450_, v_prec_2395_);
return v___x_2451_;
}
}
case 4:
{
lean_object* v_declName_2456_; lean_object* v_us_2457_; lean_object* v___y_2459_; lean_object* v___x_2472_; uint8_t v___x_2473_; 
v_declName_2456_ = lean_ctor_get(v_x_2394_, 0);
lean_inc(v_declName_2456_);
v_us_2457_ = lean_ctor_get(v_x_2394_, 1);
lean_inc(v_us_2457_);
lean_dec_ref_known(v_x_2394_, 2);
v___x_2472_ = lean_unsigned_to_nat(1024u);
v___x_2473_ = lean_nat_dec_le(v___x_2472_, v_prec_2395_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2459_ = v___x_2474_;
goto v___jp_2458_;
}
else
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2459_ = v___x_2475_;
goto v___jp_2458_;
}
v___jp_2458_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2460_ = lean_box(1);
v___x_2461_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__14));
v___x_2462_ = lean_unsigned_to_nat(1024u);
v___x_2463_ = l_Lean_Name_reprPrec(v_declName_2456_, v___x_2462_);
v___x_2464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2461_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
lean_ctor_set(v___x_2465_, 1, v___x_2460_);
v___x_2466_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_us_2457_);
v___x_2467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2465_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
lean_inc(v___y_2459_);
v___x_2468_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___y_2459_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = 0;
v___x_2470_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2470_, 0, v___x_2468_);
lean_ctor_set_uint8(v___x_2470_, sizeof(void*)*1, v___x_2469_);
v___x_2471_ = l_Repr_addAppParen(v___x_2470_, v_prec_2395_);
return v___x_2471_;
}
}
case 5:
{
lean_object* v_fn_2476_; lean_object* v_arg_2477_; lean_object* v___x_2478_; lean_object* v___y_2480_; uint8_t v___x_2492_; 
v_fn_2476_ = lean_ctor_get(v_x_2394_, 0);
lean_inc_ref(v_fn_2476_);
v_arg_2477_ = lean_ctor_get(v_x_2394_, 1);
lean_inc_ref(v_arg_2477_);
lean_dec_ref_known(v_x_2394_, 2);
v___x_2478_ = lean_unsigned_to_nat(1024u);
v___x_2492_ = lean_nat_dec_le(v___x_2478_, v_prec_2395_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; 
v___x_2493_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2480_ = v___x_2493_;
goto v___jp_2479_;
}
else
{
lean_object* v___x_2494_; 
v___x_2494_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2480_ = v___x_2494_;
goto v___jp_2479_;
}
v___jp_2479_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2481_ = lean_box(1);
v___x_2482_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__17));
v___x_2483_ = l_Lean_instReprExpr_repr(v_fn_2476_, v___x_2478_);
v___x_2484_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2482_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
lean_ctor_set(v___x_2485_, 1, v___x_2481_);
v___x_2486_ = l_Lean_instReprExpr_repr(v_arg_2477_, v___x_2478_);
v___x_2487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
lean_inc(v___y_2480_);
v___x_2488_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___y_2480_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = 0;
v___x_2490_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2490_, 0, v___x_2488_);
lean_ctor_set_uint8(v___x_2490_, sizeof(void*)*1, v___x_2489_);
v___x_2491_ = l_Repr_addAppParen(v___x_2490_, v_prec_2395_);
return v___x_2491_;
}
}
case 6:
{
lean_object* v_binderName_2495_; lean_object* v_binderType_2496_; lean_object* v_body_2497_; uint8_t v_binderInfo_2498_; lean_object* v___x_2499_; lean_object* v___y_2501_; uint8_t v___x_2519_; 
v_binderName_2495_ = lean_ctor_get(v_x_2394_, 0);
lean_inc(v_binderName_2495_);
v_binderType_2496_ = lean_ctor_get(v_x_2394_, 1);
lean_inc_ref(v_binderType_2496_);
v_body_2497_ = lean_ctor_get(v_x_2394_, 2);
lean_inc_ref(v_body_2497_);
v_binderInfo_2498_ = lean_ctor_get_uint8(v_x_2394_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2394_, 3);
v___x_2499_ = lean_unsigned_to_nat(1024u);
v___x_2519_ = lean_nat_dec_le(v___x_2499_, v_prec_2395_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2501_ = v___x_2520_;
goto v___jp_2500_;
}
else
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2501_ = v___x_2521_;
goto v___jp_2500_;
}
v___jp_2500_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2502_ = lean_box(1);
v___x_2503_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__20));
v___x_2504_ = l_Lean_Name_reprPrec(v_binderName_2495_, v___x_2499_);
v___x_2505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
lean_ctor_set(v___x_2506_, 1, v___x_2502_);
v___x_2507_ = l_Lean_instReprExpr_repr(v_binderType_2496_, v___x_2499_);
v___x_2508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2506_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
lean_ctor_set(v___x_2509_, 1, v___x_2502_);
v___x_2510_ = l_Lean_instReprExpr_repr(v_body_2497_, v___x_2499_);
v___x_2511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
lean_ctor_set(v___x_2512_, 1, v___x_2502_);
v___x_2513_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2498_, v___x_2499_);
v___x_2514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
lean_inc(v___y_2501_);
v___x_2515_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___y_2501_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v___x_2516_ = 0;
v___x_2517_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set_uint8(v___x_2517_, sizeof(void*)*1, v___x_2516_);
v___x_2518_ = l_Repr_addAppParen(v___x_2517_, v_prec_2395_);
return v___x_2518_;
}
}
case 7:
{
lean_object* v_binderName_2522_; lean_object* v_binderType_2523_; lean_object* v_body_2524_; uint8_t v_binderInfo_2525_; lean_object* v___x_2526_; lean_object* v___y_2528_; uint8_t v___x_2546_; 
v_binderName_2522_ = lean_ctor_get(v_x_2394_, 0);
lean_inc(v_binderName_2522_);
v_binderType_2523_ = lean_ctor_get(v_x_2394_, 1);
lean_inc_ref(v_binderType_2523_);
v_body_2524_ = lean_ctor_get(v_x_2394_, 2);
lean_inc_ref(v_body_2524_);
v_binderInfo_2525_ = lean_ctor_get_uint8(v_x_2394_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2394_, 3);
v___x_2526_ = lean_unsigned_to_nat(1024u);
v___x_2546_ = lean_nat_dec_le(v___x_2526_, v_prec_2395_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2528_ = v___x_2547_;
goto v___jp_2527_;
}
else
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2528_ = v___x_2548_;
goto v___jp_2527_;
}
v___jp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2529_ = lean_box(1);
v___x_2530_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__23));
v___x_2531_ = l_Lean_Name_reprPrec(v_binderName_2522_, v___x_2526_);
v___x_2532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2530_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
v___x_2533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v___x_2529_);
v___x_2534_ = l_Lean_instReprExpr_repr(v_binderType_2523_, v___x_2526_);
v___x_2535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2533_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
v___x_2536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
lean_ctor_set(v___x_2536_, 1, v___x_2529_);
v___x_2537_ = l_Lean_instReprExpr_repr(v_body_2524_, v___x_2526_);
v___x_2538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2536_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
lean_ctor_set(v___x_2539_, 1, v___x_2529_);
v___x_2540_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2525_, v___x_2526_);
v___x_2541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2539_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
lean_inc(v___y_2528_);
v___x_2542_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___y_2528_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = 0;
v___x_2544_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2544_, 0, v___x_2542_);
lean_ctor_set_uint8(v___x_2544_, sizeof(void*)*1, v___x_2543_);
v___x_2545_ = l_Repr_addAppParen(v___x_2544_, v_prec_2395_);
return v___x_2545_;
}
}
case 8:
{
lean_object* v_declName_2549_; lean_object* v_type_2550_; lean_object* v_value_2551_; lean_object* v_body_2552_; uint8_t v_nondep_2553_; lean_object* v___x_2554_; lean_object* v___y_2556_; uint8_t v___x_2577_; 
v_declName_2549_ = lean_ctor_get(v_x_2394_, 0);
lean_inc(v_declName_2549_);
v_type_2550_ = lean_ctor_get(v_x_2394_, 1);
lean_inc_ref(v_type_2550_);
v_value_2551_ = lean_ctor_get(v_x_2394_, 2);
lean_inc_ref(v_value_2551_);
v_body_2552_ = lean_ctor_get(v_x_2394_, 3);
lean_inc_ref(v_body_2552_);
v_nondep_2553_ = lean_ctor_get_uint8(v_x_2394_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_x_2394_, 4);
v___x_2554_ = lean_unsigned_to_nat(1024u);
v___x_2577_ = lean_nat_dec_le(v___x_2554_, v_prec_2395_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2556_ = v___x_2578_;
goto v___jp_2555_;
}
else
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2556_ = v___x_2579_;
goto v___jp_2555_;
}
v___jp_2555_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2557_ = lean_box(1);
v___x_2558_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__26));
v___x_2559_ = l_Lean_Name_reprPrec(v_declName_2549_, v___x_2554_);
v___x_2560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2558_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
lean_ctor_set(v___x_2561_, 1, v___x_2557_);
v___x_2562_ = l_Lean_instReprExpr_repr(v_type_2550_, v___x_2554_);
v___x_2563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2561_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
lean_ctor_set(v___x_2564_, 1, v___x_2557_);
v___x_2565_ = l_Lean_instReprExpr_repr(v_value_2551_, v___x_2554_);
v___x_2566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2564_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
lean_ctor_set(v___x_2567_, 1, v___x_2557_);
v___x_2568_ = l_Lean_instReprExpr_repr(v_body_2552_, v___x_2554_);
v___x_2569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2567_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
lean_ctor_set(v___x_2570_, 1, v___x_2557_);
v___x_2571_ = l_Bool_repr___redArg(v_nondep_2553_);
v___x_2572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2570_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
lean_inc(v___y_2556_);
v___x_2573_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___y_2556_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = 0;
v___x_2575_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set_uint8(v___x_2575_, sizeof(void*)*1, v___x_2574_);
v___x_2576_ = l_Repr_addAppParen(v___x_2575_, v_prec_2395_);
return v___x_2576_;
}
}
case 9:
{
lean_object* v_a_2580_; lean_object* v___y_2582_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
v_a_2580_ = lean_ctor_get(v_x_2394_, 0);
lean_inc_ref(v_a_2580_);
lean_dec_ref_known(v_x_2394_, 1);
v___x_2591_ = lean_unsigned_to_nat(1024u);
v___x_2592_ = lean_nat_dec_le(v___x_2591_, v_prec_2395_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; 
v___x_2593_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2582_ = v___x_2593_;
goto v___jp_2581_;
}
else
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2582_ = v___x_2594_;
goto v___jp_2581_;
}
v___jp_2581_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2583_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__29));
v___x_2584_ = lean_unsigned_to_nat(1024u);
v___x_2585_ = l_Lean_instReprLiteral_repr(v_a_2580_, v___x_2584_);
v___x_2586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2583_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
lean_inc(v___y_2582_);
v___x_2587_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___y_2582_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
v___x_2588_ = 0;
v___x_2589_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2589_, 0, v___x_2587_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*1, v___x_2588_);
v___x_2590_ = l_Repr_addAppParen(v___x_2589_, v_prec_2395_);
return v___x_2590_;
}
}
case 10:
{
lean_object* v_data_2595_; lean_object* v_expr_2596_; lean_object* v___x_2597_; lean_object* v___y_2599_; uint8_t v___x_2611_; 
v_data_2595_ = lean_ctor_get(v_x_2394_, 0);
lean_inc(v_data_2595_);
v_expr_2596_ = lean_ctor_get(v_x_2394_, 1);
lean_inc_ref(v_expr_2596_);
lean_dec_ref_known(v_x_2394_, 2);
v___x_2597_ = lean_unsigned_to_nat(1024u);
v___x_2611_ = lean_nat_dec_le(v___x_2597_, v_prec_2395_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2599_ = v___x_2612_;
goto v___jp_2598_;
}
else
{
lean_object* v___x_2613_; 
v___x_2613_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2599_ = v___x_2613_;
goto v___jp_2598_;
}
v___jp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2600_ = lean_box(1);
v___x_2601_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__32));
v___x_2602_ = l_Lean_instReprKVMap_repr___redArg(v_data_2595_);
v___x_2603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2601_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
lean_ctor_set(v___x_2604_, 1, v___x_2600_);
v___x_2605_ = l_Lean_instReprExpr_repr(v_expr_2596_, v___x_2597_);
v___x_2606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
lean_inc(v___y_2599_);
v___x_2607_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___y_2599_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = 0;
v___x_2609_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2609_, 0, v___x_2607_);
lean_ctor_set_uint8(v___x_2609_, sizeof(void*)*1, v___x_2608_);
v___x_2610_ = l_Repr_addAppParen(v___x_2609_, v_prec_2395_);
return v___x_2610_;
}
}
default: 
{
lean_object* v_typeName_2614_; lean_object* v_idx_2615_; lean_object* v_struct_2616_; lean_object* v___x_2617_; lean_object* v___y_2619_; uint8_t v___x_2635_; 
v_typeName_2614_ = lean_ctor_get(v_x_2394_, 0);
lean_inc(v_typeName_2614_);
v_idx_2615_ = lean_ctor_get(v_x_2394_, 1);
lean_inc(v_idx_2615_);
v_struct_2616_ = lean_ctor_get(v_x_2394_, 2);
lean_inc_ref(v_struct_2616_);
lean_dec_ref_known(v_x_2394_, 3);
v___x_2617_ = lean_unsigned_to_nat(1024u);
v___x_2635_ = lean_nat_dec_le(v___x_2617_, v_prec_2395_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; 
v___x_2636_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2619_ = v___x_2636_;
goto v___jp_2618_;
}
else
{
lean_object* v___x_2637_; 
v___x_2637_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2619_ = v___x_2637_;
goto v___jp_2618_;
}
v___jp_2618_:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2620_ = lean_box(1);
v___x_2621_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__35));
v___x_2622_ = l_Lean_Name_reprPrec(v_typeName_2614_, v___x_2617_);
v___x_2623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2621_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v___x_2620_);
v___x_2625_ = l_Nat_reprFast(v_idx_2615_);
v___x_2626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
v___x_2627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2624_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
lean_ctor_set(v___x_2628_, 1, v___x_2620_);
v___x_2629_ = l_Lean_instReprExpr_repr(v_struct_2616_, v___x_2617_);
v___x_2630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2628_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
lean_inc(v___y_2619_);
v___x_2631_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___y_2619_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = 0;
v___x_2633_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2633_, 0, v___x_2631_);
lean_ctor_set_uint8(v___x_2633_, sizeof(void*)*1, v___x_2632_);
v___x_2634_ = l_Repr_addAppParen(v___x_2633_, v_prec_2395_);
return v___x_2634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object* v_x_2638_, lean_object* v_prec_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_instReprExpr_repr(v_x_2638_, v_prec_2639_);
lean_dec(v_prec_2639_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object* v_a_2641_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = lean_nat_to_int(v_a_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object* v_a_2643_, lean_object* v_n_2644_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_a_2643_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object* v_a_2646_, lean_object* v_n_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0(v_a_2646_, v_n_2647_);
lean_dec(v_n_2647_);
return v_res_2648_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__2(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = lean_box(0);
v___x_2655_ = ((lean_object*)(l_Lean_instInhabitedExpr___closed__1));
v___x_2656_ = l_Lean_Expr_const___override(v___x_2655_, v___x_2654_);
return v___x_2656_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr(void){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* v_x_2670_){
_start:
{
switch(lean_obj_tag(v_x_2670_))
{
case 0:
{
lean_object* v___x_2671_; 
v___x_2671_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__0));
return v___x_2671_;
}
case 1:
{
lean_object* v___x_2672_; 
v___x_2672_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__1));
return v___x_2672_;
}
case 2:
{
lean_object* v___x_2673_; 
v___x_2673_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__2));
return v___x_2673_;
}
case 3:
{
lean_object* v___x_2674_; 
v___x_2674_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__3));
return v___x_2674_;
}
case 4:
{
lean_object* v___x_2675_; 
v___x_2675_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__4));
return v___x_2675_;
}
case 5:
{
lean_object* v___x_2676_; 
v___x_2676_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__5));
return v___x_2676_;
}
case 6:
{
lean_object* v___x_2677_; 
v___x_2677_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__6));
return v___x_2677_;
}
case 7:
{
lean_object* v___x_2678_; 
v___x_2678_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__7));
return v___x_2678_;
}
case 8:
{
lean_object* v___x_2679_; 
v___x_2679_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__8));
return v___x_2679_;
}
case 9:
{
lean_object* v___x_2680_; 
v___x_2680_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__9));
return v___x_2680_;
}
case 10:
{
lean_object* v___x_2681_; 
v___x_2681_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__10));
return v___x_2681_;
}
default: 
{
lean_object* v___x_2682_; 
v___x_2682_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__11));
return v___x_2682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* v_x_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Lean_Expr_ctorName(v_x_2683_);
lean_dec_ref(v_x_2683_);
return v_res_2684_;
}
}
uint64_t l_Lean_Expr_hash(lean_object* v_e_2685_){
_start:
{
uint64_t v___x_2686_; uint64_t v___x_2687_; 
v___x_2686_ = lean_expr_data(v_e_2685_);
v___x_2687_ = l_Lean_Expr_Data_hash(v___x_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT void l_Lean_Expr_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2685_ = stack[0].m_obj;
uint64_t v_res_2688_;
v_res_2688_ = l_Lean_Expr_hash(v_e_2685_);
stack->m_num = v_res_2688_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* v_e_2689_){
_start:
{
uint64_t v_res_2690_; lean_object* v_r_2691_; 
v_res_2690_ = l_Lean_Expr_hash(v_e_2689_);
lean_dec_ref(v_e_2689_);
v_r_2691_ = lean_box_uint64(v_res_2690_);
return v_r_2691_;
}
}
uint8_t l_Lean_Expr_hasFVar(lean_object* v_e_2694_){
_start:
{
uint64_t v___x_2695_; uint8_t v___x_2696_; 
v___x_2695_ = lean_expr_data(v_e_2694_);
v___x_2696_ = l_Lean_Expr_Data_hasFVar(v___x_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT void l_Lean_Expr_hasFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2694_ = stack[0].m_obj;
uint8_t v_res_2697_;
v_res_2697_ = l_Lean_Expr_hasFVar(v_e_2694_);
stack->m_num = v_res_2697_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* v_e_2698_){
_start:
{
uint8_t v_res_2699_; lean_object* v_r_2700_; 
v_res_2699_ = l_Lean_Expr_hasFVar(v_e_2698_);
lean_dec_ref(v_e_2698_);
v_r_2700_ = lean_box(v_res_2699_);
return v_r_2700_;
}
}
uint8_t l_Lean_Expr_hasExprMVar(lean_object* v_e_2701_){
_start:
{
uint64_t v___x_2702_; uint8_t v___x_2703_; 
v___x_2702_ = lean_expr_data(v_e_2701_);
v___x_2703_ = l_Lean_Expr_Data_hasExprMVar(v___x_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT void l_Lean_Expr_hasExprMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2701_ = stack[0].m_obj;
uint8_t v_res_2704_;
v_res_2704_ = l_Lean_Expr_hasExprMVar(v_e_2701_);
stack->m_num = v_res_2704_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* v_e_2705_){
_start:
{
uint8_t v_res_2706_; lean_object* v_r_2707_; 
v_res_2706_ = l_Lean_Expr_hasExprMVar(v_e_2705_);
lean_dec_ref(v_e_2705_);
v_r_2707_ = lean_box(v_res_2706_);
return v_r_2707_;
}
}
uint8_t l_Lean_Expr_hasLevelMVar(lean_object* v_e_2708_){
_start:
{
uint64_t v___x_2709_; uint8_t v___x_2710_; 
v___x_2709_ = lean_expr_data(v_e_2708_);
v___x_2710_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT void l_Lean_Expr_hasLevelMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2708_ = stack[0].m_obj;
uint8_t v_res_2711_;
v_res_2711_ = l_Lean_Expr_hasLevelMVar(v_e_2708_);
stack->m_num = v_res_2711_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* v_e_2712_){
_start:
{
uint8_t v_res_2713_; lean_object* v_r_2714_; 
v_res_2713_ = l_Lean_Expr_hasLevelMVar(v_e_2712_);
lean_dec_ref(v_e_2712_);
v_r_2714_ = lean_box(v_res_2713_);
return v_r_2714_;
}
}
uint8_t l_Lean_Expr_hasMVar(lean_object* v_e_2715_){
_start:
{
uint64_t v_d_2716_; uint8_t v___x_2717_; 
v_d_2716_ = lean_expr_data(v_e_2715_);
v___x_2717_ = l_Lean_Expr_Data_hasExprMVar(v_d_2716_);
if (v___x_2717_ == 0)
{
uint8_t v___x_2718_; 
v___x_2718_ = l_Lean_Expr_Data_hasLevelMVar(v_d_2716_);
return v___x_2718_;
}
else
{
return v___x_2717_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_hasMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2715_ = stack[0].m_obj;
uint8_t v_res_2719_;
v_res_2719_ = l_Lean_Expr_hasMVar(v_e_2715_);
stack->m_num = v_res_2719_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* v_e_2720_){
_start:
{
uint8_t v_res_2721_; lean_object* v_r_2722_; 
v_res_2721_ = l_Lean_Expr_hasMVar(v_e_2720_);
lean_dec_ref(v_e_2720_);
v_r_2722_ = lean_box(v_res_2721_);
return v_r_2722_;
}
}
uint8_t l_Lean_Expr_hasLevelParam(lean_object* v_e_2723_){
_start:
{
uint64_t v___x_2724_; uint8_t v___x_2725_; 
v___x_2724_ = lean_expr_data(v_e_2723_);
v___x_2725_ = l_Lean_Expr_Data_hasLevelParam(v___x_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT void l_Lean_Expr_hasLevelParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2723_ = stack[0].m_obj;
uint8_t v_res_2726_;
v_res_2726_ = l_Lean_Expr_hasLevelParam(v_e_2723_);
stack->m_num = v_res_2726_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* v_e_2727_){
_start:
{
uint8_t v_res_2728_; lean_object* v_r_2729_; 
v_res_2728_ = l_Lean_Expr_hasLevelParam(v_e_2727_);
lean_dec_ref(v_e_2727_);
v_r_2729_ = lean_box(v_res_2728_);
return v_r_2729_;
}
}
uint32_t l_Lean_Expr_approxDepth(lean_object* v_e_2730_){
_start:
{
uint64_t v___x_2731_; uint8_t v___x_2732_; uint32_t v___x_2733_; 
v___x_2731_ = lean_expr_data(v_e_2730_);
v___x_2732_ = l_Lean_Expr_Data_approxDepth(v___x_2731_);
v___x_2733_ = lean_uint8_to_uint32(v___x_2732_);
return v___x_2733_;
}
}
LEAN_EXPORT void l_Lean_Expr_approxDepth_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2730_ = stack[0].m_obj;
uint32_t v_res_2734_;
v_res_2734_ = l_Lean_Expr_approxDepth(v_e_2730_);
stack->m_num = v_res_2734_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* v_e_2735_){
_start:
{
uint32_t v_res_2736_; lean_object* v_r_2737_; 
v_res_2736_ = l_Lean_Expr_approxDepth(v_e_2735_);
lean_dec_ref(v_e_2735_);
v_r_2737_ = lean_box_uint32(v_res_2736_);
return v_r_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* v_e_2738_){
_start:
{
uint64_t v___x_2739_; uint32_t v___x_2740_; lean_object* v___x_2741_; 
v___x_2739_ = lean_expr_data(v_e_2738_);
v___x_2740_ = l_Lean_Expr_Data_looseBVarRange(v___x_2739_);
v___x_2741_ = lean_uint32_to_nat(v___x_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* v_e_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_Expr_looseBVarRange(v_e_2742_);
lean_dec_ref(v_e_2742_);
return v_res_2743_;
}
}
uint8_t l_Lean_Expr_binderInfo(lean_object* v_e_2744_){
_start:
{
switch(lean_obj_tag(v_e_2744_))
{
case 7:
{
uint8_t v_binderInfo_2745_; 
v_binderInfo_2745_ = lean_ctor_get_uint8(v_e_2744_, sizeof(void*)*3 + 8);
return v_binderInfo_2745_;
}
case 6:
{
uint8_t v_binderInfo_2746_; 
v_binderInfo_2746_ = lean_ctor_get_uint8(v_e_2744_, sizeof(void*)*3 + 8);
return v_binderInfo_2746_;
}
default: 
{
uint8_t v___x_2747_; 
v___x_2747_ = 0;
return v___x_2747_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_binderInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2744_ = stack[0].m_obj;
uint8_t v_res_2748_;
v_res_2748_ = l_Lean_Expr_binderInfo(v_e_2744_);
stack->m_num = v_res_2748_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* v_e_2749_){
_start:
{
uint8_t v_res_2750_; lean_object* v_r_2751_; 
v_res_2750_ = l_Lean_Expr_binderInfo(v_e_2749_);
lean_dec_ref(v_e_2749_);
v_r_2751_ = lean_box(v_res_2750_);
return v_r_2751_;
}
}
uint64_t lean_expr_hash(lean_object* v_a_2752_){
_start:
{
uint64_t v___x_2753_; 
v___x_2753_ = l_Lean_Expr_hash(v_a_2752_);
lean_dec_ref(v_a_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT void lean_expr_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2752_ = stack[0].m_obj;
uint64_t v_res_2754_;
v_res_2754_ = lean_expr_hash(v_a_2752_);
stack->m_num = v_res_2754_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* v_a_2755_){
_start:
{
uint64_t v_res_2756_; lean_object* v_r_2757_; 
v_res_2756_ = lean_expr_hash(v_a_2755_);
v_r_2757_ = lean_box_uint64(v_res_2756_);
return v_r_2757_;
}
}
uint8_t lean_expr_has_fvar(lean_object* v_e_2758_){
_start:
{
uint8_t v___x_2759_; 
v___x_2759_ = l_Lean_Expr_hasFVar(v_e_2758_);
lean_dec_ref(v_e_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT void lean_expr_has_fvar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2758_ = stack[0].m_obj;
uint8_t v_res_2760_;
v_res_2760_ = lean_expr_has_fvar(v_e_2758_);
stack->m_num = v_res_2760_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* v_e_2761_){
_start:
{
uint8_t v_res_2762_; lean_object* v_r_2763_; 
v_res_2762_ = lean_expr_has_fvar(v_e_2761_);
v_r_2763_ = lean_box(v_res_2762_);
return v_r_2763_;
}
}
uint8_t lean_expr_has_expr_mvar(lean_object* v_e_2764_){
_start:
{
uint8_t v___x_2765_; 
v___x_2765_ = l_Lean_Expr_hasExprMVar(v_e_2764_);
lean_dec_ref(v_e_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT void lean_expr_has_expr_mvar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2764_ = stack[0].m_obj;
uint8_t v_res_2766_;
v_res_2766_ = lean_expr_has_expr_mvar(v_e_2764_);
stack->m_num = v_res_2766_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* v_e_2767_){
_start:
{
uint8_t v_res_2768_; lean_object* v_r_2769_; 
v_res_2768_ = lean_expr_has_expr_mvar(v_e_2767_);
v_r_2769_ = lean_box(v_res_2768_);
return v_r_2769_;
}
}
uint8_t lean_expr_has_level_mvar(lean_object* v_e_2770_){
_start:
{
uint8_t v___x_2771_; 
v___x_2771_ = l_Lean_Expr_hasLevelMVar(v_e_2770_);
lean_dec_ref(v_e_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT void lean_expr_has_level_mvar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2770_ = stack[0].m_obj;
uint8_t v_res_2772_;
v_res_2772_ = lean_expr_has_level_mvar(v_e_2770_);
stack->m_num = v_res_2772_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* v_e_2773_){
_start:
{
uint8_t v_res_2774_; lean_object* v_r_2775_; 
v_res_2774_ = lean_expr_has_level_mvar(v_e_2773_);
v_r_2775_ = lean_box(v_res_2774_);
return v_r_2775_;
}
}
uint8_t lean_expr_has_level_param(lean_object* v_e_2776_){
_start:
{
uint8_t v___x_2777_; 
v___x_2777_ = l_Lean_Expr_hasLevelParam(v_e_2776_);
lean_dec_ref(v_e_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT void lean_expr_has_level_param_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2776_ = stack[0].m_obj;
uint8_t v_res_2778_;
v_res_2778_ = lean_expr_has_level_param(v_e_2776_);
stack->m_num = v_res_2778_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* v_e_2779_){
_start:
{
uint8_t v_res_2780_; lean_object* v_r_2781_; 
v_res_2780_ = lean_expr_has_level_param(v_e_2779_);
v_r_2781_ = lean_box(v_res_2780_);
return v_r_2781_;
}
}
uint32_t lean_expr_loose_bvar_range(lean_object* v_e_2782_){
_start:
{
uint64_t v___x_2783_; uint32_t v___x_2784_; 
v___x_2783_ = lean_expr_data(v_e_2782_);
lean_dec_ref(v_e_2782_);
v___x_2784_ = l_Lean_Expr_Data_looseBVarRange(v___x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT void lean_expr_loose_bvar_range_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2782_ = stack[0].m_obj;
uint32_t v_res_2785_;
v_res_2785_ = lean_expr_loose_bvar_range(v_e_2782_);
stack->m_num = v_res_2785_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* v_e_2786_){
_start:
{
uint32_t v_res_2787_; lean_object* v_r_2788_; 
v_res_2787_ = lean_expr_loose_bvar_range(v_e_2786_);
v_r_2788_ = lean_box_uint32(v_res_2787_);
return v_r_2788_;
}
}
uint8_t lean_expr_binder_info(lean_object* v_e_2789_){
_start:
{
uint8_t v___x_2790_; 
v___x_2790_ = l_Lean_Expr_binderInfo(v_e_2789_);
lean_dec_ref(v_e_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT void lean_expr_binder_info_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2789_ = stack[0].m_obj;
uint8_t v_res_2791_;
v_res_2791_ = lean_expr_binder_info(v_e_2789_);
stack->m_num = v_res_2791_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* v_e_2792_){
_start:
{
uint8_t v_res_2793_; lean_object* v_r_2794_; 
v_res_2793_ = lean_expr_binder_info(v_e_2792_);
v_r_2794_ = lean_box(v_res_2793_);
return v_r_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* v_declName_2795_, lean_object* v_us_2796_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lean_Expr_const___override(v_declName_2795_, v_us_2796_);
return v___x_2797_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2801_ = lean_box(0);
v___x_2802_ = ((lean_object*)(l_Lean_Literal_type___closed__1));
v___x_2803_ = l_Lean_Expr_const___override(v___x_2802_, v___x_2801_);
return v___x_2803_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2807_ = lean_box(0);
v___x_2808_ = ((lean_object*)(l_Lean_Literal_type___closed__4));
v___x_2809_ = l_Lean_Expr_const___override(v___x_2808_, v___x_2807_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* v_x_2810_){
_start:
{
if (lean_obj_tag(v_x_2810_) == 0)
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_2811_;
}
else
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_obj_once(&l_Lean_Literal_type___closed__5, &l_Lean_Literal_type___closed__5_once, _init_l_Lean_Literal_type___closed__5);
return v___x_2812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* v_x_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_Literal_type(v_x_2813_);
lean_dec_ref(v_x_2813_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* v_a_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_Literal_type(v_a_2815_);
lean_dec_ref(v_a_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* v_idx_2817_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l_Lean_Expr_bvar___override(v_idx_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* v_u_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_Expr_sort___override(v_u_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* v_fvarId_2821_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l_Lean_Expr_fvar___override(v_fvarId_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* v_mvarId_2823_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_Expr_mvar___override(v_mvarId_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* v_m_2825_, lean_object* v_e_2826_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_Expr_mdata___override(v_m_2825_, v_e_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* v_structName_2828_, lean_object* v_idx_2829_, lean_object* v_struct_2830_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Lean_Expr_proj___override(v_structName_2828_, v_idx_2829_, v_struct_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* v_f_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Lean_Expr_app___override(v_f_2832_, v_a_2833_);
return v___x_2834_;
}
}
lean_object* l_Lean_mkLambda(lean_object* v_x_2835_, uint8_t v_bi_2836_, lean_object* v_t_2837_, lean_object* v_b_2838_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_Expr_lam___override(v_x_2835_, v_t_2837_, v_b_2838_, v_bi_2836_);
return v___x_2839_;
}
}
LEAN_EXPORT void l_Lean_mkLambda_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2835_ = stack[0].m_obj;
uint8_t v_bi_2836_ = stack[1].m_num;
lean_object* v_t_2837_ = stack[2].m_obj;
lean_object* v_b_2838_ = stack[3].m_obj;
lean_object* v_res_2840_;
v_res_2840_ = l_Lean_mkLambda(v_x_2835_, v_bi_2836_, v_t_2837_, v_b_2838_);
stack->m_obj
 = v_res_2840_;
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* v_x_2841_, lean_object* v_bi_2842_, lean_object* v_t_2843_, lean_object* v_b_2844_){
_start:
{
uint8_t v_bi_boxed_2845_; lean_object* v_res_2846_; 
v_bi_boxed_2845_ = lean_unbox(v_bi_2842_);
v_res_2846_ = l_Lean_mkLambda(v_x_2841_, v_bi_boxed_2845_, v_t_2843_, v_b_2844_);
return v_res_2846_;
}
}
lean_object* l_Lean_mkForall(lean_object* v_x_2847_, uint8_t v_bi_2848_, lean_object* v_t_2849_, lean_object* v_b_2850_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Lean_Expr_forallE___override(v_x_2847_, v_t_2849_, v_b_2850_, v_bi_2848_);
return v___x_2851_;
}
}
LEAN_EXPORT void l_Lean_mkForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2847_ = stack[0].m_obj;
uint8_t v_bi_2848_ = stack[1].m_num;
lean_object* v_t_2849_ = stack[2].m_obj;
lean_object* v_b_2850_ = stack[3].m_obj;
lean_object* v_res_2852_;
v_res_2852_ = l_Lean_mkForall(v_x_2847_, v_bi_2848_, v_t_2849_, v_b_2850_);
stack->m_obj
 = v_res_2852_;
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* v_x_2853_, lean_object* v_bi_2854_, lean_object* v_t_2855_, lean_object* v_b_2856_){
_start:
{
uint8_t v_bi_boxed_2857_; lean_object* v_res_2858_; 
v_bi_boxed_2857_ = lean_unbox(v_bi_2854_);
v_res_2858_ = l_Lean_mkForall(v_x_2853_, v_bi_boxed_2857_, v_t_2855_, v_b_2856_);
return v_res_2858_;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__4(void){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2865_ = lean_box(0);
v___x_2866_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__3));
v___x_2867_ = l_Lean_Expr_const___override(v___x_2866_, v___x_2865_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* v_type_2868_){
_start:
{
lean_object* v___x_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2869_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2870_ = 0;
v___x_2871_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2872_ = l_Lean_Expr_forallE___override(v___x_2869_, v___x_2871_, v_type_2868_, v___x_2870_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* v_type_2873_){
_start:
{
lean_object* v___x_2874_; uint8_t v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2874_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2875_ = 0;
v___x_2876_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2877_ = l_Lean_Expr_lam___override(v___x_2874_, v___x_2876_, v_type_2873_, v___x_2875_);
return v___x_2877_;
}
}
lean_object* l_Lean_mkLet(lean_object* v_x_2878_, lean_object* v_t_2879_, lean_object* v_v_2880_, lean_object* v_b_2881_, uint8_t v_nondep_2882_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_Expr_letE___override(v_x_2878_, v_t_2879_, v_v_2880_, v_b_2881_, v_nondep_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT void l_Lean_mkLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2878_ = stack[0].m_obj;
lean_object* v_t_2879_ = stack[1].m_obj;
lean_object* v_v_2880_ = stack[2].m_obj;
lean_object* v_b_2881_ = stack[3].m_obj;
uint8_t v_nondep_2882_ = stack[4].m_num;
lean_object* v_res_2884_;
v_res_2884_ = l_Lean_mkLet(v_x_2878_, v_t_2879_, v_v_2880_, v_b_2881_, v_nondep_2882_);
stack->m_obj
 = v_res_2884_;
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* v_x_2885_, lean_object* v_t_2886_, lean_object* v_v_2887_, lean_object* v_b_2888_, lean_object* v_nondep_2889_){
_start:
{
uint8_t v_nondep_boxed_2890_; lean_object* v_res_2891_; 
v_nondep_boxed_2890_ = lean_unbox(v_nondep_2889_);
v_res_2891_ = l_Lean_mkLet(v_x_2885_, v_t_2886_, v_v_2887_, v_b_2888_, v_nondep_boxed_2890_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object* v_x_2892_, lean_object* v_t_2893_, lean_object* v_v_2894_, lean_object* v_b_2895_){
_start:
{
uint8_t v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = 1;
v___x_2897_ = l_Lean_Expr_letE___override(v_x_2892_, v_t_2893_, v_v_2894_, v_b_2895_, v___x_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* v_f_2898_, lean_object* v_a_2899_, lean_object* v_b_2900_){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = l_Lean_Expr_app___override(v_f_2898_, v_a_2899_);
v___x_2902_ = l_Lean_Expr_app___override(v___x_2901_, v_b_2900_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* v_f_2903_, lean_object* v_a_2904_, lean_object* v_b_2905_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_mkAppB(v_f_2903_, v_a_2904_, v_b_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* v_f_2907_, lean_object* v_a_2908_, lean_object* v_b_2909_, lean_object* v_c_2910_){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = l_Lean_mkAppB(v_f_2907_, v_a_2908_, v_b_2909_);
v___x_2912_ = l_Lean_Expr_app___override(v___x_2911_, v_c_2910_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* v_f_2913_, lean_object* v_a_2914_, lean_object* v_b_2915_, lean_object* v_c_2916_, lean_object* v_d_2917_){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = l_Lean_mkAppB(v_f_2913_, v_a_2914_, v_b_2915_);
v___x_2919_ = l_Lean_mkAppB(v___x_2918_, v_c_2916_, v_d_2917_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* v_f_2920_, lean_object* v_a_2921_, lean_object* v_b_2922_, lean_object* v_c_2923_, lean_object* v_d_2924_, lean_object* v_e_2925_){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = l_Lean_mkApp4(v_f_2920_, v_a_2921_, v_b_2922_, v_c_2923_, v_d_2924_);
v___x_2927_ = l_Lean_Expr_app___override(v___x_2926_, v_e_2925_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* v_f_2928_, lean_object* v_a_2929_, lean_object* v_b_2930_, lean_object* v_c_2931_, lean_object* v_d_2932_, lean_object* v_e_u2081_2933_, lean_object* v_e_u2082_2934_){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = l_Lean_mkApp4(v_f_2928_, v_a_2929_, v_b_2930_, v_c_2931_, v_d_2932_);
v___x_2936_ = l_Lean_mkAppB(v___x_2935_, v_e_u2081_2933_, v_e_u2082_2934_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* v_f_2937_, lean_object* v_a_2938_, lean_object* v_b_2939_, lean_object* v_c_2940_, lean_object* v_d_2941_, lean_object* v_e_u2081_2942_, lean_object* v_e_u2082_2943_, lean_object* v_e_u2083_2944_){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = l_Lean_mkApp4(v_f_2937_, v_a_2938_, v_b_2939_, v_c_2940_, v_d_2941_);
v___x_2946_ = l_Lean_mkApp3(v___x_2945_, v_e_u2081_2942_, v_e_u2082_2943_, v_e_u2083_2944_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* v_f_2947_, lean_object* v_a_2948_, lean_object* v_b_2949_, lean_object* v_c_2950_, lean_object* v_d_2951_, lean_object* v_e_u2081_2952_, lean_object* v_e_u2082_2953_, lean_object* v_e_u2083_2954_, lean_object* v_e_u2084_2955_){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = l_Lean_mkApp4(v_f_2947_, v_a_2948_, v_b_2949_, v_c_2950_, v_d_2951_);
v___x_2957_ = l_Lean_mkApp4(v___x_2956_, v_e_u2081_2952_, v_e_u2082_2953_, v_e_u2083_2954_, v_e_u2084_2955_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* v_f_2958_, lean_object* v_a_2959_, lean_object* v_b_2960_, lean_object* v_c_2961_, lean_object* v_d_2962_, lean_object* v_e_u2081_2963_, lean_object* v_e_u2082_2964_, lean_object* v_e_u2083_2965_, lean_object* v_e_u2084_2966_, lean_object* v_e_u2085_2967_){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = l_Lean_mkApp4(v_f_2958_, v_a_2959_, v_b_2960_, v_c_2961_, v_d_2962_);
v___x_2969_ = l_Lean_mkApp5(v___x_2968_, v_e_u2081_2963_, v_e_u2082_2964_, v_e_u2083_2965_, v_e_u2084_2966_, v_e_u2085_2967_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* v_f_2970_, lean_object* v_a_2971_, lean_object* v_b_2972_, lean_object* v_c_2973_, lean_object* v_d_2974_, lean_object* v_e_u2081_2975_, lean_object* v_e_u2082_2976_, lean_object* v_e_u2083_2977_, lean_object* v_e_u2084_2978_, lean_object* v_e_u2085_2979_, lean_object* v_e_u2086_2980_){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = l_Lean_mkApp4(v_f_2970_, v_a_2971_, v_b_2972_, v_c_2973_, v_d_2974_);
v___x_2982_ = l_Lean_mkApp6(v___x_2981_, v_e_u2081_2975_, v_e_u2082_2976_, v_e_u2083_2977_, v_e_u2084_2978_, v_e_u2085_2979_, v_e_u2086_2980_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* v_l_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_Expr_lit___override(v_l_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* v_n_2985_){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_n_2985_);
v___x_2987_ = l_Lean_Expr_lit___override(v___x_2986_);
return v___x_2987_;
}
}
static lean_object* _init_l_Lean_mkInstOfNatNat___closed__2(void){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2991_ = lean_box(0);
v___x_2992_ = ((lean_object*)(l_Lean_mkInstOfNatNat___closed__1));
v___x_2993_ = l_Lean_Expr_const___override(v___x_2992_, v___x_2991_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object* v_n_2994_){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = lean_obj_once(&l_Lean_mkInstOfNatNat___closed__2, &l_Lean_mkInstOfNatNat___closed__2_once, _init_l_Lean_mkInstOfNatNat___closed__2);
v___x_2996_ = l_Lean_Expr_app___override(v___x_2995_, v_n_2994_);
return v___x_2996_;
}
}
static lean_object* _init_l_Lean_mkNatLitCore___closed__4(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_3006_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_3007_ = l_Lean_Expr_const___override(v___x_3006_, v___x_3005_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object* v_n_3008_){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3009_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_3010_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
lean_inc_ref(v_n_3008_);
v___x_3011_ = l_Lean_mkInstOfNatNat(v_n_3008_);
v___x_3012_ = l_Lean_mkApp3(v___x_3009_, v___x_3010_, v_n_3008_, v___x_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* v_n_3013_){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = l_Lean_mkRawNatLit(v_n_3013_);
v___x_3015_ = l_Lean_mkNatLitCore(v___x_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* v_s_3016_){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_s_3016_);
v___x_3018_ = l_Lean_Expr_lit___override(v___x_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* v_idx_3019_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_Expr_bvar___override(v_idx_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* v_fvarId_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Lean_Expr_fvar___override(v_fvarId_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_Expr_sort___override(v_u_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_3025_, lean_object* v_lvls_3026_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Lean_Expr_const___override(v_c_3025_, v_lvls_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Lean_Expr_app___override(v_f_3028_, v_a_3029_);
return v___x_3030_;
}
}
lean_object* lean_expr_mk_lambda(lean_object* v_n_3031_, lean_object* v_d_3032_, lean_object* v_b_3033_, uint8_t v_bi_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_Expr_lam___override(v_n_3031_, v_d_3032_, v_b_3033_, v_bi_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT void lean_expr_mk_lambda_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3031_ = stack[0].m_obj;
lean_object* v_d_3032_ = stack[1].m_obj;
lean_object* v_b_3033_ = stack[2].m_obj;
uint8_t v_bi_3034_ = stack[3].m_num;
lean_object* v_res_3036_;
v_res_3036_ = lean_expr_mk_lambda(v_n_3031_, v_d_3032_, v_b_3033_, v_bi_3034_);
stack->m_obj
 = v_res_3036_;
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_3037_, lean_object* v_d_3038_, lean_object* v_b_3039_, lean_object* v_bi_3040_){
_start:
{
uint8_t v_bi_boxed_3041_; lean_object* v_res_3042_; 
v_bi_boxed_3041_ = lean_unbox(v_bi_3040_);
v_res_3042_ = lean_expr_mk_lambda(v_n_3037_, v_d_3038_, v_b_3039_, v_bi_boxed_3041_);
return v_res_3042_;
}
}
lean_object* lean_expr_mk_forall(lean_object* v_n_3043_, lean_object* v_d_3044_, lean_object* v_b_3045_, uint8_t v_bi_3046_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lean_Expr_forallE___override(v_n_3043_, v_d_3044_, v_b_3045_, v_bi_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT void lean_expr_mk_forall_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3043_ = stack[0].m_obj;
lean_object* v_d_3044_ = stack[1].m_obj;
lean_object* v_b_3045_ = stack[2].m_obj;
uint8_t v_bi_3046_ = stack[3].m_num;
lean_object* v_res_3048_;
v_res_3048_ = lean_expr_mk_forall(v_n_3043_, v_d_3044_, v_b_3045_, v_bi_3046_);
stack->m_obj
 = v_res_3048_;
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_3049_, lean_object* v_d_3050_, lean_object* v_b_3051_, lean_object* v_bi_3052_){
_start:
{
uint8_t v_bi_boxed_3053_; lean_object* v_res_3054_; 
v_bi_boxed_3053_ = lean_unbox(v_bi_3052_);
v_res_3054_ = lean_expr_mk_forall(v_n_3049_, v_d_3050_, v_b_3051_, v_bi_boxed_3053_);
return v_res_3054_;
}
}
lean_object* lean_expr_mk_let(lean_object* v_n_3055_, lean_object* v_t_3056_, lean_object* v_v_3057_, lean_object* v_b_3058_, uint8_t v_nondep_3059_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_Expr_letE___override(v_n_3055_, v_t_3056_, v_v_3057_, v_b_3058_, v_nondep_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT void lean_expr_mk_let_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3055_ = stack[0].m_obj;
lean_object* v_t_3056_ = stack[1].m_obj;
lean_object* v_v_3057_ = stack[2].m_obj;
lean_object* v_b_3058_ = stack[3].m_obj;
uint8_t v_nondep_3059_ = stack[4].m_num;
lean_object* v_res_3061_;
v_res_3061_ = lean_expr_mk_let(v_n_3055_, v_t_3056_, v_v_3057_, v_b_3058_, v_nondep_3059_);
stack->m_obj
 = v_res_3061_;
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_3062_, lean_object* v_t_3063_, lean_object* v_v_3064_, lean_object* v_b_3065_, lean_object* v_nondep_3066_){
_start:
{
uint8_t v_nondep_boxed_3067_; lean_object* v_res_3068_; 
v_nondep_boxed_3067_ = lean_unbox(v_nondep_3066_);
v_res_3068_ = lean_expr_mk_let(v_n_3062_, v_t_3063_, v_v_3064_, v_b_3065_, v_nondep_boxed_3067_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_3069_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Lean_Expr_lit___override(v_l_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_3071_, lean_object* v_e_3072_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Lean_Expr_mdata___override(v_m_3071_, v_e_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_3074_, lean_object* v_idx_3075_, lean_object* v_struct_3076_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Lean_Expr_proj___override(v_structName_3074_, v_idx_3075_, v_struct_3076_);
return v___x_3077_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_3078_, size_t v_i_3079_, size_t v_stop_3080_, lean_object* v_b_3081_){
_start:
{
uint8_t v___x_3082_; 
v___x_3082_ = lean_usize_dec_eq(v_i_3079_, v_stop_3080_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; size_t v___x_3085_; size_t v___x_3086_; 
v___x_3083_ = lean_array_uget_borrowed(v_as_3078_, v_i_3079_);
lean_inc(v___x_3083_);
v___x_3084_ = l_Lean_Expr_app___override(v_b_3081_, v___x_3083_);
v___x_3085_ = ((size_t)1ULL);
v___x_3086_ = lean_usize_add(v_i_3079_, v___x_3085_);
v_i_3079_ = v___x_3086_;
v_b_3081_ = v___x_3084_;
goto _start;
}
else
{
return v_b_3081_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3078_ = stack[0].m_obj;
size_t v_i_3079_ = stack[1].m_num;
size_t v_stop_3080_ = stack[2].m_num;
lean_object* v_b_3081_ = stack[3].m_obj;
lean_object* v_res_3088_;
v_res_3088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_3078_, v_i_3079_, v_stop_3080_, v_b_3081_);
stack->m_obj
 = v_res_3088_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_3089_, lean_object* v_i_3090_, lean_object* v_stop_3091_, lean_object* v_b_3092_){
_start:
{
size_t v_i_boxed_3093_; size_t v_stop_boxed_3094_; lean_object* v_res_3095_; 
v_i_boxed_3093_ = lean_unbox_usize(v_i_3090_);
lean_dec(v_i_3090_);
v_stop_boxed_3094_ = lean_unbox_usize(v_stop_3091_);
lean_dec(v_stop_3091_);
v_res_3095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_3089_, v_i_boxed_3093_, v_stop_boxed_3094_, v_b_3092_);
lean_dec_ref(v_as_3089_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_3096_, lean_object* v_args_3097_){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3098_ = lean_unsigned_to_nat(0u);
v___x_3099_ = lean_array_get_size(v_args_3097_);
v___x_3100_ = lean_nat_dec_lt(v___x_3098_, v___x_3099_);
if (v___x_3100_ == 0)
{
return v_f_3096_;
}
else
{
uint8_t v___x_3101_; 
v___x_3101_ = lean_nat_dec_le(v___x_3099_, v___x_3099_);
if (v___x_3101_ == 0)
{
if (v___x_3100_ == 0)
{
return v_f_3096_;
}
else
{
size_t v___x_3102_; size_t v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = ((size_t)0ULL);
v___x_3103_ = lean_usize_of_nat(v___x_3099_);
v___x_3104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3097_, v___x_3102_, v___x_3103_, v_f_3096_);
return v___x_3104_;
}
}
else
{
size_t v___x_3105_; size_t v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = ((size_t)0ULL);
v___x_3106_ = lean_usize_of_nat(v___x_3099_);
v___x_3107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3097_, v___x_3105_, v___x_3106_, v_f_3096_);
return v___x_3107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_3108_, lean_object* v_args_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_mkAppN(v_f_3108_, v_args_3109_);
lean_dec_ref(v_args_3109_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_3111_, lean_object* v_args_3112_, lean_object* v_i_3113_, lean_object* v_e_3114_){
_start:
{
uint8_t v___x_3115_; 
v___x_3115_ = lean_nat_dec_lt(v_i_3113_, v_n_3111_);
if (v___x_3115_ == 0)
{
lean_dec(v_i_3113_);
return v_e_3114_;
}
else
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3116_ = l_Lean_instInhabitedExpr;
v___x_3117_ = lean_unsigned_to_nat(1u);
v___x_3118_ = lean_nat_add(v_i_3113_, v___x_3117_);
v___x_3119_ = lean_array_get_borrowed(v___x_3116_, v_args_3112_, v_i_3113_);
lean_dec(v_i_3113_);
lean_inc(v___x_3119_);
v___x_3120_ = l_Lean_Expr_app___override(v_e_3114_, v___x_3119_);
v_i_3113_ = v___x_3118_;
v_e_3114_ = v___x_3120_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_3122_, lean_object* v_args_3123_, lean_object* v_i_3124_, lean_object* v_e_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_3122_, v_args_3123_, v_i_3124_, v_e_3125_);
lean_dec_ref(v_args_3123_);
lean_dec(v_n_3122_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_3127_, lean_object* v_i_3128_, lean_object* v_j_3129_, lean_object* v_args_3130_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_3129_, v_args_3130_, v_i_3128_, v_f_3127_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_3132_, lean_object* v_i_3133_, lean_object* v_j_3134_, lean_object* v_args_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_mkAppRange(v_f_3132_, v_i_3133_, v_j_3134_, v_args_3135_);
lean_dec_ref(v_args_3135_);
lean_dec(v_j_3134_);
return v_res_3136_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_3137_, size_t v_i_3138_, size_t v_stop_3139_, lean_object* v_b_3140_){
_start:
{
uint8_t v___x_3141_; 
v___x_3141_ = lean_usize_dec_eq(v_i_3138_, v_stop_3139_);
if (v___x_3141_ == 0)
{
size_t v___x_3142_; size_t v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3142_ = ((size_t)1ULL);
v___x_3143_ = lean_usize_sub(v_i_3138_, v___x_3142_);
v___x_3144_ = lean_array_uget_borrowed(v_as_3137_, v___x_3143_);
lean_inc(v___x_3144_);
v___x_3145_ = l_Lean_Expr_app___override(v_b_3140_, v___x_3144_);
v_i_3138_ = v___x_3143_;
v_b_3140_ = v___x_3145_;
goto _start;
}
else
{
return v_b_3140_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3137_ = stack[0].m_obj;
size_t v_i_3138_ = stack[1].m_num;
size_t v_stop_3139_ = stack[2].m_num;
lean_object* v_b_3140_ = stack[3].m_obj;
lean_object* v_res_3147_;
v_res_3147_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3137_, v_i_3138_, v_stop_3139_, v_b_3140_);
stack->m_obj
 = v_res_3147_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_3148_, lean_object* v_i_3149_, lean_object* v_stop_3150_, lean_object* v_b_3151_){
_start:
{
size_t v_i_boxed_3152_; size_t v_stop_boxed_3153_; lean_object* v_res_3154_; 
v_i_boxed_3152_ = lean_unbox_usize(v_i_3149_);
lean_dec(v_i_3149_);
v_stop_boxed_3153_ = lean_unbox_usize(v_stop_3150_);
lean_dec(v_stop_3150_);
v_res_3154_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3148_, v_i_boxed_3152_, v_stop_boxed_3153_, v_b_3151_);
lean_dec_ref(v_as_3148_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_3155_, lean_object* v_revArgs_3156_){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_3157_ = lean_array_get_size(v_revArgs_3156_);
v___x_3158_ = lean_unsigned_to_nat(0u);
v___x_3159_ = lean_nat_dec_lt(v___x_3158_, v___x_3157_);
if (v___x_3159_ == 0)
{
return v_fn_3155_;
}
else
{
size_t v___x_3160_; size_t v___x_3161_; lean_object* v___x_3162_; 
v___x_3160_ = lean_usize_of_nat(v___x_3157_);
v___x_3161_ = ((size_t)0ULL);
v___x_3162_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_3156_, v___x_3160_, v___x_3161_, v_fn_3155_);
return v___x_3162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_3163_, lean_object* v_revArgs_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_Lean_mkAppRev(v_fn_3163_, v_revArgs_3164_);
lean_dec_ref(v_revArgs_3164_);
return v_res_3165_;
}
}
LEAN_EXPORT void l_Lean_Expr_dbgToString_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3166_ = stack[0].m_obj;
lean_object* v_res_3167_;
v_res_3167_ = lean_expr_dbg_to_string(v_e_3166_);
stack->m_obj
 = v_res_3167_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = lean_expr_dbg_to_string(v_e_3168_);
lean_dec_ref(v_e_3168_);
return v_res_3169_;
}
}
LEAN_EXPORT void l_Lean_Expr_quickLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3170_ = stack[0].m_obj;
lean_object* v_b_3171_ = stack[1].m_obj;
uint8_t v_res_3172_;
v_res_3172_ = lean_expr_quick_lt(v_a_3170_, v_b_3171_);
stack->m_num = v_res_3172_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_3173_, lean_object* v_b_3174_){
_start:
{
uint8_t v_res_3175_; lean_object* v_r_3176_; 
v_res_3175_ = lean_expr_quick_lt(v_a_3173_, v_b_3174_);
lean_dec_ref(v_b_3174_);
lean_dec_ref(v_a_3173_);
v_r_3176_ = lean_box(v_res_3175_);
return v_r_3176_;
}
}
LEAN_EXPORT void l_Lean_Expr_lt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3177_ = stack[0].m_obj;
lean_object* v_b_3178_ = stack[1].m_obj;
uint8_t v_res_3179_;
v_res_3179_ = lean_expr_lt(v_a_3177_, v_b_3178_);
stack->m_num = v_res_3179_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_3180_, lean_object* v_b_3181_){
_start:
{
uint8_t v_res_3182_; lean_object* v_r_3183_; 
v_res_3182_ = lean_expr_lt(v_a_3180_, v_b_3181_);
lean_dec_ref(v_b_3181_);
lean_dec_ref(v_a_3180_);
v_r_3183_ = lean_box(v_res_3182_);
return v_r_3183_;
}
}
uint8_t l_Lean_Expr_quickComp(lean_object* v_a_3184_, lean_object* v_b_3185_){
_start:
{
uint8_t v___x_3186_; 
v___x_3186_ = lean_expr_quick_lt(v_a_3184_, v_b_3185_);
if (v___x_3186_ == 0)
{
uint8_t v___x_3187_; 
v___x_3187_ = lean_expr_quick_lt(v_b_3185_, v_a_3184_);
if (v___x_3187_ == 0)
{
uint8_t v___x_3188_; 
v___x_3188_ = 1;
return v___x_3188_;
}
else
{
uint8_t v___x_3189_; 
v___x_3189_ = 2;
return v___x_3189_;
}
}
else
{
uint8_t v___x_3190_; 
v___x_3190_ = 0;
return v___x_3190_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_quickComp_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3184_ = stack[0].m_obj;
lean_object* v_b_3185_ = stack[1].m_obj;
uint8_t v_res_3191_;
v_res_3191_ = l_Lean_Expr_quickComp(v_a_3184_, v_b_3185_);
stack->m_num = v_res_3191_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_3192_, lean_object* v_b_3193_){
_start:
{
uint8_t v_res_3194_; lean_object* v_r_3195_; 
v_res_3194_ = l_Lean_Expr_quickComp(v_a_3192_, v_b_3193_);
lean_dec_ref(v_b_3193_);
lean_dec_ref(v_a_3192_);
v_r_3195_ = lean_box(v_res_3194_);
return v_r_3195_;
}
}
LEAN_EXPORT void l_Lean_Expr_eqv_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3196_ = stack[0].m_obj;
lean_object* v_b_3197_ = stack[1].m_obj;
uint8_t v_res_3198_;
v_res_3198_ = lean_expr_eqv(v_a_3196_, v_b_3197_);
stack->m_num = v_res_3198_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_3199_, lean_object* v_b_3200_){
_start:
{
uint8_t v_res_3201_; lean_object* v_r_3202_; 
v_res_3201_ = lean_expr_eqv(v_a_3199_, v_b_3200_);
lean_dec_ref(v_b_3200_);
lean_dec_ref(v_a_3199_);
v_r_3202_ = lean_box(v_res_3201_);
return v_r_3202_;
}
}
LEAN_EXPORT void l_Lean_Expr_equal_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3205_ = stack[0].m_obj;
lean_object* v_b_3206_ = stack[1].m_obj;
uint8_t v_res_3207_;
v_res_3207_ = lean_expr_equal(v_a_3205_, v_b_3206_);
stack->m_num = v_res_3207_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3208_, lean_object* v_b_3209_){
_start:
{
uint8_t v_res_3210_; lean_object* v_r_3211_; 
v_res_3210_ = lean_expr_equal(v_a_3208_, v_b_3209_);
lean_dec_ref(v_b_3209_);
lean_dec_ref(v_a_3208_);
v_r_3211_ = lean_box(v_res_3210_);
return v_r_3211_;
}
}
uint8_t l_Lean_Expr_isSort(lean_object* v_x_3212_){
_start:
{
if (lean_obj_tag(v_x_3212_) == 3)
{
uint8_t v___x_3213_; 
v___x_3213_ = 1;
return v___x_3213_;
}
else
{
uint8_t v___x_3214_; 
v___x_3214_ = 0;
return v___x_3214_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isSort_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3212_ = stack[0].m_obj;
uint8_t v_res_3215_;
v_res_3215_ = l_Lean_Expr_isSort(v_x_3212_);
stack->m_num = v_res_3215_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3216_){
_start:
{
uint8_t v_res_3217_; lean_object* v_r_3218_; 
v_res_3217_ = l_Lean_Expr_isSort(v_x_3216_);
lean_dec_ref(v_x_3216_);
v_r_3218_ = lean_box(v_res_3217_);
return v_r_3218_;
}
}
uint8_t l_Lean_Expr_isType(lean_object* v_x_3219_){
_start:
{
if (lean_obj_tag(v_x_3219_) == 3)
{
lean_object* v_u_3220_; 
v_u_3220_ = lean_ctor_get(v_x_3219_, 0);
if (lean_obj_tag(v_u_3220_) == 1)
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
else
{
uint8_t v___x_3223_; 
v___x_3223_ = 0;
return v___x_3223_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isType_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3219_ = stack[0].m_obj;
uint8_t v_res_3224_;
v_res_3224_ = l_Lean_Expr_isType(v_x_3219_);
stack->m_num = v_res_3224_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3225_){
_start:
{
uint8_t v_res_3226_; lean_object* v_r_3227_; 
v_res_3226_ = l_Lean_Expr_isType(v_x_3225_);
lean_dec_ref(v_x_3225_);
v_r_3227_ = lean_box(v_res_3226_);
return v_r_3227_;
}
}
uint8_t l_Lean_Expr_isType0(lean_object* v_x_3228_){
_start:
{
if (lean_obj_tag(v_x_3228_) == 3)
{
lean_object* v_u_3229_; 
v_u_3229_ = lean_ctor_get(v_x_3228_, 0);
if (lean_obj_tag(v_u_3229_) == 1)
{
lean_object* v_a_3230_; 
v_a_3230_ = lean_ctor_get(v_u_3229_, 0);
if (lean_obj_tag(v_a_3230_) == 0)
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
else
{
uint8_t v___x_3233_; 
v___x_3233_ = 0;
return v___x_3233_;
}
}
else
{
uint8_t v___x_3234_; 
v___x_3234_ = 0;
return v___x_3234_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isType0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3228_ = stack[0].m_obj;
uint8_t v_res_3235_;
v_res_3235_ = l_Lean_Expr_isType0(v_x_3228_);
stack->m_num = v_res_3235_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3236_){
_start:
{
uint8_t v_res_3237_; lean_object* v_r_3238_; 
v_res_3237_ = l_Lean_Expr_isType0(v_x_3236_);
lean_dec_ref(v_x_3236_);
v_r_3238_ = lean_box(v_res_3237_);
return v_r_3238_;
}
}
uint8_t l_Lean_Expr_isProp(lean_object* v_x_3239_){
_start:
{
if (lean_obj_tag(v_x_3239_) == 3)
{
lean_object* v_u_3240_; 
v_u_3240_ = lean_ctor_get(v_x_3239_, 0);
if (lean_obj_tag(v_u_3240_) == 0)
{
uint8_t v___x_3241_; 
v___x_3241_ = 1;
return v___x_3241_;
}
else
{
uint8_t v___x_3242_; 
v___x_3242_ = 0;
return v___x_3242_;
}
}
else
{
uint8_t v___x_3243_; 
v___x_3243_ = 0;
return v___x_3243_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isProp_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3239_ = stack[0].m_obj;
uint8_t v_res_3244_;
v_res_3244_ = l_Lean_Expr_isProp(v_x_3239_);
stack->m_num = v_res_3244_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3245_){
_start:
{
uint8_t v_res_3246_; lean_object* v_r_3247_; 
v_res_3246_ = l_Lean_Expr_isProp(v_x_3245_);
lean_dec_ref(v_x_3245_);
v_r_3247_ = lean_box(v_res_3246_);
return v_r_3247_;
}
}
uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3248_){
_start:
{
if (lean_obj_tag(v_x_3248_) == 0)
{
uint8_t v___x_3249_; 
v___x_3249_ = 1;
return v___x_3249_;
}
else
{
uint8_t v___x_3250_; 
v___x_3250_ = 0;
return v___x_3250_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isBVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3248_ = stack[0].m_obj;
uint8_t v_res_3251_;
v_res_3251_ = l_Lean_Expr_isBVar(v_x_3248_);
stack->m_num = v_res_3251_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3252_){
_start:
{
uint8_t v_res_3253_; lean_object* v_r_3254_; 
v_res_3253_ = l_Lean_Expr_isBVar(v_x_3252_);
lean_dec_ref(v_x_3252_);
v_r_3254_ = lean_box(v_res_3253_);
return v_r_3254_;
}
}
uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3255_){
_start:
{
if (lean_obj_tag(v_x_3255_) == 2)
{
uint8_t v___x_3256_; 
v___x_3256_ = 1;
return v___x_3256_;
}
else
{
uint8_t v___x_3257_; 
v___x_3257_ = 0;
return v___x_3257_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3255_ = stack[0].m_obj;
uint8_t v_res_3258_;
v_res_3258_ = l_Lean_Expr_isMVar(v_x_3255_);
stack->m_num = v_res_3258_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3259_){
_start:
{
uint8_t v_res_3260_; lean_object* v_r_3261_; 
v_res_3260_ = l_Lean_Expr_isMVar(v_x_3259_);
lean_dec_ref(v_x_3259_);
v_r_3261_ = lean_box(v_res_3260_);
return v_r_3261_;
}
}
uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3262_){
_start:
{
if (lean_obj_tag(v_x_3262_) == 1)
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
LEAN_EXPORT void l_Lean_Expr_isFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3262_ = stack[0].m_obj;
uint8_t v_res_3265_;
v_res_3265_ = l_Lean_Expr_isFVar(v_x_3262_);
stack->m_num = v_res_3265_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3266_){
_start:
{
uint8_t v_res_3267_; lean_object* v_r_3268_; 
v_res_3267_ = l_Lean_Expr_isFVar(v_x_3266_);
lean_dec_ref(v_x_3266_);
v_r_3268_ = lean_box(v_res_3267_);
return v_r_3268_;
}
}
uint8_t l_Lean_Expr_isApp(lean_object* v_x_3269_){
_start:
{
if (lean_obj_tag(v_x_3269_) == 5)
{
uint8_t v___x_3270_; 
v___x_3270_ = 1;
return v___x_3270_;
}
else
{
uint8_t v___x_3271_; 
v___x_3271_ = 0;
return v___x_3271_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3269_ = stack[0].m_obj;
uint8_t v_res_3272_;
v_res_3272_ = l_Lean_Expr_isApp(v_x_3269_);
stack->m_num = v_res_3272_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3273_){
_start:
{
uint8_t v_res_3274_; lean_object* v_r_3275_; 
v_res_3274_ = l_Lean_Expr_isApp(v_x_3273_);
lean_dec_ref(v_x_3273_);
v_r_3275_ = lean_box(v_res_3274_);
return v_r_3275_;
}
}
uint8_t l_Lean_Expr_isProj(lean_object* v_x_3276_){
_start:
{
if (lean_obj_tag(v_x_3276_) == 11)
{
uint8_t v___x_3277_; 
v___x_3277_ = 1;
return v___x_3277_;
}
else
{
uint8_t v___x_3278_; 
v___x_3278_ = 0;
return v___x_3278_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isProj_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3276_ = stack[0].m_obj;
uint8_t v_res_3279_;
v_res_3279_ = l_Lean_Expr_isProj(v_x_3276_);
stack->m_num = v_res_3279_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3280_){
_start:
{
uint8_t v_res_3281_; lean_object* v_r_3282_; 
v_res_3281_ = l_Lean_Expr_isProj(v_x_3280_);
lean_dec_ref(v_x_3280_);
v_r_3282_ = lean_box(v_res_3281_);
return v_r_3282_;
}
}
uint8_t l_Lean_Expr_isConst(lean_object* v_x_3283_){
_start:
{
if (lean_obj_tag(v_x_3283_) == 4)
{
uint8_t v___x_3284_; 
v___x_3284_ = 1;
return v___x_3284_;
}
else
{
uint8_t v___x_3285_; 
v___x_3285_ = 0;
return v___x_3285_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isConst_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3283_ = stack[0].m_obj;
uint8_t v_res_3286_;
v_res_3286_ = l_Lean_Expr_isConst(v_x_3283_);
stack->m_num = v_res_3286_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3287_){
_start:
{
uint8_t v_res_3288_; lean_object* v_r_3289_; 
v_res_3288_ = l_Lean_Expr_isConst(v_x_3287_);
lean_dec_ref(v_x_3287_);
v_r_3289_ = lean_box(v_res_3288_);
return v_r_3289_;
}
}
uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3290_, lean_object* v_x_3291_){
_start:
{
if (lean_obj_tag(v_x_3290_) == 4)
{
lean_object* v_declName_3292_; uint8_t v___x_3293_; 
v_declName_3292_ = lean_ctor_get(v_x_3290_, 0);
v___x_3293_ = lean_name_eq(v_declName_3292_, v_x_3291_);
return v___x_3293_;
}
else
{
uint8_t v___x_3294_; 
v___x_3294_ = 0;
return v___x_3294_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isConstOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3290_ = stack[0].m_obj;
lean_object* v_x_3291_ = stack[1].m_obj;
uint8_t v_res_3295_;
v_res_3295_ = l_Lean_Expr_isConstOf(v_x_3290_, v_x_3291_);
stack->m_num = v_res_3295_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3296_, lean_object* v_x_3297_){
_start:
{
uint8_t v_res_3298_; lean_object* v_r_3299_; 
v_res_3298_ = l_Lean_Expr_isConstOf(v_x_3296_, v_x_3297_);
lean_dec(v_x_3297_);
lean_dec_ref(v_x_3296_);
v_r_3299_ = lean_box(v_res_3298_);
return v_r_3299_;
}
}
uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3300_, lean_object* v_x_3301_){
_start:
{
if (lean_obj_tag(v_x_3300_) == 1)
{
lean_object* v_fvarId_3302_; uint8_t v___x_3303_; 
v_fvarId_3302_ = lean_ctor_get(v_x_3300_, 0);
v___x_3303_ = lean_name_eq(v_fvarId_3302_, v_x_3301_);
return v___x_3303_;
}
else
{
uint8_t v___x_3304_; 
v___x_3304_ = 0;
return v___x_3304_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isFVarOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3300_ = stack[0].m_obj;
lean_object* v_x_3301_ = stack[1].m_obj;
uint8_t v_res_3305_;
v_res_3305_ = l_Lean_Expr_isFVarOf(v_x_3300_, v_x_3301_);
stack->m_num = v_res_3305_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3306_, lean_object* v_x_3307_){
_start:
{
uint8_t v_res_3308_; lean_object* v_r_3309_; 
v_res_3308_ = l_Lean_Expr_isFVarOf(v_x_3306_, v_x_3307_);
lean_dec(v_x_3307_);
lean_dec_ref(v_x_3306_);
v_r_3309_ = lean_box(v_res_3308_);
return v_r_3309_;
}
}
uint8_t l_Lean_Expr_isForall(lean_object* v_x_3310_){
_start:
{
if (lean_obj_tag(v_x_3310_) == 7)
{
uint8_t v___x_3311_; 
v___x_3311_ = 1;
return v___x_3311_;
}
else
{
uint8_t v___x_3312_; 
v___x_3312_ = 0;
return v___x_3312_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3310_ = stack[0].m_obj;
uint8_t v_res_3313_;
v_res_3313_ = l_Lean_Expr_isForall(v_x_3310_);
stack->m_num = v_res_3313_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3314_){
_start:
{
uint8_t v_res_3315_; lean_object* v_r_3316_; 
v_res_3315_ = l_Lean_Expr_isForall(v_x_3314_);
lean_dec_ref(v_x_3314_);
v_r_3316_ = lean_box(v_res_3315_);
return v_r_3316_;
}
}
uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3317_){
_start:
{
if (lean_obj_tag(v_x_3317_) == 6)
{
uint8_t v___x_3318_; 
v___x_3318_ = 1;
return v___x_3318_;
}
else
{
uint8_t v___x_3319_; 
v___x_3319_ = 0;
return v___x_3319_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isLambda_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3317_ = stack[0].m_obj;
uint8_t v_res_3320_;
v_res_3320_ = l_Lean_Expr_isLambda(v_x_3317_);
stack->m_num = v_res_3320_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3321_){
_start:
{
uint8_t v_res_3322_; lean_object* v_r_3323_; 
v_res_3322_ = l_Lean_Expr_isLambda(v_x_3321_);
lean_dec_ref(v_x_3321_);
v_r_3323_ = lean_box(v_res_3322_);
return v_r_3323_;
}
}
uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3324_){
_start:
{
switch(lean_obj_tag(v_x_3324_))
{
case 6:
{
uint8_t v___x_3325_; 
v___x_3325_ = 1;
return v___x_3325_;
}
case 7:
{
uint8_t v___x_3326_; 
v___x_3326_ = 1;
return v___x_3326_;
}
default: 
{
uint8_t v___x_3327_; 
v___x_3327_ = 0;
return v___x_3327_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_isBinding_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3324_ = stack[0].m_obj;
uint8_t v_res_3328_;
v_res_3328_ = l_Lean_Expr_isBinding(v_x_3324_);
stack->m_num = v_res_3328_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3329_){
_start:
{
uint8_t v_res_3330_; lean_object* v_r_3331_; 
v_res_3330_ = l_Lean_Expr_isBinding(v_x_3329_);
lean_dec_ref(v_x_3329_);
v_r_3331_ = lean_box(v_res_3330_);
return v_r_3331_;
}
}
uint8_t l_Lean_Expr_isLet(lean_object* v_x_3332_){
_start:
{
if (lean_obj_tag(v_x_3332_) == 8)
{
uint8_t v___x_3333_; 
v___x_3333_ = 1;
return v___x_3333_;
}
else
{
uint8_t v___x_3334_; 
v___x_3334_ = 0;
return v___x_3334_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3332_ = stack[0].m_obj;
uint8_t v_res_3335_;
v_res_3335_ = l_Lean_Expr_isLet(v_x_3332_);
stack->m_num = v_res_3335_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3336_){
_start:
{
uint8_t v_res_3337_; lean_object* v_r_3338_; 
v_res_3337_ = l_Lean_Expr_isLet(v_x_3336_);
lean_dec_ref(v_x_3336_);
v_r_3338_ = lean_box(v_res_3337_);
return v_r_3338_;
}
}
uint8_t l_Lean_Expr_isHave(lean_object* v_x_3339_){
_start:
{
if (lean_obj_tag(v_x_3339_) == 8)
{
uint8_t v_nondep_3340_; 
v_nondep_3340_ = lean_ctor_get_uint8(v_x_3339_, sizeof(void*)*4 + 8);
return v_nondep_3340_;
}
else
{
uint8_t v___x_3341_; 
v___x_3341_ = 0;
return v___x_3341_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isHave_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3339_ = stack[0].m_obj;
uint8_t v_res_3342_;
v_res_3342_ = l_Lean_Expr_isHave(v_x_3339_);
stack->m_num = v_res_3342_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3343_){
_start:
{
uint8_t v_res_3344_; lean_object* v_r_3345_; 
v_res_3344_ = l_Lean_Expr_isHave(v_x_3343_);
lean_dec_ref(v_x_3343_);
v_r_3345_ = lean_box(v_res_3344_);
return v_r_3345_;
}
}
uint8_t lean_expr_is_have(lean_object* v_a_3346_){
_start:
{
uint8_t v___x_3347_; 
v___x_3347_ = l_Lean_Expr_isHave(v_a_3346_);
lean_dec_ref(v_a_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT void lean_expr_is_have_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3346_ = stack[0].m_obj;
uint8_t v_res_3348_;
v_res_3348_ = lean_expr_is_have(v_a_3346_);
stack->m_num = v_res_3348_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3349_){
_start:
{
uint8_t v_res_3350_; lean_object* v_r_3351_; 
v_res_3350_ = lean_expr_is_have(v_a_3349_);
v_r_3351_ = lean_box(v_res_3350_);
return v_r_3351_;
}
}
uint8_t l_Lean_Expr_isMData(lean_object* v_x_3352_){
_start:
{
if (lean_obj_tag(v_x_3352_) == 10)
{
uint8_t v___x_3353_; 
v___x_3353_ = 1;
return v___x_3353_;
}
else
{
uint8_t v___x_3354_; 
v___x_3354_ = 0;
return v___x_3354_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isMData_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3352_ = stack[0].m_obj;
uint8_t v_res_3355_;
v_res_3355_ = l_Lean_Expr_isMData(v_x_3352_);
stack->m_num = v_res_3355_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3356_){
_start:
{
uint8_t v_res_3357_; lean_object* v_r_3358_; 
v_res_3357_ = l_Lean_Expr_isMData(v_x_3356_);
lean_dec_ref(v_x_3356_);
v_r_3358_ = lean_box(v_res_3357_);
return v_r_3358_;
}
}
uint8_t l_Lean_Expr_isLit(lean_object* v_x_3359_){
_start:
{
if (lean_obj_tag(v_x_3359_) == 9)
{
uint8_t v___x_3360_; 
v___x_3360_ = 1;
return v___x_3360_;
}
else
{
uint8_t v___x_3361_; 
v___x_3361_ = 0;
return v___x_3361_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isLit_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3359_ = stack[0].m_obj;
uint8_t v_res_3362_;
v_res_3362_ = l_Lean_Expr_isLit(v_x_3359_);
stack->m_num = v_res_3362_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3363_){
_start:
{
uint8_t v_res_3364_; lean_object* v_r_3365_; 
v_res_3364_ = l_Lean_Expr_isLit(v_x_3363_);
lean_dec_ref(v_x_3363_);
v_r_3365_ = lean_box(v_res_3364_);
return v_r_3365_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3366_){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = l_Lean_instInhabitedExpr;
v___x_3368_ = lean_panic_fn_borrowed(v___x_3367_, v_msg_3366_);
return v___x_3368_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3372_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3373_ = lean_unsigned_to_nat(15u);
v___x_3374_ = lean_unsigned_to_nat(931u);
v___x_3375_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3376_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3377_ = l_mkPanicMessageWithDecl(v___x_3376_, v___x_3375_, v___x_3374_, v___x_3373_, v___x_3372_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3378_){
_start:
{
if (lean_obj_tag(v_x_3378_) == 5)
{
lean_object* v_fn_3379_; 
v_fn_3379_ = lean_ctor_get(v_x_3378_, 0);
lean_inc_ref(v_fn_3379_);
return v_fn_3379_;
}
else
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3381_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3380_);
return v___x_3381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Lean_Expr_appFn_x21(v_x_3382_);
lean_dec_ref(v_x_3382_);
return v_res_3383_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3385_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3386_ = lean_unsigned_to_nat(15u);
v___x_3387_ = lean_unsigned_to_nat(935u);
v___x_3388_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3389_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3390_ = l_mkPanicMessageWithDecl(v___x_3389_, v___x_3388_, v___x_3387_, v___x_3386_, v___x_3385_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3391_){
_start:
{
if (lean_obj_tag(v_x_3391_) == 5)
{
lean_object* v_arg_3392_; 
v_arg_3392_ = lean_ctor_get(v_x_3391_, 1);
lean_inc_ref(v_arg_3392_);
return v_arg_3392_;
}
else
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3394_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3393_);
return v___x_3394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_Expr_appArg_x21(v_x_3395_);
lean_dec_ref(v_x_3395_);
return v_res_3396_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3398_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3399_ = lean_unsigned_to_nat(17u);
v___x_3400_ = lean_unsigned_to_nat(940u);
v___x_3401_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3402_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3403_ = l_mkPanicMessageWithDecl(v___x_3402_, v___x_3401_, v___x_3400_, v___x_3399_, v___x_3398_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3404_){
_start:
{
switch(lean_obj_tag(v_x_3404_))
{
case 10:
{
lean_object* v_expr_3405_; 
v_expr_3405_ = lean_ctor_get(v_x_3404_, 1);
v_x_3404_ = v_expr_3405_;
goto _start;
}
case 5:
{
lean_object* v_fn_3407_; 
v_fn_3407_ = lean_ctor_get(v_x_3404_, 0);
lean_inc_ref(v_fn_3407_);
return v_fn_3407_;
}
default: 
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3409_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3408_);
return v___x_3409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_Lean_Expr_appFn_x21_x27(v_x_3410_);
lean_dec_ref(v_x_3410_);
return v_res_3411_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3413_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3414_ = lean_unsigned_to_nat(17u);
v___x_3415_ = lean_unsigned_to_nat(945u);
v___x_3416_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3417_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3418_ = l_mkPanicMessageWithDecl(v___x_3417_, v___x_3416_, v___x_3415_, v___x_3414_, v___x_3413_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3419_){
_start:
{
switch(lean_obj_tag(v_x_3419_))
{
case 10:
{
lean_object* v_expr_3420_; 
v_expr_3420_ = lean_ctor_get(v_x_3419_, 1);
v_x_3419_ = v_expr_3420_;
goto _start;
}
case 5:
{
lean_object* v_arg_3422_; 
v_arg_3422_ = lean_ctor_get(v_x_3419_, 1);
lean_inc_ref(v_arg_3422_);
return v_arg_3422_;
}
default: 
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3424_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3423_);
return v___x_3424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Lean_Expr_appArg_x21_x27(v_x_3425_);
lean_dec_ref(v_x_3425_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3427_){
_start:
{
lean_object* v_arg_3428_; 
v_arg_3428_ = lean_ctor_get(v_e_3427_, 1);
lean_inc_ref(v_arg_3428_);
return v_arg_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_Expr_appArg___redArg(v_e_3429_);
lean_dec_ref(v_e_3429_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3431_, lean_object* v_h_3432_){
_start:
{
lean_object* v_arg_3433_; 
v_arg_3433_ = lean_ctor_get(v_e_3431_, 1);
lean_inc_ref(v_arg_3433_);
return v_arg_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3434_, lean_object* v_h_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_Expr_appArg(v_e_3434_, v_h_3435_);
lean_dec_ref(v_e_3434_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3437_){
_start:
{
lean_object* v_fn_3438_; 
v_fn_3438_ = lean_ctor_get(v_e_3437_, 0);
lean_inc_ref(v_fn_3438_);
return v_fn_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_Lean_Expr_appFn___redArg(v_e_3439_);
lean_dec_ref(v_e_3439_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3441_, lean_object* v_h_3442_){
_start:
{
lean_object* v_fn_3443_; 
v_fn_3443_ = lean_ctor_get(v_e_3441_, 0);
lean_inc_ref(v_fn_3443_);
return v_fn_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3444_, lean_object* v_h_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Lean_Expr_appFn(v_e_3444_, v_h_3445_);
lean_dec_ref(v_e_3444_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3447_){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3448_ = lean_box(0);
v___x_3449_ = lean_panic_fn_borrowed(v___x_3448_, v_msg_3447_);
return v___x_3449_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3452_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3453_ = lean_unsigned_to_nat(14u);
v___x_3454_ = lean_unsigned_to_nat(957u);
v___x_3455_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3456_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3457_ = l_mkPanicMessageWithDecl(v___x_3456_, v___x_3455_, v___x_3454_, v___x_3453_, v___x_3452_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3458_){
_start:
{
if (lean_obj_tag(v_x_3458_) == 3)
{
lean_object* v_u_3459_; 
v_u_3459_ = lean_ctor_get(v_x_3458_, 0);
lean_inc(v_u_3459_);
return v_u_3459_;
}
else
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3460_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3461_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3460_);
return v___x_3461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_Lean_Expr_sortLevel_x21(v_x_3462_);
lean_dec_ref(v_x_3462_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3464_){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3466_ = lean_panic_fn_borrowed(v___x_3465_, v_msg_3464_);
return v___x_3466_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3469_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3470_ = lean_unsigned_to_nat(13u);
v___x_3471_ = lean_unsigned_to_nat(961u);
v___x_3472_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3473_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3474_ = l_mkPanicMessageWithDecl(v___x_3473_, v___x_3472_, v___x_3471_, v___x_3470_, v___x_3469_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3475_){
_start:
{
if (lean_obj_tag(v_x_3475_) == 9)
{
lean_object* v_a_3476_; 
v_a_3476_ = lean_ctor_get(v_x_3475_, 0);
lean_inc_ref(v_a_3476_);
return v_a_3476_;
}
else
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3478_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3477_);
return v___x_3478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_Expr_litValue_x21(v_x_3479_);
lean_dec_ref(v_x_3479_);
return v_res_3480_;
}
}
uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3481_){
_start:
{
if (lean_obj_tag(v_x_3481_) == 9)
{
lean_object* v_a_3482_; 
v_a_3482_ = lean_ctor_get(v_x_3481_, 0);
if (lean_obj_tag(v_a_3482_) == 0)
{
uint8_t v___x_3483_; 
v___x_3483_ = 1;
return v___x_3483_;
}
else
{
uint8_t v___x_3484_; 
v___x_3484_ = 0;
return v___x_3484_;
}
}
else
{
uint8_t v___x_3485_; 
v___x_3485_ = 0;
return v___x_3485_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isRawNatLit_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3481_ = stack[0].m_obj;
uint8_t v_res_3486_;
v_res_3486_ = l_Lean_Expr_isRawNatLit(v_x_3481_);
stack->m_num = v_res_3486_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3487_){
_start:
{
uint8_t v_res_3488_; lean_object* v_r_3489_; 
v_res_3488_ = l_Lean_Expr_isRawNatLit(v_x_3487_);
lean_dec_ref(v_x_3487_);
v_r_3489_ = lean_box(v_res_3488_);
return v_r_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3490_){
_start:
{
if (lean_obj_tag(v_x_3490_) == 9)
{
lean_object* v_a_3491_; 
v_a_3491_ = lean_ctor_get(v_x_3490_, 0);
lean_inc_ref(v_a_3491_);
lean_dec_ref_known(v_x_3490_, 1);
if (lean_obj_tag(v_a_3491_) == 0)
{
lean_object* v_val_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
v_val_3492_ = lean_ctor_get(v_a_3491_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v_a_3491_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v_a_3491_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_val_3492_);
lean_dec(v_a_3491_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
lean_ctor_set_tag(v___x_3494_, 1);
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_val_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
else
{
lean_object* v___x_3500_; 
lean_dec_ref(v_a_3491_);
v___x_3500_ = lean_box(0);
return v___x_3500_;
}
}
else
{
lean_object* v___x_3501_; 
lean_dec_ref(v_x_3490_);
v___x_3501_ = lean_box(0);
return v___x_3501_;
}
}
}
uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3502_){
_start:
{
if (lean_obj_tag(v_x_3502_) == 9)
{
lean_object* v_a_3503_; 
v_a_3503_ = lean_ctor_get(v_x_3502_, 0);
if (lean_obj_tag(v_a_3503_) == 1)
{
uint8_t v___x_3504_; 
v___x_3504_ = 1;
return v___x_3504_;
}
else
{
uint8_t v___x_3505_; 
v___x_3505_ = 0;
return v___x_3505_;
}
}
else
{
uint8_t v___x_3506_; 
v___x_3506_ = 0;
return v___x_3506_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isStringLit_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3502_ = stack[0].m_obj;
uint8_t v_res_3507_;
v_res_3507_ = l_Lean_Expr_isStringLit(v_x_3502_);
stack->m_num = v_res_3507_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3508_){
_start:
{
uint8_t v_res_3509_; lean_object* v_r_3510_; 
v_res_3509_ = l_Lean_Expr_isStringLit(v_x_3508_);
lean_dec_ref(v_x_3508_);
v_r_3510_ = lean_box(v_res_3509_);
return v_r_3510_;
}
}
uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3515_){
_start:
{
if (lean_obj_tag(v_x_3515_) == 5)
{
lean_object* v_fn_3516_; 
v_fn_3516_ = lean_ctor_get(v_x_3515_, 0);
if (lean_obj_tag(v_fn_3516_) == 4)
{
lean_object* v_arg_3517_; lean_object* v_declName_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v_arg_3517_ = lean_ctor_get(v_x_3515_, 1);
v_declName_3518_ = lean_ctor_get(v_fn_3516_, 0);
v___x_3519_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3520_ = lean_name_eq(v_declName_3518_, v___x_3519_);
if (v___x_3520_ == 0)
{
return v___x_3520_;
}
else
{
uint8_t v___x_3521_; 
v___x_3521_ = l_Lean_Expr_isRawNatLit(v_arg_3517_);
return v___x_3521_;
}
}
else
{
uint8_t v___x_3522_; 
v___x_3522_ = 0;
return v___x_3522_;
}
}
else
{
uint8_t v___x_3523_; 
v___x_3523_ = 0;
return v___x_3523_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isCharLit_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3515_ = stack[0].m_obj;
uint8_t v_res_3524_;
v_res_3524_ = l_Lean_Expr_isCharLit(v_x_3515_);
stack->m_num = v_res_3524_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3525_){
_start:
{
uint8_t v_res_3526_; lean_object* v_r_3527_; 
v_res_3526_ = l_Lean_Expr_isCharLit(v_x_3525_);
lean_dec_ref(v_x_3525_);
v_r_3527_ = lean_box(v_res_3526_);
return v_r_3527_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3528_){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = lean_box(0);
v___x_3530_ = lean_panic_fn_borrowed(v___x_3529_, v_msg_3528_);
return v___x_3530_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3533_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3534_ = lean_unsigned_to_nat(17u);
v___x_3535_ = lean_unsigned_to_nat(985u);
v___x_3536_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3537_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3538_ = l_mkPanicMessageWithDecl(v___x_3537_, v___x_3536_, v___x_3535_, v___x_3534_, v___x_3533_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3539_){
_start:
{
if (lean_obj_tag(v_x_3539_) == 4)
{
lean_object* v_declName_3540_; 
v_declName_3540_ = lean_ctor_get(v_x_3539_, 0);
lean_inc(v_declName_3540_);
return v_declName_3540_;
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3542_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3541_);
return v___x_3542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_Expr_constName_x21(v_x_3543_);
lean_dec_ref(v_x_3543_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3545_){
_start:
{
if (lean_obj_tag(v_x_3545_) == 4)
{
lean_object* v_declName_3546_; lean_object* v___x_3547_; 
v_declName_3546_ = lean_ctor_get(v_x_3545_, 0);
lean_inc(v_declName_3546_);
v___x_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3547_, 0, v_declName_3546_);
return v___x_3547_;
}
else
{
lean_object* v___x_3548_; 
v___x_3548_ = lean_box(0);
return v___x_3548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Lean_Expr_constName_x3f(v_x_3549_);
lean_dec_ref(v_x_3549_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3551_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_Expr_constName_x3f(v_e_3551_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v___x_3553_; 
v___x_3553_ = lean_box(0);
return v___x_3553_;
}
else
{
lean_object* v_val_3554_; 
v_val_3554_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_val_3554_);
lean_dec_ref_known(v___x_3552_, 1);
return v_val_3554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Lean_Expr_constName(v_e_3555_);
lean_dec_ref(v_e_3555_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3557_){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = lean_box(0);
v___x_3559_ = lean_panic_fn_borrowed(v___x_3558_, v_msg_3557_);
return v___x_3559_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3561_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3562_ = lean_unsigned_to_nat(18u);
v___x_3563_ = lean_unsigned_to_nat(1005u);
v___x_3564_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3565_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3566_ = l_mkPanicMessageWithDecl(v___x_3565_, v___x_3564_, v___x_3563_, v___x_3562_, v___x_3561_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3567_){
_start:
{
if (lean_obj_tag(v_x_3567_) == 4)
{
lean_object* v_us_3568_; 
v_us_3568_ = lean_ctor_get(v_x_3567_, 1);
lean_inc(v_us_3568_);
return v_us_3568_;
}
else
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3570_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3569_);
return v___x_3570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Lean_Expr_constLevels_x21(v_x_3571_);
lean_dec_ref(v_x_3571_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3573_){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = lean_unsigned_to_nat(0u);
v___x_3575_ = lean_panic_fn_borrowed(v___x_3574_, v_msg_3573_);
return v___x_3575_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3578_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3579_ = lean_unsigned_to_nat(16u);
v___x_3580_ = lean_unsigned_to_nat(1009u);
v___x_3581_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3582_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3583_ = l_mkPanicMessageWithDecl(v___x_3582_, v___x_3581_, v___x_3580_, v___x_3579_, v___x_3578_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3584_){
_start:
{
if (lean_obj_tag(v_x_3584_) == 0)
{
lean_object* v_deBruijnIndex_3585_; 
v_deBruijnIndex_3585_ = lean_ctor_get(v_x_3584_, 0);
lean_inc(v_deBruijnIndex_3585_);
return v_deBruijnIndex_3585_;
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3587_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3586_);
return v___x_3587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Lean_Expr_bvarIdx_x21(v_x_3588_);
lean_dec_ref(v_x_3588_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3590_){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = lean_box(0);
v___x_3592_ = lean_panic_fn_borrowed(v___x_3591_, v_msg_3590_);
return v___x_3592_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3595_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3596_ = lean_unsigned_to_nat(14u);
v___x_3597_ = lean_unsigned_to_nat(1013u);
v___x_3598_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3599_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3600_ = l_mkPanicMessageWithDecl(v___x_3599_, v___x_3598_, v___x_3597_, v___x_3596_, v___x_3595_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3601_){
_start:
{
if (lean_obj_tag(v_x_3601_) == 1)
{
lean_object* v_fvarId_3602_; 
v_fvarId_3602_ = lean_ctor_get(v_x_3601_, 0);
lean_inc(v_fvarId_3602_);
return v_fvarId_3602_;
}
else
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3603_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3604_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3603_);
return v___x_3604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Lean_Expr_fvarId_x21(v_x_3605_);
lean_dec_ref(v_x_3605_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3607_){
_start:
{
if (lean_obj_tag(v_x_3607_) == 1)
{
lean_object* v_fvarId_3608_; lean_object* v___x_3609_; 
v_fvarId_3608_ = lean_ctor_get(v_x_3607_, 0);
lean_inc(v_fvarId_3608_);
v___x_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3609_, 0, v_fvarId_3608_);
return v___x_3609_;
}
else
{
lean_object* v___x_3610_; 
v___x_3610_ = lean_box(0);
return v___x_3610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Lean_Expr_fvarId_x3f(v_x_3611_);
lean_dec_ref(v_x_3611_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3613_){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3614_ = lean_box(0);
v___x_3615_ = lean_panic_fn_borrowed(v___x_3614_, v_msg_3613_);
return v___x_3615_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3618_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3619_ = lean_unsigned_to_nat(14u);
v___x_3620_ = lean_unsigned_to_nat(1021u);
v___x_3621_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3622_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3623_ = l_mkPanicMessageWithDecl(v___x_3622_, v___x_3621_, v___x_3620_, v___x_3619_, v___x_3618_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3624_){
_start:
{
if (lean_obj_tag(v_x_3624_) == 2)
{
lean_object* v_mvarId_3625_; 
v_mvarId_3625_ = lean_ctor_get(v_x_3624_, 0);
lean_inc(v_mvarId_3625_);
return v_mvarId_3625_;
}
else
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3627_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3626_);
return v___x_3627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Lean_Expr_mvarId_x21(v_x_3628_);
lean_dec_ref(v_x_3628_);
return v_res_3629_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3632_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3633_ = lean_unsigned_to_nat(23u);
v___x_3634_ = lean_unsigned_to_nat(1026u);
v___x_3635_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3636_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3637_ = l_mkPanicMessageWithDecl(v___x_3636_, v___x_3635_, v___x_3634_, v___x_3633_, v___x_3632_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3638_){
_start:
{
switch(lean_obj_tag(v_x_3638_))
{
case 7:
{
lean_object* v_binderName_3639_; 
v_binderName_3639_ = lean_ctor_get(v_x_3638_, 0);
lean_inc(v_binderName_3639_);
return v_binderName_3639_;
}
case 6:
{
lean_object* v_binderName_3640_; 
v_binderName_3640_ = lean_ctor_get(v_x_3638_, 0);
lean_inc(v_binderName_3640_);
return v_binderName_3640_;
}
default: 
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3642_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3641_);
return v___x_3642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_Lean_Expr_bindingName_x21(v_x_3643_);
lean_dec_ref(v_x_3643_);
return v_res_3644_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3646_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3647_ = lean_unsigned_to_nat(23u);
v___x_3648_ = lean_unsigned_to_nat(1031u);
v___x_3649_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3650_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3651_ = l_mkPanicMessageWithDecl(v___x_3650_, v___x_3649_, v___x_3648_, v___x_3647_, v___x_3646_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3652_){
_start:
{
switch(lean_obj_tag(v_x_3652_))
{
case 7:
{
lean_object* v_binderType_3653_; 
v_binderType_3653_ = lean_ctor_get(v_x_3652_, 1);
lean_inc_ref(v_binderType_3653_);
return v_binderType_3653_;
}
case 6:
{
lean_object* v_binderType_3654_; 
v_binderType_3654_ = lean_ctor_get(v_x_3652_, 1);
lean_inc_ref(v_binderType_3654_);
return v_binderType_3654_;
}
default: 
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3656_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3655_);
return v___x_3656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Lean_Expr_bindingDomain_x21(v_x_3657_);
lean_dec_ref(v_x_3657_);
return v_res_3658_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3660_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3661_ = lean_unsigned_to_nat(23u);
v___x_3662_ = lean_unsigned_to_nat(1036u);
v___x_3663_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3664_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3665_ = l_mkPanicMessageWithDecl(v___x_3664_, v___x_3663_, v___x_3662_, v___x_3661_, v___x_3660_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3666_){
_start:
{
switch(lean_obj_tag(v_x_3666_))
{
case 7:
{
lean_object* v_body_3667_; 
v_body_3667_ = lean_ctor_get(v_x_3666_, 2);
lean_inc_ref(v_body_3667_);
return v_body_3667_;
}
case 6:
{
lean_object* v_body_3668_; 
v_body_3668_ = lean_ctor_get(v_x_3666_, 2);
lean_inc_ref(v_body_3668_);
return v_body_3668_;
}
default: 
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3669_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3670_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3669_);
return v___x_3670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_Expr_bindingBody_x21(v_x_3671_);
lean_dec_ref(v_x_3671_);
return v_res_3672_;
}
}
uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3673_){
_start:
{
uint8_t v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; uint8_t v___x_3677_; 
v___x_3674_ = 0;
v___x_3675_ = lean_box(v___x_3674_);
v___x_3676_ = lean_panic_fn_borrowed(v___x_3675_, v_msg_3673_);
lean_dec(v___x_3675_);
v___x_3677_ = lean_unbox(v___x_3676_);
lean_dec(v___x_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3673_ = stack[0].m_obj;
uint8_t v_res_3678_;
v_res_3678_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3673_);
stack->m_num = v_res_3678_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3679_){
_start:
{
uint8_t v_res_3680_; lean_object* v_r_3681_; 
v_res_3680_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3679_);
v_r_3681_ = lean_box(v_res_3680_);
return v_r_3681_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3683_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3684_ = lean_unsigned_to_nat(24u);
v___x_3685_ = lean_unsigned_to_nat(1041u);
v___x_3686_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3687_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3688_ = l_mkPanicMessageWithDecl(v___x_3687_, v___x_3686_, v___x_3685_, v___x_3684_, v___x_3683_);
return v___x_3688_;
}
}
uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3689_){
_start:
{
switch(lean_obj_tag(v_x_3689_))
{
case 7:
{
uint8_t v_binderInfo_3690_; 
v_binderInfo_3690_ = lean_ctor_get_uint8(v_x_3689_, sizeof(void*)*3 + 8);
return v_binderInfo_3690_;
}
case 6:
{
uint8_t v_binderInfo_3691_; 
v_binderInfo_3691_ = lean_ctor_get_uint8(v_x_3689_, sizeof(void*)*3 + 8);
return v_binderInfo_3691_;
}
default: 
{
lean_object* v___x_3692_; uint8_t v___x_3693_; 
v___x_3692_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3693_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3692_);
return v___x_3693_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_bindingInfo_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3689_ = stack[0].m_obj;
uint8_t v_res_3694_;
v_res_3694_ = l_Lean_Expr_bindingInfo_x21(v_x_3689_);
stack->m_num = v_res_3694_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3695_){
_start:
{
uint8_t v_res_3696_; lean_object* v_r_3697_; 
v_res_3696_ = l_Lean_Expr_bindingInfo_x21(v_x_3695_);
lean_dec_ref(v_x_3695_);
v_r_3697_ = lean_box(v_res_3696_);
return v_r_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3698_){
_start:
{
lean_object* v_binderName_3699_; 
v_binderName_3699_ = lean_ctor_get(v_x_3698_, 0);
lean_inc(v_binderName_3699_);
return v_binderName_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_Expr_forallName___redArg(v_x_3700_);
lean_dec_ref(v_x_3700_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3702_, lean_object* v_x_3703_){
_start:
{
lean_object* v_binderName_3704_; 
v_binderName_3704_ = lean_ctor_get(v_x_3702_, 0);
lean_inc(v_binderName_3704_);
return v_binderName_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3705_, lean_object* v_x_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l_Lean_Expr_forallName(v_x_3705_, v_x_3706_);
lean_dec_ref(v_x_3705_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3708_){
_start:
{
lean_object* v_binderType_3709_; 
v_binderType_3709_ = lean_ctor_get(v_x_3708_, 1);
lean_inc_ref(v_binderType_3709_);
return v_binderType_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Lean_Expr_forallDomain___redArg(v_x_3710_);
lean_dec_ref(v_x_3710_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3712_, lean_object* v_x_3713_){
_start:
{
lean_object* v_binderType_3714_; 
v_binderType_3714_ = lean_ctor_get(v_x_3712_, 1);
lean_inc_ref(v_binderType_3714_);
return v_binderType_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3715_, lean_object* v_x_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lean_Expr_forallDomain(v_x_3715_, v_x_3716_);
lean_dec_ref(v_x_3715_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3718_){
_start:
{
lean_object* v_body_3719_; 
v_body_3719_ = lean_ctor_get(v_x_3718_, 2);
lean_inc_ref(v_body_3719_);
return v_body_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Lean_Expr_forallBody___redArg(v_x_3720_);
lean_dec_ref(v_x_3720_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3722_, lean_object* v_x_3723_){
_start:
{
lean_object* v_body_3724_; 
v_body_3724_ = lean_ctor_get(v_x_3722_, 2);
lean_inc_ref(v_body_3724_);
return v_body_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3725_, lean_object* v_x_3726_){
_start:
{
lean_object* v_res_3727_; 
v_res_3727_ = l_Lean_Expr_forallBody(v_x_3725_, v_x_3726_);
lean_dec_ref(v_x_3725_);
return v_res_3727_;
}
}
uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3728_){
_start:
{
uint8_t v_binderInfo_3729_; 
v_binderInfo_3729_ = lean_ctor_get_uint8(v_x_3728_, sizeof(void*)*3 + 8);
return v_binderInfo_3729_;
}
}
LEAN_EXPORT void l_Lean_Expr_forallInfo___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3728_ = stack[0].m_obj;
uint8_t v_res_3730_;
v_res_3730_ = l_Lean_Expr_forallInfo___redArg(v_x_3728_);
stack->m_num = v_res_3730_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3731_){
_start:
{
uint8_t v_res_3732_; lean_object* v_r_3733_; 
v_res_3732_ = l_Lean_Expr_forallInfo___redArg(v_x_3731_);
lean_dec_ref(v_x_3731_);
v_r_3733_ = lean_box(v_res_3732_);
return v_r_3733_;
}
}
uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3734_, lean_object* v_x_3735_){
_start:
{
uint8_t v_binderInfo_3736_; 
v_binderInfo_3736_ = lean_ctor_get_uint8(v_x_3734_, sizeof(void*)*3 + 8);
return v_binderInfo_3736_;
}
}
LEAN_EXPORT void l_Lean_Expr_forallInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3734_ = stack[0].m_obj;
uint8_t v_res_3737_;
v_res_3737_ = l_Lean_Expr_forallInfo(v_x_3734_, lean_box(0));
stack->m_num = v_res_3737_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3738_, lean_object* v_x_3739_){
_start:
{
uint8_t v_res_3740_; lean_object* v_r_3741_; 
v_res_3740_ = l_Lean_Expr_forallInfo(v_x_3738_, v_x_3739_);
lean_dec_ref(v_x_3738_);
v_r_3741_ = lean_box(v_res_3740_);
return v_r_3741_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3744_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3745_ = lean_unsigned_to_nat(17u);
v___x_3746_ = lean_unsigned_to_nat(1057u);
v___x_3747_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3748_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3749_ = l_mkPanicMessageWithDecl(v___x_3748_, v___x_3747_, v___x_3746_, v___x_3745_, v___x_3744_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3750_){
_start:
{
if (lean_obj_tag(v_x_3750_) == 8)
{
lean_object* v_declName_3751_; 
v_declName_3751_ = lean_ctor_get(v_x_3750_, 0);
lean_inc(v_declName_3751_);
return v_declName_3751_;
}
else
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3753_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3752_);
return v___x_3753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_Expr_letName_x21(v_x_3754_);
lean_dec_ref(v_x_3754_);
return v_res_3755_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3757_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3758_ = lean_unsigned_to_nat(19u);
v___x_3759_ = lean_unsigned_to_nat(1061u);
v___x_3760_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3761_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3762_ = l_mkPanicMessageWithDecl(v___x_3761_, v___x_3760_, v___x_3759_, v___x_3758_, v___x_3757_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3763_){
_start:
{
if (lean_obj_tag(v_x_3763_) == 8)
{
lean_object* v_type_3764_; 
v_type_3764_ = lean_ctor_get(v_x_3763_, 1);
lean_inc_ref(v_type_3764_);
return v_type_3764_;
}
else
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3765_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3766_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3765_);
return v___x_3766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_Expr_letType_x21(v_x_3767_);
lean_dec_ref(v_x_3767_);
return v_res_3768_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3770_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3771_ = lean_unsigned_to_nat(21u);
v___x_3772_ = lean_unsigned_to_nat(1065u);
v___x_3773_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3774_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3775_ = l_mkPanicMessageWithDecl(v___x_3774_, v___x_3773_, v___x_3772_, v___x_3771_, v___x_3770_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3776_){
_start:
{
if (lean_obj_tag(v_x_3776_) == 8)
{
lean_object* v_value_3777_; 
v_value_3777_ = lean_ctor_get(v_x_3776_, 2);
lean_inc_ref(v_value_3777_);
return v_value_3777_;
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3779_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3778_);
return v___x_3779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l_Lean_Expr_letValue_x21(v_x_3780_);
lean_dec_ref(v_x_3780_);
return v_res_3781_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3783_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3784_ = lean_unsigned_to_nat(23u);
v___x_3785_ = lean_unsigned_to_nat(1069u);
v___x_3786_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3787_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3788_ = l_mkPanicMessageWithDecl(v___x_3787_, v___x_3786_, v___x_3785_, v___x_3784_, v___x_3783_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3789_){
_start:
{
if (lean_obj_tag(v_x_3789_) == 8)
{
lean_object* v_body_3790_; 
v_body_3790_ = lean_ctor_get(v_x_3789_, 3);
lean_inc_ref(v_body_3790_);
return v_body_3790_;
}
else
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3792_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3791_);
return v___x_3792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_Lean_Expr_letBody_x21(v_x_3793_);
lean_dec_ref(v_x_3793_);
return v_res_3794_;
}
}
uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3795_){
_start:
{
uint8_t v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; uint8_t v___x_3799_; 
v___x_3796_ = 0;
v___x_3797_ = lean_box(v___x_3796_);
v___x_3798_ = lean_panic_fn_borrowed(v___x_3797_, v_msg_3795_);
lean_dec(v___x_3797_);
v___x_3799_ = lean_unbox(v___x_3798_);
lean_dec(v___x_3798_);
return v___x_3799_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Expr_letNondep_x21_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3795_ = stack[0].m_obj;
uint8_t v_res_3800_;
v_res_3800_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3795_);
stack->m_num = v_res_3800_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3801_){
_start:
{
uint8_t v_res_3802_; lean_object* v_r_3803_; 
v_res_3802_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3801_);
v_r_3803_ = lean_box(v_res_3802_);
return v_r_3803_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3805_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3806_ = lean_unsigned_to_nat(27u);
v___x_3807_ = lean_unsigned_to_nat(1073u);
v___x_3808_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3809_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3810_ = l_mkPanicMessageWithDecl(v___x_3809_, v___x_3808_, v___x_3807_, v___x_3806_, v___x_3805_);
return v___x_3810_;
}
}
uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3811_){
_start:
{
if (lean_obj_tag(v_x_3811_) == 8)
{
uint8_t v_nondep_3812_; 
v_nondep_3812_ = lean_ctor_get_uint8(v_x_3811_, sizeof(void*)*4 + 8);
return v_nondep_3812_;
}
else
{
lean_object* v___x_3813_; uint8_t v___x_3814_; 
v___x_3813_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3814_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3813_);
return v___x_3814_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_letNondep_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3811_ = stack[0].m_obj;
uint8_t v_res_3815_;
v_res_3815_ = l_Lean_Expr_letNondep_x21(v_x_3811_);
stack->m_num = v_res_3815_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3816_){
_start:
{
uint8_t v_res_3817_; lean_object* v_r_3818_; 
v_res_3817_ = l_Lean_Expr_letNondep_x21(v_x_3816_);
lean_dec_ref(v_x_3816_);
v_r_3818_ = lean_box(v_res_3817_);
return v_r_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3819_){
_start:
{
if (lean_obj_tag(v_x_3819_) == 10)
{
lean_object* v_expr_3820_; 
v_expr_3820_ = lean_ctor_get(v_x_3819_, 1);
v_x_3819_ = v_expr_3820_;
goto _start;
}
else
{
lean_inc_ref(v_x_3819_);
return v_x_3819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Lean_Expr_consumeMData(v_x_3822_);
lean_dec_ref(v_x_3822_);
return v_res_3823_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3826_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3827_ = lean_unsigned_to_nat(17u);
v___x_3828_ = lean_unsigned_to_nat(1081u);
v___x_3829_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3830_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3831_ = l_mkPanicMessageWithDecl(v___x_3830_, v___x_3829_, v___x_3828_, v___x_3827_, v___x_3826_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3832_){
_start:
{
if (lean_obj_tag(v_x_3832_) == 10)
{
lean_object* v_expr_3833_; 
v_expr_3833_ = lean_ctor_get(v_x_3832_, 1);
lean_inc_ref(v_expr_3833_);
return v_expr_3833_;
}
else
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3834_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3835_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3834_);
return v___x_3835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_Expr_mdataExpr_x21(v_x_3836_);
lean_dec_ref(v_x_3836_);
return v_res_3837_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3840_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3841_ = lean_unsigned_to_nat(18u);
v___x_3842_ = lean_unsigned_to_nat(1085u);
v___x_3843_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3844_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3845_ = l_mkPanicMessageWithDecl(v___x_3844_, v___x_3843_, v___x_3842_, v___x_3841_, v___x_3840_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3846_){
_start:
{
if (lean_obj_tag(v_x_3846_) == 11)
{
lean_object* v_struct_3847_; 
v_struct_3847_ = lean_ctor_get(v_x_3846_, 2);
lean_inc_ref(v_struct_3847_);
return v_struct_3847_;
}
else
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3848_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3849_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3848_);
return v___x_3849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lean_Expr_projExpr_x21(v_x_3850_);
lean_dec_ref(v_x_3850_);
return v_res_3851_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3853_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3854_ = lean_unsigned_to_nat(18u);
v___x_3855_ = lean_unsigned_to_nat(1089u);
v___x_3856_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3857_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3858_ = l_mkPanicMessageWithDecl(v___x_3857_, v___x_3856_, v___x_3855_, v___x_3854_, v___x_3853_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3859_){
_start:
{
if (lean_obj_tag(v_x_3859_) == 11)
{
lean_object* v_idx_3860_; 
v_idx_3860_ = lean_ctor_get(v_x_3859_, 1);
lean_inc(v_idx_3860_);
return v_idx_3860_;
}
else
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3862_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3861_);
return v___x_3862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Lean_Expr_projIdx_x21(v_x_3863_);
lean_dec_ref(v_x_3863_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3865_){
_start:
{
if (lean_obj_tag(v_x_3865_) == 7)
{
lean_object* v_body_3866_; 
v_body_3866_ = lean_ctor_get(v_x_3865_, 2);
v_x_3865_ = v_body_3866_;
goto _start;
}
else
{
lean_inc_ref(v_x_3865_);
return v_x_3865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_Lean_Expr_getForallBody(v_x_3868_);
lean_dec_ref(v_x_3868_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3870_, lean_object* v_x_3871_){
_start:
{
lean_object* v_zero_3872_; uint8_t v_isZero_3873_; 
v_zero_3872_ = lean_unsigned_to_nat(0u);
v_isZero_3873_ = lean_nat_dec_eq(v_x_3870_, v_zero_3872_);
if (v_isZero_3873_ == 1)
{
lean_dec(v_x_3870_);
lean_inc_ref(v_x_3871_);
return v_x_3871_;
}
else
{
if (lean_obj_tag(v_x_3871_) == 7)
{
lean_object* v_body_3874_; lean_object* v_one_3875_; lean_object* v_n_3876_; 
v_body_3874_ = lean_ctor_get(v_x_3871_, 2);
v_one_3875_ = lean_unsigned_to_nat(1u);
v_n_3876_ = lean_nat_sub(v_x_3870_, v_one_3875_);
lean_dec(v_x_3870_);
v_x_3870_ = v_n_3876_;
v_x_3871_ = v_body_3874_;
goto _start;
}
else
{
lean_dec(v_x_3870_);
lean_inc_ref(v_x_3871_);
return v_x_3871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3878_, lean_object* v_x_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3878_, v_x_3879_);
lean_dec_ref(v_x_3879_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3881_){
_start:
{
if (lean_obj_tag(v_x_3881_) == 7)
{
lean_object* v_binderName_3882_; lean_object* v_body_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v_binderName_3882_ = lean_ctor_get(v_x_3881_, 0);
v_body_3883_ = lean_ctor_get(v_x_3881_, 2);
v___x_3884_ = l_Lean_Expr_getForallBinderNames(v_body_3883_);
lean_inc(v_binderName_3882_);
v___x_3885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3885_, 0, v_binderName_3882_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
return v___x_3885_;
}
else
{
lean_object* v___x_3886_; 
v___x_3886_ = lean_box(0);
return v___x_3886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Lean_Expr_getForallBinderNames(v_x_3887_);
lean_dec_ref(v_x_3887_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3889_){
_start:
{
switch(lean_obj_tag(v_x_3889_))
{
case 10:
{
lean_object* v_expr_3890_; 
v_expr_3890_ = lean_ctor_get(v_x_3889_, 1);
v_x_3889_ = v_expr_3890_;
goto _start;
}
case 7:
{
lean_object* v_body_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_body_3892_ = lean_ctor_get(v_x_3889_, 2);
v___x_3893_ = l_Lean_Expr_getNumHeadForalls(v_body_3892_);
v___x_3894_ = lean_unsigned_to_nat(1u);
v___x_3895_ = lean_nat_add(v___x_3893_, v___x_3894_);
lean_dec(v___x_3893_);
return v___x_3895_;
}
default: 
{
lean_object* v___x_3896_; 
v___x_3896_ = lean_unsigned_to_nat(0u);
return v___x_3896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_Expr_getNumHeadForalls(v_x_3897_);
lean_dec_ref(v_x_3897_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3899_){
_start:
{
if (lean_obj_tag(v_x_3899_) == 5)
{
lean_object* v_fn_3900_; 
v_fn_3900_ = lean_ctor_get(v_x_3899_, 0);
v_x_3899_ = v_fn_3900_;
goto _start;
}
else
{
lean_inc_ref(v_x_3899_);
return v_x_3899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Lean_Expr_getAppFn(v_x_3902_);
lean_dec_ref(v_x_3902_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3904_){
_start:
{
switch(lean_obj_tag(v_x_3904_))
{
case 5:
{
lean_object* v_fn_3905_; 
v_fn_3905_ = lean_ctor_get(v_x_3904_, 0);
v_x_3904_ = v_fn_3905_;
goto _start;
}
case 10:
{
lean_object* v_expr_3907_; 
v_expr_3907_ = lean_ctor_get(v_x_3904_, 1);
v_x_3904_ = v_expr_3907_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3904_);
return v_x_3904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Lean_Expr_getAppFn_x27(v_x_3909_);
lean_dec_ref(v_x_3909_);
return v_res_3910_;
}
}
uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3911_, lean_object* v_n_3912_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_Expr_getAppFn(v_e_3911_);
if (lean_obj_tag(v___x_3913_) == 4)
{
lean_object* v_declName_3914_; uint8_t v___x_3915_; 
v_declName_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_declName_3914_);
lean_dec_ref_known(v___x_3913_, 2);
v___x_3915_ = lean_name_eq(v_declName_3914_, v_n_3912_);
lean_dec(v_declName_3914_);
return v___x_3915_;
}
else
{
uint8_t v___x_3916_; 
lean_dec_ref(v___x_3913_);
v___x_3916_ = 0;
return v___x_3916_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isAppOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3911_ = stack[0].m_obj;
lean_object* v_n_3912_ = stack[1].m_obj;
uint8_t v_res_3917_;
v_res_3917_ = l_Lean_Expr_isAppOf(v_e_3911_, v_n_3912_);
stack->m_num = v_res_3917_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3918_, lean_object* v_n_3919_){
_start:
{
uint8_t v_res_3920_; lean_object* v_r_3921_; 
v_res_3920_ = l_Lean_Expr_isAppOf(v_e_3918_, v_n_3919_);
lean_dec(v_n_3919_);
lean_dec_ref(v_e_3918_);
v_r_3921_ = lean_box(v_res_3920_);
return v_r_3921_;
}
}
uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3922_, lean_object* v_x_3923_, lean_object* v_x_3924_){
_start:
{
switch(lean_obj_tag(v_x_3922_))
{
case 4:
{
lean_object* v_declName_3925_; lean_object* v___x_3926_; uint8_t v___x_3927_; 
v_declName_3925_ = lean_ctor_get(v_x_3922_, 0);
v___x_3926_ = lean_unsigned_to_nat(0u);
v___x_3927_ = lean_nat_dec_eq(v_x_3924_, v___x_3926_);
lean_dec(v_x_3924_);
if (v___x_3927_ == 0)
{
return v___x_3927_;
}
else
{
uint8_t v___x_3928_; 
v___x_3928_ = lean_name_eq(v_declName_3925_, v_x_3923_);
return v___x_3928_;
}
}
case 5:
{
lean_object* v_fn_3929_; lean_object* v_zero_3930_; uint8_t v_isZero_3931_; 
v_fn_3929_ = lean_ctor_get(v_x_3922_, 0);
v_zero_3930_ = lean_unsigned_to_nat(0u);
v_isZero_3931_ = lean_nat_dec_eq(v_x_3924_, v_zero_3930_);
if (v_isZero_3931_ == 0)
{
lean_object* v_one_3932_; lean_object* v_n_3933_; 
v_one_3932_ = lean_unsigned_to_nat(1u);
v_n_3933_ = lean_nat_sub(v_x_3924_, v_one_3932_);
lean_dec(v_x_3924_);
v_x_3922_ = v_fn_3929_;
v_x_3924_ = v_n_3933_;
goto _start;
}
else
{
uint8_t v___x_3935_; 
lean_dec(v_x_3924_);
v___x_3935_ = 0;
return v___x_3935_;
}
}
default: 
{
uint8_t v___x_3936_; 
lean_dec(v_x_3924_);
v___x_3936_ = 0;
return v___x_3936_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_isAppOfArity_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3922_ = stack[0].m_obj;
lean_object* v_x_3923_ = stack[1].m_obj;
lean_object* v_x_3924_ = stack[2].m_obj;
uint8_t v_res_3937_;
v_res_3937_ = l_Lean_Expr_isAppOfArity(v_x_3922_, v_x_3923_, v_x_3924_);
stack->m_num = v_res_3937_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3938_, lean_object* v_x_3939_, lean_object* v_x_3940_){
_start:
{
uint8_t v_res_3941_; lean_object* v_r_3942_; 
v_res_3941_ = l_Lean_Expr_isAppOfArity(v_x_3938_, v_x_3939_, v_x_3940_);
lean_dec(v_x_3939_);
lean_dec_ref(v_x_3938_);
v_r_3942_ = lean_box(v_res_3941_);
return v_r_3942_;
}
}
uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3943_, lean_object* v_x_3944_, lean_object* v_x_3945_){
_start:
{
switch(lean_obj_tag(v_x_3943_))
{
case 10:
{
lean_object* v_expr_3946_; 
v_expr_3946_ = lean_ctor_get(v_x_3943_, 1);
v_x_3943_ = v_expr_3946_;
goto _start;
}
case 4:
{
lean_object* v_declName_3948_; lean_object* v___x_3949_; uint8_t v___x_3950_; 
v_declName_3948_ = lean_ctor_get(v_x_3943_, 0);
v___x_3949_ = lean_unsigned_to_nat(0u);
v___x_3950_ = lean_nat_dec_eq(v_x_3945_, v___x_3949_);
lean_dec(v_x_3945_);
if (v___x_3950_ == 0)
{
return v___x_3950_;
}
else
{
uint8_t v___x_3951_; 
v___x_3951_ = lean_name_eq(v_declName_3948_, v_x_3944_);
return v___x_3951_;
}
}
case 5:
{
lean_object* v_fn_3952_; lean_object* v_zero_3953_; uint8_t v_isZero_3954_; 
v_fn_3952_ = lean_ctor_get(v_x_3943_, 0);
v_zero_3953_ = lean_unsigned_to_nat(0u);
v_isZero_3954_ = lean_nat_dec_eq(v_x_3945_, v_zero_3953_);
if (v_isZero_3954_ == 0)
{
lean_object* v_one_3955_; lean_object* v_n_3956_; 
v_one_3955_ = lean_unsigned_to_nat(1u);
v_n_3956_ = lean_nat_sub(v_x_3945_, v_one_3955_);
lean_dec(v_x_3945_);
v_x_3943_ = v_fn_3952_;
v_x_3945_ = v_n_3956_;
goto _start;
}
else
{
uint8_t v___x_3958_; 
lean_dec(v_x_3945_);
v___x_3958_ = 0;
return v___x_3958_;
}
}
default: 
{
uint8_t v___x_3959_; 
lean_dec(v_x_3945_);
v___x_3959_ = 0;
return v___x_3959_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_isAppOfArity_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3943_ = stack[0].m_obj;
lean_object* v_x_3944_ = stack[1].m_obj;
lean_object* v_x_3945_ = stack[2].m_obj;
uint8_t v_res_3960_;
v_res_3960_ = l_Lean_Expr_isAppOfArity_x27(v_x_3943_, v_x_3944_, v_x_3945_);
stack->m_num = v_res_3960_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3961_, lean_object* v_x_3962_, lean_object* v_x_3963_){
_start:
{
uint8_t v_res_3964_; lean_object* v_r_3965_; 
v_res_3964_ = l_Lean_Expr_isAppOfArity_x27(v_x_3961_, v_x_3962_, v_x_3963_);
lean_dec(v_x_3962_);
lean_dec_ref(v_x_3961_);
v_r_3965_ = lean_box(v_res_3964_);
return v_r_3965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3966_, lean_object* v_x_3967_){
_start:
{
if (lean_obj_tag(v_x_3966_) == 5)
{
lean_object* v_fn_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v_fn_3968_ = lean_ctor_get(v_x_3966_, 0);
v___x_3969_ = lean_unsigned_to_nat(1u);
v___x_3970_ = lean_nat_add(v_x_3967_, v___x_3969_);
lean_dec(v_x_3967_);
v_x_3966_ = v_fn_3968_;
v_x_3967_ = v___x_3970_;
goto _start;
}
else
{
return v_x_3967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3972_, lean_object* v_x_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3972_, v_x_3973_);
lean_dec_ref(v_x_3972_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3975_){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = lean_unsigned_to_nat(0u);
v___x_3977_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3975_, v___x_3976_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l_Lean_Expr_getAppNumArgs(v_e_3978_);
lean_dec_ref(v_e_3978_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
switch(lean_obj_tag(v_a_3980_))
{
case 10:
{
lean_object* v_expr_3982_; 
v_expr_3982_ = lean_ctor_get(v_a_3980_, 1);
v_a_3980_ = v_expr_3982_;
goto _start;
}
case 5:
{
lean_object* v_fn_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_fn_3984_ = lean_ctor_get(v_a_3980_, 0);
v___x_3985_ = lean_unsigned_to_nat(1u);
v___x_3986_ = lean_nat_add(v_a_3981_, v___x_3985_);
lean_dec(v_a_3981_);
v_a_3980_ = v_fn_3984_;
v_a_3981_ = v___x_3986_;
goto _start;
}
default: 
{
return v_a_3981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3988_, v_a_3989_);
lean_dec_ref(v_a_3988_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3991_){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3992_ = lean_unsigned_to_nat(0u);
v___x_3993_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3991_, v___x_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3994_);
lean_dec_ref(v_e_3994_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3996_, lean_object* v_x_3997_){
_start:
{
lean_object* v_zero_3998_; uint8_t v_isZero_3999_; 
v_zero_3998_ = lean_unsigned_to_nat(0u);
v_isZero_3999_ = lean_nat_dec_eq(v_x_3996_, v_zero_3998_);
if (v_isZero_3999_ == 0)
{
if (lean_obj_tag(v_x_3997_) == 5)
{
lean_object* v_fn_4000_; lean_object* v_one_4001_; lean_object* v_n_4002_; 
v_fn_4000_ = lean_ctor_get(v_x_3997_, 0);
v_one_4001_ = lean_unsigned_to_nat(1u);
v_n_4002_ = lean_nat_sub(v_x_3996_, v_one_4001_);
lean_dec(v_x_3996_);
v_x_3996_ = v_n_4002_;
v_x_3997_ = v_fn_4000_;
goto _start;
}
else
{
lean_dec(v_x_3996_);
lean_inc_ref(v_x_3997_);
return v_x_3997_;
}
}
else
{
lean_dec(v_x_3996_);
lean_inc_ref(v_x_3997_);
return v_x_3997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_4004_, lean_object* v_x_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Lean_Expr_getBoundedAppFn(v_x_4004_, v_x_4005_);
lean_dec_ref(v_x_4005_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_4007_, lean_object* v_x_4008_, lean_object* v_x_4009_){
_start:
{
if (lean_obj_tag(v_x_4007_) == 5)
{
lean_object* v_fn_4010_; lean_object* v_arg_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v_fn_4010_ = lean_ctor_get(v_x_4007_, 0);
lean_inc_ref(v_fn_4010_);
v_arg_4011_ = lean_ctor_get(v_x_4007_, 1);
lean_inc_ref(v_arg_4011_);
lean_dec_ref_known(v_x_4007_, 2);
v___x_4012_ = lean_array_set(v_x_4008_, v_x_4009_, v_arg_4011_);
v___x_4013_ = lean_unsigned_to_nat(1u);
v___x_4014_ = lean_nat_sub(v_x_4009_, v___x_4013_);
lean_dec(v_x_4009_);
v_x_4007_ = v_fn_4010_;
v_x_4008_ = v___x_4012_;
v_x_4009_ = v___x_4014_;
goto _start;
}
else
{
lean_dec(v_x_4009_);
lean_dec_ref(v_x_4007_);
return v_x_4008_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_4016_; lean_object* v_dummy_4017_; 
v___x_4016_ = lean_box(0);
v_dummy_4017_ = l_Lean_Expr_sort___override(v___x_4016_);
return v_dummy_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_4018_){
_start:
{
lean_object* v_dummy_4019_; lean_object* v_nargs_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v_dummy_4019_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4020_ = l_Lean_Expr_getAppNumArgs(v_e_4018_);
lean_inc(v_nargs_4020_);
v___x_4021_ = lean_mk_array(v_nargs_4020_, v_dummy_4019_);
v___x_4022_ = lean_unsigned_to_nat(1u);
v___x_4023_ = lean_nat_sub(v_nargs_4020_, v___x_4022_);
lean_dec(v_nargs_4020_);
v___x_4024_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4018_, v___x_4021_, v___x_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_4025_, lean_object* v_x_4026_, lean_object* v_x_4027_){
_start:
{
if (lean_obj_tag(v_x_4025_) == 5)
{
lean_object* v_fn_4028_; lean_object* v_arg_4029_; lean_object* v_zero_4030_; uint8_t v_isZero_4031_; 
v_fn_4028_ = lean_ctor_get(v_x_4025_, 0);
lean_inc_ref(v_fn_4028_);
v_arg_4029_ = lean_ctor_get(v_x_4025_, 1);
lean_inc_ref(v_arg_4029_);
lean_dec_ref_known(v_x_4025_, 2);
v_zero_4030_ = lean_unsigned_to_nat(0u);
v_isZero_4031_ = lean_nat_dec_eq(v_x_4027_, v_zero_4030_);
if (v_isZero_4031_ == 0)
{
lean_object* v_one_4032_; lean_object* v_n_4033_; lean_object* v___x_4034_; 
v_one_4032_ = lean_unsigned_to_nat(1u);
v_n_4033_ = lean_nat_sub(v_x_4027_, v_one_4032_);
lean_dec(v_x_4027_);
v___x_4034_ = lean_array_set(v_x_4026_, v_n_4033_, v_arg_4029_);
v_x_4025_ = v_fn_4028_;
v_x_4026_ = v___x_4034_;
v_x_4027_ = v_n_4033_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4029_);
lean_dec_ref(v_fn_4028_);
lean_dec(v_x_4027_);
return v_x_4026_;
}
}
else
{
lean_dec(v_x_4027_);
lean_dec_ref(v_x_4025_);
return v_x_4026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_4036_, lean_object* v_e_4037_){
_start:
{
lean_object* v_dummy_4038_; lean_object* v___y_4040_; lean_object* v___x_4043_; uint8_t v___x_4044_; 
v_dummy_4038_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_4043_ = l_Lean_Expr_getAppNumArgs(v_e_4037_);
v___x_4044_ = lean_nat_dec_le(v_maxArgs_4036_, v___x_4043_);
if (v___x_4044_ == 0)
{
lean_dec(v_maxArgs_4036_);
v___y_4040_ = v___x_4043_;
goto v___jp_4039_;
}
else
{
lean_dec(v___x_4043_);
v___y_4040_ = v_maxArgs_4036_;
goto v___jp_4039_;
}
v___jp_4039_:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
lean_inc(v___y_4040_);
v___x_4041_ = lean_mk_array(v___y_4040_, v_dummy_4038_);
v___x_4042_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_4037_, v___x_4041_, v___y_4040_);
return v___x_4042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_4045_, lean_object* v_x_4046_){
_start:
{
if (lean_obj_tag(v_x_4045_) == 5)
{
lean_object* v_fn_4047_; lean_object* v_arg_4048_; lean_object* v___x_4049_; 
v_fn_4047_ = lean_ctor_get(v_x_4045_, 0);
lean_inc_ref(v_fn_4047_);
v_arg_4048_ = lean_ctor_get(v_x_4045_, 1);
lean_inc_ref(v_arg_4048_);
lean_dec_ref_known(v_x_4045_, 2);
v___x_4049_ = lean_array_push(v_x_4046_, v_arg_4048_);
v_x_4045_ = v_fn_4047_;
v_x_4046_ = v___x_4049_;
goto _start;
}
else
{
lean_dec_ref(v_x_4045_);
return v_x_4046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_4051_){
_start:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4052_ = l_Lean_Expr_getAppNumArgs(v_e_4051_);
v___x_4053_ = lean_mk_empty_array_with_capacity(v___x_4052_);
lean_dec(v___x_4052_);
v___x_4054_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4051_, v___x_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_4055_, lean_object* v_x_4056_, lean_object* v_x_4057_, lean_object* v_x_4058_){
_start:
{
if (lean_obj_tag(v_x_4056_) == 5)
{
lean_object* v_fn_4059_; lean_object* v_arg_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v_fn_4059_ = lean_ctor_get(v_x_4056_, 0);
lean_inc_ref(v_fn_4059_);
v_arg_4060_ = lean_ctor_get(v_x_4056_, 1);
lean_inc_ref(v_arg_4060_);
lean_dec_ref_known(v_x_4056_, 2);
v___x_4061_ = lean_array_set(v_x_4057_, v_x_4058_, v_arg_4060_);
v___x_4062_ = lean_unsigned_to_nat(1u);
v___x_4063_ = lean_nat_sub(v_x_4058_, v___x_4062_);
lean_dec(v_x_4058_);
v_x_4056_ = v_fn_4059_;
v_x_4057_ = v___x_4061_;
v_x_4058_ = v___x_4063_;
goto _start;
}
else
{
lean_object* v___x_4065_; 
lean_dec(v_x_4058_);
v___x_4065_ = lean_apply_2(v_k_4055_, v_x_4056_, v_x_4057_);
return v___x_4065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_4066_, lean_object* v_k_4067_, lean_object* v_x_4068_, lean_object* v_x_4069_, lean_object* v_x_4070_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Lean_Expr_withAppAux___redArg(v_k_4067_, v_x_4068_, v_x_4069_, v_x_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_4072_, lean_object* v_k_4073_){
_start:
{
lean_object* v_dummy_4074_; lean_object* v_nargs_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v_dummy_4074_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4075_ = l_Lean_Expr_getAppNumArgs(v_e_4072_);
lean_inc(v_nargs_4075_);
v___x_4076_ = lean_mk_array(v_nargs_4075_, v_dummy_4074_);
v___x_4077_ = lean_unsigned_to_nat(1u);
v___x_4078_ = lean_nat_sub(v_nargs_4075_, v___x_4077_);
lean_dec(v_nargs_4075_);
v___x_4079_ = l_Lean_Expr_withAppAux___redArg(v_k_4073_, v_e_4072_, v___x_4076_, v___x_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_4080_, lean_object* v_e_4081_, lean_object* v_k_4082_){
_start:
{
lean_object* v_dummy_4083_; lean_object* v_nargs_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v_dummy_4083_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4084_ = l_Lean_Expr_getAppNumArgs(v_e_4081_);
lean_inc(v_nargs_4084_);
v___x_4085_ = lean_mk_array(v_nargs_4084_, v_dummy_4083_);
v___x_4086_ = lean_unsigned_to_nat(1u);
v___x_4087_ = lean_nat_sub(v_nargs_4084_, v___x_4086_);
lean_dec(v_nargs_4084_);
v___x_4088_ = l_Lean_Expr_withAppAux___redArg(v_k_4082_, v_e_4081_, v___x_4085_, v___x_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_4089_, lean_object* v_x_4090_, lean_object* v_x_4091_){
_start:
{
if (lean_obj_tag(v_x_4089_) == 5)
{
lean_object* v_fn_4092_; lean_object* v_arg_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v_fn_4092_ = lean_ctor_get(v_x_4089_, 0);
lean_inc_ref(v_fn_4092_);
v_arg_4093_ = lean_ctor_get(v_x_4089_, 1);
lean_inc_ref(v_arg_4093_);
lean_dec_ref_known(v_x_4089_, 2);
v___x_4094_ = lean_array_set(v_x_4090_, v_x_4091_, v_arg_4093_);
v___x_4095_ = lean_unsigned_to_nat(1u);
v___x_4096_ = lean_nat_sub(v_x_4091_, v___x_4095_);
lean_dec(v_x_4091_);
v_x_4089_ = v_fn_4092_;
v_x_4090_ = v___x_4094_;
v_x_4091_ = v___x_4096_;
goto _start;
}
else
{
lean_object* v___x_4098_; lean_object* v___x_4099_; 
lean_dec(v_x_4091_);
v___x_4098_ = l_Lean_Expr_constName(v_x_4089_);
lean_dec_ref(v_x_4089_);
v___x_4099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4098_);
lean_ctor_set(v___x_4099_, 1, v_x_4090_);
return v___x_4099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_4100_){
_start:
{
lean_object* v_dummy_4101_; lean_object* v_nargs_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v_dummy_4101_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4102_ = l_Lean_Expr_getAppNumArgs(v_e_4100_);
lean_inc(v_nargs_4102_);
v___x_4103_ = lean_mk_array(v_nargs_4102_, v_dummy_4101_);
v___x_4104_ = lean_unsigned_to_nat(1u);
v___x_4105_ = lean_nat_sub(v_nargs_4102_, v___x_4104_);
lean_dec(v_nargs_4102_);
v___x_4106_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_4100_, v___x_4103_, v___x_4105_);
return v___x_4106_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = l_Array_instInhabited___redArg();
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_4108_){
_start:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4109_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_4110_ = lean_panic_fn_borrowed(v___x_4109_, v_msg_4108_);
return v___x_4110_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4113_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_4114_ = lean_unsigned_to_nat(27u);
v___x_4115_ = lean_unsigned_to_nat(1246u);
v___x_4116_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_4117_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4118_ = l_mkPanicMessageWithDecl(v___x_4117_, v___x_4116_, v___x_4115_, v___x_4114_, v___x_4113_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v_zero_4122_; uint8_t v_isZero_4123_; 
v_zero_4122_ = lean_unsigned_to_nat(0u);
v_isZero_4123_ = lean_nat_dec_eq(v_a_4119_, v_zero_4122_);
if (v_isZero_4123_ == 1)
{
lean_dec_ref(v_a_4120_);
lean_dec(v_a_4119_);
return v_a_4121_;
}
else
{
if (lean_obj_tag(v_a_4120_) == 5)
{
lean_object* v_fn_4124_; lean_object* v_arg_4125_; lean_object* v_one_4126_; lean_object* v_n_4127_; lean_object* v___x_4128_; 
v_fn_4124_ = lean_ctor_get(v_a_4120_, 0);
lean_inc_ref(v_fn_4124_);
v_arg_4125_ = lean_ctor_get(v_a_4120_, 1);
lean_inc_ref(v_arg_4125_);
lean_dec_ref_known(v_a_4120_, 2);
v_one_4126_ = lean_unsigned_to_nat(1u);
v_n_4127_ = lean_nat_sub(v_a_4119_, v_one_4126_);
lean_dec(v_a_4119_);
v___x_4128_ = lean_array_set(v_a_4121_, v_n_4127_, v_arg_4125_);
v_a_4119_ = v_n_4127_;
v_a_4120_ = v_fn_4124_;
v_a_4121_ = v___x_4128_;
goto _start;
}
else
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
lean_dec_ref(v_a_4121_);
lean_dec_ref(v_a_4120_);
lean_dec(v_a_4119_);
v___x_4130_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_4131_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_4130_);
return v___x_4131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_4132_, lean_object* v_n_4133_){
_start:
{
lean_object* v_dummy_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
v_dummy_4134_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_4133_);
v___x_4135_ = lean_mk_array(v_n_4133_, v_dummy_4134_);
v___x_4136_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_4133_, v_e_4132_, v___x_4135_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_4137_, lean_object* v_n_4138_){
_start:
{
lean_object* v_zero_4139_; uint8_t v_isZero_4140_; 
v_zero_4139_ = lean_unsigned_to_nat(0u);
v_isZero_4140_ = lean_nat_dec_eq(v_n_4138_, v_zero_4139_);
if (v_isZero_4140_ == 1)
{
lean_dec(v_n_4138_);
lean_inc_ref(v_e_4137_);
return v_e_4137_;
}
else
{
if (lean_obj_tag(v_e_4137_) == 5)
{
lean_object* v_fn_4141_; lean_object* v_one_4142_; lean_object* v_n_4143_; 
v_fn_4141_ = lean_ctor_get(v_e_4137_, 0);
v_one_4142_ = lean_unsigned_to_nat(1u);
v_n_4143_ = lean_nat_sub(v_n_4138_, v_one_4142_);
lean_dec(v_n_4138_);
v_e_4137_ = v_fn_4141_;
v_n_4138_ = v_n_4143_;
goto _start;
}
else
{
lean_dec(v_n_4138_);
lean_inc_ref(v_e_4137_);
return v_e_4137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_4145_, lean_object* v_n_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l_Lean_Expr_stripArgsN(v_e_4145_, v_n_4146_);
lean_dec_ref(v_e_4145_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_4148_, lean_object* v_n_4149_){
_start:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4150_ = l_Lean_Expr_getAppNumArgs(v_e_4148_);
v___x_4151_ = lean_nat_sub(v___x_4150_, v_n_4149_);
lean_dec(v___x_4150_);
v___x_4152_ = l_Lean_Expr_stripArgsN(v_e_4148_, v___x_4151_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_4153_, lean_object* v_n_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l_Lean_Expr_getAppPrefix(v_e_4153_, v_n_4154_);
lean_dec(v_n_4154_);
lean_dec_ref(v_e_4153_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_4156_, lean_object* v_inst_4157_, lean_object* v_f_4158_, lean_object* v_x_4159_){
_start:
{
size_t v_sz_4160_; size_t v___x_4161_; lean_object* v___x_4162_; 
v_sz_4160_ = lean_array_size(v_args_4156_);
v___x_4161_ = ((size_t)0ULL);
v___x_4162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4157_, v_f_4158_, v_sz_4160_, v___x_4161_, v_args_4156_);
return v___x_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_4164_, lean_object* v_inst_4165_, lean_object* v_f_4166_, lean_object* v_toSeq_4167_, lean_object* v_fn_4168_, lean_object* v_args_4169_){
_start:
{
lean_object* v_map_4170_; lean_object* v___f_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v_map_4170_ = lean_ctor_get(v_toFunctor_4164_, 0);
lean_inc(v_map_4170_);
lean_dec_ref(v_toFunctor_4164_);
lean_inc(v_f_4166_);
v___f_4171_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4171_, 0, v_args_4169_);
lean_closure_set(v___f_4171_, 1, v_inst_4165_);
lean_closure_set(v___f_4171_, 2, v_f_4166_);
v___x_4172_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_4173_ = lean_apply_1(v_f_4166_, v_fn_4168_);
v___x_4174_ = lean_apply_4(v_map_4170_, lean_box(0), lean_box(0), v___x_4172_, v___x_4173_);
v___x_4175_ = lean_apply_4(v_toSeq_4167_, lean_box(0), lean_box(0), v___x_4174_, v___f_4171_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_4176_, lean_object* v_f_4177_, lean_object* v_e_4178_){
_start:
{
lean_object* v_toApplicative_4179_; lean_object* v_toFunctor_4180_; lean_object* v_toSeq_4181_; lean_object* v___f_4182_; lean_object* v_dummy_4183_; lean_object* v_nargs_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v_toApplicative_4179_ = lean_ctor_get(v_inst_4176_, 0);
v_toFunctor_4180_ = lean_ctor_get(v_toApplicative_4179_, 0);
lean_inc_ref(v_toFunctor_4180_);
v_toSeq_4181_ = lean_ctor_get(v_toApplicative_4179_, 2);
lean_inc(v_toSeq_4181_);
v___f_4182_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_4182_, 0, v_toFunctor_4180_);
lean_closure_set(v___f_4182_, 1, v_inst_4176_);
lean_closure_set(v___f_4182_, 2, v_f_4177_);
lean_closure_set(v___f_4182_, 3, v_toSeq_4181_);
v_dummy_4183_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4184_ = l_Lean_Expr_getAppNumArgs(v_e_4178_);
lean_inc(v_nargs_4184_);
v___x_4185_ = lean_mk_array(v_nargs_4184_, v_dummy_4183_);
v___x_4186_ = lean_unsigned_to_nat(1u);
v___x_4187_ = lean_nat_sub(v_nargs_4184_, v___x_4186_);
lean_dec(v_nargs_4184_);
v___x_4188_ = l_Lean_Expr_withAppAux___redArg(v___f_4182_, v_e_4178_, v___x_4185_, v___x_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_4189_, lean_object* v_inst_4190_, lean_object* v_f_4191_, lean_object* v_e_4192_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = l_Lean_Expr_traverseApp___redArg(v_inst_4190_, v_f_4191_, v_e_4192_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_4194_, lean_object* v_x_4195_, lean_object* v_x_4196_){
_start:
{
if (lean_obj_tag(v_x_4195_) == 5)
{
lean_object* v_fn_4197_; lean_object* v_arg_4198_; lean_object* v___x_4199_; 
v_fn_4197_ = lean_ctor_get(v_x_4195_, 0);
lean_inc_ref(v_fn_4197_);
v_arg_4198_ = lean_ctor_get(v_x_4195_, 1);
lean_inc_ref(v_arg_4198_);
lean_dec_ref_known(v_x_4195_, 2);
v___x_4199_ = lean_array_push(v_x_4196_, v_arg_4198_);
v_x_4195_ = v_fn_4197_;
v_x_4196_ = v___x_4199_;
goto _start;
}
else
{
lean_object* v___x_4201_; 
v___x_4201_ = lean_apply_2(v_k_4194_, v_x_4195_, v_x_4196_);
return v___x_4201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_4202_, lean_object* v_k_4203_, lean_object* v_x_4204_, lean_object* v_x_4205_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4203_, v_x_4204_, v_x_4205_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_4207_, lean_object* v_k_4208_){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = l_Lean_Expr_getAppNumArgs(v_e_4207_);
v___x_4210_ = lean_mk_empty_array_with_capacity(v___x_4209_);
lean_dec(v___x_4209_);
v___x_4211_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4208_, v_e_4207_, v___x_4210_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_4212_, lean_object* v_e_4213_, lean_object* v_k_4214_){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4215_ = l_Lean_Expr_getAppNumArgs(v_e_4213_);
v___x_4216_ = lean_mk_empty_array_with_capacity(v___x_4215_);
lean_dec(v___x_4215_);
v___x_4217_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4214_, v_e_4213_, v___x_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_4218_, lean_object* v_x_4219_, lean_object* v_x_4220_){
_start:
{
if (lean_obj_tag(v_x_4218_) == 5)
{
lean_object* v_fn_4221_; lean_object* v_arg_4222_; lean_object* v_zero_4223_; uint8_t v_isZero_4224_; 
v_fn_4221_ = lean_ctor_get(v_x_4218_, 0);
v_arg_4222_ = lean_ctor_get(v_x_4218_, 1);
v_zero_4223_ = lean_unsigned_to_nat(0u);
v_isZero_4224_ = lean_nat_dec_eq(v_x_4219_, v_zero_4223_);
if (v_isZero_4224_ == 1)
{
lean_dec(v_x_4219_);
lean_inc_ref(v_arg_4222_);
return v_arg_4222_;
}
else
{
lean_object* v_one_4225_; lean_object* v_n_4226_; 
v_one_4225_ = lean_unsigned_to_nat(1u);
v_n_4226_ = lean_nat_sub(v_x_4219_, v_one_4225_);
lean_dec(v_x_4219_);
v_x_4218_ = v_fn_4221_;
v_x_4219_ = v_n_4226_;
goto _start;
}
}
else
{
lean_dec(v_x_4219_);
lean_inc_ref(v_x_4220_);
return v_x_4220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_4228_, lean_object* v_x_4229_, lean_object* v_x_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l_Lean_Expr_getRevArgD(v_x_4228_, v_x_4229_, v_x_4230_);
lean_dec_ref(v_x_4230_);
lean_dec_ref(v_x_4228_);
return v_res_4231_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
v___x_4234_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4235_ = lean_unsigned_to_nat(20u);
v___x_4236_ = lean_unsigned_to_nat(1287u);
v___x_4237_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4238_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4239_ = l_mkPanicMessageWithDecl(v___x_4238_, v___x_4237_, v___x_4236_, v___x_4235_, v___x_4234_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4240_, lean_object* v_x_4241_){
_start:
{
if (lean_obj_tag(v_x_4240_) == 5)
{
lean_object* v_fn_4242_; lean_object* v_arg_4243_; lean_object* v_zero_4244_; uint8_t v_isZero_4245_; 
v_fn_4242_ = lean_ctor_get(v_x_4240_, 0);
v_arg_4243_ = lean_ctor_get(v_x_4240_, 1);
v_zero_4244_ = lean_unsigned_to_nat(0u);
v_isZero_4245_ = lean_nat_dec_eq(v_x_4241_, v_zero_4244_);
if (v_isZero_4245_ == 1)
{
lean_dec(v_x_4241_);
lean_inc_ref(v_arg_4243_);
return v_arg_4243_;
}
else
{
lean_object* v_one_4246_; lean_object* v_n_4247_; 
v_one_4246_ = lean_unsigned_to_nat(1u);
v_n_4247_ = lean_nat_sub(v_x_4241_, v_one_4246_);
lean_dec(v_x_4241_);
v_x_4240_ = v_fn_4242_;
v_x_4241_ = v_n_4247_;
goto _start;
}
}
else
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
lean_dec(v_x_4241_);
v___x_4249_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4250_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4249_);
return v___x_4250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4251_, lean_object* v_x_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = l_Lean_Expr_getRevArg_x21(v_x_4251_, v_x_4252_);
lean_dec_ref(v_x_4251_);
return v_res_4253_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v___x_4255_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4256_ = lean_unsigned_to_nat(20u);
v___x_4257_ = lean_unsigned_to_nat(1294u);
v___x_4258_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4259_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4260_ = l_mkPanicMessageWithDecl(v___x_4259_, v___x_4258_, v___x_4257_, v___x_4256_, v___x_4255_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4261_, lean_object* v_x_4262_){
_start:
{
switch(lean_obj_tag(v_x_4261_))
{
case 10:
{
lean_object* v_expr_4263_; 
v_expr_4263_ = lean_ctor_get(v_x_4261_, 1);
v_x_4261_ = v_expr_4263_;
goto _start;
}
case 5:
{
lean_object* v_fn_4265_; lean_object* v_arg_4266_; lean_object* v_zero_4267_; uint8_t v_isZero_4268_; 
v_fn_4265_ = lean_ctor_get(v_x_4261_, 0);
v_arg_4266_ = lean_ctor_get(v_x_4261_, 1);
v_zero_4267_ = lean_unsigned_to_nat(0u);
v_isZero_4268_ = lean_nat_dec_eq(v_x_4262_, v_zero_4267_);
if (v_isZero_4268_ == 1)
{
lean_dec(v_x_4262_);
lean_inc_ref(v_arg_4266_);
return v_arg_4266_;
}
else
{
lean_object* v_one_4269_; lean_object* v_n_4270_; 
v_one_4269_ = lean_unsigned_to_nat(1u);
v_n_4270_ = lean_nat_sub(v_x_4262_, v_one_4269_);
lean_dec(v_x_4262_);
v_x_4261_ = v_fn_4265_;
v_x_4262_ = v_n_4270_;
goto _start;
}
}
default: 
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
lean_dec(v_x_4262_);
v___x_4272_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4273_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4272_);
return v___x_4273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4274_, lean_object* v_x_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4274_, v_x_4275_);
lean_dec_ref(v_x_4274_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4277_, lean_object* v_i_4278_, lean_object* v_n_4279_){
_start:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4280_ = lean_nat_sub(v_n_4279_, v_i_4278_);
v___x_4281_ = lean_unsigned_to_nat(1u);
v___x_4282_ = lean_nat_sub(v___x_4280_, v___x_4281_);
lean_dec(v___x_4280_);
v___x_4283_ = l_Lean_Expr_getRevArg_x21(v_e_4277_, v___x_4282_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4284_, lean_object* v_i_4285_, lean_object* v_n_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l_Lean_Expr_getArg_x21(v_e_4284_, v_i_4285_, v_n_4286_);
lean_dec(v_n_4286_);
lean_dec(v_i_4285_);
lean_dec_ref(v_e_4284_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4288_, lean_object* v_i_4289_, lean_object* v_n_4290_){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4291_ = lean_nat_sub(v_n_4290_, v_i_4289_);
v___x_4292_ = lean_unsigned_to_nat(1u);
v___x_4293_ = lean_nat_sub(v___x_4291_, v___x_4292_);
lean_dec(v___x_4291_);
v___x_4294_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4288_, v___x_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4295_, lean_object* v_i_4296_, lean_object* v_n_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Lean_Expr_getArg_x21_x27(v_e_4295_, v_i_4296_, v_n_4297_);
lean_dec(v_n_4297_);
lean_dec(v_i_4296_);
lean_dec_ref(v_e_4295_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4299_, lean_object* v_i_4300_, lean_object* v_v_u2080_4301_, lean_object* v_n_4302_){
_start:
{
lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4303_ = lean_nat_sub(v_n_4302_, v_i_4300_);
v___x_4304_ = lean_unsigned_to_nat(1u);
v___x_4305_ = lean_nat_sub(v___x_4303_, v___x_4304_);
lean_dec(v___x_4303_);
v___x_4306_ = l_Lean_Expr_getRevArgD(v_e_4299_, v___x_4305_, v_v_u2080_4301_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4307_, lean_object* v_i_4308_, lean_object* v_v_u2080_4309_, lean_object* v_n_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Lean_Expr_getArgD(v_e_4307_, v_i_4308_, v_v_u2080_4309_, v_n_4310_);
lean_dec(v_n_4310_);
lean_dec_ref(v_v_u2080_4309_);
lean_dec(v_i_4308_);
lean_dec_ref(v_e_4307_);
return v_res_4311_;
}
}
uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4312_){
_start:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; uint8_t v___x_4315_; 
v___x_4313_ = lean_unsigned_to_nat(0u);
v___x_4314_ = l_Lean_Expr_looseBVarRange(v_e_4312_);
v___x_4315_ = lean_nat_dec_lt(v___x_4313_, v___x_4314_);
lean_dec(v___x_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT void l_Lean_Expr_hasLooseBVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4312_ = stack[0].m_obj;
uint8_t v_res_4316_;
v_res_4316_ = l_Lean_Expr_hasLooseBVars(v_e_4312_);
stack->m_num = v_res_4316_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4317_){
_start:
{
uint8_t v_res_4318_; lean_object* v_r_4319_; 
v_res_4318_ = l_Lean_Expr_hasLooseBVars(v_e_4317_);
lean_dec_ref(v_e_4317_);
v_r_4319_ = lean_box(v_res_4318_);
return v_r_4319_;
}
}
uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4320_){
_start:
{
if (lean_obj_tag(v_e_4320_) == 7)
{
lean_object* v_body_4321_; uint8_t v___x_4322_; 
v_body_4321_ = lean_ctor_get(v_e_4320_, 2);
v___x_4322_ = l_Lean_Expr_hasLooseBVars(v_body_4321_);
if (v___x_4322_ == 0)
{
uint8_t v___x_4323_; 
v___x_4323_ = 1;
return v___x_4323_;
}
else
{
uint8_t v___x_4324_; 
v___x_4324_ = 0;
return v___x_4324_;
}
}
else
{
uint8_t v___x_4325_; 
v___x_4325_ = 0;
return v___x_4325_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isArrow_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4320_ = stack[0].m_obj;
uint8_t v_res_4326_;
v_res_4326_ = l_Lean_Expr_isArrow(v_e_4320_);
stack->m_num = v_res_4326_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4327_){
_start:
{
uint8_t v_res_4328_; lean_object* v_r_4329_; 
v_res_4328_ = l_Lean_Expr_isArrow(v_e_4327_);
lean_dec_ref(v_e_4327_);
v_r_4329_ = lean_box(v_res_4328_);
return v_r_4329_;
}
}
LEAN_EXPORT void l_Lean_Expr_hasLooseBVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4330_ = stack[0].m_obj;
lean_object* v_bvarIdx_4331_ = stack[1].m_obj;
uint8_t v_res_4332_;
v_res_4332_ = lean_expr_has_loose_bvar(v_e_4330_, v_bvarIdx_4331_);
stack->m_num = v_res_4332_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4333_, lean_object* v_bvarIdx_4334_){
_start:
{
uint8_t v_res_4335_; lean_object* v_r_4336_; 
v_res_4335_ = lean_expr_has_loose_bvar(v_e_4333_, v_bvarIdx_4334_);
lean_dec(v_bvarIdx_4334_);
lean_dec_ref(v_e_4333_);
v_r_4336_ = lean_box(v_res_4335_);
return v_r_4336_;
}
}
uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4337_, lean_object* v_bvarIdx_4338_, uint8_t v_considerRange_4339_){
_start:
{
if (lean_obj_tag(v_e_4337_) == 7)
{
lean_object* v_binderType_4340_; lean_object* v_body_4341_; uint8_t v_binderInfo_4342_; uint8_t v___y_4344_; uint8_t v___x_4348_; 
v_binderType_4340_ = lean_ctor_get(v_e_4337_, 1);
v_body_4341_ = lean_ctor_get(v_e_4337_, 2);
v_binderInfo_4342_ = lean_ctor_get_uint8(v_e_4337_, sizeof(void*)*3 + 8);
v___x_4348_ = lean_expr_has_loose_bvar(v_binderType_4340_, v_bvarIdx_4338_);
if (v___x_4348_ == 0)
{
v___y_4344_ = v___x_4348_;
goto v___jp_4343_;
}
else
{
uint8_t v___x_4349_; 
v___x_4349_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4342_);
if (v___x_4349_ == 0)
{
lean_object* v___x_4350_; uint8_t v___x_4351_; 
v___x_4350_ = lean_unsigned_to_nat(0u);
v___x_4351_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4341_, v___x_4350_, v_considerRange_4339_);
v___y_4344_ = v___x_4351_;
goto v___jp_4343_;
}
else
{
v___y_4344_ = v___x_4349_;
goto v___jp_4343_;
}
}
v___jp_4343_:
{
if (v___y_4344_ == 0)
{
lean_object* v___x_4345_; lean_object* v___x_4346_; 
v___x_4345_ = lean_unsigned_to_nat(1u);
v___x_4346_ = lean_nat_add(v_bvarIdx_4338_, v___x_4345_);
lean_dec(v_bvarIdx_4338_);
v_e_4337_ = v_body_4341_;
v_bvarIdx_4338_ = v___x_4346_;
goto _start;
}
else
{
lean_dec(v_bvarIdx_4338_);
return v___y_4344_;
}
}
}
else
{
if (v_considerRange_4339_ == 0)
{
lean_dec(v_bvarIdx_4338_);
return v_considerRange_4339_;
}
else
{
uint8_t v___x_4352_; 
v___x_4352_ = lean_expr_has_loose_bvar(v_e_4337_, v_bvarIdx_4338_);
lean_dec(v_bvarIdx_4338_);
return v___x_4352_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_hasLooseBVarInExplicitDomain_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4337_ = stack[0].m_obj;
lean_object* v_bvarIdx_4338_ = stack[1].m_obj;
uint8_t v_considerRange_4339_ = stack[2].m_num;
uint8_t v_res_4353_;
v_res_4353_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4337_, v_bvarIdx_4338_, v_considerRange_4339_);
stack->m_num = v_res_4353_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4354_, lean_object* v_bvarIdx_4355_, lean_object* v_considerRange_4356_){
_start:
{
uint8_t v_considerRange_boxed_4357_; uint8_t v_res_4358_; lean_object* v_r_4359_; 
v_considerRange_boxed_4357_ = lean_unbox(v_considerRange_4356_);
v_res_4358_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4354_, v_bvarIdx_4355_, v_considerRange_boxed_4357_);
lean_dec_ref(v_e_4354_);
v_r_4359_ = lean_box(v_res_4358_);
return v_r_4359_;
}
}
LEAN_EXPORT void l_Lean_Expr_lowerLooseBVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4360_ = stack[0].m_obj;
lean_object* v_s_4361_ = stack[1].m_obj;
lean_object* v_d_4362_ = stack[2].m_obj;
lean_object* v_res_4363_;
v_res_4363_ = lean_expr_lower_loose_bvars(v_e_4360_, v_s_4361_, v_d_4362_);
stack->m_obj
 = v_res_4363_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4364_, lean_object* v_s_4365_, lean_object* v_d_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = lean_expr_lower_loose_bvars(v_e_4364_, v_s_4365_, v_d_4366_);
lean_dec(v_d_4366_);
lean_dec(v_s_4365_);
lean_dec_ref(v_e_4364_);
return v_res_4367_;
}
}
LEAN_EXPORT void l_Lean_Expr_liftLooseBVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4368_ = stack[0].m_obj;
lean_object* v_s_4369_ = stack[1].m_obj;
lean_object* v_d_4370_ = stack[2].m_obj;
lean_object* v_res_4371_;
v_res_4371_ = lean_expr_lift_loose_bvars(v_e_4368_, v_s_4369_, v_d_4370_);
stack->m_obj
 = v_res_4371_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4372_, lean_object* v_s_4373_, lean_object* v_d_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = lean_expr_lift_loose_bvars(v_e_4372_, v_s_4373_, v_d_4374_);
lean_dec(v_d_4374_);
lean_dec(v_s_4373_);
lean_dec_ref(v_e_4372_);
return v_res_4375_;
}
}
lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4376_, lean_object* v_numParams_4377_, uint8_t v_considerRange_4378_){
_start:
{
if (lean_obj_tag(v_e_4376_) == 7)
{
lean_object* v_binderName_4379_; lean_object* v_binderType_4380_; lean_object* v_body_4381_; uint8_t v_binderInfo_4382_; lean_object* v_zero_4383_; uint8_t v_isZero_4384_; 
v_binderName_4379_ = lean_ctor_get(v_e_4376_, 0);
v_binderType_4380_ = lean_ctor_get(v_e_4376_, 1);
v_body_4381_ = lean_ctor_get(v_e_4376_, 2);
v_binderInfo_4382_ = lean_ctor_get_uint8(v_e_4376_, sizeof(void*)*3 + 8);
v_zero_4383_ = lean_unsigned_to_nat(0u);
v_isZero_4384_ = lean_nat_dec_eq(v_numParams_4377_, v_zero_4383_);
if (v_isZero_4384_ == 0)
{
lean_object* v_one_4385_; lean_object* v_n_4386_; lean_object* v_b_4387_; uint8_t v___y_4389_; uint8_t v___x_4393_; 
lean_inc_ref(v_body_4381_);
lean_inc_ref(v_binderType_4380_);
lean_inc(v_binderName_4379_);
lean_dec_ref_known(v_e_4376_, 3);
v_one_4385_ = lean_unsigned_to_nat(1u);
v_n_4386_ = lean_nat_sub(v_numParams_4377_, v_one_4385_);
v_b_4387_ = l_Lean_Expr_inferImplicit(v_body_4381_, v_n_4386_, v_considerRange_4378_);
lean_dec(v_n_4386_);
v___x_4393_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4382_);
if (v___x_4393_ == 0)
{
v___y_4389_ = v___x_4393_;
goto v___jp_4388_;
}
else
{
uint8_t v___x_4394_; 
v___x_4394_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4387_, v_zero_4383_, v_considerRange_4378_);
v___y_4389_ = v___x_4394_;
goto v___jp_4388_;
}
v___jp_4388_:
{
if (v___y_4389_ == 0)
{
lean_object* v___x_4390_; 
v___x_4390_ = l_Lean_Expr_forallE___override(v_binderName_4379_, v_binderType_4380_, v_b_4387_, v_binderInfo_4382_);
return v___x_4390_;
}
else
{
uint8_t v___x_4391_; lean_object* v___x_4392_; 
v___x_4391_ = 1;
v___x_4392_ = l_Lean_Expr_forallE___override(v_binderName_4379_, v_binderType_4380_, v_b_4387_, v___x_4391_);
return v___x_4392_;
}
}
}
else
{
return v_e_4376_;
}
}
else
{
return v_e_4376_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_inferImplicit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4376_ = stack[0].m_obj;
lean_object* v_numParams_4377_ = stack[1].m_obj;
uint8_t v_considerRange_4378_ = stack[2].m_num;
lean_object* v_res_4395_;
v_res_4395_ = l_Lean_Expr_inferImplicit(v_e_4376_, v_numParams_4377_, v_considerRange_4378_);
stack->m_obj
 = v_res_4395_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4396_, lean_object* v_numParams_4397_, lean_object* v_considerRange_4398_){
_start:
{
uint8_t v_considerRange_boxed_4399_; lean_object* v_res_4400_; 
v_considerRange_boxed_4399_ = lean_unbox(v_considerRange_4398_);
v_res_4400_ = l_Lean_Expr_inferImplicit(v_e_4396_, v_numParams_4397_, v_considerRange_boxed_4399_);
lean_dec(v_numParams_4397_);
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4401_, lean_object* v_binderInfos_x3f_4402_){
_start:
{
if (lean_obj_tag(v_e_4401_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4402_) == 1)
{
lean_object* v_binderName_4403_; lean_object* v_binderType_4404_; lean_object* v_body_4405_; uint8_t v_binderInfo_4406_; lean_object* v_head_4407_; lean_object* v_tail_4408_; lean_object* v_b_4409_; 
v_binderName_4403_ = lean_ctor_get(v_e_4401_, 0);
lean_inc(v_binderName_4403_);
v_binderType_4404_ = lean_ctor_get(v_e_4401_, 1);
lean_inc_ref(v_binderType_4404_);
v_body_4405_ = lean_ctor_get(v_e_4401_, 2);
lean_inc_ref(v_body_4405_);
v_binderInfo_4406_ = lean_ctor_get_uint8(v_e_4401_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4401_, 3);
v_head_4407_ = lean_ctor_get(v_binderInfos_x3f_4402_, 0);
v_tail_4408_ = lean_ctor_get(v_binderInfos_x3f_4402_, 1);
v_b_4409_ = l_Lean_Expr_updateForallBinderInfos(v_body_4405_, v_tail_4408_);
if (lean_obj_tag(v_head_4407_) == 0)
{
lean_object* v___x_4410_; 
v___x_4410_ = l_Lean_Expr_forallE___override(v_binderName_4403_, v_binderType_4404_, v_b_4409_, v_binderInfo_4406_);
return v___x_4410_;
}
else
{
lean_object* v_val_4411_; uint8_t v___x_4412_; lean_object* v___x_4413_; 
v_val_4411_ = lean_ctor_get(v_head_4407_, 0);
v___x_4412_ = lean_unbox(v_val_4411_);
v___x_4413_ = l_Lean_Expr_forallE___override(v_binderName_4403_, v_binderType_4404_, v_b_4409_, v___x_4412_);
return v___x_4413_;
}
}
else
{
return v_e_4401_;
}
}
else
{
return v_e_4401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4414_, lean_object* v_binderInfos_x3f_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l_Lean_Expr_updateForallBinderInfos(v_e_4414_, v_binderInfos_x3f_4415_);
lean_dec(v_binderInfos_x3f_4415_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4417_, lean_object* v_binderNames_x3f_4418_){
_start:
{
switch(lean_obj_tag(v_e_4417_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4418_) == 1)
{
lean_object* v_binderName_4419_; lean_object* v_binderType_4420_; lean_object* v_body_4421_; uint8_t v_binderInfo_4422_; lean_object* v_head_4423_; lean_object* v_tail_4424_; lean_object* v_b_4425_; 
v_binderName_4419_ = lean_ctor_get(v_e_4417_, 0);
lean_inc(v_binderName_4419_);
v_binderType_4420_ = lean_ctor_get(v_e_4417_, 1);
lean_inc_ref(v_binderType_4420_);
v_body_4421_ = lean_ctor_get(v_e_4417_, 2);
lean_inc_ref(v_body_4421_);
v_binderInfo_4422_ = lean_ctor_get_uint8(v_e_4417_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4417_, 3);
v_head_4423_ = lean_ctor_get(v_binderNames_x3f_4418_, 0);
lean_inc(v_head_4423_);
v_tail_4424_ = lean_ctor_get(v_binderNames_x3f_4418_, 1);
lean_inc(v_tail_4424_);
lean_dec_ref_known(v_binderNames_x3f_4418_, 2);
v_b_4425_ = l_Lean_Expr_updateBinderNames(v_body_4421_, v_tail_4424_);
if (lean_obj_tag(v_head_4423_) == 0)
{
lean_object* v___x_4426_; 
v___x_4426_ = l_Lean_Expr_forallE___override(v_binderName_4419_, v_binderType_4420_, v_b_4425_, v_binderInfo_4422_);
return v___x_4426_;
}
else
{
lean_object* v_val_4427_; lean_object* v___x_4428_; 
lean_dec(v_binderName_4419_);
v_val_4427_ = lean_ctor_get(v_head_4423_, 0);
lean_inc(v_val_4427_);
lean_dec_ref_known(v_head_4423_, 1);
v___x_4428_ = l_Lean_Expr_forallE___override(v_val_4427_, v_binderType_4420_, v_b_4425_, v_binderInfo_4422_);
return v___x_4428_;
}
}
else
{
lean_dec(v_binderNames_x3f_4418_);
return v_e_4417_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4418_) == 1)
{
lean_object* v_binderName_4429_; lean_object* v_binderType_4430_; lean_object* v_body_4431_; uint8_t v_binderInfo_4432_; lean_object* v_head_4433_; lean_object* v_tail_4434_; lean_object* v_b_4435_; 
v_binderName_4429_ = lean_ctor_get(v_e_4417_, 0);
lean_inc(v_binderName_4429_);
v_binderType_4430_ = lean_ctor_get(v_e_4417_, 1);
lean_inc_ref(v_binderType_4430_);
v_body_4431_ = lean_ctor_get(v_e_4417_, 2);
lean_inc_ref(v_body_4431_);
v_binderInfo_4432_ = lean_ctor_get_uint8(v_e_4417_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4417_, 3);
v_head_4433_ = lean_ctor_get(v_binderNames_x3f_4418_, 0);
lean_inc(v_head_4433_);
v_tail_4434_ = lean_ctor_get(v_binderNames_x3f_4418_, 1);
lean_inc(v_tail_4434_);
lean_dec_ref_known(v_binderNames_x3f_4418_, 2);
v_b_4435_ = l_Lean_Expr_updateBinderNames(v_body_4431_, v_tail_4434_);
if (lean_obj_tag(v_head_4433_) == 0)
{
lean_object* v___x_4436_; 
v___x_4436_ = l_Lean_Expr_lam___override(v_binderName_4429_, v_binderType_4430_, v_b_4435_, v_binderInfo_4432_);
return v___x_4436_;
}
else
{
lean_object* v_val_4437_; lean_object* v___x_4438_; 
lean_dec(v_binderName_4429_);
v_val_4437_ = lean_ctor_get(v_head_4433_, 0);
lean_inc(v_val_4437_);
lean_dec_ref_known(v_head_4433_, 1);
v___x_4438_ = l_Lean_Expr_lam___override(v_val_4437_, v_binderType_4430_, v_b_4435_, v_binderInfo_4432_);
return v___x_4438_;
}
}
else
{
lean_dec(v_binderNames_x3f_4418_);
return v_e_4417_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4418_);
return v_e_4417_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_instantiate_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4439_ = stack[0].m_obj;
lean_object* v_subst_4440_ = stack[1].m_obj;
lean_object* v_res_4441_;
v_res_4441_ = lean_expr_instantiate(v_e_4439_, v_subst_4440_);
stack->m_obj
 = v_res_4441_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4442_, lean_object* v_subst_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = lean_expr_instantiate(v_e_4442_, v_subst_4443_);
lean_dec_ref(v_subst_4443_);
lean_dec_ref(v_e_4442_);
return v_res_4444_;
}
}
LEAN_EXPORT void l_Lean_Expr_instantiate1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4445_ = stack[0].m_obj;
lean_object* v_subst_4446_ = stack[1].m_obj;
lean_object* v_res_4447_;
v_res_4447_ = lean_expr_instantiate1(v_e_4445_, v_subst_4446_);
stack->m_obj
 = v_res_4447_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4448_, lean_object* v_subst_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = lean_expr_instantiate1(v_e_4448_, v_subst_4449_);
lean_dec_ref(v_subst_4449_);
lean_dec_ref(v_e_4448_);
return v_res_4450_;
}
}
LEAN_EXPORT void l_Lean_Expr_instantiateRev_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4451_ = stack[0].m_obj;
lean_object* v_subst_4452_ = stack[1].m_obj;
lean_object* v_res_4453_;
v_res_4453_ = lean_expr_instantiate_rev(v_e_4451_, v_subst_4452_);
stack->m_obj
 = v_res_4453_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4454_, lean_object* v_subst_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = lean_expr_instantiate_rev(v_e_4454_, v_subst_4455_);
lean_dec_ref(v_subst_4455_);
lean_dec_ref(v_e_4454_);
return v_res_4456_;
}
}
LEAN_EXPORT void l_Lean_Expr_instantiateRange_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4457_ = stack[0].m_obj;
lean_object* v_beginIdx_4458_ = stack[1].m_obj;
lean_object* v_endIdx_4459_ = stack[2].m_obj;
lean_object* v_subst_4460_ = stack[3].m_obj;
lean_object* v_res_4461_;
v_res_4461_ = lean_expr_instantiate_range(v_e_4457_, v_beginIdx_4458_, v_endIdx_4459_, v_subst_4460_);
stack->m_obj
 = v_res_4461_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4462_, lean_object* v_beginIdx_4463_, lean_object* v_endIdx_4464_, lean_object* v_subst_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = lean_expr_instantiate_range(v_e_4462_, v_beginIdx_4463_, v_endIdx_4464_, v_subst_4465_);
lean_dec_ref(v_subst_4465_);
lean_dec(v_endIdx_4464_);
lean_dec(v_beginIdx_4463_);
lean_dec_ref(v_e_4462_);
return v_res_4466_;
}
}
LEAN_EXPORT void l_Lean_Expr_instantiateRevRange_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4467_ = stack[0].m_obj;
lean_object* v_beginIdx_4468_ = stack[1].m_obj;
lean_object* v_endIdx_4469_ = stack[2].m_obj;
lean_object* v_subst_4470_ = stack[3].m_obj;
lean_object* v_res_4471_;
v_res_4471_ = lean_expr_instantiate_rev_range(v_e_4467_, v_beginIdx_4468_, v_endIdx_4469_, v_subst_4470_);
stack->m_obj
 = v_res_4471_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4472_, lean_object* v_beginIdx_4473_, lean_object* v_endIdx_4474_, lean_object* v_subst_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = lean_expr_instantiate_rev_range(v_e_4472_, v_beginIdx_4473_, v_endIdx_4474_, v_subst_4475_);
lean_dec_ref(v_subst_4475_);
lean_dec(v_endIdx_4474_);
lean_dec(v_beginIdx_4473_);
lean_dec_ref(v_e_4472_);
return v_res_4476_;
}
}
LEAN_EXPORT void l_Lean_Expr_abstract_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4477_ = stack[0].m_obj;
lean_object* v_xs_4478_ = stack[1].m_obj;
lean_object* v_res_4479_;
v_res_4479_ = lean_expr_abstract(v_e_4477_, v_xs_4478_);
stack->m_obj
 = v_res_4479_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4480_, lean_object* v_xs_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = lean_expr_abstract(v_e_4480_, v_xs_4481_);
lean_dec_ref(v_xs_4481_);
lean_dec_ref(v_e_4480_);
return v_res_4482_;
}
}
LEAN_EXPORT void l_Lean_Expr_abstractRange_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4483_ = stack[0].m_obj;
lean_object* v_n_4484_ = stack[1].m_obj;
lean_object* v_xs_4485_ = stack[2].m_obj;
lean_object* v_res_4486_;
v_res_4486_ = lean_expr_abstract_range(v_e_4483_, v_n_4484_, v_xs_4485_);
stack->m_obj
 = v_res_4486_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4487_, lean_object* v_n_4488_, lean_object* v_xs_4489_){
_start:
{
lean_object* v_res_4490_; 
v_res_4490_ = lean_expr_abstract_range(v_e_4487_, v_n_4488_, v_xs_4489_);
lean_dec_ref(v_xs_4489_);
lean_dec(v_n_4488_);
lean_dec_ref(v_e_4487_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4491_, lean_object* v_fvar_4492_, lean_object* v_v_4493_){
_start:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4494_ = lean_unsigned_to_nat(1u);
v___x_4495_ = lean_mk_empty_array_with_capacity(v___x_4494_);
v___x_4496_ = lean_array_push(v___x_4495_, v_fvar_4492_);
v___x_4497_ = lean_expr_abstract(v_e_4491_, v___x_4496_);
lean_dec_ref(v___x_4496_);
v___x_4498_ = lean_expr_instantiate1(v___x_4497_, v_v_4493_);
lean_dec_ref(v___x_4497_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4499_, lean_object* v_fvar_4500_, lean_object* v_v_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l_Lean_Expr_replaceFVar(v_e_4499_, v_fvar_4500_, v_v_4501_);
lean_dec_ref(v_v_4501_);
lean_dec_ref(v_e_4499_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4503_, lean_object* v_fvarId_4504_, lean_object* v_v_4505_){
_start:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4506_ = l_Lean_Expr_fvar___override(v_fvarId_4504_);
v___x_4507_ = l_Lean_Expr_replaceFVar(v_e_4503_, v___x_4506_, v_v_4505_);
return v___x_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4508_, lean_object* v_fvarId_4509_, lean_object* v_v_4510_){
_start:
{
lean_object* v_res_4511_; 
v_res_4511_ = l_Lean_Expr_replaceFVarId(v_e_4508_, v_fvarId_4509_, v_v_4510_);
lean_dec_ref(v_v_4510_);
lean_dec_ref(v_e_4508_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4512_, lean_object* v_fvars_4513_, lean_object* v_vs_4514_){
_start:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4515_ = lean_expr_abstract(v_e_4512_, v_fvars_4513_);
v___x_4516_ = lean_expr_instantiate_rev(v___x_4515_, v_vs_4514_);
lean_dec_ref(v___x_4515_);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4517_, lean_object* v_fvars_4518_, lean_object* v_vs_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Lean_Expr_replaceFVars(v_e_4517_, v_fvars_4518_, v_vs_4519_);
lean_dec_ref(v_vs_4519_);
lean_dec_ref(v_fvars_4518_);
lean_dec_ref(v_e_4517_);
return v_res_4520_;
}
}
uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4523_){
_start:
{
switch(lean_obj_tag(v_x_4523_))
{
case 4:
{
uint8_t v___x_4524_; 
v___x_4524_ = 1;
return v___x_4524_;
}
case 3:
{
uint8_t v___x_4525_; 
v___x_4525_ = 1;
return v___x_4525_;
}
case 0:
{
uint8_t v___x_4526_; 
v___x_4526_ = 1;
return v___x_4526_;
}
case 9:
{
uint8_t v___x_4527_; 
v___x_4527_ = 1;
return v___x_4527_;
}
case 2:
{
uint8_t v___x_4528_; 
v___x_4528_ = 1;
return v___x_4528_;
}
case 1:
{
uint8_t v___x_4529_; 
v___x_4529_ = 1;
return v___x_4529_;
}
default: 
{
uint8_t v___x_4530_; 
v___x_4530_ = 0;
return v___x_4530_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_isAtomic_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4523_ = stack[0].m_obj;
uint8_t v_res_4531_;
v_res_4531_ = l_Lean_Expr_isAtomic(v_x_4523_);
stack->m_num = v_res_4531_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4532_){
_start:
{
uint8_t v_res_4533_; lean_object* v_r_4534_; 
v_res_4533_ = l_Lean_Expr_isAtomic(v_x_4532_);
lean_dec_ref(v_x_4532_);
v_r_4534_ = lean_box(v_res_4533_);
return v_r_4534_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4540_ = lean_box(0);
v___x_4541_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4542_ = l_Lean_Expr_const___override(v___x_4541_, v___x_4540_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4543_, lean_object* v_proof_4544_){
_start:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4545_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4546_ = l_Lean_mkAppB(v___x_4545_, v_pred_4543_, v_proof_4544_);
return v___x_4546_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4551_ = lean_box(0);
v___x_4552_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4553_ = l_Lean_Expr_const___override(v___x_4552_, v___x_4551_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4554_, lean_object* v_proof_4555_){
_start:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4556_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4557_ = l_Lean_mkAppB(v___x_4556_, v_pred_4554_, v_proof_4555_);
return v___x_4557_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4558_; 
v___x_4558_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4558_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4559_; 
v___x_4559_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4560_){
_start:
{
lean_inc_ref(v_val_4560_);
return v_val_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4561_);
lean_dec_ref(v_val_4561_);
return v_res_4562_;
}
}
uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4565_, lean_object* v_x_4566_){
_start:
{
uint8_t v___x_4567_; 
v___x_4567_ = lean_expr_equal(v_x_4565_, v_x_4566_);
return v___x_4567_;
}
}
LEAN_EXPORT void l_Lean_ExprStructEq_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4565_ = stack[0].m_obj;
lean_object* v_x_4566_ = stack[1].m_obj;
uint8_t v_res_4568_;
v_res_4568_ = l_Lean_ExprStructEq_beq(v_x_4565_, v_x_4566_);
stack->m_num = v_res_4568_;
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4569_, lean_object* v_x_4570_){
_start:
{
uint8_t v_res_4571_; lean_object* v_r_4572_; 
v_res_4571_ = l_Lean_ExprStructEq_beq(v_x_4569_, v_x_4570_);
lean_dec_ref(v_x_4570_);
lean_dec_ref(v_x_4569_);
v_r_4572_ = lean_box(v_res_4571_);
return v_r_4572_;
}
}
uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4573_){
_start:
{
uint64_t v___x_4574_; 
v___x_4574_ = l_Lean_Expr_hash(v_x_4573_);
return v___x_4574_;
}
}
LEAN_EXPORT void l_Lean_ExprStructEq_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4573_ = stack[0].m_obj;
uint64_t v_res_4575_;
v_res_4575_ = l_Lean_ExprStructEq_hash(v_x_4573_);
stack->m_num = v_res_4575_;
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4576_){
_start:
{
uint64_t v_res_4577_; lean_object* v_r_4578_; 
v_res_4577_ = l_Lean_ExprStructEq_hash(v_x_4576_);
lean_dec_ref(v_x_4576_);
v_r_4578_ = lean_box_uint64(v_res_4577_);
return v_r_4578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4585_, lean_object* v_start_4586_, lean_object* v_b_4587_, lean_object* v_i_4588_){
_start:
{
uint8_t v___x_4589_; 
v___x_4589_ = lean_nat_dec_le(v_i_4588_, v_start_4586_);
if (v___x_4589_ == 0)
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v_i_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4590_ = l_Lean_instInhabitedExpr;
v___x_4591_ = lean_unsigned_to_nat(1u);
v_i_4592_ = lean_nat_sub(v_i_4588_, v___x_4591_);
lean_dec(v_i_4588_);
v___x_4593_ = lean_array_get_borrowed(v___x_4590_, v_revArgs_4585_, v_i_4592_);
lean_inc(v___x_4593_);
v___x_4594_ = l_Lean_Expr_app___override(v_b_4587_, v___x_4593_);
v_b_4587_ = v___x_4594_;
v_i_4588_ = v_i_4592_;
goto _start;
}
else
{
lean_dec(v_i_4588_);
return v_b_4587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4596_, lean_object* v_start_4597_, lean_object* v_b_4598_, lean_object* v_i_4599_){
_start:
{
lean_object* v_res_4600_; 
v_res_4600_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4596_, v_start_4597_, v_b_4598_, v_i_4599_);
lean_dec(v_start_4597_);
lean_dec_ref(v_revArgs_4596_);
return v_res_4600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4601_, lean_object* v_beginIdx_4602_, lean_object* v_endIdx_4603_, lean_object* v_revArgs_4604_){
_start:
{
lean_object* v___x_4605_; 
v___x_4605_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4604_, v_beginIdx_4602_, v_f_4601_, v_endIdx_4603_);
return v___x_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4606_, lean_object* v_beginIdx_4607_, lean_object* v_endIdx_4608_, lean_object* v_revArgs_4609_){
_start:
{
lean_object* v_res_4610_; 
v_res_4610_ = l_Lean_Expr_mkAppRevRange(v_f_4606_, v_beginIdx_4607_, v_endIdx_4608_, v_revArgs_4609_);
lean_dec_ref(v_revArgs_4609_);
lean_dec(v_beginIdx_4607_);
return v_res_4610_;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4611_, uint8_t v_useZeta_4612_, uint8_t v_preserveMData_4613_, lean_object* v_sz_4614_, lean_object* v_e_4615_, lean_object* v_i_4616_){
_start:
{
switch(lean_obj_tag(v_e_4615_))
{
case 6:
{
lean_object* v_body_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; uint8_t v___x_4625_; 
v_body_4622_ = lean_ctor_get(v_e_4615_, 2);
lean_inc_ref(v_body_4622_);
lean_dec_ref_known(v_e_4615_, 3);
v___x_4623_ = lean_unsigned_to_nat(1u);
v___x_4624_ = lean_nat_add(v_i_4616_, v___x_4623_);
lean_dec(v_i_4616_);
v___x_4625_ = lean_nat_dec_lt(v___x_4624_, v_sz_4614_);
if (v___x_4625_ == 0)
{
lean_object* v___x_4626_; 
lean_dec(v___x_4624_);
v___x_4626_ = lean_expr_instantiate(v_body_4622_, v_revArgs_4611_);
lean_dec_ref(v_body_4622_);
return v___x_4626_;
}
else
{
v_e_4615_ = v_body_4622_;
v_i_4616_ = v___x_4624_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4612_ == 0)
{
goto v___jp_4617_;
}
else
{
lean_object* v_value_4628_; lean_object* v_body_4629_; uint8_t v___x_4630_; 
v_value_4628_ = lean_ctor_get(v_e_4615_, 2);
v_body_4629_ = lean_ctor_get(v_e_4615_, 3);
v___x_4630_ = lean_nat_dec_lt(v_i_4616_, v_sz_4614_);
if (v___x_4630_ == 0)
{
goto v___jp_4617_;
}
else
{
lean_object* v___x_4631_; 
lean_inc_ref(v_body_4629_);
lean_inc_ref(v_value_4628_);
lean_dec_ref_known(v_e_4615_, 4);
v___x_4631_ = lean_expr_instantiate1(v_body_4629_, v_value_4628_);
lean_dec_ref(v_value_4628_);
lean_dec_ref(v_body_4629_);
v_e_4615_ = v___x_4631_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4613_ == 0)
{
lean_object* v_expr_4633_; 
v_expr_4633_ = lean_ctor_get(v_e_4615_, 1);
lean_inc_ref(v_expr_4633_);
lean_dec_ref_known(v_e_4615_, 2);
v_e_4615_ = v_expr_4633_;
goto _start;
}
else
{
goto v___jp_4617_;
}
}
default: 
{
goto v___jp_4617_;
}
}
v___jp_4617_:
{
lean_object* v_n_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v_n_4618_ = lean_nat_sub(v_sz_4614_, v_i_4616_);
lean_dec(v_i_4616_);
v___x_4619_ = lean_expr_instantiate_range(v_e_4615_, v_n_4618_, v_sz_4614_, v_revArgs_4611_);
lean_dec_ref(v_e_4615_);
v___x_4620_ = lean_unsigned_to_nat(0u);
v___x_4621_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4611_, v___x_4620_, v___x_4619_, v_n_4618_);
return v___x_4621_;
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_betaRev_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_revArgs_4611_ = stack[0].m_obj;
uint8_t v_useZeta_4612_ = stack[1].m_num;
uint8_t v_preserveMData_4613_ = stack[2].m_num;
lean_object* v_sz_4614_ = stack[3].m_obj;
lean_object* v_e_4615_ = stack[4].m_obj;
lean_object* v_i_4616_ = stack[5].m_obj;
lean_object* v_res_4635_;
v_res_4635_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4611_, v_useZeta_4612_, v_preserveMData_4613_, v_sz_4614_, v_e_4615_, v_i_4616_);
stack->m_obj
 = v_res_4635_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4636_, lean_object* v_useZeta_4637_, lean_object* v_preserveMData_4638_, lean_object* v_sz_4639_, lean_object* v_e_4640_, lean_object* v_i_4641_){
_start:
{
uint8_t v_useZeta_boxed_4642_; uint8_t v_preserveMData_boxed_4643_; lean_object* v_res_4644_; 
v_useZeta_boxed_4642_ = lean_unbox(v_useZeta_4637_);
v_preserveMData_boxed_4643_ = lean_unbox(v_preserveMData_4638_);
v_res_4644_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4636_, v_useZeta_boxed_4642_, v_preserveMData_boxed_4643_, v_sz_4639_, v_e_4640_, v_i_4641_);
lean_dec(v_sz_4639_);
lean_dec_ref(v_revArgs_4636_);
return v_res_4644_;
}
}
lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4645_, lean_object* v_revArgs_4646_, uint8_t v_useZeta_4647_, uint8_t v_preserveMData_4648_){
_start:
{
lean_object* v_sz_4649_; lean_object* v___x_4650_; uint8_t v___x_4651_; 
v_sz_4649_ = lean_array_get_size(v_revArgs_4646_);
v___x_4650_ = lean_unsigned_to_nat(0u);
v___x_4651_ = lean_nat_dec_eq(v_sz_4649_, v___x_4650_);
if (v___x_4651_ == 0)
{
lean_object* v___x_4652_; 
v___x_4652_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4646_, v_useZeta_4647_, v_preserveMData_4648_, v_sz_4649_, v_f_4645_, v___x_4650_);
return v___x_4652_;
}
else
{
return v_f_4645_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_betaRev_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4645_ = stack[0].m_obj;
lean_object* v_revArgs_4646_ = stack[1].m_obj;
uint8_t v_useZeta_4647_ = stack[2].m_num;
uint8_t v_preserveMData_4648_ = stack[3].m_num;
lean_object* v_res_4653_;
v_res_4653_ = l_Lean_Expr_betaRev(v_f_4645_, v_revArgs_4646_, v_useZeta_4647_, v_preserveMData_4648_);
stack->m_obj
 = v_res_4653_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4654_, lean_object* v_revArgs_4655_, lean_object* v_useZeta_4656_, lean_object* v_preserveMData_4657_){
_start:
{
uint8_t v_useZeta_boxed_4658_; uint8_t v_preserveMData_boxed_4659_; lean_object* v_res_4660_; 
v_useZeta_boxed_4658_ = lean_unbox(v_useZeta_4656_);
v_preserveMData_boxed_4659_ = lean_unbox(v_preserveMData_4657_);
v_res_4660_ = l_Lean_Expr_betaRev(v_f_4654_, v_revArgs_4655_, v_useZeta_boxed_4658_, v_preserveMData_boxed_4659_);
lean_dec_ref(v_revArgs_4655_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4661_, lean_object* v_args_4662_){
_start:
{
lean_object* v___x_4663_; uint8_t v___x_4664_; lean_object* v___x_4665_; 
v___x_4663_ = l_Array_reverse___redArg(v_args_4662_);
v___x_4664_ = 0;
v___x_4665_ = l_Lean_Expr_betaRev(v_f_4661_, v___x_4663_, v___x_4664_, v___x_4664_);
lean_dec_ref(v___x_4663_);
return v___x_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4666_){
_start:
{
switch(lean_obj_tag(v_x_4666_))
{
case 6:
{
lean_object* v_body_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v_body_4667_ = lean_ctor_get(v_x_4666_, 2);
v___x_4668_ = l_Lean_Expr_getNumHeadLambdas(v_body_4667_);
v___x_4669_ = lean_unsigned_to_nat(1u);
v___x_4670_ = lean_nat_add(v___x_4668_, v___x_4669_);
lean_dec(v___x_4668_);
return v___x_4670_;
}
case 10:
{
lean_object* v_expr_4671_; 
v_expr_4671_ = lean_ctor_get(v_x_4666_, 1);
v_x_4666_ = v_expr_4671_;
goto _start;
}
default: 
{
lean_object* v___x_4673_; 
v___x_4673_ = lean_unsigned_to_nat(0u);
return v___x_4673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l_Lean_Expr_getNumHeadLambdas(v_x_4674_);
lean_dec_ref(v_x_4674_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object* v_x_4676_){
_start:
{
switch(lean_obj_tag(v_x_4676_))
{
case 6:
{
lean_object* v_body_4677_; 
v_body_4677_ = lean_ctor_get(v_x_4676_, 2);
v_x_4676_ = v_body_4677_;
goto _start;
}
case 10:
{
lean_object* v_expr_4679_; 
v_expr_4679_ = lean_ctor_get(v_x_4676_, 1);
v_x_4676_ = v_expr_4679_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_4676_);
return v_x_4676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object* v_x_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l_Lean_Expr_getLambdaBody(v_x_4681_);
lean_dec_ref(v_x_4681_);
return v_res_4682_;
}
}
uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4683_, lean_object* v_x_4684_){
_start:
{
switch(lean_obj_tag(v_x_4684_))
{
case 6:
{
uint8_t v___x_4685_; 
v___x_4685_ = 1;
return v___x_4685_;
}
case 8:
{
if (v_useZeta_4683_ == 0)
{
return v_useZeta_4683_;
}
else
{
lean_object* v_body_4686_; 
v_body_4686_ = lean_ctor_get(v_x_4684_, 3);
v_x_4684_ = v_body_4686_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4688_; 
v_expr_4688_ = lean_ctor_get(v_x_4684_, 1);
v_x_4684_ = v_expr_4688_;
goto _start;
}
default: 
{
uint8_t v___x_4690_; 
v___x_4690_ = 0;
return v___x_4690_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_isHeadBetaTargetFn_0interp(lean_interpreter_value* stack)
{
uint8_t v_useZeta_4683_ = stack[0].m_num;
lean_object* v_x_4684_ = stack[1].m_obj;
uint8_t v_res_4691_;
v_res_4691_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4683_, v_x_4684_);
stack->m_num = v_res_4691_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4692_, lean_object* v_x_4693_){
_start:
{
uint8_t v_useZeta_boxed_4694_; uint8_t v_res_4695_; lean_object* v_r_4696_; 
v_useZeta_boxed_4694_ = lean_unbox(v_useZeta_4692_);
v_res_4695_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4694_, v_x_4693_);
lean_dec_ref(v_x_4693_);
v_r_4696_ = lean_box(v_res_4695_);
return v_r_4696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4697_){
_start:
{
lean_object* v_f_4698_; uint8_t v___x_4699_; uint8_t v___x_4700_; 
v_f_4698_ = l_Lean_Expr_getAppFn(v_e_4697_);
v___x_4699_ = 0;
v___x_4700_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4699_, v_f_4698_);
if (v___x_4700_ == 0)
{
lean_dec_ref(v_f_4698_);
return v_e_4697_;
}
else
{
lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4701_ = l_Lean_Expr_getAppNumArgs(v_e_4697_);
v___x_4702_ = lean_mk_empty_array_with_capacity(v___x_4701_);
lean_dec(v___x_4701_);
v___x_4703_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4697_, v___x_4702_);
v___x_4704_ = l_Lean_Expr_betaRev(v_f_4698_, v___x_4703_, v___x_4699_, v___x_4699_);
lean_dec_ref(v___x_4703_);
return v___x_4704_;
}
}
}
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4705_, uint8_t v_useZeta_4706_){
_start:
{
uint8_t v___x_4707_; 
v___x_4707_ = l_Lean_Expr_isApp(v_e_4705_);
if (v___x_4707_ == 0)
{
return v___x_4707_;
}
else
{
lean_object* v___x_4708_; uint8_t v___x_4709_; 
v___x_4708_ = l_Lean_Expr_getAppFn(v_e_4705_);
v___x_4709_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4706_, v___x_4708_);
lean_dec_ref(v___x_4708_);
return v___x_4709_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isHeadBetaTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4705_ = stack[0].m_obj;
uint8_t v_useZeta_4706_ = stack[1].m_num;
uint8_t v_res_4710_;
v_res_4710_ = l_Lean_Expr_isHeadBetaTarget(v_e_4705_, v_useZeta_4706_);
stack->m_num = v_res_4710_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4711_, lean_object* v_useZeta_4712_){
_start:
{
uint8_t v_useZeta_boxed_4713_; uint8_t v_res_4714_; lean_object* v_r_4715_; 
v_useZeta_boxed_4713_ = lean_unbox(v_useZeta_4712_);
v_res_4714_ = l_Lean_Expr_isHeadBetaTarget(v_e_4711_, v_useZeta_boxed_4713_);
lean_dec_ref(v_e_4711_);
v_r_4715_ = lean_box(v_res_4714_);
return v_r_4715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4716_, lean_object* v_x_4717_, lean_object* v_x_4718_){
_start:
{
lean_object* v_f_4720_; 
if (lean_obj_tag(v_x_4716_) == 5)
{
lean_object* v_arg_4724_; 
v_arg_4724_ = lean_ctor_get(v_x_4716_, 1);
if (lean_obj_tag(v_arg_4724_) == 0)
{
lean_object* v_fn_4725_; lean_object* v_deBruijnIndex_4726_; lean_object* v_zero_4727_; uint8_t v_isZero_4728_; 
v_fn_4725_ = lean_ctor_get(v_x_4716_, 0);
v_deBruijnIndex_4726_ = lean_ctor_get(v_arg_4724_, 0);
v_zero_4727_ = lean_unsigned_to_nat(0u);
v_isZero_4728_ = lean_nat_dec_eq(v_x_4717_, v_zero_4727_);
if (v_isZero_4728_ == 1)
{
lean_dec(v_x_4718_);
lean_dec(v_x_4717_);
v_f_4720_ = v_x_4716_;
goto v___jp_4719_;
}
else
{
uint8_t v___x_4729_; 
lean_inc(v_deBruijnIndex_4726_);
lean_inc_ref(v_fn_4725_);
lean_dec_ref_known(v_x_4716_, 2);
v___x_4729_ = lean_nat_dec_eq(v_deBruijnIndex_4726_, v_x_4718_);
lean_dec(v_deBruijnIndex_4726_);
if (v___x_4729_ == 0)
{
lean_object* v___x_4730_; 
lean_dec_ref(v_fn_4725_);
lean_dec(v_x_4718_);
lean_dec(v_x_4717_);
v___x_4730_ = lean_box(0);
return v___x_4730_;
}
else
{
lean_object* v_one_4731_; lean_object* v_n_4732_; lean_object* v___x_4733_; 
v_one_4731_ = lean_unsigned_to_nat(1u);
v_n_4732_ = lean_nat_sub(v_x_4717_, v_one_4731_);
lean_dec(v_x_4717_);
v___x_4733_ = lean_nat_add(v_x_4718_, v_one_4731_);
lean_dec(v_x_4718_);
v_x_4716_ = v_fn_4725_;
v_x_4717_ = v_n_4732_;
v_x_4718_ = v___x_4733_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4735_; uint8_t v_isZero_4736_; 
lean_dec(v_x_4718_);
v_zero_4735_ = lean_unsigned_to_nat(0u);
v_isZero_4736_ = lean_nat_dec_eq(v_x_4717_, v_zero_4735_);
lean_dec(v_x_4717_);
if (v_isZero_4736_ == 1)
{
v_f_4720_ = v_x_4716_;
goto v___jp_4719_;
}
else
{
lean_object* v___x_4737_; 
lean_dec_ref_known(v_x_4716_, 2);
v___x_4737_ = lean_box(0);
return v___x_4737_;
}
}
}
else
{
lean_object* v_zero_4738_; uint8_t v_isZero_4739_; 
lean_dec(v_x_4718_);
v_zero_4738_ = lean_unsigned_to_nat(0u);
v_isZero_4739_ = lean_nat_dec_eq(v_x_4717_, v_zero_4738_);
lean_dec(v_x_4717_);
if (v_isZero_4739_ == 1)
{
v_f_4720_ = v_x_4716_;
goto v___jp_4719_;
}
else
{
lean_object* v___x_4740_; 
lean_dec_ref(v_x_4716_);
v___x_4740_ = lean_box(0);
return v___x_4740_;
}
}
v___jp_4719_:
{
uint8_t v___x_4721_; 
v___x_4721_ = l_Lean_Expr_hasLooseBVars(v_f_4720_);
if (v___x_4721_ == 0)
{
lean_object* v___x_4722_; 
v___x_4722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4722_, 0, v_f_4720_);
return v___x_4722_;
}
else
{
lean_object* v___x_4723_; 
lean_dec_ref(v_f_4720_);
v___x_4723_ = lean_box(0);
return v___x_4723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4741_, lean_object* v_x_4742_){
_start:
{
if (lean_obj_tag(v_x_4741_) == 6)
{
lean_object* v_body_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; 
v_body_4743_ = lean_ctor_get(v_x_4741_, 2);
lean_inc_ref(v_body_4743_);
lean_dec_ref_known(v_x_4741_, 3);
v___x_4744_ = lean_unsigned_to_nat(1u);
v___x_4745_ = lean_nat_add(v_x_4742_, v___x_4744_);
lean_dec(v_x_4742_);
v_x_4741_ = v_body_4743_;
v_x_4742_ = v___x_4745_;
goto _start;
}
else
{
lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4747_ = lean_unsigned_to_nat(0u);
v___x_4748_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4741_, v_x_4742_, v___x_4747_);
return v___x_4748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4749_){
_start:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4750_ = lean_unsigned_to_nat(0u);
v___x_4751_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4749_, v___x_4750_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4752_){
_start:
{
if (lean_obj_tag(v_x_4752_) == 6)
{
lean_object* v_body_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; 
v_body_4753_ = lean_ctor_get(v_x_4752_, 2);
lean_inc_ref(v_body_4753_);
lean_dec_ref_known(v_x_4752_, 3);
v___x_4754_ = lean_unsigned_to_nat(1u);
v___x_4755_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4753_, v___x_4754_);
return v___x_4755_;
}
else
{
lean_object* v___x_4756_; 
lean_dec_ref(v_x_4752_);
v___x_4756_ = lean_box(0);
return v___x_4756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4760_){
_start:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; uint8_t v___x_4763_; 
v___x_4761_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4762_ = lean_unsigned_to_nat(2u);
v___x_4763_ = l_Lean_Expr_isAppOfArity(v_e_4760_, v___x_4761_, v___x_4762_);
if (v___x_4763_ == 0)
{
lean_object* v___x_4764_; 
v___x_4764_ = lean_box(0);
return v___x_4764_;
}
else
{
lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4765_ = l_Lean_Expr_appArg_x21(v_e_4760_);
v___x_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4766_, 0, v___x_4765_);
return v___x_4766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4767_){
_start:
{
lean_object* v_res_4768_; 
v_res_4768_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4767_);
lean_dec_ref(v_e_4767_);
return v_res_4768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4772_){
_start:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; uint8_t v___x_4775_; 
v___x_4773_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4774_ = lean_unsigned_to_nat(2u);
v___x_4775_ = l_Lean_Expr_isAppOfArity(v_e_4772_, v___x_4773_, v___x_4774_);
if (v___x_4775_ == 0)
{
lean_object* v___x_4776_; 
v___x_4776_ = lean_box(0);
return v___x_4776_;
}
else
{
lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4777_ = l_Lean_Expr_appArg_x21(v_e_4772_);
v___x_4778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4777_);
return v___x_4778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4779_);
lean_dec_ref(v_e_4779_);
return v_res_4780_;
}
}
uint8_t l_Lean_Expr_isOutParam(lean_object* v_e_4784_){
_start:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; uint8_t v___x_4787_; 
v___x_4785_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4786_ = lean_unsigned_to_nat(1u);
v___x_4787_ = l_Lean_Expr_isAppOfArity(v_e_4784_, v___x_4785_, v___x_4786_);
return v___x_4787_;
}
}
LEAN_EXPORT void l_Lean_Expr_isOutParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4784_ = stack[0].m_obj;
uint8_t v_res_4788_;
v_res_4788_ = l_Lean_Expr_isOutParam(v_e_4784_);
stack->m_num = v_res_4788_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4789_){
_start:
{
uint8_t v_res_4790_; lean_object* v_r_4791_; 
v_res_4790_ = l_Lean_Expr_isOutParam(v_e_4789_);
lean_dec_ref(v_e_4789_);
v_r_4791_ = lean_box(v_res_4790_);
return v_r_4791_;
}
}
uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4795_){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; uint8_t v___x_4798_; 
v___x_4796_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4797_ = lean_unsigned_to_nat(1u);
v___x_4798_ = l_Lean_Expr_isAppOfArity(v_e_4795_, v___x_4796_, v___x_4797_);
return v___x_4798_;
}
}
LEAN_EXPORT void l_Lean_Expr_isSemiOutParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4795_ = stack[0].m_obj;
uint8_t v_res_4799_;
v_res_4799_ = l_Lean_Expr_isSemiOutParam(v_e_4795_);
stack->m_num = v_res_4799_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4800_){
_start:
{
uint8_t v_res_4801_; lean_object* v_r_4802_; 
v_res_4801_ = l_Lean_Expr_isSemiOutParam(v_e_4800_);
lean_dec_ref(v_e_4800_);
v_r_4802_ = lean_box(v_res_4801_);
return v_r_4802_;
}
}
uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4803_){
_start:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; uint8_t v___x_4806_; 
v___x_4804_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4805_ = lean_unsigned_to_nat(2u);
v___x_4806_ = l_Lean_Expr_isAppOfArity(v_e_4803_, v___x_4804_, v___x_4805_);
return v___x_4806_;
}
}
LEAN_EXPORT void l_Lean_Expr_isOptParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4803_ = stack[0].m_obj;
uint8_t v_res_4807_;
v_res_4807_ = l_Lean_Expr_isOptParam(v_e_4803_);
stack->m_num = v_res_4807_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4808_){
_start:
{
uint8_t v_res_4809_; lean_object* v_r_4810_; 
v_res_4809_ = l_Lean_Expr_isOptParam(v_e_4808_);
lean_dec_ref(v_e_4808_);
v_r_4810_ = lean_box(v_res_4809_);
return v_r_4810_;
}
}
uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4811_){
_start:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; uint8_t v___x_4814_; 
v___x_4812_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4813_ = lean_unsigned_to_nat(2u);
v___x_4814_ = l_Lean_Expr_isAppOfArity(v_e_4811_, v___x_4812_, v___x_4813_);
return v___x_4814_;
}
}
LEAN_EXPORT void l_Lean_Expr_isAutoParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4811_ = stack[0].m_obj;
uint8_t v_res_4815_;
v_res_4815_ = l_Lean_Expr_isAutoParam(v_e_4811_);
stack->m_num = v_res_4815_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4816_){
_start:
{
uint8_t v_res_4817_; lean_object* v_r_4818_; 
v_res_4817_ = l_Lean_Expr_isAutoParam(v_e_4816_);
lean_dec_ref(v_e_4816_);
v_r_4818_ = lean_box(v_res_4817_);
return v_r_4818_;
}
}
uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4819_){
_start:
{
lean_object* v___x_4820_; 
v___x_4820_ = l_Lean_Expr_getAppFn(v_e_4819_);
if (lean_obj_tag(v___x_4820_) == 4)
{
lean_object* v_declName_4821_; uint8_t v___y_4823_; lean_object* v___x_4828_; uint8_t v___x_4829_; 
v_declName_4821_ = lean_ctor_get(v___x_4820_, 0);
lean_inc(v_declName_4821_);
lean_dec_ref_known(v___x_4820_, 2);
v___x_4828_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4829_ = lean_name_eq(v_declName_4821_, v___x_4828_);
if (v___x_4829_ == 0)
{
lean_object* v___x_4830_; uint8_t v___x_4831_; 
v___x_4830_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4831_ = lean_name_eq(v_declName_4821_, v___x_4830_);
v___y_4823_ = v___x_4831_;
goto v___jp_4822_;
}
else
{
v___y_4823_ = v___x_4829_;
goto v___jp_4822_;
}
v___jp_4822_:
{
if (v___y_4823_ == 0)
{
lean_object* v___x_4824_; uint8_t v___x_4825_; 
v___x_4824_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4825_ = lean_name_eq(v_declName_4821_, v___x_4824_);
if (v___x_4825_ == 0)
{
lean_object* v___x_4826_; uint8_t v___x_4827_; 
v___x_4826_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4827_ = lean_name_eq(v_declName_4821_, v___x_4826_);
lean_dec(v_declName_4821_);
return v___x_4827_;
}
else
{
lean_dec(v_declName_4821_);
return v___x_4825_;
}
}
else
{
lean_dec(v_declName_4821_);
return v___y_4823_;
}
}
}
else
{
uint8_t v___x_4832_; 
lean_dec_ref(v___x_4820_);
v___x_4832_ = 0;
return v___x_4832_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_isTypeAnnotation_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4819_ = stack[0].m_obj;
uint8_t v_res_4833_;
v_res_4833_ = l_Lean_Expr_isTypeAnnotation(v_e_4819_);
stack->m_num = v_res_4833_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4834_){
_start:
{
uint8_t v_res_4835_; lean_object* v_r_4836_; 
v_res_4835_ = l_Lean_Expr_isTypeAnnotation(v_e_4834_);
lean_dec_ref(v_e_4834_);
v_r_4836_ = lean_box(v_res_4835_);
return v_r_4836_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4837_){
_start:
{
uint8_t v___y_4839_; uint8_t v___y_4843_; uint8_t v___x_4849_; 
v___x_4849_ = l_Lean_Expr_isOptParam(v_e_4837_);
if (v___x_4849_ == 0)
{
uint8_t v___x_4850_; 
v___x_4850_ = l_Lean_Expr_isAutoParam(v_e_4837_);
v___y_4843_ = v___x_4850_;
goto v___jp_4842_;
}
else
{
v___y_4843_ = v___x_4849_;
goto v___jp_4842_;
}
v___jp_4838_:
{
if (v___y_4839_ == 0)
{
return v_e_4837_;
}
else
{
lean_object* v___x_4840_; 
v___x_4840_ = l_Lean_Expr_appArg_x21(v_e_4837_);
lean_dec_ref(v_e_4837_);
v_e_4837_ = v___x_4840_;
goto _start;
}
}
v___jp_4842_:
{
if (v___y_4843_ == 0)
{
uint8_t v___x_4844_; 
v___x_4844_ = l_Lean_Expr_isOutParam(v_e_4837_);
if (v___x_4844_ == 0)
{
uint8_t v___x_4845_; 
v___x_4845_ = l_Lean_Expr_isSemiOutParam(v_e_4837_);
v___y_4839_ = v___x_4845_;
goto v___jp_4838_;
}
else
{
v___y_4839_ = v___x_4844_;
goto v___jp_4838_;
}
}
else
{
lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4846_ = l_Lean_Expr_appFn_x21(v_e_4837_);
lean_dec_ref(v_e_4837_);
v___x_4847_ = l_Lean_Expr_appArg_x21(v___x_4846_);
lean_dec_ref(v___x_4846_);
v_e_4837_ = v___x_4847_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4851_){
_start:
{
lean_object* v___x_4852_; lean_object* v_e_x27_4853_; uint8_t v___x_4854_; 
v___x_4852_ = l_Lean_Expr_consumeMData(v_e_4851_);
v_e_x27_4853_ = lean_expr_consume_type_annotations(v___x_4852_);
v___x_4854_ = lean_expr_eqv(v_e_x27_4853_, v_e_4851_);
if (v___x_4854_ == 0)
{
lean_dec_ref(v_e_4851_);
v_e_4851_ = v_e_x27_4853_;
goto _start;
}
else
{
lean_dec_ref(v_e_x27_4853_);
return v_e_4851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4856_){
_start:
{
lean_object* v_fn_4857_; lean_object* v___x_4858_; 
v_fn_4857_ = lean_ctor_get(v_e_4856_, 0);
lean_inc_ref(v_fn_4857_);
lean_dec_ref(v_e_4856_);
v___x_4858_ = l_Lean_Expr_cleanupAnnotations(v_fn_4857_);
return v___x_4858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* v_e_4859_, lean_object* v_h_4860_){
_start:
{
lean_object* v___x_4861_; 
v___x_4861_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4859_);
return v___x_4861_;
}
}
uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4865_){
_start:
{
lean_object* v___x_4866_; lean_object* v___x_4867_; uint8_t v___x_4868_; 
v___x_4866_ = l_Lean_Expr_cleanupAnnotations(v_e_4865_);
v___x_4867_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4868_ = l_Lean_Expr_isConstOf(v___x_4866_, v___x_4867_);
lean_dec_ref(v___x_4866_);
return v___x_4868_;
}
}
LEAN_EXPORT void l_Lean_Expr_isFalse_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4865_ = stack[0].m_obj;
uint8_t v_res_4869_;
v_res_4869_ = l_Lean_Expr_isFalse(v_e_4865_);
stack->m_num = v_res_4869_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4870_){
_start:
{
uint8_t v_res_4871_; lean_object* v_r_4872_; 
v_res_4871_ = l_Lean_Expr_isFalse(v_e_4870_);
v_r_4872_ = lean_box(v_res_4871_);
return v_r_4872_;
}
}
uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4876_){
_start:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; uint8_t v___x_4879_; 
v___x_4877_ = l_Lean_Expr_cleanupAnnotations(v_e_4876_);
v___x_4878_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4879_ = l_Lean_Expr_isConstOf(v___x_4877_, v___x_4878_);
lean_dec_ref(v___x_4877_);
return v___x_4879_;
}
}
LEAN_EXPORT void l_Lean_Expr_isTrue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4876_ = stack[0].m_obj;
uint8_t v_res_4880_;
v_res_4880_ = l_Lean_Expr_isTrue(v_e_4876_);
stack->m_num = v_res_4880_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4881_){
_start:
{
uint8_t v_res_4882_; lean_object* v_r_4883_; 
v_res_4882_ = l_Lean_Expr_isTrue(v_e_4881_);
v_r_4883_ = lean_box(v_res_4882_);
return v_r_4883_;
}
}
uint8_t l_Lean_Expr_isBoolFalse(lean_object* v_e_4888_){
_start:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; uint8_t v___x_4891_; 
v___x_4889_ = l_Lean_Expr_cleanupAnnotations(v_e_4888_);
v___x_4890_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_4891_ = l_Lean_Expr_isConstOf(v___x_4889_, v___x_4890_);
lean_dec_ref(v___x_4889_);
return v___x_4891_;
}
}
LEAN_EXPORT void l_Lean_Expr_isBoolFalse_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4888_ = stack[0].m_obj;
uint8_t v_res_4892_;
v_res_4892_ = l_Lean_Expr_isBoolFalse(v_e_4888_);
stack->m_num = v_res_4892_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object* v_e_4893_){
_start:
{
uint8_t v_res_4894_; lean_object* v_r_4895_; 
v_res_4894_ = l_Lean_Expr_isBoolFalse(v_e_4893_);
v_r_4895_ = lean_box(v_res_4894_);
return v_r_4895_;
}
}
uint8_t l_Lean_Expr_isBoolTrue(lean_object* v_e_4899_){
_start:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; uint8_t v___x_4902_; 
v___x_4900_ = l_Lean_Expr_cleanupAnnotations(v_e_4899_);
v___x_4901_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_4902_ = l_Lean_Expr_isConstOf(v___x_4900_, v___x_4901_);
lean_dec_ref(v___x_4900_);
return v___x_4902_;
}
}
LEAN_EXPORT void l_Lean_Expr_isBoolTrue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4899_ = stack[0].m_obj;
uint8_t v_res_4903_;
v_res_4903_ = l_Lean_Expr_isBoolTrue(v_e_4899_);
stack->m_num = v_res_4903_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object* v_e_4904_){
_start:
{
uint8_t v_res_4905_; lean_object* v_r_4906_; 
v_res_4905_ = l_Lean_Expr_isBoolTrue(v_e_4904_);
v_r_4906_ = lean_box(v_res_4905_);
return v_r_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* v_x_4907_){
_start:
{
switch(lean_obj_tag(v_x_4907_))
{
case 10:
{
lean_object* v_expr_4908_; 
v_expr_4908_ = lean_ctor_get(v_x_4907_, 1);
lean_inc_ref(v_expr_4908_);
lean_dec_ref_known(v_x_4907_, 2);
v_x_4907_ = v_expr_4908_;
goto _start;
}
case 7:
{
lean_object* v_body_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; 
v_body_4910_ = lean_ctor_get(v_x_4907_, 2);
lean_inc_ref(v_body_4910_);
lean_dec_ref_known(v_x_4907_, 3);
v___x_4911_ = l_Lean_Expr_getForallArity(v_body_4910_);
v___x_4912_ = lean_unsigned_to_nat(1u);
v___x_4913_ = lean_nat_add(v___x_4911_, v___x_4912_);
lean_dec(v___x_4911_);
return v___x_4913_;
}
default: 
{
uint8_t v___x_4914_; uint8_t v___x_4915_; 
v___x_4914_ = 0;
v___x_4915_ = l_Lean_Expr_isHeadBetaTarget(v_x_4907_, v___x_4914_);
if (v___x_4915_ == 0)
{
lean_object* v_e_x27_4916_; uint8_t v___x_4917_; 
lean_inc_ref(v_x_4907_);
v_e_x27_4916_ = l_Lean_Expr_cleanupAnnotations(v_x_4907_);
v___x_4917_ = lean_expr_eqv(v_x_4907_, v_e_x27_4916_);
lean_dec_ref(v_x_4907_);
if (v___x_4917_ == 0)
{
v_x_4907_ = v_e_x27_4916_;
goto _start;
}
else
{
if (v___x_4915_ == 0)
{
lean_object* v___x_4919_; 
lean_dec_ref(v_e_x27_4916_);
v___x_4919_ = lean_unsigned_to_nat(0u);
return v___x_4919_;
}
else
{
v_x_4907_ = v_e_x27_4916_;
goto _start;
}
}
}
else
{
lean_object* v___x_4921_; 
v___x_4921_ = l_Lean_Expr_headBeta(v_x_4907_);
v_x_4907_ = v___x_4921_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4923_){
_start:
{
lean_object* v___x_4924_; uint8_t v___x_4925_; 
v___x_4924_ = l_Lean_Expr_cleanupAnnotations(v_e_4923_);
v___x_4925_ = l_Lean_Expr_isApp(v___x_4924_);
if (v___x_4925_ == 0)
{
lean_object* v___x_4926_; 
lean_dec_ref(v___x_4924_);
v___x_4926_ = lean_box(0);
return v___x_4926_;
}
else
{
lean_object* v___x_4927_; uint8_t v___x_4928_; 
v___x_4927_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4924_);
v___x_4928_ = l_Lean_Expr_isApp(v___x_4927_);
if (v___x_4928_ == 0)
{
lean_object* v___x_4929_; 
lean_dec_ref(v___x_4927_);
v___x_4929_ = lean_box(0);
return v___x_4929_;
}
else
{
lean_object* v_arg_4930_; lean_object* v___x_4931_; uint8_t v___x_4932_; 
v_arg_4930_ = lean_ctor_get(v___x_4927_, 1);
lean_inc_ref(v_arg_4930_);
v___x_4931_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4927_);
v___x_4932_ = l_Lean_Expr_isApp(v___x_4931_);
if (v___x_4932_ == 0)
{
lean_object* v___x_4933_; 
lean_dec_ref(v___x_4931_);
lean_dec_ref(v_arg_4930_);
v___x_4933_ = lean_box(0);
return v___x_4933_;
}
else
{
lean_object* v___x_4934_; lean_object* v___x_4935_; uint8_t v___x_4936_; 
v___x_4934_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4931_);
v___x_4935_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4936_ = l_Lean_Expr_isConstOf(v___x_4934_, v___x_4935_);
lean_dec_ref(v___x_4934_);
if (v___x_4936_ == 0)
{
lean_object* v___x_4937_; 
lean_dec_ref(v_arg_4930_);
v___x_4937_ = lean_box(0);
return v___x_4937_;
}
else
{
if (lean_obj_tag(v_arg_4930_) == 9)
{
lean_object* v_a_4938_; 
v_a_4938_ = lean_ctor_get(v_arg_4930_, 0);
lean_inc_ref(v_a_4938_);
lean_dec_ref_known(v_arg_4930_, 1);
if (lean_obj_tag(v_a_4938_) == 0)
{
lean_object* v_val_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_4946_; 
v_val_4939_ = lean_ctor_get(v_a_4938_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v_a_4938_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4941_ = v_a_4938_;
v_isShared_4942_ = v_isSharedCheck_4946_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_val_4939_);
lean_dec(v_a_4938_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_4946_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v___x_4944_; 
if (v_isShared_4942_ == 0)
{
lean_ctor_set_tag(v___x_4941_, 1);
v___x_4944_ = v___x_4941_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_val_4939_);
v___x_4944_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
return v___x_4944_;
}
}
}
else
{
lean_object* v___x_4947_; 
lean_dec_ref(v_a_4938_);
v___x_4947_ = lean_box(0);
return v___x_4947_;
}
}
else
{
lean_object* v___x_4948_; 
lean_dec_ref(v_arg_4930_);
v___x_4948_ = lean_box(0);
return v___x_4948_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4954_){
_start:
{
lean_object* v___x_4967_; uint8_t v___x_4968_; 
lean_inc_ref(v_e_4954_);
v___x_4967_ = l_Lean_Expr_cleanupAnnotations(v_e_4954_);
v___x_4968_ = l_Lean_Expr_isApp(v___x_4967_);
if (v___x_4968_ == 0)
{
lean_dec_ref(v___x_4967_);
goto v___jp_4955_;
}
else
{
lean_object* v_arg_4969_; lean_object* v___x_4970_; uint8_t v___x_4971_; 
v_arg_4969_ = lean_ctor_get(v___x_4967_, 1);
lean_inc_ref(v_arg_4969_);
v___x_4970_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4967_);
v___x_4971_ = l_Lean_Expr_isApp(v___x_4970_);
if (v___x_4971_ == 0)
{
lean_dec_ref(v___x_4970_);
lean_dec_ref(v_arg_4969_);
goto v___jp_4955_;
}
else
{
lean_object* v___x_4972_; uint8_t v___x_4973_; 
v___x_4972_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4970_);
v___x_4973_ = l_Lean_Expr_isApp(v___x_4972_);
if (v___x_4973_ == 0)
{
lean_dec_ref(v___x_4972_);
lean_dec_ref(v_arg_4969_);
goto v___jp_4955_;
}
else
{
lean_object* v___x_4974_; lean_object* v___x_4975_; uint8_t v___x_4976_; 
v___x_4974_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4972_);
v___x_4975_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4976_ = l_Lean_Expr_isConstOf(v___x_4974_, v___x_4975_);
lean_dec_ref(v___x_4974_);
if (v___x_4976_ == 0)
{
lean_dec_ref(v_arg_4969_);
goto v___jp_4955_;
}
else
{
lean_object* v___x_4977_; 
lean_dec_ref(v_e_4954_);
v___x_4977_ = l_Lean_Expr_nat_x3f(v_arg_4969_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v___x_4978_; 
v___x_4978_ = lean_box(0);
return v___x_4978_;
}
else
{
lean_object* v_val_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_4991_; 
v_val_4979_ = lean_ctor_get(v___x_4977_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4981_ = v___x_4977_;
v_isShared_4982_ = v_isSharedCheck_4991_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_val_4979_);
lean_dec(v___x_4977_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_4991_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v___x_4983_; uint8_t v___x_4984_; 
v___x_4983_ = lean_unsigned_to_nat(0u);
v___x_4984_ = lean_nat_dec_eq(v_val_4979_, v___x_4983_);
if (v___x_4984_ == 0)
{
lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4988_; 
v___x_4985_ = lean_nat_to_int(v_val_4979_);
v___x_4986_ = lean_int_neg(v___x_4985_);
lean_dec(v___x_4985_);
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 0, v___x_4986_);
v___x_4988_ = v___x_4981_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4986_);
v___x_4988_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
return v___x_4988_;
}
}
else
{
lean_object* v___x_4990_; 
lean_del_object(v___x_4981_);
lean_dec(v_val_4979_);
v___x_4990_ = lean_box(0);
return v___x_4990_;
}
}
}
}
}
}
}
v___jp_4955_:
{
lean_object* v___x_4956_; 
v___x_4956_ = l_Lean_Expr_nat_x3f(v_e_4954_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v___x_4957_; 
v___x_4957_ = lean_box(0);
return v___x_4957_;
}
else
{
lean_object* v_val_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4966_; 
v_val_4958_ = lean_ctor_get(v___x_4956_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4960_ = v___x_4956_;
v_isShared_4961_ = v_isSharedCheck_4966_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_val_4958_);
lean_dec(v___x_4956_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4966_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4962_; lean_object* v___x_4964_; 
v___x_4962_ = lean_nat_to_int(v_val_4958_);
if (v_isShared_4961_ == 0)
{
lean_ctor_set(v___x_4960_, 0, v___x_4962_);
v___x_4964_ = v___x_4960_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v___x_4962_);
v___x_4964_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
return v___x_4964_;
}
}
}
}
}
}
uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4992_, lean_object* v_e_4993_){
_start:
{
uint8_t v___x_4994_; lean_object* v_d_4996_; lean_object* v_b_4997_; 
v___x_4994_ = l_Lean_Expr_hasFVar(v_e_4993_);
if (v___x_4994_ == 0)
{
lean_dec_ref(v_e_4993_);
lean_dec_ref(v_p_4992_);
return v___x_4994_;
}
else
{
switch(lean_obj_tag(v_e_4993_))
{
case 7:
{
lean_object* v_binderType_5000_; lean_object* v_body_5001_; 
v_binderType_5000_ = lean_ctor_get(v_e_4993_, 1);
lean_inc_ref(v_binderType_5000_);
v_body_5001_ = lean_ctor_get(v_e_4993_, 2);
lean_inc_ref(v_body_5001_);
lean_dec_ref_known(v_e_4993_, 3);
v_d_4996_ = v_binderType_5000_;
v_b_4997_ = v_body_5001_;
goto v___jp_4995_;
}
case 6:
{
lean_object* v_binderType_5002_; lean_object* v_body_5003_; 
v_binderType_5002_ = lean_ctor_get(v_e_4993_, 1);
lean_inc_ref(v_binderType_5002_);
v_body_5003_ = lean_ctor_get(v_e_4993_, 2);
lean_inc_ref(v_body_5003_);
lean_dec_ref_known(v_e_4993_, 3);
v_d_4996_ = v_binderType_5002_;
v_b_4997_ = v_body_5003_;
goto v___jp_4995_;
}
case 10:
{
lean_object* v_expr_5004_; 
v_expr_5004_ = lean_ctor_get(v_e_4993_, 1);
lean_inc_ref(v_expr_5004_);
lean_dec_ref_known(v_e_4993_, 2);
v_e_4993_ = v_expr_5004_;
goto _start;
}
case 8:
{
lean_object* v_type_5006_; lean_object* v_value_5007_; lean_object* v_body_5008_; uint8_t v___x_5009_; 
v_type_5006_ = lean_ctor_get(v_e_4993_, 1);
lean_inc_ref(v_type_5006_);
v_value_5007_ = lean_ctor_get(v_e_4993_, 2);
lean_inc_ref(v_value_5007_);
v_body_5008_ = lean_ctor_get(v_e_4993_, 3);
lean_inc_ref(v_body_5008_);
lean_dec_ref_known(v_e_4993_, 4);
lean_inc_ref(v_p_4992_);
v___x_5009_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4992_, v_type_5006_);
if (v___x_5009_ == 0)
{
uint8_t v___x_5010_; 
lean_inc_ref(v_p_4992_);
v___x_5010_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4992_, v_value_5007_);
if (v___x_5010_ == 0)
{
v_e_4993_ = v_body_5008_;
goto _start;
}
else
{
lean_dec_ref(v_body_5008_);
lean_dec_ref(v_p_4992_);
return v___x_4994_;
}
}
else
{
lean_dec_ref(v_body_5008_);
lean_dec_ref(v_value_5007_);
lean_dec_ref(v_p_4992_);
return v___x_4994_;
}
}
case 5:
{
lean_object* v_fn_5012_; lean_object* v_arg_5013_; uint8_t v___x_5014_; 
v_fn_5012_ = lean_ctor_get(v_e_4993_, 0);
lean_inc_ref(v_fn_5012_);
v_arg_5013_ = lean_ctor_get(v_e_4993_, 1);
lean_inc_ref(v_arg_5013_);
lean_dec_ref_known(v_e_4993_, 2);
lean_inc_ref(v_p_4992_);
v___x_5014_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4992_, v_fn_5012_);
if (v___x_5014_ == 0)
{
v_e_4993_ = v_arg_5013_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5013_);
lean_dec_ref(v_p_4992_);
return v___x_4994_;
}
}
case 11:
{
lean_object* v_struct_5016_; 
v_struct_5016_ = lean_ctor_get(v_e_4993_, 2);
lean_inc_ref(v_struct_5016_);
lean_dec_ref_known(v_e_4993_, 3);
v_e_4993_ = v_struct_5016_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5018_; lean_object* v___x_5019_; uint8_t v___x_5020_; 
v_fvarId_5018_ = lean_ctor_get(v_e_4993_, 0);
lean_inc(v_fvarId_5018_);
lean_dec_ref_known(v_e_4993_, 1);
v___x_5019_ = lean_apply_1(v_p_4992_, v_fvarId_5018_);
v___x_5020_ = lean_unbox(v___x_5019_);
return v___x_5020_;
}
default: 
{
uint8_t v___x_5021_; 
lean_dec_ref(v_e_4993_);
lean_dec_ref(v_p_4992_);
v___x_5021_ = 0;
return v___x_5021_;
}
}
}
v___jp_4995_:
{
uint8_t v___x_4998_; 
lean_inc_ref(v_p_4992_);
v___x_4998_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4992_, v_d_4996_);
if (v___x_4998_ == 0)
{
v_e_4993_ = v_b_4997_;
goto _start;
}
else
{
lean_dec_ref(v_b_4997_);
lean_dec_ref(v_p_4992_);
return v___x_4994_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_4992_ = stack[0].m_obj;
lean_object* v_e_4993_ = stack[1].m_obj;
uint8_t v_res_5022_;
v_res_5022_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4992_, v_e_4993_);
stack->m_num = v_res_5022_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_5023_, lean_object* v_e_5024_){
_start:
{
uint8_t v_res_5025_; lean_object* v_r_5026_; 
v_res_5025_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_5023_, v_e_5024_);
v_r_5026_ = lean_box(v_res_5025_);
return v_r_5026_;
}
}
uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_5027_, lean_object* v_p_5028_){
_start:
{
uint8_t v___x_5029_; 
v___x_5029_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_5028_, v_e_5027_);
return v___x_5029_;
}
}
LEAN_EXPORT void l_Lean_Expr_hasAnyFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5027_ = stack[0].m_obj;
lean_object* v_p_5028_ = stack[1].m_obj;
uint8_t v_res_5030_;
v_res_5030_ = l_Lean_Expr_hasAnyFVar(v_e_5027_, v_p_5028_);
stack->m_num = v_res_5030_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_5031_, lean_object* v_p_5032_){
_start:
{
uint8_t v_res_5033_; lean_object* v_r_5034_; 
v_res_5033_ = l_Lean_Expr_hasAnyFVar(v_e_5031_, v_p_5032_);
v_r_5034_ = lean_box(v_res_5033_);
return v_r_5034_;
}
}
uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_5035_, lean_object* v_e_5036_){
_start:
{
uint8_t v___x_5037_; lean_object* v_d_5039_; lean_object* v_b_5040_; 
v___x_5037_ = l_Lean_Expr_hasFVar(v_e_5036_);
if (v___x_5037_ == 0)
{
return v___x_5037_;
}
else
{
switch(lean_obj_tag(v_e_5036_))
{
case 7:
{
lean_object* v_binderType_5043_; lean_object* v_body_5044_; 
v_binderType_5043_ = lean_ctor_get(v_e_5036_, 1);
v_body_5044_ = lean_ctor_get(v_e_5036_, 2);
v_d_5039_ = v_binderType_5043_;
v_b_5040_ = v_body_5044_;
goto v___jp_5038_;
}
case 6:
{
lean_object* v_binderType_5045_; lean_object* v_body_5046_; 
v_binderType_5045_ = lean_ctor_get(v_e_5036_, 1);
v_body_5046_ = lean_ctor_get(v_e_5036_, 2);
v_d_5039_ = v_binderType_5045_;
v_b_5040_ = v_body_5046_;
goto v___jp_5038_;
}
case 10:
{
lean_object* v_expr_5047_; 
v_expr_5047_ = lean_ctor_get(v_e_5036_, 1);
v_e_5036_ = v_expr_5047_;
goto _start;
}
case 8:
{
lean_object* v_type_5049_; lean_object* v_value_5050_; lean_object* v_body_5051_; uint8_t v___x_5052_; 
v_type_5049_ = lean_ctor_get(v_e_5036_, 1);
v_value_5050_ = lean_ctor_get(v_e_5036_, 2);
v_body_5051_ = lean_ctor_get(v_e_5036_, 3);
v___x_5052_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_5035_, v_type_5049_);
if (v___x_5052_ == 0)
{
uint8_t v___x_5053_; 
v___x_5053_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_5035_, v_value_5050_);
if (v___x_5053_ == 0)
{
v_e_5036_ = v_body_5051_;
goto _start;
}
else
{
return v___x_5037_;
}
}
else
{
return v___x_5037_;
}
}
case 5:
{
lean_object* v_fn_5055_; lean_object* v_arg_5056_; uint8_t v___x_5057_; 
v_fn_5055_ = lean_ctor_get(v_e_5036_, 0);
v_arg_5056_ = lean_ctor_get(v_e_5036_, 1);
v___x_5057_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_5035_, v_fn_5055_);
if (v___x_5057_ == 0)
{
v_e_5036_ = v_arg_5056_;
goto _start;
}
else
{
return v___x_5037_;
}
}
case 11:
{
lean_object* v_struct_5059_; 
v_struct_5059_ = lean_ctor_get(v_e_5036_, 2);
v_e_5036_ = v_struct_5059_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5061_; uint8_t v___x_5062_; 
v_fvarId_5061_ = lean_ctor_get(v_e_5036_, 0);
v___x_5062_ = lean_name_eq(v_fvarId_5061_, v_fvarId_5035_);
return v___x_5062_;
}
default: 
{
uint8_t v___x_5063_; 
v___x_5063_ = 0;
return v___x_5063_;
}
}
}
v___jp_5038_:
{
uint8_t v___x_5041_; 
v___x_5041_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_5035_, v_d_5039_);
if (v___x_5041_ == 0)
{
v_e_5036_ = v_b_5040_;
goto _start;
}
else
{
return v___x_5037_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_5035_ = stack[0].m_obj;
lean_object* v_e_5036_ = stack[1].m_obj;
uint8_t v_res_5064_;
v_res_5064_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_5035_, v_e_5036_);
stack->m_num = v_res_5064_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_5065_, lean_object* v_e_5066_){
_start:
{
uint8_t v_res_5067_; lean_object* v_r_5068_; 
v_res_5067_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_5065_, v_e_5066_);
lean_dec_ref(v_e_5066_);
lean_dec(v_fvarId_5065_);
v_r_5068_ = lean_box(v_res_5067_);
return v_r_5068_;
}
}
uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_5069_, lean_object* v_fvarId_5070_){
_start:
{
uint8_t v___x_5071_; 
v___x_5071_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_5070_, v_e_5069_);
return v___x_5071_;
}
}
LEAN_EXPORT void l_Lean_Expr_containsFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5069_ = stack[0].m_obj;
lean_object* v_fvarId_5070_ = stack[1].m_obj;
uint8_t v_res_5072_;
v_res_5072_ = l_Lean_Expr_containsFVar(v_e_5069_, v_fvarId_5070_);
stack->m_num = v_res_5072_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_5073_, lean_object* v_fvarId_5074_){
_start:
{
uint8_t v_res_5075_; lean_object* v_r_5076_; 
v_res_5075_ = l_Lean_Expr_containsFVar(v_e_5073_, v_fvarId_5074_);
lean_dec(v_fvarId_5074_);
lean_dec_ref(v_e_5073_);
v_r_5076_ = lean_box(v_res_5075_);
return v_r_5076_;
}
}
uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(lean_object* v_p_5077_, lean_object* v_e_5078_){
_start:
{
uint8_t v___x_5079_; lean_object* v_d_5081_; lean_object* v_b_5082_; 
v___x_5079_ = l_Lean_Expr_hasExprMVar(v_e_5078_);
if (v___x_5079_ == 0)
{
lean_dec_ref(v_e_5078_);
lean_dec_ref(v_p_5077_);
return v___x_5079_;
}
else
{
switch(lean_obj_tag(v_e_5078_))
{
case 7:
{
lean_object* v_binderType_5085_; lean_object* v_body_5086_; 
v_binderType_5085_ = lean_ctor_get(v_e_5078_, 1);
lean_inc_ref(v_binderType_5085_);
v_body_5086_ = lean_ctor_get(v_e_5078_, 2);
lean_inc_ref(v_body_5086_);
lean_dec_ref_known(v_e_5078_, 3);
v_d_5081_ = v_binderType_5085_;
v_b_5082_ = v_body_5086_;
goto v___jp_5080_;
}
case 6:
{
lean_object* v_binderType_5087_; lean_object* v_body_5088_; 
v_binderType_5087_ = lean_ctor_get(v_e_5078_, 1);
lean_inc_ref(v_binderType_5087_);
v_body_5088_ = lean_ctor_get(v_e_5078_, 2);
lean_inc_ref(v_body_5088_);
lean_dec_ref_known(v_e_5078_, 3);
v_d_5081_ = v_binderType_5087_;
v_b_5082_ = v_body_5088_;
goto v___jp_5080_;
}
case 10:
{
lean_object* v_expr_5089_; 
v_expr_5089_ = lean_ctor_get(v_e_5078_, 1);
lean_inc_ref(v_expr_5089_);
lean_dec_ref_known(v_e_5078_, 2);
v_e_5078_ = v_expr_5089_;
goto _start;
}
case 8:
{
lean_object* v_type_5091_; lean_object* v_value_5092_; lean_object* v_body_5093_; uint8_t v___x_5094_; 
v_type_5091_ = lean_ctor_get(v_e_5078_, 1);
lean_inc_ref(v_type_5091_);
v_value_5092_ = lean_ctor_get(v_e_5078_, 2);
lean_inc_ref(v_value_5092_);
v_body_5093_ = lean_ctor_get(v_e_5078_, 3);
lean_inc_ref(v_body_5093_);
lean_dec_ref_known(v_e_5078_, 4);
lean_inc_ref(v_p_5077_);
v___x_5094_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_5077_, v_type_5091_);
if (v___x_5094_ == 0)
{
uint8_t v___x_5095_; 
lean_inc_ref(v_p_5077_);
v___x_5095_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_5077_, v_value_5092_);
if (v___x_5095_ == 0)
{
v_e_5078_ = v_body_5093_;
goto _start;
}
else
{
lean_dec_ref(v_body_5093_);
lean_dec_ref(v_p_5077_);
return v___x_5079_;
}
}
else
{
lean_dec_ref(v_body_5093_);
lean_dec_ref(v_value_5092_);
lean_dec_ref(v_p_5077_);
return v___x_5079_;
}
}
case 5:
{
lean_object* v_fn_5097_; lean_object* v_arg_5098_; uint8_t v___x_5099_; 
v_fn_5097_ = lean_ctor_get(v_e_5078_, 0);
lean_inc_ref(v_fn_5097_);
v_arg_5098_ = lean_ctor_get(v_e_5078_, 1);
lean_inc_ref(v_arg_5098_);
lean_dec_ref_known(v_e_5078_, 2);
lean_inc_ref(v_p_5077_);
v___x_5099_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_5077_, v_fn_5097_);
if (v___x_5099_ == 0)
{
v_e_5078_ = v_arg_5098_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5098_);
lean_dec_ref(v_p_5077_);
return v___x_5079_;
}
}
case 11:
{
lean_object* v_struct_5101_; 
v_struct_5101_ = lean_ctor_get(v_e_5078_, 2);
lean_inc_ref(v_struct_5101_);
lean_dec_ref_known(v_e_5078_, 3);
v_e_5078_ = v_struct_5101_;
goto _start;
}
case 2:
{
lean_object* v_mvarId_5103_; lean_object* v___x_5104_; uint8_t v___x_5105_; 
v_mvarId_5103_ = lean_ctor_get(v_e_5078_, 0);
lean_inc(v_mvarId_5103_);
lean_dec_ref_known(v_e_5078_, 1);
v___x_5104_ = lean_apply_1(v_p_5077_, v_mvarId_5103_);
v___x_5105_ = lean_unbox(v___x_5104_);
return v___x_5105_;
}
default: 
{
uint8_t v___x_5106_; 
lean_dec_ref(v_e_5078_);
lean_dec_ref(v_p_5077_);
v___x_5106_ = 0;
return v___x_5106_;
}
}
}
v___jp_5080_:
{
uint8_t v___x_5083_; 
lean_inc_ref(v_p_5077_);
v___x_5083_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_5077_, v_d_5081_);
if (v___x_5083_ == 0)
{
v_e_5078_ = v_b_5082_;
goto _start;
}
else
{
lean_dec_ref(v_b_5082_);
lean_dec_ref(v_p_5077_);
return v___x_5079_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_5077_ = stack[0].m_obj;
lean_object* v_e_5078_ = stack[1].m_obj;
uint8_t v_res_5107_;
v_res_5107_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_5077_, v_e_5078_);
stack->m_num = v_res_5107_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___boxed(lean_object* v_p_5108_, lean_object* v_e_5109_){
_start:
{
uint8_t v_res_5110_; lean_object* v_r_5111_; 
v_res_5110_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_5108_, v_e_5109_);
v_r_5111_ = lean_box(v_res_5110_);
return v_r_5111_;
}
}
uint8_t l_Lean_Expr_hasAnyMVar(lean_object* v_e_5112_, lean_object* v_p_5113_){
_start:
{
uint8_t v___x_5114_; 
v___x_5114_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_5113_, v_e_5112_);
return v___x_5114_;
}
}
LEAN_EXPORT void l_Lean_Expr_hasAnyMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5112_ = stack[0].m_obj;
lean_object* v_p_5113_ = stack[1].m_obj;
uint8_t v_res_5115_;
v_res_5115_ = l_Lean_Expr_hasAnyMVar(v_e_5112_, v_p_5113_);
stack->m_num = v_res_5115_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyMVar___boxed(lean_object* v_e_5116_, lean_object* v_p_5117_){
_start:
{
uint8_t v_res_5118_; lean_object* v_r_5119_; 
v_res_5118_ = l_Lean_Expr_hasAnyMVar(v_e_5116_, v_p_5117_);
v_r_5119_ = lean_box(v_res_5118_);
return v_r_5119_;
}
}
uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(lean_object* v_mvarId_5120_, lean_object* v_e_5121_){
_start:
{
uint8_t v___x_5122_; lean_object* v_d_5124_; lean_object* v_b_5125_; 
v___x_5122_ = l_Lean_Expr_hasExprMVar(v_e_5121_);
if (v___x_5122_ == 0)
{
return v___x_5122_;
}
else
{
switch(lean_obj_tag(v_e_5121_))
{
case 7:
{
lean_object* v_binderType_5128_; lean_object* v_body_5129_; 
v_binderType_5128_ = lean_ctor_get(v_e_5121_, 1);
v_body_5129_ = lean_ctor_get(v_e_5121_, 2);
v_d_5124_ = v_binderType_5128_;
v_b_5125_ = v_body_5129_;
goto v___jp_5123_;
}
case 6:
{
lean_object* v_binderType_5130_; lean_object* v_body_5131_; 
v_binderType_5130_ = lean_ctor_get(v_e_5121_, 1);
v_body_5131_ = lean_ctor_get(v_e_5121_, 2);
v_d_5124_ = v_binderType_5130_;
v_b_5125_ = v_body_5131_;
goto v___jp_5123_;
}
case 10:
{
lean_object* v_expr_5132_; 
v_expr_5132_ = lean_ctor_get(v_e_5121_, 1);
v_e_5121_ = v_expr_5132_;
goto _start;
}
case 8:
{
lean_object* v_type_5134_; lean_object* v_value_5135_; lean_object* v_body_5136_; uint8_t v___x_5137_; 
v_type_5134_ = lean_ctor_get(v_e_5121_, 1);
v_value_5135_ = lean_ctor_get(v_e_5121_, 2);
v_body_5136_ = lean_ctor_get(v_e_5121_, 3);
v___x_5137_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5120_, v_type_5134_);
if (v___x_5137_ == 0)
{
uint8_t v___x_5138_; 
v___x_5138_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5120_, v_value_5135_);
if (v___x_5138_ == 0)
{
v_e_5121_ = v_body_5136_;
goto _start;
}
else
{
return v___x_5122_;
}
}
else
{
return v___x_5122_;
}
}
case 5:
{
lean_object* v_fn_5140_; lean_object* v_arg_5141_; uint8_t v___x_5142_; 
v_fn_5140_ = lean_ctor_get(v_e_5121_, 0);
v_arg_5141_ = lean_ctor_get(v_e_5121_, 1);
v___x_5142_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5120_, v_fn_5140_);
if (v___x_5142_ == 0)
{
v_e_5121_ = v_arg_5141_;
goto _start;
}
else
{
return v___x_5122_;
}
}
case 11:
{
lean_object* v_struct_5144_; 
v_struct_5144_ = lean_ctor_get(v_e_5121_, 2);
v_e_5121_ = v_struct_5144_;
goto _start;
}
case 2:
{
lean_object* v_mvarId_5146_; uint8_t v___x_5147_; 
v_mvarId_5146_ = lean_ctor_get(v_e_5121_, 0);
v___x_5147_ = lean_name_eq(v_mvarId_5146_, v_mvarId_5120_);
return v___x_5147_;
}
default: 
{
uint8_t v___x_5148_; 
v___x_5148_ = 0;
return v___x_5148_;
}
}
}
v___jp_5123_:
{
uint8_t v___x_5126_; 
v___x_5126_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5120_, v_d_5124_);
if (v___x_5126_ == 0)
{
v_e_5121_ = v_b_5125_;
goto _start;
}
else
{
return v___x_5122_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_5120_ = stack[0].m_obj;
lean_object* v_e_5121_ = stack[1].m_obj;
uint8_t v_res_5149_;
v_res_5149_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5120_, v_e_5121_);
stack->m_num = v_res_5149_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0___boxed(lean_object* v_mvarId_5150_, lean_object* v_e_5151_){
_start:
{
uint8_t v_res_5152_; lean_object* v_r_5153_; 
v_res_5152_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5150_, v_e_5151_);
lean_dec_ref(v_e_5151_);
lean_dec(v_mvarId_5150_);
v_r_5153_ = lean_box(v_res_5152_);
return v_r_5153_;
}
}
uint8_t l_Lean_Expr_containsMVar(lean_object* v_e_5154_, lean_object* v_mvarId_5155_){
_start:
{
uint8_t v___x_5156_; 
v___x_5156_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5155_, v_e_5154_);
return v___x_5156_;
}
}
LEAN_EXPORT void l_Lean_Expr_containsMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5154_ = stack[0].m_obj;
lean_object* v_mvarId_5155_ = stack[1].m_obj;
uint8_t v_res_5157_;
v_res_5157_ = l_Lean_Expr_containsMVar(v_e_5154_, v_mvarId_5155_);
stack->m_num = v_res_5157_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsMVar___boxed(lean_object* v_e_5158_, lean_object* v_mvarId_5159_){
_start:
{
uint8_t v_res_5160_; lean_object* v_r_5161_; 
v_res_5160_ = l_Lean_Expr_containsMVar(v_e_5158_, v_mvarId_5159_);
lean_dec(v_mvarId_5159_);
lean_dec_ref(v_e_5158_);
v_r_5161_ = lean_box(v_res_5160_);
return v_r_5161_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; 
v___x_5163_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_5164_ = lean_unsigned_to_nat(18u);
v___x_5165_ = lean_unsigned_to_nat(1864u);
v___x_5166_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_5167_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5168_ = l_mkPanicMessageWithDecl(v___x_5167_, v___x_5166_, v___x_5165_, v___x_5164_, v___x_5163_);
return v___x_5168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_5169_, lean_object* v_newFn_5170_, lean_object* v_newArg_5171_){
_start:
{
if (lean_obj_tag(v_e_5169_) == 5)
{
lean_object* v_fn_5172_; lean_object* v_arg_5173_; size_t v___x_5174_; size_t v___x_5175_; uint8_t v___x_5176_; 
v_fn_5172_ = lean_ctor_get(v_e_5169_, 0);
v_arg_5173_ = lean_ctor_get(v_e_5169_, 1);
v___x_5174_ = lean_ptr_addr(v_fn_5172_);
v___x_5175_ = lean_ptr_addr(v_newFn_5170_);
v___x_5176_ = lean_usize_dec_eq(v___x_5174_, v___x_5175_);
if (v___x_5176_ == 0)
{
lean_object* v___x_5177_; 
v___x_5177_ = l_Lean_Expr_app___override(v_newFn_5170_, v_newArg_5171_);
return v___x_5177_;
}
else
{
size_t v___x_5178_; size_t v___x_5179_; uint8_t v___x_5180_; 
v___x_5178_ = lean_ptr_addr(v_arg_5173_);
v___x_5179_ = lean_ptr_addr(v_newArg_5171_);
v___x_5180_ = lean_usize_dec_eq(v___x_5178_, v___x_5179_);
if (v___x_5180_ == 0)
{
lean_object* v___x_5181_; 
v___x_5181_ = l_Lean_Expr_app___override(v_newFn_5170_, v_newArg_5171_);
return v___x_5181_;
}
else
{
lean_dec_ref(v_newArg_5171_);
lean_dec_ref(v_newFn_5170_);
lean_inc_ref(v_e_5169_);
return v_e_5169_;
}
}
}
else
{
lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; 
lean_dec_ref(v_newArg_5171_);
lean_dec_ref(v_newFn_5170_);
v___x_5182_ = l_Lean_instInhabitedExpr;
v___x_5183_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_5184_ = l_panic___redArg(v___x_5182_, v___x_5183_);
return v___x_5184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_5185_, lean_object* v_newFn_5186_, lean_object* v_newArg_5187_){
_start:
{
lean_object* v_res_5188_; 
v_res_5188_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_5185_, v_newFn_5186_, v_newArg_5187_);
lean_dec_ref(v_e_5185_);
return v_res_5188_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; 
v___x_5190_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_5191_ = lean_unsigned_to_nat(20u);
v___x_5192_ = lean_unsigned_to_nat(1875u);
v___x_5193_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_5194_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5195_ = l_mkPanicMessageWithDecl(v___x_5194_, v___x_5193_, v___x_5192_, v___x_5191_, v___x_5190_);
return v___x_5195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_5196_, lean_object* v_fvarIdNew_5197_){
_start:
{
if (lean_obj_tag(v_e_5196_) == 1)
{
lean_object* v_fvarId_5198_; uint8_t v___x_5199_; 
v_fvarId_5198_ = lean_ctor_get(v_e_5196_, 0);
v___x_5199_ = lean_name_eq(v_fvarId_5198_, v_fvarIdNew_5197_);
if (v___x_5199_ == 0)
{
lean_object* v___x_5200_; 
v___x_5200_ = l_Lean_Expr_fvar___override(v_fvarIdNew_5197_);
return v___x_5200_;
}
else
{
lean_dec(v_fvarIdNew_5197_);
lean_inc_ref(v_e_5196_);
return v_e_5196_;
}
}
else
{
lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; 
lean_dec(v_fvarIdNew_5197_);
v___x_5201_ = l_Lean_instInhabitedExpr;
v___x_5202_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_5203_ = l_panic___redArg(v___x_5201_, v___x_5202_);
return v___x_5203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_5204_, lean_object* v_fvarIdNew_5205_){
_start:
{
lean_object* v_res_5206_; 
v_res_5206_ = l_Lean_Expr_updateFVar_x21(v_e_5204_, v_fvarIdNew_5205_);
lean_dec_ref(v_e_5204_);
return v_res_5206_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; 
v___x_5208_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_5209_ = lean_unsigned_to_nat(18u);
v___x_5210_ = lean_unsigned_to_nat(1880u);
v___x_5211_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_5212_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5213_ = l_mkPanicMessageWithDecl(v___x_5212_, v___x_5211_, v___x_5210_, v___x_5209_, v___x_5208_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_5214_, lean_object* v_newLevels_5215_){
_start:
{
if (lean_obj_tag(v_e_5214_) == 4)
{
lean_object* v_declName_5216_; lean_object* v_us_5217_; uint8_t v___x_5218_; 
v_declName_5216_ = lean_ctor_get(v_e_5214_, 0);
v_us_5217_ = lean_ctor_get(v_e_5214_, 1);
v___x_5218_ = l_ptrEqList___redArg(v_us_5217_, v_newLevels_5215_);
if (v___x_5218_ == 0)
{
lean_object* v___x_5219_; 
lean_inc(v_declName_5216_);
lean_dec_ref_known(v_e_5214_, 2);
v___x_5219_ = l_Lean_Expr_const___override(v_declName_5216_, v_newLevels_5215_);
return v___x_5219_;
}
else
{
lean_dec(v_newLevels_5215_);
return v_e_5214_;
}
}
else
{
lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; 
lean_dec(v_newLevels_5215_);
lean_dec_ref(v_e_5214_);
v___x_5220_ = l_Lean_instInhabitedExpr;
v___x_5221_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_5222_ = l_panic___redArg(v___x_5220_, v___x_5221_);
return v___x_5222_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; 
v___x_5225_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_5226_ = lean_unsigned_to_nat(14u);
v___x_5227_ = lean_unsigned_to_nat(1891u);
v___x_5228_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_5229_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5230_ = l_mkPanicMessageWithDecl(v___x_5229_, v___x_5228_, v___x_5227_, v___x_5226_, v___x_5225_);
return v___x_5230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_5231_, lean_object* v_u_x27_5232_){
_start:
{
if (lean_obj_tag(v_e_5231_) == 3)
{
lean_object* v_u_5233_; size_t v___x_5234_; size_t v___x_5235_; uint8_t v___x_5236_; 
v_u_5233_ = lean_ctor_get(v_e_5231_, 0);
v___x_5234_ = lean_ptr_addr(v_u_5233_);
v___x_5235_ = lean_ptr_addr(v_u_x27_5232_);
v___x_5236_ = lean_usize_dec_eq(v___x_5234_, v___x_5235_);
if (v___x_5236_ == 0)
{
lean_object* v___x_5237_; 
v___x_5237_ = l_Lean_Expr_sort___override(v_u_x27_5232_);
return v___x_5237_;
}
else
{
lean_dec(v_u_x27_5232_);
lean_inc_ref(v_e_5231_);
return v_e_5231_;
}
}
else
{
lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; 
lean_dec(v_u_x27_5232_);
v___x_5238_ = l_Lean_instInhabitedExpr;
v___x_5239_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_5240_ = l_panic___redArg(v___x_5238_, v___x_5239_);
return v___x_5240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_5241_, lean_object* v_u_x27_5242_){
_start:
{
lean_object* v_res_5243_; 
v_res_5243_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_5241_, v_u_x27_5242_);
lean_dec_ref(v_e_5241_);
return v_res_5243_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; 
v___x_5246_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_5247_ = lean_unsigned_to_nat(17u);
v___x_5248_ = lean_unsigned_to_nat(1902u);
v___x_5249_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_5250_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5251_ = l_mkPanicMessageWithDecl(v___x_5250_, v___x_5249_, v___x_5248_, v___x_5247_, v___x_5246_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_5252_, lean_object* v_newExpr_5253_){
_start:
{
if (lean_obj_tag(v_e_5252_) == 10)
{
lean_object* v_data_5254_; lean_object* v_expr_5255_; size_t v___x_5256_; size_t v___x_5257_; uint8_t v___x_5258_; 
v_data_5254_ = lean_ctor_get(v_e_5252_, 0);
v_expr_5255_ = lean_ctor_get(v_e_5252_, 1);
v___x_5256_ = lean_ptr_addr(v_expr_5255_);
v___x_5257_ = lean_ptr_addr(v_newExpr_5253_);
v___x_5258_ = lean_usize_dec_eq(v___x_5256_, v___x_5257_);
if (v___x_5258_ == 0)
{
lean_object* v___x_5259_; 
lean_inc(v_data_5254_);
lean_dec_ref_known(v_e_5252_, 2);
v___x_5259_ = l_Lean_Expr_mdata___override(v_data_5254_, v_newExpr_5253_);
return v___x_5259_;
}
else
{
lean_dec_ref(v_newExpr_5253_);
return v_e_5252_;
}
}
else
{
lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; 
lean_dec_ref(v_newExpr_5253_);
lean_dec_ref(v_e_5252_);
v___x_5260_ = l_Lean_instInhabitedExpr;
v___x_5261_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_5262_ = l_panic___redArg(v___x_5260_, v___x_5261_);
return v___x_5262_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; 
v___x_5265_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_5266_ = lean_unsigned_to_nat(18u);
v___x_5267_ = lean_unsigned_to_nat(1913u);
v___x_5268_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_5269_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5270_ = l_mkPanicMessageWithDecl(v___x_5269_, v___x_5268_, v___x_5267_, v___x_5266_, v___x_5265_);
return v___x_5270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_5271_, lean_object* v_newExpr_5272_){
_start:
{
if (lean_obj_tag(v_e_5271_) == 11)
{
lean_object* v_typeName_5273_; lean_object* v_idx_5274_; lean_object* v_struct_5275_; size_t v___x_5276_; size_t v___x_5277_; uint8_t v___x_5278_; 
v_typeName_5273_ = lean_ctor_get(v_e_5271_, 0);
v_idx_5274_ = lean_ctor_get(v_e_5271_, 1);
v_struct_5275_ = lean_ctor_get(v_e_5271_, 2);
v___x_5276_ = lean_ptr_addr(v_struct_5275_);
v___x_5277_ = lean_ptr_addr(v_newExpr_5272_);
v___x_5278_ = lean_usize_dec_eq(v___x_5276_, v___x_5277_);
if (v___x_5278_ == 0)
{
lean_object* v___x_5279_; 
lean_inc(v_idx_5274_);
lean_inc(v_typeName_5273_);
lean_dec_ref_known(v_e_5271_, 3);
v___x_5279_ = l_Lean_Expr_proj___override(v_typeName_5273_, v_idx_5274_, v_newExpr_5272_);
return v___x_5279_;
}
else
{
lean_dec_ref(v_newExpr_5272_);
return v_e_5271_;
}
}
else
{
lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; 
lean_dec_ref(v_newExpr_5272_);
lean_dec_ref(v_e_5271_);
v___x_5280_ = l_Lean_instInhabitedExpr;
v___x_5281_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_5282_ = l_panic___redArg(v___x_5280_, v___x_5281_);
return v___x_5282_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; 
v___x_5285_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5286_ = lean_unsigned_to_nat(23u);
v___x_5287_ = lean_unsigned_to_nat(1928u);
v___x_5288_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_5289_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5290_ = l_mkPanicMessageWithDecl(v___x_5289_, v___x_5288_, v___x_5287_, v___x_5286_, v___x_5285_);
return v___x_5290_;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_5291_, uint8_t v_newBinfo_5292_, lean_object* v_newDomain_5293_, lean_object* v_newBody_5294_){
_start:
{
if (lean_obj_tag(v_e_5291_) == 7)
{
lean_object* v_binderName_5295_; lean_object* v_binderType_5296_; lean_object* v_body_5297_; uint8_t v_binderInfo_5298_; size_t v___x_5299_; size_t v___x_5300_; uint8_t v___x_5301_; 
v_binderName_5295_ = lean_ctor_get(v_e_5291_, 0);
v_binderType_5296_ = lean_ctor_get(v_e_5291_, 1);
v_body_5297_ = lean_ctor_get(v_e_5291_, 2);
v_binderInfo_5298_ = lean_ctor_get_uint8(v_e_5291_, sizeof(void*)*3 + 8);
v___x_5299_ = lean_ptr_addr(v_binderType_5296_);
v___x_5300_ = lean_ptr_addr(v_newDomain_5293_);
v___x_5301_ = lean_usize_dec_eq(v___x_5299_, v___x_5300_);
if (v___x_5301_ == 0)
{
lean_object* v___x_5302_; 
lean_inc(v_binderName_5295_);
lean_dec_ref_known(v_e_5291_, 3);
v___x_5302_ = l_Lean_Expr_forallE___override(v_binderName_5295_, v_newDomain_5293_, v_newBody_5294_, v_newBinfo_5292_);
return v___x_5302_;
}
else
{
size_t v___x_5303_; size_t v___x_5304_; uint8_t v___x_5305_; 
v___x_5303_ = lean_ptr_addr(v_body_5297_);
v___x_5304_ = lean_ptr_addr(v_newBody_5294_);
v___x_5305_ = lean_usize_dec_eq(v___x_5303_, v___x_5304_);
if (v___x_5305_ == 0)
{
lean_object* v___x_5306_; 
lean_inc(v_binderName_5295_);
lean_dec_ref_known(v_e_5291_, 3);
v___x_5306_ = l_Lean_Expr_forallE___override(v_binderName_5295_, v_newDomain_5293_, v_newBody_5294_, v_newBinfo_5292_);
return v___x_5306_;
}
else
{
uint8_t v___x_5307_; 
v___x_5307_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5298_, v_newBinfo_5292_);
if (v___x_5307_ == 0)
{
lean_object* v___x_5308_; 
lean_inc(v_binderName_5295_);
lean_dec_ref_known(v_e_5291_, 3);
v___x_5308_ = l_Lean_Expr_forallE___override(v_binderName_5295_, v_newDomain_5293_, v_newBody_5294_, v_newBinfo_5292_);
return v___x_5308_;
}
else
{
lean_dec_ref(v_newBody_5294_);
lean_dec_ref(v_newDomain_5293_);
return v_e_5291_;
}
}
}
}
else
{
lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; 
lean_dec_ref(v_newBody_5294_);
lean_dec_ref(v_newDomain_5293_);
lean_dec_ref(v_e_5291_);
v___x_5309_ = l_Lean_instInhabitedExpr;
v___x_5310_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_5311_ = l_panic___redArg(v___x_5309_, v___x_5310_);
return v___x_5311_;
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5291_ = stack[0].m_obj;
uint8_t v_newBinfo_5292_ = stack[1].m_num;
lean_object* v_newDomain_5293_ = stack[2].m_obj;
lean_object* v_newBody_5294_ = stack[3].m_obj;
lean_object* v_res_5312_;
v_res_5312_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5291_, v_newBinfo_5292_, v_newDomain_5293_, v_newBody_5294_);
stack->m_obj
 = v_res_5312_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_5313_, lean_object* v_newBinfo_5314_, lean_object* v_newDomain_5315_, lean_object* v_newBody_5316_){
_start:
{
uint8_t v_newBinfo_boxed_5317_; lean_object* v_res_5318_; 
v_newBinfo_boxed_5317_ = lean_unbox(v_newBinfo_5314_);
v_res_5318_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5313_, v_newBinfo_boxed_5317_, v_newDomain_5315_, v_newBody_5316_);
return v_res_5318_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; 
v___x_5320_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5321_ = lean_unsigned_to_nat(24u);
v___x_5322_ = lean_unsigned_to_nat(1939u);
v___x_5323_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_5324_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5325_ = l_mkPanicMessageWithDecl(v___x_5324_, v___x_5323_, v___x_5322_, v___x_5321_, v___x_5320_);
return v___x_5325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_5326_, lean_object* v_newDomain_5327_, lean_object* v_newBody_5328_){
_start:
{
if (lean_obj_tag(v_e_5326_) == 7)
{
lean_object* v_binderName_5329_; lean_object* v_binderType_5330_; lean_object* v_body_5331_; uint8_t v_binderInfo_5332_; size_t v___x_5333_; size_t v___x_5334_; uint8_t v___x_5335_; 
v_binderName_5329_ = lean_ctor_get(v_e_5326_, 0);
v_binderType_5330_ = lean_ctor_get(v_e_5326_, 1);
v_body_5331_ = lean_ctor_get(v_e_5326_, 2);
v_binderInfo_5332_ = lean_ctor_get_uint8(v_e_5326_, sizeof(void*)*3 + 8);
v___x_5333_ = lean_ptr_addr(v_binderType_5330_);
v___x_5334_ = lean_ptr_addr(v_newDomain_5327_);
v___x_5335_ = lean_usize_dec_eq(v___x_5333_, v___x_5334_);
if (v___x_5335_ == 0)
{
lean_object* v___x_5336_; 
lean_inc(v_binderName_5329_);
lean_dec_ref_known(v_e_5326_, 3);
v___x_5336_ = l_Lean_Expr_forallE___override(v_binderName_5329_, v_newDomain_5327_, v_newBody_5328_, v_binderInfo_5332_);
return v___x_5336_;
}
else
{
size_t v___x_5337_; size_t v___x_5338_; uint8_t v___x_5339_; 
v___x_5337_ = lean_ptr_addr(v_body_5331_);
v___x_5338_ = lean_ptr_addr(v_newBody_5328_);
v___x_5339_ = lean_usize_dec_eq(v___x_5337_, v___x_5338_);
if (v___x_5339_ == 0)
{
lean_object* v___x_5340_; 
lean_inc(v_binderName_5329_);
lean_dec_ref_known(v_e_5326_, 3);
v___x_5340_ = l_Lean_Expr_forallE___override(v_binderName_5329_, v_newDomain_5327_, v_newBody_5328_, v_binderInfo_5332_);
return v___x_5340_;
}
else
{
uint8_t v___x_5341_; 
v___x_5341_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5332_, v_binderInfo_5332_);
if (v___x_5341_ == 0)
{
lean_object* v___x_5342_; 
lean_inc(v_binderName_5329_);
lean_dec_ref_known(v_e_5326_, 3);
v___x_5342_ = l_Lean_Expr_forallE___override(v_binderName_5329_, v_newDomain_5327_, v_newBody_5328_, v_binderInfo_5332_);
return v___x_5342_;
}
else
{
lean_dec_ref(v_newBody_5328_);
lean_dec_ref(v_newDomain_5327_);
return v_e_5326_;
}
}
}
}
else
{
lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; 
lean_dec_ref(v_newBody_5328_);
lean_dec_ref(v_newDomain_5327_);
lean_dec_ref(v_e_5326_);
v___x_5343_ = l_Lean_instInhabitedExpr;
v___x_5344_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_5345_ = l_panic___redArg(v___x_5343_, v___x_5344_);
return v___x_5345_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; 
v___x_5348_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5349_ = lean_unsigned_to_nat(19u);
v___x_5350_ = lean_unsigned_to_nat(1948u);
v___x_5351_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_5352_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5353_ = l_mkPanicMessageWithDecl(v___x_5352_, v___x_5351_, v___x_5350_, v___x_5349_, v___x_5348_);
return v___x_5353_;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_5354_, uint8_t v_newBinfo_5355_, lean_object* v_newDomain_5356_, lean_object* v_newBody_5357_){
_start:
{
if (lean_obj_tag(v_e_5354_) == 6)
{
lean_object* v_binderName_5358_; lean_object* v_binderType_5359_; lean_object* v_body_5360_; uint8_t v_binderInfo_5361_; size_t v___x_5362_; size_t v___x_5363_; uint8_t v___x_5364_; 
v_binderName_5358_ = lean_ctor_get(v_e_5354_, 0);
v_binderType_5359_ = lean_ctor_get(v_e_5354_, 1);
v_body_5360_ = lean_ctor_get(v_e_5354_, 2);
v_binderInfo_5361_ = lean_ctor_get_uint8(v_e_5354_, sizeof(void*)*3 + 8);
v___x_5362_ = lean_ptr_addr(v_binderType_5359_);
v___x_5363_ = lean_ptr_addr(v_newDomain_5356_);
v___x_5364_ = lean_usize_dec_eq(v___x_5362_, v___x_5363_);
if (v___x_5364_ == 0)
{
lean_object* v___x_5365_; 
lean_inc(v_binderName_5358_);
lean_dec_ref_known(v_e_5354_, 3);
v___x_5365_ = l_Lean_Expr_lam___override(v_binderName_5358_, v_newDomain_5356_, v_newBody_5357_, v_newBinfo_5355_);
return v___x_5365_;
}
else
{
size_t v___x_5366_; size_t v___x_5367_; uint8_t v___x_5368_; 
v___x_5366_ = lean_ptr_addr(v_body_5360_);
v___x_5367_ = lean_ptr_addr(v_newBody_5357_);
v___x_5368_ = lean_usize_dec_eq(v___x_5366_, v___x_5367_);
if (v___x_5368_ == 0)
{
lean_object* v___x_5369_; 
lean_inc(v_binderName_5358_);
lean_dec_ref_known(v_e_5354_, 3);
v___x_5369_ = l_Lean_Expr_lam___override(v_binderName_5358_, v_newDomain_5356_, v_newBody_5357_, v_newBinfo_5355_);
return v___x_5369_;
}
else
{
uint8_t v___x_5370_; 
v___x_5370_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5361_, v_newBinfo_5355_);
if (v___x_5370_ == 0)
{
lean_object* v___x_5371_; 
lean_inc(v_binderName_5358_);
lean_dec_ref_known(v_e_5354_, 3);
v___x_5371_ = l_Lean_Expr_lam___override(v_binderName_5358_, v_newDomain_5356_, v_newBody_5357_, v_newBinfo_5355_);
return v___x_5371_;
}
else
{
lean_dec_ref(v_newBody_5357_);
lean_dec_ref(v_newDomain_5356_);
return v_e_5354_;
}
}
}
}
else
{
lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; 
lean_dec_ref(v_newBody_5357_);
lean_dec_ref(v_newDomain_5356_);
lean_dec_ref(v_e_5354_);
v___x_5372_ = l_Lean_instInhabitedExpr;
v___x_5373_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_5374_ = l_panic___redArg(v___x_5372_, v___x_5373_);
return v___x_5374_;
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5354_ = stack[0].m_obj;
uint8_t v_newBinfo_5355_ = stack[1].m_num;
lean_object* v_newDomain_5356_ = stack[2].m_obj;
lean_object* v_newBody_5357_ = stack[3].m_obj;
lean_object* v_res_5375_;
v_res_5375_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5354_, v_newBinfo_5355_, v_newDomain_5356_, v_newBody_5357_);
stack->m_obj
 = v_res_5375_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_5376_, lean_object* v_newBinfo_5377_, lean_object* v_newDomain_5378_, lean_object* v_newBody_5379_){
_start:
{
uint8_t v_newBinfo_boxed_5380_; lean_object* v_res_5381_; 
v_newBinfo_boxed_5380_ = lean_unbox(v_newBinfo_5377_);
v_res_5381_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5376_, v_newBinfo_boxed_5380_, v_newDomain_5378_, v_newBody_5379_);
return v_res_5381_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; 
v___x_5383_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5384_ = lean_unsigned_to_nat(20u);
v___x_5385_ = lean_unsigned_to_nat(1959u);
v___x_5386_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5387_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5388_ = l_mkPanicMessageWithDecl(v___x_5387_, v___x_5386_, v___x_5385_, v___x_5384_, v___x_5383_);
return v___x_5388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5389_, lean_object* v_newDomain_5390_, lean_object* v_newBody_5391_){
_start:
{
if (lean_obj_tag(v_e_5389_) == 6)
{
lean_object* v_binderName_5392_; lean_object* v_binderType_5393_; lean_object* v_body_5394_; uint8_t v_binderInfo_5395_; size_t v___x_5396_; size_t v___x_5397_; uint8_t v___x_5398_; 
v_binderName_5392_ = lean_ctor_get(v_e_5389_, 0);
v_binderType_5393_ = lean_ctor_get(v_e_5389_, 1);
v_body_5394_ = lean_ctor_get(v_e_5389_, 2);
v_binderInfo_5395_ = lean_ctor_get_uint8(v_e_5389_, sizeof(void*)*3 + 8);
v___x_5396_ = lean_ptr_addr(v_binderType_5393_);
v___x_5397_ = lean_ptr_addr(v_newDomain_5390_);
v___x_5398_ = lean_usize_dec_eq(v___x_5396_, v___x_5397_);
if (v___x_5398_ == 0)
{
lean_object* v___x_5399_; 
lean_inc(v_binderName_5392_);
lean_dec_ref_known(v_e_5389_, 3);
v___x_5399_ = l_Lean_Expr_lam___override(v_binderName_5392_, v_newDomain_5390_, v_newBody_5391_, v_binderInfo_5395_);
return v___x_5399_;
}
else
{
size_t v___x_5400_; size_t v___x_5401_; uint8_t v___x_5402_; 
v___x_5400_ = lean_ptr_addr(v_body_5394_);
v___x_5401_ = lean_ptr_addr(v_newBody_5391_);
v___x_5402_ = lean_usize_dec_eq(v___x_5400_, v___x_5401_);
if (v___x_5402_ == 0)
{
lean_object* v___x_5403_; 
lean_inc(v_binderName_5392_);
lean_dec_ref_known(v_e_5389_, 3);
v___x_5403_ = l_Lean_Expr_lam___override(v_binderName_5392_, v_newDomain_5390_, v_newBody_5391_, v_binderInfo_5395_);
return v___x_5403_;
}
else
{
uint8_t v___x_5404_; 
v___x_5404_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5395_, v_binderInfo_5395_);
if (v___x_5404_ == 0)
{
lean_object* v___x_5405_; 
lean_inc(v_binderName_5392_);
lean_dec_ref_known(v_e_5389_, 3);
v___x_5405_ = l_Lean_Expr_lam___override(v_binderName_5392_, v_newDomain_5390_, v_newBody_5391_, v_binderInfo_5395_);
return v___x_5405_;
}
else
{
lean_dec_ref(v_newBody_5391_);
lean_dec_ref(v_newDomain_5390_);
return v_e_5389_;
}
}
}
}
else
{
lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; 
lean_dec_ref(v_newBody_5391_);
lean_dec_ref(v_newDomain_5390_);
lean_dec_ref(v_e_5389_);
v___x_5406_ = l_Lean_instInhabitedExpr;
v___x_5407_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5408_ = l_panic___redArg(v___x_5406_, v___x_5407_);
return v___x_5408_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; 
v___x_5410_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5411_ = lean_unsigned_to_nat(22u);
v___x_5412_ = lean_unsigned_to_nat(1968u);
v___x_5413_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5414_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5415_ = l_mkPanicMessageWithDecl(v___x_5414_, v___x_5413_, v___x_5412_, v___x_5411_, v___x_5410_);
return v___x_5415_;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5416_, lean_object* v_newType_5417_, lean_object* v_newVal_5418_, lean_object* v_newBody_5419_, uint8_t v_newNondep_5420_){
_start:
{
if (lean_obj_tag(v_e_5416_) == 8)
{
lean_object* v_declName_5421_; lean_object* v_type_5422_; lean_object* v_value_5423_; lean_object* v_body_5424_; uint8_t v_nondep_5425_; size_t v___x_5426_; size_t v___x_5427_; uint8_t v___x_5428_; 
v_declName_5421_ = lean_ctor_get(v_e_5416_, 0);
v_type_5422_ = lean_ctor_get(v_e_5416_, 1);
v_value_5423_ = lean_ctor_get(v_e_5416_, 2);
v_body_5424_ = lean_ctor_get(v_e_5416_, 3);
v_nondep_5425_ = lean_ctor_get_uint8(v_e_5416_, sizeof(void*)*4 + 8);
v___x_5426_ = lean_ptr_addr(v_type_5422_);
v___x_5427_ = lean_ptr_addr(v_newType_5417_);
v___x_5428_ = lean_usize_dec_eq(v___x_5426_, v___x_5427_);
if (v___x_5428_ == 0)
{
lean_object* v___x_5429_; 
lean_inc(v_declName_5421_);
lean_dec_ref_known(v_e_5416_, 4);
v___x_5429_ = l_Lean_Expr_letE___override(v_declName_5421_, v_newType_5417_, v_newVal_5418_, v_newBody_5419_, v_newNondep_5420_);
return v___x_5429_;
}
else
{
size_t v___x_5430_; size_t v___x_5431_; uint8_t v___x_5432_; 
v___x_5430_ = lean_ptr_addr(v_value_5423_);
v___x_5431_ = lean_ptr_addr(v_newVal_5418_);
v___x_5432_ = lean_usize_dec_eq(v___x_5430_, v___x_5431_);
if (v___x_5432_ == 0)
{
lean_object* v___x_5433_; 
lean_inc(v_declName_5421_);
lean_dec_ref_known(v_e_5416_, 4);
v___x_5433_ = l_Lean_Expr_letE___override(v_declName_5421_, v_newType_5417_, v_newVal_5418_, v_newBody_5419_, v_newNondep_5420_);
return v___x_5433_;
}
else
{
size_t v___x_5434_; size_t v___x_5435_; uint8_t v___x_5436_; 
v___x_5434_ = lean_ptr_addr(v_body_5424_);
v___x_5435_ = lean_ptr_addr(v_newBody_5419_);
v___x_5436_ = lean_usize_dec_eq(v___x_5434_, v___x_5435_);
if (v___x_5436_ == 0)
{
lean_object* v___x_5437_; 
lean_inc(v_declName_5421_);
lean_dec_ref_known(v_e_5416_, 4);
v___x_5437_ = l_Lean_Expr_letE___override(v_declName_5421_, v_newType_5417_, v_newVal_5418_, v_newBody_5419_, v_newNondep_5420_);
return v___x_5437_;
}
else
{
if (v_newNondep_5420_ == 0)
{
if (v_nondep_5425_ == 0)
{
lean_dec_ref(v_newBody_5419_);
lean_dec_ref(v_newVal_5418_);
lean_dec_ref(v_newType_5417_);
return v_e_5416_;
}
else
{
lean_object* v___x_5438_; 
lean_inc(v_declName_5421_);
lean_dec_ref_known(v_e_5416_, 4);
v___x_5438_ = l_Lean_Expr_letE___override(v_declName_5421_, v_newType_5417_, v_newVal_5418_, v_newBody_5419_, v_newNondep_5420_);
return v___x_5438_;
}
}
else
{
if (v_nondep_5425_ == 0)
{
lean_object* v___x_5439_; 
lean_inc(v_declName_5421_);
lean_dec_ref_known(v_e_5416_, 4);
v___x_5439_ = l_Lean_Expr_letE___override(v_declName_5421_, v_newType_5417_, v_newVal_5418_, v_newBody_5419_, v_newNondep_5420_);
return v___x_5439_;
}
else
{
lean_dec_ref(v_newBody_5419_);
lean_dec_ref(v_newVal_5418_);
lean_dec_ref(v_newType_5417_);
return v_e_5416_;
}
}
}
}
}
}
else
{
lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; 
lean_dec_ref(v_newBody_5419_);
lean_dec_ref(v_newVal_5418_);
lean_dec_ref(v_newType_5417_);
lean_dec_ref(v_e_5416_);
v___x_5440_ = l_Lean_instInhabitedExpr;
v___x_5441_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5442_ = l_panic___redArg(v___x_5440_, v___x_5441_);
return v___x_5442_;
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5416_ = stack[0].m_obj;
lean_object* v_newType_5417_ = stack[1].m_obj;
lean_object* v_newVal_5418_ = stack[2].m_obj;
lean_object* v_newBody_5419_ = stack[3].m_obj;
uint8_t v_newNondep_5420_ = stack[4].m_num;
lean_object* v_res_5443_;
v_res_5443_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5416_, v_newType_5417_, v_newVal_5418_, v_newBody_5419_, v_newNondep_5420_);
stack->m_obj
 = v_res_5443_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5444_, lean_object* v_newType_5445_, lean_object* v_newVal_5446_, lean_object* v_newBody_5447_, lean_object* v_newNondep_5448_){
_start:
{
uint8_t v_newNondep_boxed_5449_; lean_object* v_res_5450_; 
v_newNondep_boxed_5449_ = lean_unbox(v_newNondep_5448_);
v_res_5450_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5444_, v_newType_5445_, v_newVal_5446_, v_newBody_5447_, v_newNondep_boxed_5449_);
return v_res_5450_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; 
v___x_5452_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5453_ = lean_unsigned_to_nat(27u);
v___x_5454_ = lean_unsigned_to_nat(1981u);
v___x_5455_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5456_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5457_ = l_mkPanicMessageWithDecl(v___x_5456_, v___x_5455_, v___x_5454_, v___x_5453_, v___x_5452_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5458_, lean_object* v_newType_5459_, lean_object* v_newVal_5460_, lean_object* v_newBody_5461_){
_start:
{
if (lean_obj_tag(v_e_5458_) == 8)
{
lean_object* v_declName_5462_; lean_object* v_type_5463_; lean_object* v_value_5464_; lean_object* v_body_5465_; uint8_t v_nondep_5466_; size_t v___x_5467_; size_t v___x_5468_; uint8_t v___x_5469_; 
v_declName_5462_ = lean_ctor_get(v_e_5458_, 0);
v_type_5463_ = lean_ctor_get(v_e_5458_, 1);
v_value_5464_ = lean_ctor_get(v_e_5458_, 2);
v_body_5465_ = lean_ctor_get(v_e_5458_, 3);
v_nondep_5466_ = lean_ctor_get_uint8(v_e_5458_, sizeof(void*)*4 + 8);
v___x_5467_ = lean_ptr_addr(v_type_5463_);
v___x_5468_ = lean_ptr_addr(v_newType_5459_);
v___x_5469_ = lean_usize_dec_eq(v___x_5467_, v___x_5468_);
if (v___x_5469_ == 0)
{
lean_object* v___x_5470_; 
lean_inc(v_declName_5462_);
lean_dec_ref_known(v_e_5458_, 4);
v___x_5470_ = l_Lean_Expr_letE___override(v_declName_5462_, v_newType_5459_, v_newVal_5460_, v_newBody_5461_, v_nondep_5466_);
return v___x_5470_;
}
else
{
size_t v___x_5471_; size_t v___x_5472_; uint8_t v___x_5473_; 
v___x_5471_ = lean_ptr_addr(v_value_5464_);
v___x_5472_ = lean_ptr_addr(v_newVal_5460_);
v___x_5473_ = lean_usize_dec_eq(v___x_5471_, v___x_5472_);
if (v___x_5473_ == 0)
{
lean_object* v___x_5474_; 
lean_inc(v_declName_5462_);
lean_dec_ref_known(v_e_5458_, 4);
v___x_5474_ = l_Lean_Expr_letE___override(v_declName_5462_, v_newType_5459_, v_newVal_5460_, v_newBody_5461_, v_nondep_5466_);
return v___x_5474_;
}
else
{
size_t v___x_5475_; size_t v___x_5476_; uint8_t v___x_5477_; 
v___x_5475_ = lean_ptr_addr(v_body_5465_);
v___x_5476_ = lean_ptr_addr(v_newBody_5461_);
v___x_5477_ = lean_usize_dec_eq(v___x_5475_, v___x_5476_);
if (v___x_5477_ == 0)
{
lean_object* v___x_5478_; 
lean_inc(v_declName_5462_);
lean_dec_ref_known(v_e_5458_, 4);
v___x_5478_ = l_Lean_Expr_letE___override(v_declName_5462_, v_newType_5459_, v_newVal_5460_, v_newBody_5461_, v_nondep_5466_);
return v___x_5478_;
}
else
{
lean_dec_ref(v_newBody_5461_);
lean_dec_ref(v_newVal_5460_);
lean_dec_ref(v_newType_5459_);
return v_e_5458_;
}
}
}
}
else
{
lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; 
lean_dec_ref(v_newBody_5461_);
lean_dec_ref(v_newVal_5460_);
lean_dec_ref(v_newType_5459_);
lean_dec_ref(v_e_5458_);
v___x_5479_ = l_Lean_instInhabitedExpr;
v___x_5480_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5481_ = l_panic___redArg(v___x_5479_, v___x_5480_);
return v___x_5481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5482_, lean_object* v_x_5483_){
_start:
{
if (lean_obj_tag(v_x_5482_) == 5)
{
lean_object* v_fn_5484_; lean_object* v_arg_5485_; lean_object* v___x_5486_; size_t v___x_5487_; size_t v___x_5488_; uint8_t v___x_5489_; 
v_fn_5484_ = lean_ctor_get(v_x_5482_, 0);
v_arg_5485_ = lean_ctor_get(v_x_5482_, 1);
lean_inc_ref(v_fn_5484_);
v___x_5486_ = l_Lean_Expr_updateFn(v_fn_5484_, v_x_5483_);
v___x_5487_ = lean_ptr_addr(v_fn_5484_);
v___x_5488_ = lean_ptr_addr(v___x_5486_);
v___x_5489_ = lean_usize_dec_eq(v___x_5487_, v___x_5488_);
if (v___x_5489_ == 0)
{
lean_object* v___x_5490_; 
lean_inc_ref(v_arg_5485_);
lean_dec_ref_known(v_x_5482_, 2);
v___x_5490_ = l_Lean_Expr_app___override(v___x_5486_, v_arg_5485_);
return v___x_5490_;
}
else
{
size_t v___x_5491_; uint8_t v___x_5492_; 
v___x_5491_ = lean_ptr_addr(v_arg_5485_);
v___x_5492_ = lean_usize_dec_eq(v___x_5491_, v___x_5491_);
if (v___x_5492_ == 0)
{
lean_object* v___x_5493_; 
lean_inc_ref(v_arg_5485_);
lean_dec_ref_known(v_x_5482_, 2);
v___x_5493_ = l_Lean_Expr_app___override(v___x_5486_, v_arg_5485_);
return v___x_5493_;
}
else
{
lean_dec_ref(v___x_5486_);
return v_x_5482_;
}
}
}
else
{
lean_dec_ref(v_x_5482_);
lean_inc_ref(v_x_5483_);
return v_x_5483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5494_, lean_object* v_x_5495_){
_start:
{
lean_object* v_res_5496_; 
v_res_5496_ = l_Lean_Expr_updateFn(v_x_5494_, v_x_5495_);
lean_dec_ref(v_x_5495_);
return v_res_5496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5497_){
_start:
{
if (lean_obj_tag(v_e_5497_) == 6)
{
lean_object* v_binderName_5498_; lean_object* v_binderType_5499_; lean_object* v_body_5500_; uint8_t v_binderInfo_5501_; lean_object* v_b_x27_5502_; 
v_binderName_5498_ = lean_ctor_get(v_e_5497_, 0);
v_binderType_5499_ = lean_ctor_get(v_e_5497_, 1);
v_body_5500_ = lean_ctor_get(v_e_5497_, 2);
v_binderInfo_5501_ = lean_ctor_get_uint8(v_e_5497_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5500_);
v_b_x27_5502_ = l_Lean_Expr_eta(v_body_5500_);
if (lean_obj_tag(v_b_x27_5502_) == 5)
{
lean_object* v_arg_5513_; 
v_arg_5513_ = lean_ctor_get(v_b_x27_5502_, 1);
if (lean_obj_tag(v_arg_5513_) == 0)
{
lean_object* v_fn_5514_; lean_object* v_deBruijnIndex_5515_; lean_object* v___x_5516_; uint8_t v___x_5517_; 
v_fn_5514_ = lean_ctor_get(v_b_x27_5502_, 0);
v_deBruijnIndex_5515_ = lean_ctor_get(v_arg_5513_, 0);
v___x_5516_ = lean_unsigned_to_nat(0u);
v___x_5517_ = lean_nat_dec_eq(v_deBruijnIndex_5515_, v___x_5516_);
if (v___x_5517_ == 0)
{
goto v___jp_5503_;
}
else
{
uint8_t v___x_5518_; 
v___x_5518_ = lean_expr_has_loose_bvar(v_fn_5514_, v___x_5516_);
if (v___x_5518_ == 0)
{
lean_object* v___x_5519_; lean_object* v___x_5520_; 
lean_inc_ref(v_fn_5514_);
lean_dec_ref_known(v_b_x27_5502_, 2);
lean_dec_ref_known(v_e_5497_, 3);
v___x_5519_ = lean_unsigned_to_nat(1u);
v___x_5520_ = lean_expr_lower_loose_bvars(v_fn_5514_, v___x_5519_, v___x_5519_);
lean_dec_ref(v_fn_5514_);
return v___x_5520_;
}
else
{
size_t v___x_5521_; uint8_t v___x_5522_; 
v___x_5521_ = lean_ptr_addr(v_binderType_5499_);
v___x_5522_ = lean_usize_dec_eq(v___x_5521_, v___x_5521_);
if (v___x_5522_ == 0)
{
lean_object* v___x_5523_; 
lean_inc_ref(v_binderType_5499_);
lean_inc(v_binderName_5498_);
lean_dec_ref_known(v_e_5497_, 3);
v___x_5523_ = l_Lean_Expr_lam___override(v_binderName_5498_, v_binderType_5499_, v_b_x27_5502_, v_binderInfo_5501_);
return v___x_5523_;
}
else
{
size_t v___x_5524_; size_t v___x_5525_; uint8_t v___x_5526_; 
v___x_5524_ = lean_ptr_addr(v_body_5500_);
v___x_5525_ = lean_ptr_addr(v_b_x27_5502_);
v___x_5526_ = lean_usize_dec_eq(v___x_5524_, v___x_5525_);
if (v___x_5526_ == 0)
{
lean_object* v___x_5527_; 
lean_inc_ref(v_binderType_5499_);
lean_inc(v_binderName_5498_);
lean_dec_ref_known(v_e_5497_, 3);
v___x_5527_ = l_Lean_Expr_lam___override(v_binderName_5498_, v_binderType_5499_, v_b_x27_5502_, v_binderInfo_5501_);
return v___x_5527_;
}
else
{
uint8_t v___x_5528_; 
v___x_5528_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5501_, v_binderInfo_5501_);
if (v___x_5528_ == 0)
{
lean_object* v___x_5529_; 
lean_inc_ref(v_binderType_5499_);
lean_inc(v_binderName_5498_);
lean_dec_ref_known(v_e_5497_, 3);
v___x_5529_ = l_Lean_Expr_lam___override(v_binderName_5498_, v_binderType_5499_, v_b_x27_5502_, v_binderInfo_5501_);
return v___x_5529_;
}
else
{
lean_dec_ref_known(v_b_x27_5502_, 2);
return v_e_5497_;
}
}
}
}
}
}
else
{
goto v___jp_5503_;
}
}
else
{
goto v___jp_5503_;
}
v___jp_5503_:
{
size_t v___x_5504_; uint8_t v___x_5505_; 
v___x_5504_ = lean_ptr_addr(v_binderType_5499_);
v___x_5505_ = lean_usize_dec_eq(v___x_5504_, v___x_5504_);
if (v___x_5505_ == 0)
{
lean_object* v___x_5506_; 
lean_inc_ref(v_binderType_5499_);
lean_inc(v_binderName_5498_);
lean_dec_ref_known(v_e_5497_, 3);
v___x_5506_ = l_Lean_Expr_lam___override(v_binderName_5498_, v_binderType_5499_, v_b_x27_5502_, v_binderInfo_5501_);
return v___x_5506_;
}
else
{
size_t v___x_5507_; size_t v___x_5508_; uint8_t v___x_5509_; 
v___x_5507_ = lean_ptr_addr(v_body_5500_);
v___x_5508_ = lean_ptr_addr(v_b_x27_5502_);
v___x_5509_ = lean_usize_dec_eq(v___x_5507_, v___x_5508_);
if (v___x_5509_ == 0)
{
lean_object* v___x_5510_; 
lean_inc_ref(v_binderType_5499_);
lean_inc(v_binderName_5498_);
lean_dec_ref_known(v_e_5497_, 3);
v___x_5510_ = l_Lean_Expr_lam___override(v_binderName_5498_, v_binderType_5499_, v_b_x27_5502_, v_binderInfo_5501_);
return v___x_5510_;
}
else
{
uint8_t v___x_5511_; 
v___x_5511_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5501_, v_binderInfo_5501_);
if (v___x_5511_ == 0)
{
lean_object* v___x_5512_; 
lean_inc_ref(v_binderType_5499_);
lean_inc(v_binderName_5498_);
lean_dec_ref_known(v_e_5497_, 3);
v___x_5512_ = l_Lean_Expr_lam___override(v_binderName_5498_, v_binderType_5499_, v_b_x27_5502_, v_binderInfo_5501_);
return v___x_5512_;
}
else
{
lean_dec_ref(v_b_x27_5502_);
return v_e_5497_;
}
}
}
}
}
else
{
return v_e_5497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5530_, lean_object* v_optionName_5531_, lean_object* v_inst_5532_, lean_object* v_val_5533_){
_start:
{
lean_object* v_toDataValue_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; 
v_toDataValue_5534_ = lean_ctor_get(v_inst_5532_, 0);
lean_inc_ref(v_toDataValue_5534_);
lean_dec_ref(v_inst_5532_);
v___x_5535_ = lean_box(0);
v___x_5536_ = lean_apply_1(v_toDataValue_5534_, v_val_5533_);
v___x_5537_ = l_Lean_KVMap_insert(v___x_5535_, v_optionName_5531_, v___x_5536_);
v___x_5538_ = l_Lean_Expr_mdata___override(v___x_5537_, v_e_5530_);
return v___x_5538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5539_, lean_object* v_e_5540_, lean_object* v_optionName_5541_, lean_object* v_inst_5542_, lean_object* v_val_5543_){
_start:
{
lean_object* v___x_5544_; 
v___x_5544_ = l_Lean_Expr_setOption___redArg(v_e_5540_, v_optionName_5541_, v_inst_5542_, v_val_5543_);
return v___x_5544_;
}
}
lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5545_, lean_object* v_optionName_5546_, uint8_t v_val_5547_){
_start:
{
lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; 
v___x_5548_ = lean_box(0);
v___x_5549_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5549_, 0, v_val_5547_);
v___x_5550_ = l_Lean_KVMap_insert(v___x_5548_, v_optionName_5546_, v___x_5549_);
v___x_5551_ = l_Lean_Expr_mdata___override(v___x_5550_, v_e_5545_);
return v___x_5551_;
}
}
LEAN_EXPORT void l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5545_ = stack[0].m_obj;
lean_object* v_optionName_5546_ = stack[1].m_obj;
uint8_t v_val_5547_ = stack[2].m_num;
lean_object* v_res_5552_;
v_res_5552_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5545_, v_optionName_5546_, v_val_5547_);
stack->m_obj
 = v_res_5552_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5553_, lean_object* v_optionName_5554_, lean_object* v_val_5555_){
_start:
{
uint8_t v_val_boxed_5556_; lean_object* v_res_5557_; 
v_val_boxed_5556_ = lean_unbox(v_val_5555_);
v_res_5557_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5553_, v_optionName_5554_, v_val_boxed_5556_);
return v_res_5557_;
}
}
lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5563_, uint8_t v_flag_5564_){
_start:
{
lean_object* v___x_5565_; lean_object* v___x_5566_; 
v___x_5565_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5566_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5563_, v___x_5565_, v_flag_5564_);
return v___x_5566_;
}
}
LEAN_EXPORT void l_Lean_Expr_setPPExplicit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5563_ = stack[0].m_obj;
uint8_t v_flag_5564_ = stack[1].m_num;
lean_object* v_res_5567_;
v_res_5567_ = l_Lean_Expr_setPPExplicit(v_e_5563_, v_flag_5564_);
stack->m_obj
 = v_res_5567_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5568_, lean_object* v_flag_5569_){
_start:
{
uint8_t v_flag_boxed_5570_; lean_object* v_res_5571_; 
v_flag_boxed_5570_ = lean_unbox(v_flag_5569_);
v_res_5571_ = l_Lean_Expr_setPPExplicit(v_e_5568_, v_flag_boxed_5570_);
return v_res_5571_;
}
}
lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5576_, uint8_t v_flag_5577_){
_start:
{
lean_object* v___x_5578_; lean_object* v___x_5579_; 
v___x_5578_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5579_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5576_, v___x_5578_, v_flag_5577_);
return v___x_5579_;
}
}
LEAN_EXPORT void l_Lean_Expr_setPPUniverses_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5576_ = stack[0].m_obj;
uint8_t v_flag_5577_ = stack[1].m_num;
lean_object* v_res_5580_;
v_res_5580_ = l_Lean_Expr_setPPUniverses(v_e_5576_, v_flag_5577_);
stack->m_obj
 = v_res_5580_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5581_, lean_object* v_flag_5582_){
_start:
{
uint8_t v_flag_boxed_5583_; lean_object* v_res_5584_; 
v_flag_boxed_5583_ = lean_unbox(v_flag_5582_);
v_res_5584_ = l_Lean_Expr_setPPUniverses(v_e_5581_, v_flag_boxed_5583_);
return v_res_5584_;
}
}
lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5589_, uint8_t v_flag_5590_){
_start:
{
lean_object* v___x_5591_; lean_object* v___x_5592_; 
v___x_5591_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5592_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5589_, v___x_5591_, v_flag_5590_);
return v___x_5592_;
}
}
LEAN_EXPORT void l_Lean_Expr_setPPPiBinderTypes_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5589_ = stack[0].m_obj;
uint8_t v_flag_5590_ = stack[1].m_num;
lean_object* v_res_5593_;
v_res_5593_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5589_, v_flag_5590_);
stack->m_obj
 = v_res_5593_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5594_, lean_object* v_flag_5595_){
_start:
{
uint8_t v_flag_boxed_5596_; lean_object* v_res_5597_; 
v_flag_boxed_5596_ = lean_unbox(v_flag_5595_);
v_res_5597_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5594_, v_flag_boxed_5596_);
return v_res_5597_;
}
}
lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5602_, uint8_t v_flag_5603_){
_start:
{
lean_object* v___x_5604_; lean_object* v___x_5605_; 
v___x_5604_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5605_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5602_, v___x_5604_, v_flag_5603_);
return v___x_5605_;
}
}
LEAN_EXPORT void l_Lean_Expr_setPPFunBinderTypes_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5602_ = stack[0].m_obj;
uint8_t v_flag_5603_ = stack[1].m_num;
lean_object* v_res_5606_;
v_res_5606_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5602_, v_flag_5603_);
stack->m_obj
 = v_res_5606_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5607_, lean_object* v_flag_5608_){
_start:
{
uint8_t v_flag_boxed_5609_; lean_object* v_res_5610_; 
v_flag_boxed_5609_ = lean_unbox(v_flag_5608_);
v_res_5610_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5607_, v_flag_boxed_5609_);
return v_res_5610_;
}
}
lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5615_, uint8_t v_flag_5616_){
_start:
{
lean_object* v___x_5617_; lean_object* v___x_5618_; 
v___x_5617_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5618_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5615_, v___x_5617_, v_flag_5616_);
return v___x_5618_;
}
}
LEAN_EXPORT void l_Lean_Expr_setPPNumericTypes_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5615_ = stack[0].m_obj;
uint8_t v_flag_5616_ = stack[1].m_num;
lean_object* v_res_5619_;
v_res_5619_ = l_Lean_Expr_setPPNumericTypes(v_e_5615_, v_flag_5616_);
stack->m_obj
 = v_res_5619_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5620_, lean_object* v_flag_5621_){
_start:
{
uint8_t v_flag_boxed_5622_; lean_object* v_res_5623_; 
v_flag_boxed_5622_ = lean_unbox(v_flag_5621_);
v_res_5623_ = l_Lean_Expr_setPPNumericTypes(v_e_5620_, v_flag_boxed_5622_);
return v_res_5623_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5624_, size_t v_i_5625_, lean_object* v_bs_5626_){
_start:
{
uint8_t v___x_5627_; 
v___x_5627_ = lean_usize_dec_lt(v_i_5625_, v_sz_5624_);
if (v___x_5627_ == 0)
{
return v_bs_5626_;
}
else
{
uint8_t v___x_5628_; lean_object* v_v_5629_; lean_object* v___x_5630_; lean_object* v_bs_x27_5631_; lean_object* v___x_5632_; size_t v___x_5633_; size_t v___x_5634_; lean_object* v___x_5635_; 
v___x_5628_ = 0;
v_v_5629_ = lean_array_uget(v_bs_5626_, v_i_5625_);
v___x_5630_ = lean_unsigned_to_nat(0u);
v_bs_x27_5631_ = lean_array_uset(v_bs_5626_, v_i_5625_, v___x_5630_);
v___x_5632_ = l_Lean_Expr_setPPExplicit(v_v_5629_, v___x_5628_);
v___x_5633_ = ((size_t)1ULL);
v___x_5634_ = lean_usize_add(v_i_5625_, v___x_5633_);
v___x_5635_ = lean_array_uset(v_bs_x27_5631_, v_i_5625_, v___x_5632_);
v_i_5625_ = v___x_5634_;
v_bs_5626_ = v___x_5635_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_5624_ = stack[0].m_num;
size_t v_i_5625_ = stack[1].m_num;
lean_object* v_bs_5626_ = stack[2].m_obj;
lean_object* v_res_5637_;
v_res_5637_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5624_, v_i_5625_, v_bs_5626_);
stack->m_obj
 = v_res_5637_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5638_, lean_object* v_i_5639_, lean_object* v_bs_5640_){
_start:
{
size_t v_sz_boxed_5641_; size_t v_i_boxed_5642_; lean_object* v_res_5643_; 
v_sz_boxed_5641_ = lean_unbox_usize(v_sz_5638_);
lean_dec(v_sz_5638_);
v_i_boxed_5642_ = lean_unbox_usize(v_i_5639_);
lean_dec(v_i_5639_);
v_res_5643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5641_, v_i_boxed_5642_, v_bs_5640_);
return v_res_5643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5644_){
_start:
{
if (lean_obj_tag(v_e_5644_) == 5)
{
lean_object* v___x_5645_; uint8_t v___x_5646_; lean_object* v_f_5647_; lean_object* v_dummy_5648_; lean_object* v_nargs_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; size_t v_sz_5654_; size_t v___x_5655_; lean_object* v_args_5656_; lean_object* v___x_5657_; uint8_t v___x_5658_; lean_object* v___x_5659_; 
v___x_5645_ = l_Lean_Expr_getAppFn(v_e_5644_);
v___x_5646_ = 0;
v_f_5647_ = l_Lean_Expr_setPPExplicit(v___x_5645_, v___x_5646_);
v_dummy_5648_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5649_ = l_Lean_Expr_getAppNumArgs(v_e_5644_);
lean_inc(v_nargs_5649_);
v___x_5650_ = lean_mk_array(v_nargs_5649_, v_dummy_5648_);
v___x_5651_ = lean_unsigned_to_nat(1u);
v___x_5652_ = lean_nat_sub(v_nargs_5649_, v___x_5651_);
lean_dec(v_nargs_5649_);
v___x_5653_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5644_, v___x_5650_, v___x_5652_);
v_sz_5654_ = lean_array_size(v___x_5653_);
v___x_5655_ = ((size_t)0ULL);
v_args_5656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5654_, v___x_5655_, v___x_5653_);
v___x_5657_ = l_Lean_mkAppN(v_f_5647_, v_args_5656_);
lean_dec_ref(v_args_5656_);
v___x_5658_ = 1;
v___x_5659_ = l_Lean_Expr_setPPExplicit(v___x_5657_, v___x_5658_);
return v___x_5659_;
}
else
{
return v_e_5644_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5660_, size_t v_i_5661_, lean_object* v_bs_5662_){
_start:
{
uint8_t v___x_5663_; 
v___x_5663_ = lean_usize_dec_lt(v_i_5661_, v_sz_5660_);
if (v___x_5663_ == 0)
{
return v_bs_5662_;
}
else
{
lean_object* v_v_5664_; lean_object* v___x_5665_; lean_object* v_bs_x27_5666_; lean_object* v___y_5668_; uint8_t v___x_5673_; 
v_v_5664_ = lean_array_uget(v_bs_5662_, v_i_5661_);
v___x_5665_ = lean_unsigned_to_nat(0u);
v_bs_x27_5666_ = lean_array_uset(v_bs_5662_, v_i_5661_, v___x_5665_);
v___x_5673_ = l_Lean_Expr_hasMVar(v_v_5664_);
if (v___x_5673_ == 0)
{
lean_object* v___x_5674_; 
v___x_5674_ = l_Lean_Expr_setPPExplicit(v_v_5664_, v___x_5673_);
v___y_5668_ = v___x_5674_;
goto v___jp_5667_;
}
else
{
v___y_5668_ = v_v_5664_;
goto v___jp_5667_;
}
v___jp_5667_:
{
size_t v___x_5669_; size_t v___x_5670_; lean_object* v___x_5671_; 
v___x_5669_ = ((size_t)1ULL);
v___x_5670_ = lean_usize_add(v_i_5661_, v___x_5669_);
v___x_5671_ = lean_array_uset(v_bs_x27_5666_, v_i_5661_, v___y_5668_);
v_i_5661_ = v___x_5670_;
v_bs_5662_ = v___x_5671_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_5660_ = stack[0].m_num;
size_t v_i_5661_ = stack[1].m_num;
lean_object* v_bs_5662_ = stack[2].m_obj;
lean_object* v_res_5675_;
v_res_5675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5660_, v_i_5661_, v_bs_5662_);
stack->m_obj
 = v_res_5675_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5676_, lean_object* v_i_5677_, lean_object* v_bs_5678_){
_start:
{
size_t v_sz_boxed_5679_; size_t v_i_boxed_5680_; lean_object* v_res_5681_; 
v_sz_boxed_5679_ = lean_unbox_usize(v_sz_5676_);
lean_dec(v_sz_5676_);
v_i_boxed_5680_ = lean_unbox_usize(v_i_5677_);
lean_dec(v_i_5677_);
v_res_5681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5679_, v_i_boxed_5680_, v_bs_5678_);
return v_res_5681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5682_){
_start:
{
if (lean_obj_tag(v_e_5682_) == 5)
{
lean_object* v___x_5683_; uint8_t v___x_5684_; lean_object* v_f_5685_; lean_object* v_dummy_5686_; lean_object* v_nargs_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; size_t v_sz_5692_; size_t v___x_5693_; lean_object* v_args_5694_; lean_object* v___x_5695_; uint8_t v___x_5696_; lean_object* v___x_5697_; 
v___x_5683_ = l_Lean_Expr_getAppFn(v_e_5682_);
v___x_5684_ = 0;
v_f_5685_ = l_Lean_Expr_setPPExplicit(v___x_5683_, v___x_5684_);
v_dummy_5686_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5687_ = l_Lean_Expr_getAppNumArgs(v_e_5682_);
lean_inc(v_nargs_5687_);
v___x_5688_ = lean_mk_array(v_nargs_5687_, v_dummy_5686_);
v___x_5689_ = lean_unsigned_to_nat(1u);
v___x_5690_ = lean_nat_sub(v_nargs_5687_, v___x_5689_);
lean_dec(v_nargs_5687_);
v___x_5691_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5682_, v___x_5688_, v___x_5690_);
v_sz_5692_ = lean_array_size(v___x_5691_);
v___x_5693_ = ((size_t)0ULL);
v_args_5694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5692_, v___x_5693_, v___x_5691_);
v___x_5695_ = l_Lean_mkAppN(v_f_5685_, v_args_5694_);
lean_dec_ref(v_args_5694_);
v___x_5696_ = 1;
v___x_5697_ = l_Lean_Expr_setPPExplicit(v___x_5695_, v___x_5696_);
return v___x_5697_;
}
else
{
return v_e_5682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5698_, lean_object* v_body_5699_, lean_object* v_x_5700_){
_start:
{
lean_object* v___x_5701_; 
v___x_5701_ = lean_apply_1(v_f_5698_, v_body_5699_);
return v___x_5701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5702_, lean_object* v_binderType_5703_, lean_object* v_x_5704_){
_start:
{
lean_object* v___x_5705_; 
v___x_5705_ = lean_apply_1(v_f_5702_, v_binderType_5703_);
return v___x_5705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5706_, lean_object* v_value_5707_, lean_object* v_x_5708_){
_start:
{
lean_object* v___x_5709_; 
v___x_5709_ = lean_apply_1(v_f_5706_, v_value_5707_);
return v___x_5709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5710_, lean_object* v_type_5711_, lean_object* v_x_5712_){
_start:
{
lean_object* v___x_5713_; 
v___x_5713_ = lean_apply_1(v_f_5710_, v_type_5711_);
return v___x_5713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5714_, lean_object* v_arg_5715_, lean_object* v_x_5716_){
_start:
{
lean_object* v___x_5717_; 
v___x_5717_ = lean_apply_1(v_f_5714_, v_arg_5715_);
return v___x_5717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5718_, lean_object* v_fn_5719_, lean_object* v_x_5720_){
_start:
{
lean_object* v___x_5721_; 
v___x_5721_ = lean_apply_1(v_f_5718_, v_fn_5719_);
return v___x_5721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5722_, lean_object* v_f_5723_, lean_object* v_x_5724_){
_start:
{
switch(lean_obj_tag(v_x_5724_))
{
case 7:
{
lean_object* v_toPure_5725_; lean_object* v_toSeq_5726_; lean_object* v_binderType_5727_; lean_object* v_body_5728_; lean_object* v___f_5729_; lean_object* v___f_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; 
v_toPure_5725_ = lean_ctor_get(v_inst_5722_, 1);
lean_inc(v_toPure_5725_);
v_toSeq_5726_ = lean_ctor_get(v_inst_5722_, 2);
lean_inc_n(v_toSeq_5726_, 2);
lean_dec_ref(v_inst_5722_);
v_binderType_5727_ = lean_ctor_get(v_x_5724_, 1);
v_body_5728_ = lean_ctor_get(v_x_5724_, 2);
lean_inc_ref(v_body_5728_);
lean_inc(v_f_5723_);
v___f_5729_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5729_, 0, v_f_5723_);
lean_closure_set(v___f_5729_, 1, v_body_5728_);
lean_inc_ref(v_binderType_5727_);
v___f_5730_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5730_, 0, v_f_5723_);
lean_closure_set(v___f_5730_, 1, v_binderType_5727_);
v___x_5731_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5731_, 0, v_x_5724_);
v___x_5732_ = lean_apply_2(v_toPure_5725_, lean_box(0), v___x_5731_);
v___x_5733_ = lean_apply_4(v_toSeq_5726_, lean_box(0), lean_box(0), v___x_5732_, v___f_5730_);
v___x_5734_ = lean_apply_4(v_toSeq_5726_, lean_box(0), lean_box(0), v___x_5733_, v___f_5729_);
return v___x_5734_;
}
case 6:
{
lean_object* v_toPure_5735_; lean_object* v_toSeq_5736_; lean_object* v_binderType_5737_; lean_object* v_body_5738_; lean_object* v___f_5739_; lean_object* v___f_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; 
v_toPure_5735_ = lean_ctor_get(v_inst_5722_, 1);
lean_inc(v_toPure_5735_);
v_toSeq_5736_ = lean_ctor_get(v_inst_5722_, 2);
lean_inc_n(v_toSeq_5736_, 2);
lean_dec_ref(v_inst_5722_);
v_binderType_5737_ = lean_ctor_get(v_x_5724_, 1);
v_body_5738_ = lean_ctor_get(v_x_5724_, 2);
lean_inc_ref(v_body_5738_);
lean_inc(v_f_5723_);
v___f_5739_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5739_, 0, v_f_5723_);
lean_closure_set(v___f_5739_, 1, v_body_5738_);
lean_inc_ref(v_binderType_5737_);
v___f_5740_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5740_, 0, v_f_5723_);
lean_closure_set(v___f_5740_, 1, v_binderType_5737_);
v___x_5741_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5741_, 0, v_x_5724_);
v___x_5742_ = lean_apply_2(v_toPure_5735_, lean_box(0), v___x_5741_);
v___x_5743_ = lean_apply_4(v_toSeq_5736_, lean_box(0), lean_box(0), v___x_5742_, v___f_5740_);
v___x_5744_ = lean_apply_4(v_toSeq_5736_, lean_box(0), lean_box(0), v___x_5743_, v___f_5739_);
return v___x_5744_;
}
case 10:
{
lean_object* v_toFunctor_5745_; lean_object* v_expr_5746_; lean_object* v_map_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; 
v_toFunctor_5745_ = lean_ctor_get(v_inst_5722_, 0);
lean_inc_ref(v_toFunctor_5745_);
lean_dec_ref(v_inst_5722_);
v_expr_5746_ = lean_ctor_get(v_x_5724_, 1);
lean_inc_ref(v_expr_5746_);
v_map_5747_ = lean_ctor_get(v_toFunctor_5745_, 0);
lean_inc(v_map_5747_);
lean_dec_ref(v_toFunctor_5745_);
v___x_5748_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5748_, 0, v_x_5724_);
v___x_5749_ = lean_apply_1(v_f_5723_, v_expr_5746_);
v___x_5750_ = lean_apply_4(v_map_5747_, lean_box(0), lean_box(0), v___x_5748_, v___x_5749_);
return v___x_5750_;
}
case 8:
{
lean_object* v_toPure_5751_; lean_object* v_toSeq_5752_; lean_object* v_type_5753_; lean_object* v_value_5754_; lean_object* v_body_5755_; lean_object* v___f_5756_; lean_object* v___f_5757_; lean_object* v___f_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; 
v_toPure_5751_ = lean_ctor_get(v_inst_5722_, 1);
lean_inc(v_toPure_5751_);
v_toSeq_5752_ = lean_ctor_get(v_inst_5722_, 2);
lean_inc_n(v_toSeq_5752_, 3);
lean_dec_ref(v_inst_5722_);
v_type_5753_ = lean_ctor_get(v_x_5724_, 1);
v_value_5754_ = lean_ctor_get(v_x_5724_, 2);
v_body_5755_ = lean_ctor_get(v_x_5724_, 3);
lean_inc_ref(v_body_5755_);
lean_inc_n(v_f_5723_, 2);
v___f_5756_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5756_, 0, v_f_5723_);
lean_closure_set(v___f_5756_, 1, v_body_5755_);
lean_inc_ref(v_value_5754_);
v___f_5757_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5757_, 0, v_f_5723_);
lean_closure_set(v___f_5757_, 1, v_value_5754_);
lean_inc_ref(v_type_5753_);
v___f_5758_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5758_, 0, v_f_5723_);
lean_closure_set(v___f_5758_, 1, v_type_5753_);
v___x_5759_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5759_, 0, v_x_5724_);
v___x_5760_ = lean_apply_2(v_toPure_5751_, lean_box(0), v___x_5759_);
v___x_5761_ = lean_apply_4(v_toSeq_5752_, lean_box(0), lean_box(0), v___x_5760_, v___f_5758_);
v___x_5762_ = lean_apply_4(v_toSeq_5752_, lean_box(0), lean_box(0), v___x_5761_, v___f_5757_);
v___x_5763_ = lean_apply_4(v_toSeq_5752_, lean_box(0), lean_box(0), v___x_5762_, v___f_5756_);
return v___x_5763_;
}
case 5:
{
lean_object* v_toPure_5764_; lean_object* v_toSeq_5765_; lean_object* v_fn_5766_; lean_object* v_arg_5767_; lean_object* v___f_5768_; lean_object* v___f_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; 
v_toPure_5764_ = lean_ctor_get(v_inst_5722_, 1);
lean_inc(v_toPure_5764_);
v_toSeq_5765_ = lean_ctor_get(v_inst_5722_, 2);
lean_inc_n(v_toSeq_5765_, 2);
lean_dec_ref(v_inst_5722_);
v_fn_5766_ = lean_ctor_get(v_x_5724_, 0);
v_arg_5767_ = lean_ctor_get(v_x_5724_, 1);
lean_inc_ref(v_arg_5767_);
lean_inc(v_f_5723_);
v___f_5768_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5768_, 0, v_f_5723_);
lean_closure_set(v___f_5768_, 1, v_arg_5767_);
lean_inc_ref(v_fn_5766_);
v___f_5769_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5769_, 0, v_f_5723_);
lean_closure_set(v___f_5769_, 1, v_fn_5766_);
v___x_5770_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5770_, 0, v_x_5724_);
v___x_5771_ = lean_apply_2(v_toPure_5764_, lean_box(0), v___x_5770_);
v___x_5772_ = lean_apply_4(v_toSeq_5765_, lean_box(0), lean_box(0), v___x_5771_, v___f_5769_);
v___x_5773_ = lean_apply_4(v_toSeq_5765_, lean_box(0), lean_box(0), v___x_5772_, v___f_5768_);
return v___x_5773_;
}
case 11:
{
lean_object* v_toFunctor_5774_; lean_object* v_struct_5775_; lean_object* v_map_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; 
v_toFunctor_5774_ = lean_ctor_get(v_inst_5722_, 0);
lean_inc_ref(v_toFunctor_5774_);
lean_dec_ref(v_inst_5722_);
v_struct_5775_ = lean_ctor_get(v_x_5724_, 2);
lean_inc_ref(v_struct_5775_);
v_map_5776_ = lean_ctor_get(v_toFunctor_5774_, 0);
lean_inc(v_map_5776_);
lean_dec_ref(v_toFunctor_5774_);
v___x_5777_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5777_, 0, v_x_5724_);
v___x_5778_ = lean_apply_1(v_f_5723_, v_struct_5775_);
v___x_5779_ = lean_apply_4(v_map_5776_, lean_box(0), lean_box(0), v___x_5777_, v___x_5778_);
return v___x_5779_;
}
default: 
{
lean_object* v_toPure_5780_; lean_object* v___x_5781_; 
lean_dec(v_f_5723_);
v_toPure_5780_ = lean_ctor_get(v_inst_5722_, 1);
lean_inc(v_toPure_5780_);
lean_dec_ref(v_inst_5722_);
v___x_5781_ = lean_apply_2(v_toPure_5780_, lean_box(0), v_x_5724_);
return v___x_5781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5782_, lean_object* v_inst_5783_, lean_object* v_f_5784_, lean_object* v_x_5785_){
_start:
{
lean_object* v___x_5786_; 
v___x_5786_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5783_, v_f_5784_, v_x_5785_);
return v___x_5786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5787_){
_start:
{
lean_object* v_snd_5788_; 
v_snd_5788_ = lean_ctor_get(v_self_5787_, 1);
lean_inc(v_snd_5788_);
return v_snd_5788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5789_){
_start:
{
lean_object* v_res_5790_; 
v_res_5790_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5789_);
lean_dec_ref(v_self_5789_);
return v_res_5790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5791_, lean_object* v_snd_5792_){
_start:
{
lean_object* v___x_5793_; 
v___x_5793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5793_, 0, v_e_x27_5791_);
lean_ctor_set(v___x_5793_, 1, v_snd_5792_);
return v___x_5793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5794_, lean_object* v_map_5795_, lean_object* v_e_x27_5796_, lean_object* v_a_5797_){
_start:
{
lean_object* v___f_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; 
lean_inc_ref(v_e_x27_5796_);
v___f_5798_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5798_, 0, v_e_x27_5796_);
v___x_5799_ = lean_apply_2(v_f_5794_, v_a_5797_, v_e_x27_5796_);
v___x_5800_ = lean_apply_4(v_map_5795_, lean_box(0), lean_box(0), v___f_5798_, v___x_5799_);
return v___x_5800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5802_, lean_object* v_f_5803_, lean_object* v_init_5804_, lean_object* v_e_5805_){
_start:
{
lean_object* v_toApplicative_5806_; lean_object* v_toFunctor_5807_; lean_object* v___x_5809_; uint8_t v_isShared_5810_; uint8_t v_isSharedCheck_5834_; 
v_toApplicative_5806_ = lean_ctor_get(v_inst_5802_, 0);
lean_inc_ref(v_toApplicative_5806_);
v_toFunctor_5807_ = lean_ctor_get(v_toApplicative_5806_, 0);
v_isSharedCheck_5834_ = !lean_is_exclusive(v_toApplicative_5806_);
if (v_isSharedCheck_5834_ == 0)
{
lean_object* v_unused_5835_; lean_object* v_unused_5836_; lean_object* v_unused_5837_; lean_object* v_unused_5838_; 
v_unused_5835_ = lean_ctor_get(v_toApplicative_5806_, 4);
lean_dec(v_unused_5835_);
v_unused_5836_ = lean_ctor_get(v_toApplicative_5806_, 3);
lean_dec(v_unused_5836_);
v_unused_5837_ = lean_ctor_get(v_toApplicative_5806_, 2);
lean_dec(v_unused_5837_);
v_unused_5838_ = lean_ctor_get(v_toApplicative_5806_, 1);
lean_dec(v_unused_5838_);
v___x_5809_ = v_toApplicative_5806_;
v_isShared_5810_ = v_isSharedCheck_5834_;
goto v_resetjp_5808_;
}
else
{
lean_inc(v_toFunctor_5807_);
lean_dec(v_toApplicative_5806_);
v___x_5809_ = lean_box(0);
v_isShared_5810_ = v_isSharedCheck_5834_;
goto v_resetjp_5808_;
}
v_resetjp_5808_:
{
lean_object* v_map_5811_; lean_object* v___x_5813_; uint8_t v_isShared_5814_; uint8_t v_isSharedCheck_5832_; 
v_map_5811_ = lean_ctor_get(v_toFunctor_5807_, 0);
v_isSharedCheck_5832_ = !lean_is_exclusive(v_toFunctor_5807_);
if (v_isSharedCheck_5832_ == 0)
{
lean_object* v_unused_5833_; 
v_unused_5833_ = lean_ctor_get(v_toFunctor_5807_, 1);
lean_dec(v_unused_5833_);
v___x_5813_ = v_toFunctor_5807_;
v_isShared_5814_ = v_isSharedCheck_5832_;
goto v_resetjp_5812_;
}
else
{
lean_inc(v_map_5811_);
lean_dec(v_toFunctor_5807_);
v___x_5813_ = lean_box(0);
v_isShared_5814_ = v_isSharedCheck_5832_;
goto v_resetjp_5812_;
}
v_resetjp_5812_:
{
lean_object* v___f_5815_; lean_object* v___f_5816_; lean_object* v___f_5817_; lean_object* v___f_5818_; lean_object* v___f_5819_; lean_object* v___f_5820_; lean_object* v___x_5821_; lean_object* v___x_5823_; 
v___f_5815_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5811_);
v___f_5816_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5816_, 0, v_f_5803_);
lean_closure_set(v___f_5816_, 1, v_map_5811_);
lean_inc_ref_n(v_inst_5802_, 5);
v___f_5817_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5817_, 0, v_inst_5802_);
v___f_5818_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5818_, 0, v_inst_5802_);
v___f_5819_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5819_, 0, v_inst_5802_);
v___f_5820_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5820_, 0, v_inst_5802_);
v___x_5821_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5821_, 0, lean_box(0));
lean_closure_set(v___x_5821_, 1, lean_box(0));
lean_closure_set(v___x_5821_, 2, v_inst_5802_);
if (v_isShared_5814_ == 0)
{
lean_ctor_set(v___x_5813_, 1, v___f_5817_);
lean_ctor_set(v___x_5813_, 0, v___x_5821_);
v___x_5823_ = v___x_5813_;
goto v_reusejp_5822_;
}
else
{
lean_object* v_reuseFailAlloc_5831_; 
v_reuseFailAlloc_5831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5831_, 0, v___x_5821_);
lean_ctor_set(v_reuseFailAlloc_5831_, 1, v___f_5817_);
v___x_5823_ = v_reuseFailAlloc_5831_;
goto v_reusejp_5822_;
}
v_reusejp_5822_:
{
lean_object* v___x_5824_; lean_object* v___x_5826_; 
v___x_5824_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5824_, 0, lean_box(0));
lean_closure_set(v___x_5824_, 1, lean_box(0));
lean_closure_set(v___x_5824_, 2, v_inst_5802_);
if (v_isShared_5810_ == 0)
{
lean_ctor_set(v___x_5809_, 4, v___f_5820_);
lean_ctor_set(v___x_5809_, 3, v___f_5819_);
lean_ctor_set(v___x_5809_, 2, v___f_5818_);
lean_ctor_set(v___x_5809_, 1, v___x_5824_);
lean_ctor_set(v___x_5809_, 0, v___x_5823_);
v___x_5826_ = v___x_5809_;
goto v_reusejp_5825_;
}
else
{
lean_object* v_reuseFailAlloc_5830_; 
v_reuseFailAlloc_5830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5830_, 0, v___x_5823_);
lean_ctor_set(v_reuseFailAlloc_5830_, 1, v___x_5824_);
lean_ctor_set(v_reuseFailAlloc_5830_, 2, v___f_5818_);
lean_ctor_set(v_reuseFailAlloc_5830_, 3, v___f_5819_);
lean_ctor_set(v_reuseFailAlloc_5830_, 4, v___f_5820_);
v___x_5826_ = v_reuseFailAlloc_5830_;
goto v_reusejp_5825_;
}
v_reusejp_5825_:
{
lean_object* v___x_30__overap_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; 
v___x_30__overap_5827_ = l_Lean_Expr_traverseChildren___redArg(v___x_5826_, v___f_5816_, v_e_5805_);
v___x_5828_ = lean_apply_1(v___x_30__overap_5827_, v_init_5804_);
v___x_5829_ = lean_apply_4(v_map_5811_, lean_box(0), lean_box(0), v___f_5815_, v___x_5828_);
return v___x_5829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5839_, lean_object* v_m_5840_, lean_object* v_inst_5841_, lean_object* v_f_5842_, lean_object* v_init_5843_, lean_object* v_e_5844_){
_start:
{
lean_object* v___x_5845_; 
v___x_5845_ = l_Lean_Expr_foldlM___redArg(v_inst_5841_, v_f_5842_, v_init_5843_, v_e_5844_);
return v___x_5845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5846_){
_start:
{
lean_object* v_d_5848_; lean_object* v_b_5849_; 
switch(lean_obj_tag(v_x_5846_))
{
case 5:
{
lean_object* v_fn_5855_; lean_object* v_arg_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; 
v_fn_5855_ = lean_ctor_get(v_x_5846_, 0);
v_arg_5856_ = lean_ctor_get(v_x_5846_, 1);
v___x_5857_ = lean_unsigned_to_nat(1u);
v___x_5858_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5855_);
v___x_5859_ = lean_nat_add(v___x_5857_, v___x_5858_);
lean_dec(v___x_5858_);
v___x_5860_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5856_);
v___x_5861_ = lean_nat_add(v___x_5859_, v___x_5860_);
lean_dec(v___x_5860_);
lean_dec(v___x_5859_);
return v___x_5861_;
}
case 6:
{
lean_object* v_binderType_5862_; lean_object* v_body_5863_; 
v_binderType_5862_ = lean_ctor_get(v_x_5846_, 1);
v_body_5863_ = lean_ctor_get(v_x_5846_, 2);
v_d_5848_ = v_binderType_5862_;
v_b_5849_ = v_body_5863_;
goto v___jp_5847_;
}
case 7:
{
lean_object* v_binderType_5864_; lean_object* v_body_5865_; 
v_binderType_5864_ = lean_ctor_get(v_x_5846_, 1);
v_body_5865_ = lean_ctor_get(v_x_5846_, 2);
v_d_5848_ = v_binderType_5864_;
v_b_5849_ = v_body_5865_;
goto v___jp_5847_;
}
case 8:
{
lean_object* v_type_5866_; lean_object* v_value_5867_; lean_object* v_body_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; 
v_type_5866_ = lean_ctor_get(v_x_5846_, 1);
v_value_5867_ = lean_ctor_get(v_x_5846_, 2);
v_body_5868_ = lean_ctor_get(v_x_5846_, 3);
v___x_5869_ = lean_unsigned_to_nat(1u);
v___x_5870_ = l_Lean_Expr_sizeWithoutSharing(v_type_5866_);
v___x_5871_ = lean_nat_add(v___x_5869_, v___x_5870_);
lean_dec(v___x_5870_);
v___x_5872_ = l_Lean_Expr_sizeWithoutSharing(v_value_5867_);
v___x_5873_ = lean_nat_add(v___x_5871_, v___x_5872_);
lean_dec(v___x_5872_);
lean_dec(v___x_5871_);
v___x_5874_ = l_Lean_Expr_sizeWithoutSharing(v_body_5868_);
v___x_5875_ = lean_nat_add(v___x_5873_, v___x_5874_);
lean_dec(v___x_5874_);
lean_dec(v___x_5873_);
return v___x_5875_;
}
case 10:
{
lean_object* v_expr_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; 
v_expr_5876_ = lean_ctor_get(v_x_5846_, 1);
v___x_5877_ = lean_unsigned_to_nat(1u);
v___x_5878_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5876_);
v___x_5879_ = lean_nat_add(v___x_5877_, v___x_5878_);
lean_dec(v___x_5878_);
return v___x_5879_;
}
case 11:
{
lean_object* v_struct_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; 
v_struct_5880_ = lean_ctor_get(v_x_5846_, 2);
v___x_5881_ = lean_unsigned_to_nat(1u);
v___x_5882_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5880_);
v___x_5883_ = lean_nat_add(v___x_5881_, v___x_5882_);
lean_dec(v___x_5882_);
return v___x_5883_;
}
default: 
{
lean_object* v___x_5884_; 
v___x_5884_ = lean_unsigned_to_nat(1u);
return v___x_5884_;
}
}
v___jp_5847_:
{
lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5850_ = lean_unsigned_to_nat(1u);
v___x_5851_ = l_Lean_Expr_sizeWithoutSharing(v_d_5848_);
v___x_5852_ = lean_nat_add(v___x_5850_, v___x_5851_);
lean_dec(v___x_5851_);
v___x_5853_ = l_Lean_Expr_sizeWithoutSharing(v_b_5849_);
v___x_5854_ = lean_nat_add(v___x_5852_, v___x_5853_);
lean_dec(v___x_5853_);
lean_dec(v___x_5852_);
return v___x_5854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5885_){
_start:
{
lean_object* v_res_5886_; 
v_res_5886_ = l_Lean_Expr_sizeWithoutSharing(v_x_5885_);
lean_dec_ref(v_x_5885_);
return v_res_5886_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5889_, lean_object* v_e_5890_){
_start:
{
lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; 
v___x_5891_ = l_Lean_KVMap_empty;
v___x_5892_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5893_ = l_Lean_KVMap_insert(v___x_5891_, v_kind_5889_, v___x_5892_);
v___x_5894_ = l_Lean_Expr_mdata___override(v___x_5893_, v_e_5890_);
return v___x_5894_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5895_, lean_object* v_e_5896_){
_start:
{
if (lean_obj_tag(v_e_5896_) == 10)
{
lean_object* v_data_5897_; lean_object* v_expr_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; uint8_t v___x_5901_; 
v_data_5897_ = lean_ctor_get(v_e_5896_, 0);
v_expr_5898_ = lean_ctor_get(v_e_5896_, 1);
v___x_5899_ = l_Lean_KVMap_size(v_data_5897_);
v___x_5900_ = lean_unsigned_to_nat(1u);
v___x_5901_ = lean_nat_dec_eq(v___x_5899_, v___x_5900_);
lean_dec(v___x_5899_);
if (v___x_5901_ == 0)
{
lean_object* v___x_5902_; 
v___x_5902_ = lean_box(0);
return v___x_5902_;
}
else
{
uint8_t v___x_5903_; uint8_t v___x_5904_; 
v___x_5903_ = 0;
v___x_5904_ = l_Lean_KVMap_getBool(v_data_5897_, v_kind_5895_, v___x_5903_);
if (v___x_5904_ == 0)
{
lean_object* v___x_5905_; 
v___x_5905_ = lean_box(0);
return v___x_5905_;
}
else
{
lean_object* v___x_5906_; 
lean_inc_ref(v_expr_5898_);
v___x_5906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5906_, 0, v_expr_5898_);
return v___x_5906_;
}
}
}
else
{
lean_object* v___x_5907_; 
v___x_5907_ = lean_box(0);
return v___x_5907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* v_kind_5908_, lean_object* v_e_5909_){
_start:
{
lean_object* v_res_5910_; 
v_res_5910_ = l_Lean_annotation_x3f(v_kind_5908_, v_e_5909_);
lean_dec_ref(v_e_5909_);
lean_dec(v_kind_5908_);
return v_res_5910_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* v_e_5914_){
_start:
{
lean_object* v___x_5915_; lean_object* v___x_5916_; 
v___x_5915_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5916_ = l_Lean_mkAnnotation(v___x_5915_, v_e_5914_);
return v___x_5916_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* v_e_5917_){
_start:
{
lean_object* v___x_5918_; lean_object* v___x_5919_; 
v___x_5918_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5919_ = l_Lean_annotation_x3f(v___x_5918_, v_e_5917_);
return v___x_5919_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* v_e_5920_){
_start:
{
lean_object* v_res_5921_; 
v_res_5921_ = l_Lean_inaccessible_x3f(v_e_5920_);
lean_dec_ref(v_e_5920_);
return v_res_5921_;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* v_p_5926_){
_start:
{
if (lean_obj_tag(v_p_5926_) == 10)
{
lean_object* v_data_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; 
v_data_5927_ = lean_ctor_get(v_p_5926_, 0);
v___x_5928_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5929_ = l_Lean_KVMap_find(v_data_5927_, v___x_5928_);
if (lean_obj_tag(v___x_5929_) == 1)
{
lean_object* v_val_5930_; lean_object* v___x_5932_; uint8_t v_isShared_5933_; uint8_t v_isSharedCheck_5941_; 
v_val_5930_ = lean_ctor_get(v___x_5929_, 0);
v_isSharedCheck_5941_ = !lean_is_exclusive(v___x_5929_);
if (v_isSharedCheck_5941_ == 0)
{
v___x_5932_ = v___x_5929_;
v_isShared_5933_ = v_isSharedCheck_5941_;
goto v_resetjp_5931_;
}
else
{
lean_inc(v_val_5930_);
lean_dec(v___x_5929_);
v___x_5932_ = lean_box(0);
v_isShared_5933_ = v_isSharedCheck_5941_;
goto v_resetjp_5931_;
}
v_resetjp_5931_:
{
if (lean_obj_tag(v_val_5930_) == 5)
{
lean_object* v_v_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5938_; 
v_v_5934_ = lean_ctor_get(v_val_5930_, 0);
lean_inc(v_v_5934_);
lean_dec_ref_known(v_val_5930_, 1);
v___x_5935_ = l_Lean_Expr_mdataExpr_x21(v_p_5926_);
v___x_5936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5936_, 0, v_v_5934_);
lean_ctor_set(v___x_5936_, 1, v___x_5935_);
if (v_isShared_5933_ == 0)
{
lean_ctor_set(v___x_5932_, 0, v___x_5936_);
v___x_5938_ = v___x_5932_;
goto v_reusejp_5937_;
}
else
{
lean_object* v_reuseFailAlloc_5939_; 
v_reuseFailAlloc_5939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5939_, 0, v___x_5936_);
v___x_5938_ = v_reuseFailAlloc_5939_;
goto v_reusejp_5937_;
}
v_reusejp_5937_:
{
return v___x_5938_;
}
}
else
{
lean_object* v___x_5940_; 
lean_del_object(v___x_5932_);
lean_dec(v_val_5930_);
v___x_5940_ = lean_box(0);
return v___x_5940_;
}
}
}
else
{
lean_object* v___x_5942_; 
lean_dec(v___x_5929_);
v___x_5942_ = lean_box(0);
return v___x_5942_;
}
}
else
{
lean_object* v___x_5943_; 
v___x_5943_ = lean_box(0);
return v___x_5943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* v_p_5944_){
_start:
{
lean_object* v_res_5945_; 
v_res_5945_ = l_Lean_patternWithRef_x3f(v_p_5944_);
lean_dec_ref(v_p_5944_);
return v_res_5945_;
}
}
uint8_t l_Lean_isPatternWithRef(lean_object* v_p_5946_){
_start:
{
lean_object* v___x_5947_; 
v___x_5947_ = l_Lean_patternWithRef_x3f(v_p_5946_);
if (lean_obj_tag(v___x_5947_) == 0)
{
uint8_t v___x_5948_; 
v___x_5948_ = 0;
return v___x_5948_;
}
else
{
uint8_t v___x_5949_; 
lean_dec_ref_known(v___x_5947_, 1);
v___x_5949_ = 1;
return v___x_5949_;
}
}
}
LEAN_EXPORT void l_Lean_isPatternWithRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_5946_ = stack[0].m_obj;
uint8_t v_res_5950_;
v_res_5950_ = l_Lean_isPatternWithRef(v_p_5946_);
stack->m_num = v_res_5950_;
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* v_p_5951_){
_start:
{
uint8_t v_res_5952_; lean_object* v_r_5953_; 
v_res_5952_ = l_Lean_isPatternWithRef(v_p_5951_);
lean_dec_ref(v_p_5951_);
v_r_5953_ = lean_box(v_res_5952_);
return v_r_5953_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* v_p_5954_, lean_object* v_stx_5955_){
_start:
{
lean_object* v___x_5956_; 
v___x_5956_ = l_Lean_patternWithRef_x3f(v_p_5954_);
if (lean_obj_tag(v___x_5956_) == 0)
{
lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; 
v___x_5957_ = l_Lean_KVMap_empty;
v___x_5958_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5959_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_5959_, 0, v_stx_5955_);
v___x_5960_ = l_Lean_KVMap_insert(v___x_5957_, v___x_5958_, v___x_5959_);
v___x_5961_ = l_Lean_Expr_mdata___override(v___x_5960_, v_p_5954_);
return v___x_5961_;
}
else
{
lean_dec_ref_known(v___x_5956_, 1);
lean_dec(v_stx_5955_);
return v_p_5954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* v_e_5962_){
_start:
{
lean_object* v___x_5963_; 
v___x_5963_ = l_Lean_inaccessible_x3f(v_e_5962_);
if (lean_obj_tag(v___x_5963_) == 1)
{
return v___x_5963_;
}
else
{
lean_object* v___x_5964_; 
lean_dec(v___x_5963_);
v___x_5964_ = l_Lean_patternWithRef_x3f(v_e_5962_);
if (lean_obj_tag(v___x_5964_) == 1)
{
lean_object* v_val_5965_; lean_object* v___x_5967_; uint8_t v_isShared_5968_; uint8_t v_isSharedCheck_5973_; 
v_val_5965_ = lean_ctor_get(v___x_5964_, 0);
v_isSharedCheck_5973_ = !lean_is_exclusive(v___x_5964_);
if (v_isSharedCheck_5973_ == 0)
{
v___x_5967_ = v___x_5964_;
v_isShared_5968_ = v_isSharedCheck_5973_;
goto v_resetjp_5966_;
}
else
{
lean_inc(v_val_5965_);
lean_dec(v___x_5964_);
v___x_5967_ = lean_box(0);
v_isShared_5968_ = v_isSharedCheck_5973_;
goto v_resetjp_5966_;
}
v_resetjp_5966_:
{
lean_object* v_snd_5969_; lean_object* v___x_5971_; 
v_snd_5969_ = lean_ctor_get(v_val_5965_, 1);
lean_inc(v_snd_5969_);
lean_dec(v_val_5965_);
if (v_isShared_5968_ == 0)
{
lean_ctor_set(v___x_5967_, 0, v_snd_5969_);
v___x_5971_ = v___x_5967_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_snd_5969_);
v___x_5971_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
return v___x_5971_;
}
}
}
else
{
lean_object* v___x_5974_; 
lean_dec(v___x_5964_);
v___x_5974_ = lean_box(0);
return v___x_5974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* v_e_5975_){
_start:
{
lean_object* v_res_5976_; 
v_res_5976_ = l_Lean_patternAnnotation_x3f(v_e_5975_);
lean_dec_ref(v_e_5975_);
return v_res_5976_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* v_e_5980_){
_start:
{
lean_object* v___x_5981_; lean_object* v___x_5982_; 
v___x_5981_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5982_ = l_Lean_mkAnnotation(v___x_5981_, v_e_5980_);
return v___x_5982_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* v_e_5986_){
_start:
{
lean_object* v___x_5987_; lean_object* v___x_5988_; 
v___x_5987_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5988_ = l_Lean_annotation_x3f(v___x_5987_, v_e_5986_);
if (lean_obj_tag(v___x_5988_) == 0)
{
return v___x_5988_;
}
else
{
lean_object* v_val_5989_; lean_object* v___x_5991_; uint8_t v_isShared_5992_; uint8_t v_isSharedCheck_6002_; 
v_val_5989_ = lean_ctor_get(v___x_5988_, 0);
v_isSharedCheck_6002_ = !lean_is_exclusive(v___x_5988_);
if (v_isSharedCheck_6002_ == 0)
{
v___x_5991_ = v___x_5988_;
v_isShared_5992_ = v_isSharedCheck_6002_;
goto v_resetjp_5990_;
}
else
{
lean_inc(v_val_5989_);
lean_dec(v___x_5988_);
v___x_5991_ = lean_box(0);
v_isShared_5992_ = v_isSharedCheck_6002_;
goto v_resetjp_5990_;
}
v_resetjp_5990_:
{
lean_object* v___x_5993_; lean_object* v___x_5994_; uint8_t v___x_5995_; 
v___x_5993_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5994_ = lean_unsigned_to_nat(3u);
v___x_5995_ = l_Lean_Expr_isAppOfArity(v_val_5989_, v___x_5993_, v___x_5994_);
if (v___x_5995_ == 0)
{
lean_object* v___x_5996_; 
lean_del_object(v___x_5991_);
lean_dec(v_val_5989_);
v___x_5996_ = lean_box(0);
return v___x_5996_;
}
else
{
lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_6000_; 
v___x_5997_ = l_Lean_Expr_appFn_x21(v_val_5989_);
lean_dec(v_val_5989_);
v___x_5998_ = l_Lean_Expr_appArg_x21(v___x_5997_);
lean_dec_ref(v___x_5997_);
if (v_isShared_5992_ == 0)
{
lean_ctor_set(v___x_5991_, 0, v___x_5998_);
v___x_6000_ = v___x_5991_;
goto v_reusejp_5999_;
}
else
{
lean_object* v_reuseFailAlloc_6001_; 
v_reuseFailAlloc_6001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6001_, 0, v___x_5998_);
v___x_6000_ = v_reuseFailAlloc_6001_;
goto v_reusejp_5999_;
}
v_reusejp_5999_:
{
return v___x_6000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* v_e_6003_){
_start:
{
lean_object* v_res_6004_; 
v_res_6004_ = l_Lean_isLHSGoal_x3f(v_e_6003_);
lean_dec_ref(v_e_6003_);
return v_res_6004_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* v_toPure_6005_, lean_object* v_____do__lift_6006_){
_start:
{
lean_object* v___x_6007_; 
v___x_6007_ = lean_apply_2(v_toPure_6005_, lean_box(0), v_____do__lift_6006_);
return v___x_6007_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* v_inst_6008_, lean_object* v_inst_6009_){
_start:
{
lean_object* v_toApplicative_6010_; lean_object* v_toBind_6011_; lean_object* v_toPure_6012_; lean_object* v___x_6013_; lean_object* v___f_6014_; lean_object* v___x_6015_; 
v_toApplicative_6010_ = lean_ctor_get(v_inst_6008_, 0);
v_toBind_6011_ = lean_ctor_get(v_inst_6008_, 1);
lean_inc(v_toBind_6011_);
v_toPure_6012_ = lean_ctor_get(v_toApplicative_6010_, 1);
lean_inc(v_toPure_6012_);
v___x_6013_ = l_Lean_mkFreshId___redArg(v_inst_6008_, v_inst_6009_);
v___f_6014_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_6014_, 0, v_toPure_6012_);
v___x_6015_ = lean_apply_4(v_toBind_6011_, lean_box(0), lean_box(0), v___x_6013_, v___f_6014_);
return v___x_6015_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* v_m_6016_, lean_object* v_inst_6017_, lean_object* v_inst_6018_){
_start:
{
lean_object* v___x_6019_; 
v___x_6019_ = l_Lean_mkFreshFVarId___redArg(v_inst_6017_, v_inst_6018_);
return v___x_6019_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* v_inst_6020_, lean_object* v_inst_6021_){
_start:
{
lean_object* v_toApplicative_6022_; lean_object* v_toBind_6023_; lean_object* v_toPure_6024_; lean_object* v___x_6025_; lean_object* v___f_6026_; lean_object* v___x_6027_; 
v_toApplicative_6022_ = lean_ctor_get(v_inst_6020_, 0);
v_toBind_6023_ = lean_ctor_get(v_inst_6020_, 1);
lean_inc(v_toBind_6023_);
v_toPure_6024_ = lean_ctor_get(v_toApplicative_6022_, 1);
lean_inc(v_toPure_6024_);
v___x_6025_ = l_Lean_mkFreshId___redArg(v_inst_6020_, v_inst_6021_);
v___f_6026_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_6026_, 0, v_toPure_6024_);
v___x_6027_ = lean_apply_4(v_toBind_6023_, lean_box(0), lean_box(0), v___x_6025_, v___f_6026_);
return v___x_6027_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* v_m_6028_, lean_object* v_inst_6029_, lean_object* v_inst_6030_){
_start:
{
lean_object* v___x_6031_; 
v___x_6031_ = l_Lean_mkFreshMVarId___redArg(v_inst_6029_, v_inst_6030_);
return v___x_6031_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* v_inst_6032_, lean_object* v_inst_6033_){
_start:
{
lean_object* v_toApplicative_6034_; lean_object* v_toBind_6035_; lean_object* v_toPure_6036_; lean_object* v___x_6037_; lean_object* v___f_6038_; lean_object* v___x_6039_; 
v_toApplicative_6034_ = lean_ctor_get(v_inst_6032_, 0);
v_toBind_6035_ = lean_ctor_get(v_inst_6032_, 1);
lean_inc(v_toBind_6035_);
v_toPure_6036_ = lean_ctor_get(v_toApplicative_6034_, 1);
lean_inc(v_toPure_6036_);
v___x_6037_ = l_Lean_mkFreshId___redArg(v_inst_6032_, v_inst_6033_);
v___f_6038_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_6038_, 0, v_toPure_6036_);
v___x_6039_ = lean_apply_4(v_toBind_6035_, lean_box(0), lean_box(0), v___x_6037_, v___f_6038_);
return v___x_6039_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* v_m_6040_, lean_object* v_inst_6041_, lean_object* v_inst_6042_){
_start:
{
lean_object* v___x_6043_; 
v___x_6043_ = l_Lean_mkFreshLMVarId___redArg(v_inst_6041_, v_inst_6042_);
return v___x_6043_;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2(void){
_start:
{
lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; 
v___x_6047_ = lean_box(0);
v___x_6048_ = ((lean_object*)(l_Lean_mkNot___closed__1));
v___x_6049_ = l_Lean_Expr_const___override(v___x_6048_, v___x_6047_);
return v___x_6049_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* v_p_6050_){
_start:
{
lean_object* v___x_6051_; lean_object* v___x_6052_; 
v___x_6051_ = lean_obj_once(&l_Lean_mkNot___closed__2, &l_Lean_mkNot___closed__2_once, _init_l_Lean_mkNot___closed__2);
v___x_6052_ = l_Lean_Expr_app___override(v___x_6051_, v_p_6050_);
return v___x_6052_;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2(void){
_start:
{
lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; 
v___x_6056_ = lean_box(0);
v___x_6057_ = ((lean_object*)(l_Lean_mkOr___closed__1));
v___x_6058_ = l_Lean_Expr_const___override(v___x_6057_, v___x_6056_);
return v___x_6058_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* v_p_6059_, lean_object* v_q_6060_){
_start:
{
lean_object* v___x_6061_; lean_object* v___x_6062_; 
v___x_6061_ = lean_obj_once(&l_Lean_mkOr___closed__2, &l_Lean_mkOr___closed__2_once, _init_l_Lean_mkOr___closed__2);
v___x_6062_ = l_Lean_mkAppB(v___x_6061_, v_p_6059_, v_q_6060_);
return v___x_6062_;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2(void){
_start:
{
lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; 
v___x_6066_ = lean_box(0);
v___x_6067_ = ((lean_object*)(l_Lean_mkAnd___closed__1));
v___x_6068_ = l_Lean_Expr_const___override(v___x_6067_, v___x_6066_);
return v___x_6068_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* v_p_6069_, lean_object* v_q_6070_){
_start:
{
lean_object* v___x_6071_; lean_object* v___x_6072_; 
v___x_6071_ = lean_obj_once(&l_Lean_mkAnd___closed__2, &l_Lean_mkAnd___closed__2_once, _init_l_Lean_mkAnd___closed__2);
v___x_6072_ = l_Lean_mkAppB(v___x_6071_, v_p_6069_, v_q_6070_);
return v___x_6072_;
}
}
static lean_object* _init_l_Lean_mkAndN___closed__0(void){
_start:
{
lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; 
v___x_6073_ = lean_box(0);
v___x_6074_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_6075_ = l_Lean_Expr_const___override(v___x_6074_, v___x_6073_);
return v___x_6075_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* v_x_6076_){
_start:
{
if (lean_obj_tag(v_x_6076_) == 0)
{
lean_object* v___x_6077_; 
v___x_6077_ = lean_obj_once(&l_Lean_mkAndN___closed__0, &l_Lean_mkAndN___closed__0_once, _init_l_Lean_mkAndN___closed__0);
return v___x_6077_;
}
else
{
lean_object* v_tail_6078_; 
v_tail_6078_ = lean_ctor_get(v_x_6076_, 1);
if (lean_obj_tag(v_tail_6078_) == 0)
{
lean_object* v_head_6079_; 
v_head_6079_ = lean_ctor_get(v_x_6076_, 0);
lean_inc(v_head_6079_);
lean_dec_ref_known(v_x_6076_, 2);
return v_head_6079_;
}
else
{
lean_object* v_head_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; 
lean_inc(v_tail_6078_);
v_head_6080_ = lean_ctor_get(v_x_6076_, 0);
lean_inc(v_head_6080_);
lean_dec_ref_known(v_x_6076_, 2);
v___x_6081_ = l_Lean_mkAndN(v_tail_6078_);
v___x_6082_ = l_Lean_mkAnd(v_head_6080_, v___x_6081_);
return v___x_6082_;
}
}
}
}
static lean_object* _init_l_Lean_mkEM___closed__3(void){
_start:
{
lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; 
v___x_6088_ = lean_box(0);
v___x_6089_ = ((lean_object*)(l_Lean_mkEM___closed__2));
v___x_6090_ = l_Lean_Expr_const___override(v___x_6089_, v___x_6088_);
return v___x_6090_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* v_p_6091_){
_start:
{
lean_object* v___x_6092_; lean_object* v___x_6093_; 
v___x_6092_ = lean_obj_once(&l_Lean_mkEM___closed__3, &l_Lean_mkEM___closed__3_once, _init_l_Lean_mkEM___closed__3);
v___x_6093_ = l_Lean_Expr_app___override(v___x_6092_, v_p_6091_);
return v___x_6093_;
}
}
static lean_object* _init_l_Lean_mkIff___closed__2(void){
_start:
{
lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; 
v___x_6097_ = lean_box(0);
v___x_6098_ = ((lean_object*)(l_Lean_mkIff___closed__1));
v___x_6099_ = l_Lean_Expr_const___override(v___x_6098_, v___x_6097_);
return v___x_6099_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* v_p_6100_, lean_object* v_q_6101_){
_start:
{
lean_object* v___x_6102_; lean_object* v___x_6103_; 
v___x_6102_ = lean_obj_once(&l_Lean_mkIff___closed__2, &l_Lean_mkIff___closed__2_once, _init_l_Lean_mkIff___closed__2);
v___x_6103_ = l_Lean_mkAppB(v___x_6102_, v_p_6100_, v_q_6101_);
return v___x_6103_;
}
}
static lean_object* _init_l_Lean_Nat_mkType(void){
_start:
{
lean_object* v___x_6104_; 
v___x_6104_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_6104_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; 
v___x_6108_ = lean_box(0);
v___x_6109_ = ((lean_object*)(l_Lean_Nat_mkInstAdd___closed__1));
v___x_6110_ = l_Lean_Expr_const___override(v___x_6109_, v___x_6108_);
return v___x_6110_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd(void){
_start:
{
lean_object* v___x_6111_; 
v___x_6111_ = lean_obj_once(&l_Lean_Nat_mkInstAdd___closed__2, &l_Lean_Nat_mkInstAdd___closed__2_once, _init_l_Lean_Nat_mkInstAdd___closed__2);
return v___x_6111_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__2(void){
_start:
{
lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; 
v___x_6115_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6116_ = ((lean_object*)(l_Lean_Nat_mkInstHAdd___closed__1));
v___x_6117_ = l_Lean_Expr_const___override(v___x_6116_, v___x_6115_);
return v___x_6117_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__3(void){
_start:
{
lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; 
v___x_6118_ = l_Lean_Nat_mkInstAdd;
v___x_6119_ = l_Lean_Nat_mkType;
v___x_6120_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6121_ = l_Lean_mkAppB(v___x_6120_, v___x_6119_, v___x_6118_);
return v___x_6121_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd(void){
_start:
{
lean_object* v___x_6122_; 
v___x_6122_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__3, &l_Lean_Nat_mkInstHAdd___closed__3_once, _init_l_Lean_Nat_mkInstHAdd___closed__3);
return v___x_6122_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; 
v___x_6126_ = lean_box(0);
v___x_6127_ = ((lean_object*)(l_Lean_Nat_mkInstSub___closed__1));
v___x_6128_ = l_Lean_Expr_const___override(v___x_6127_, v___x_6126_);
return v___x_6128_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub(void){
_start:
{
lean_object* v___x_6129_; 
v___x_6129_ = lean_obj_once(&l_Lean_Nat_mkInstSub___closed__2, &l_Lean_Nat_mkInstSub___closed__2_once, _init_l_Lean_Nat_mkInstSub___closed__2);
return v___x_6129_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__2(void){
_start:
{
lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; 
v___x_6133_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6134_ = ((lean_object*)(l_Lean_Nat_mkInstHSub___closed__1));
v___x_6135_ = l_Lean_Expr_const___override(v___x_6134_, v___x_6133_);
return v___x_6135_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__3(void){
_start:
{
lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; 
v___x_6136_ = l_Lean_Nat_mkInstSub;
v___x_6137_ = l_Lean_Nat_mkType;
v___x_6138_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6139_ = l_Lean_mkAppB(v___x_6138_, v___x_6137_, v___x_6136_);
return v___x_6139_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub(void){
_start:
{
lean_object* v___x_6140_; 
v___x_6140_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__3, &l_Lean_Nat_mkInstHSub___closed__3_once, _init_l_Lean_Nat_mkInstHSub___closed__3);
return v___x_6140_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; 
v___x_6144_ = lean_box(0);
v___x_6145_ = ((lean_object*)(l_Lean_Nat_mkInstMul___closed__1));
v___x_6146_ = l_Lean_Expr_const___override(v___x_6145_, v___x_6144_);
return v___x_6146_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul(void){
_start:
{
lean_object* v___x_6147_; 
v___x_6147_ = lean_obj_once(&l_Lean_Nat_mkInstMul___closed__2, &l_Lean_Nat_mkInstMul___closed__2_once, _init_l_Lean_Nat_mkInstMul___closed__2);
return v___x_6147_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__2(void){
_start:
{
lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; 
v___x_6151_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6152_ = ((lean_object*)(l_Lean_Nat_mkInstHMul___closed__1));
v___x_6153_ = l_Lean_Expr_const___override(v___x_6152_, v___x_6151_);
return v___x_6153_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; 
v___x_6154_ = l_Lean_Nat_mkInstMul;
v___x_6155_ = l_Lean_Nat_mkType;
v___x_6156_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6157_ = l_Lean_mkAppB(v___x_6156_, v___x_6155_, v___x_6154_);
return v___x_6157_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul(void){
_start:
{
lean_object* v___x_6158_; 
v___x_6158_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__3, &l_Lean_Nat_mkInstHMul___closed__3_once, _init_l_Lean_Nat_mkInstHMul___closed__3);
return v___x_6158_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv___closed__2(void){
_start:
{
lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; 
v___x_6163_ = lean_box(0);
v___x_6164_ = ((lean_object*)(l_Lean_Nat_mkInstDiv___closed__1));
v___x_6165_ = l_Lean_Expr_const___override(v___x_6164_, v___x_6163_);
return v___x_6165_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv(void){
_start:
{
lean_object* v___x_6166_; 
v___x_6166_ = lean_obj_once(&l_Lean_Nat_mkInstDiv___closed__2, &l_Lean_Nat_mkInstDiv___closed__2_once, _init_l_Lean_Nat_mkInstDiv___closed__2);
return v___x_6166_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__2(void){
_start:
{
lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; 
v___x_6170_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6171_ = ((lean_object*)(l_Lean_Nat_mkInstHDiv___closed__1));
v___x_6172_ = l_Lean_Expr_const___override(v___x_6171_, v___x_6170_);
return v___x_6172_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__3(void){
_start:
{
lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; 
v___x_6173_ = l_Lean_Nat_mkInstDiv;
v___x_6174_ = l_Lean_Nat_mkType;
v___x_6175_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6176_ = l_Lean_mkAppB(v___x_6175_, v___x_6174_, v___x_6173_);
return v___x_6176_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv(void){
_start:
{
lean_object* v___x_6177_; 
v___x_6177_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__3, &l_Lean_Nat_mkInstHDiv___closed__3_once, _init_l_Lean_Nat_mkInstHDiv___closed__3);
return v___x_6177_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod___closed__2(void){
_start:
{
lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; 
v___x_6182_ = lean_box(0);
v___x_6183_ = ((lean_object*)(l_Lean_Nat_mkInstMod___closed__1));
v___x_6184_ = l_Lean_Expr_const___override(v___x_6183_, v___x_6182_);
return v___x_6184_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod(void){
_start:
{
lean_object* v___x_6185_; 
v___x_6185_ = lean_obj_once(&l_Lean_Nat_mkInstMod___closed__2, &l_Lean_Nat_mkInstMod___closed__2_once, _init_l_Lean_Nat_mkInstMod___closed__2);
return v___x_6185_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__2(void){
_start:
{
lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; 
v___x_6189_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6190_ = ((lean_object*)(l_Lean_Nat_mkInstHMod___closed__1));
v___x_6191_ = l_Lean_Expr_const___override(v___x_6190_, v___x_6189_);
return v___x_6191_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__3(void){
_start:
{
lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; 
v___x_6192_ = l_Lean_Nat_mkInstMod;
v___x_6193_ = l_Lean_Nat_mkType;
v___x_6194_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6195_ = l_Lean_mkAppB(v___x_6194_, v___x_6193_, v___x_6192_);
return v___x_6195_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod(void){
_start:
{
lean_object* v___x_6196_; 
v___x_6196_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__3, &l_Lean_Nat_mkInstHMod___closed__3_once, _init_l_Lean_Nat_mkInstHMod___closed__3);
return v___x_6196_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow___closed__2(void){
_start:
{
lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; 
v___x_6200_ = lean_box(0);
v___x_6201_ = ((lean_object*)(l_Lean_Nat_mkInstNatPow___closed__1));
v___x_6202_ = l_Lean_Expr_const___override(v___x_6201_, v___x_6200_);
return v___x_6202_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow(void){
_start:
{
lean_object* v___x_6203_; 
v___x_6203_ = lean_obj_once(&l_Lean_Nat_mkInstNatPow___closed__2, &l_Lean_Nat_mkInstNatPow___closed__2_once, _init_l_Lean_Nat_mkInstNatPow___closed__2);
return v___x_6203_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; 
v___x_6207_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6208_ = ((lean_object*)(l_Lean_Nat_mkInstPow___closed__1));
v___x_6209_ = l_Lean_Expr_const___override(v___x_6208_, v___x_6207_);
return v___x_6209_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__3(void){
_start:
{
lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; 
v___x_6210_ = l_Lean_Nat_mkInstNatPow;
v___x_6211_ = l_Lean_Nat_mkType;
v___x_6212_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6213_ = l_Lean_mkAppB(v___x_6212_, v___x_6211_, v___x_6210_);
return v___x_6213_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow(void){
_start:
{
lean_object* v___x_6214_; 
v___x_6214_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__3, &l_Lean_Nat_mkInstPow___closed__3_once, _init_l_Lean_Nat_mkInstPow___closed__3);
return v___x_6214_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__3(void){
_start:
{
lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; 
v___x_6221_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__2));
v___x_6222_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__1));
v___x_6223_ = l_Lean_Expr_const___override(v___x_6222_, v___x_6221_);
return v___x_6223_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__4(void){
_start:
{
lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; 
v___x_6224_ = l_Lean_Nat_mkInstPow;
v___x_6225_ = l_Lean_Nat_mkType;
v___x_6226_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6227_ = l_Lean_mkApp3(v___x_6226_, v___x_6225_, v___x_6225_, v___x_6224_);
return v___x_6227_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow(void){
_start:
{
lean_object* v___x_6228_; 
v___x_6228_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__4, &l_Lean_Nat_mkInstHPow___closed__4_once, _init_l_Lean_Nat_mkInstHPow___closed__4);
return v___x_6228_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; 
v___x_6232_ = lean_box(0);
v___x_6233_ = ((lean_object*)(l_Lean_Nat_mkInstLT___closed__1));
v___x_6234_ = l_Lean_Expr_const___override(v___x_6233_, v___x_6232_);
return v___x_6234_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT(void){
_start:
{
lean_object* v___x_6235_; 
v___x_6235_ = lean_obj_once(&l_Lean_Nat_mkInstLT___closed__2, &l_Lean_Nat_mkInstLT___closed__2_once, _init_l_Lean_Nat_mkInstLT___closed__2);
return v___x_6235_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6239_; lean_object* v___x_6240_; lean_object* v___x_6241_; 
v___x_6239_ = lean_box(0);
v___x_6240_ = ((lean_object*)(l_Lean_Nat_mkInstLE___closed__1));
v___x_6241_ = l_Lean_Expr_const___override(v___x_6240_, v___x_6239_);
return v___x_6241_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE(void){
_start:
{
lean_object* v___x_6242_; 
v___x_6242_ = lean_obj_once(&l_Lean_Nat_mkInstLE___closed__2, &l_Lean_Nat_mkInstLE___closed__2_once, _init_l_Lean_Nat_mkInstLE___closed__2);
return v___x_6242_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3(void){
_start:
{
lean_object* v___x_6248_; lean_object* v___x_6249_; 
v___x_6248_ = lean_unsigned_to_nat(0u);
v___x_6249_ = l_Lean_Level_ofNat(v___x_6248_);
return v___x_6249_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4(void){
_start:
{
lean_object* v___x_6250_; lean_object* v___x_6251_; lean_object* v___x_6252_; 
v___x_6250_ = lean_box(0);
v___x_6251_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6252_, 0, v___x_6251_);
lean_ctor_set(v___x_6252_, 1, v___x_6250_);
return v___x_6252_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5(void){
_start:
{
lean_object* v___x_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; 
v___x_6253_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6254_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6255_, 0, v___x_6254_);
lean_ctor_set(v___x_6255_, 1, v___x_6253_);
return v___x_6255_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6(void){
_start:
{
lean_object* v___x_6256_; lean_object* v___x_6257_; lean_object* v___x_6258_; 
v___x_6256_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__5, &l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5);
v___x_6257_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6258_, 0, v___x_6257_);
lean_ctor_set(v___x_6258_, 1, v___x_6256_);
return v___x_6258_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7(void){
_start:
{
lean_object* v___x_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; 
v___x_6259_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6260_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natAddFn___closed__2));
v___x_6261_ = l_Lean_Expr_const___override(v___x_6260_, v___x_6259_);
return v___x_6261_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8(void){
_start:
{
lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; 
v___x_6262_ = l_Lean_Nat_mkInstHAdd;
v___x_6263_ = l_Lean_Nat_mkType;
v___x_6264_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6265_ = l_Lean_mkApp4(v___x_6264_, v___x_6263_, v___x_6263_, v___x_6263_, v___x_6262_);
return v___x_6265_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn(void){
_start:
{
lean_object* v___x_6266_; 
v___x_6266_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__8, &l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8);
return v___x_6266_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3(void){
_start:
{
lean_object* v___x_6272_; lean_object* v___x_6273_; lean_object* v___x_6274_; 
v___x_6272_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6273_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natSubFn___closed__2));
v___x_6274_ = l_Lean_Expr_const___override(v___x_6273_, v___x_6272_);
return v___x_6274_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4(void){
_start:
{
lean_object* v___x_6275_; lean_object* v___x_6276_; lean_object* v___x_6277_; lean_object* v___x_6278_; 
v___x_6275_ = l_Lean_Nat_mkInstHSub;
v___x_6276_ = l_Lean_Nat_mkType;
v___x_6277_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6278_ = l_Lean_mkApp4(v___x_6277_, v___x_6276_, v___x_6276_, v___x_6276_, v___x_6275_);
return v___x_6278_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn(void){
_start:
{
lean_object* v___x_6279_; 
v___x_6279_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__4, &l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4);
return v___x_6279_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3(void){
_start:
{
lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; 
v___x_6285_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6286_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natMulFn___closed__2));
v___x_6287_ = l_Lean_Expr_const___override(v___x_6286_, v___x_6285_);
return v___x_6287_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4(void){
_start:
{
lean_object* v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; 
v___x_6288_ = l_Lean_Nat_mkInstHMul;
v___x_6289_ = l_Lean_Nat_mkType;
v___x_6290_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6291_ = l_Lean_mkApp4(v___x_6290_, v___x_6289_, v___x_6289_, v___x_6289_, v___x_6288_);
return v___x_6291_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn(void){
_start:
{
lean_object* v___x_6292_; 
v___x_6292_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__4, &l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4);
return v___x_6292_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3(void){
_start:
{
lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; 
v___x_6298_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6299_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natPowFn___closed__2));
v___x_6300_ = l_Lean_Expr_const___override(v___x_6299_, v___x_6298_);
return v___x_6300_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4(void){
_start:
{
lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; lean_object* v___x_6304_; 
v___x_6301_ = l_Lean_Nat_mkInstHPow;
v___x_6302_ = l_Lean_Nat_mkType;
v___x_6303_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6304_ = l_Lean_mkApp4(v___x_6303_, v___x_6302_, v___x_6302_, v___x_6302_, v___x_6301_);
return v___x_6304_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn(void){
_start:
{
lean_object* v___x_6305_; 
v___x_6305_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__4, &l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4);
return v___x_6305_;
}
}
static lean_object* _init_l_Lean_mkNatSucc___closed__2(void){
_start:
{
lean_object* v___x_6310_; lean_object* v___x_6311_; lean_object* v___x_6312_; 
v___x_6310_ = lean_box(0);
v___x_6311_ = ((lean_object*)(l_Lean_mkNatSucc___closed__1));
v___x_6312_ = l_Lean_Expr_const___override(v___x_6311_, v___x_6310_);
return v___x_6312_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* v_a_6313_){
_start:
{
lean_object* v___x_6314_; lean_object* v___x_6315_; 
v___x_6314_ = lean_obj_once(&l_Lean_mkNatSucc___closed__2, &l_Lean_mkNatSucc___closed__2_once, _init_l_Lean_mkNatSucc___closed__2);
v___x_6315_ = l_Lean_Expr_app___override(v___x_6314_, v_a_6313_);
return v___x_6315_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* v_a_6316_, lean_object* v_b_6317_){
_start:
{
lean_object* v___x_6318_; lean_object* v___x_6319_; 
v___x_6318_ = l___private_Lean_Expr_0__Lean_natAddFn;
v___x_6319_ = l_Lean_mkAppB(v___x_6318_, v_a_6316_, v_b_6317_);
return v___x_6319_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* v_a_6320_, lean_object* v_b_6321_){
_start:
{
lean_object* v___x_6322_; lean_object* v___x_6323_; 
v___x_6322_ = l___private_Lean_Expr_0__Lean_natSubFn;
v___x_6323_ = l_Lean_mkAppB(v___x_6322_, v_a_6320_, v_b_6321_);
return v___x_6323_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* v_a_6324_, lean_object* v_b_6325_){
_start:
{
lean_object* v___x_6326_; lean_object* v___x_6327_; 
v___x_6326_ = l___private_Lean_Expr_0__Lean_natMulFn;
v___x_6327_ = l_Lean_mkAppB(v___x_6326_, v_a_6324_, v_b_6325_);
return v___x_6327_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object* v_a_6328_, lean_object* v_b_6329_){
_start:
{
lean_object* v___x_6330_; lean_object* v___x_6331_; 
v___x_6330_ = l___private_Lean_Expr_0__Lean_natPowFn;
v___x_6331_ = l_Lean_mkAppB(v___x_6330_, v_a_6328_, v_b_6329_);
return v___x_6331_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3(void){
_start:
{
lean_object* v___x_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; 
v___x_6337_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6338_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natLEPred___closed__2));
v___x_6339_ = l_Lean_Expr_const___override(v___x_6338_, v___x_6337_);
return v___x_6339_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4(void){
_start:
{
lean_object* v___x_6340_; lean_object* v___x_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; 
v___x_6340_ = l_Lean_Nat_mkInstLE;
v___x_6341_ = l_Lean_Nat_mkType;
v___x_6342_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6343_ = l_Lean_mkAppB(v___x_6342_, v___x_6341_, v___x_6340_);
return v___x_6343_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred(void){
_start:
{
lean_object* v___x_6344_; 
v___x_6344_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__4, &l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4);
return v___x_6344_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* v_a_6345_, lean_object* v_b_6346_){
_start:
{
lean_object* v___x_6347_; lean_object* v___x_6348_; 
v___x_6347_ = l___private_Lean_Expr_0__Lean_natLEPred;
v___x_6348_ = l_Lean_mkAppB(v___x_6347_, v_a_6345_, v_b_6346_);
return v___x_6348_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0(void){
_start:
{
lean_object* v___x_6349_; lean_object* v___x_6350_; 
v___x_6349_ = lean_unsigned_to_nat(1u);
v___x_6350_ = l_Lean_Level_ofNat(v___x_6349_);
return v___x_6350_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1(void){
_start:
{
lean_object* v___x_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; 
v___x_6351_ = lean_box(0);
v___x_6352_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__0, &l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0);
v___x_6353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6353_, 0, v___x_6352_);
lean_ctor_set(v___x_6353_, 1, v___x_6351_);
return v___x_6353_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2(void){
_start:
{
lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6356_; 
v___x_6354_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__1, &l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1);
v___x_6355_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_6356_ = l_Lean_Expr_const___override(v___x_6355_, v___x_6354_);
return v___x_6356_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3(void){
_start:
{
lean_object* v___x_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; 
v___x_6357_ = l_Lean_Nat_mkType;
v___x_6358_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6359_ = l_Lean_Expr_app___override(v___x_6358_, v___x_6357_);
return v___x_6359_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred(void){
_start:
{
lean_object* v___x_6360_; 
v___x_6360_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__3, &l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3);
return v___x_6360_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* v_a_6361_, lean_object* v_b_6362_){
_start:
{
lean_object* v___x_6363_; lean_object* v___x_6364_; 
v___x_6363_ = l___private_Lean_Expr_0__Lean_natEqPred;
v___x_6364_ = l_Lean_mkAppB(v___x_6363_, v_a_6361_, v_b_6362_);
return v___x_6364_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__0(void){
_start:
{
lean_object* v___x_6365_; lean_object* v___x_6366_; 
v___x_6365_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6366_ = l_Lean_Expr_sort___override(v___x_6365_);
return v___x_6366_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__1(void){
_start:
{
lean_object* v___x_6367_; lean_object* v___x_6368_; lean_object* v___x_6369_; 
v___x_6367_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__0, &l___private_Lean_Expr_0__Lean_propEq___closed__0_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__0);
v___x_6368_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6369_ = l_Lean_Expr_app___override(v___x_6368_, v___x_6367_);
return v___x_6369_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq(void){
_start:
{
lean_object* v___x_6370_; 
v___x_6370_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__1, &l___private_Lean_Expr_0__Lean_propEq___closed__1_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__1);
return v___x_6370_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* v_a_6371_, lean_object* v_b_6372_){
_start:
{
lean_object* v___x_6373_; lean_object* v___x_6374_; 
v___x_6373_ = l___private_Lean_Expr_0__Lean_propEq;
v___x_6374_ = l_Lean_mkAppB(v___x_6373_, v_a_6371_, v_b_6372_);
return v___x_6374_;
}
}
static lean_object* _init_l_Lean_Int_mkType___closed__2(void){
_start:
{
lean_object* v___x_6378_; lean_object* v___x_6379_; lean_object* v___x_6380_; 
v___x_6378_ = lean_box(0);
v___x_6379_ = ((lean_object*)(l_Lean_Int_mkType___closed__1));
v___x_6380_ = l_Lean_Expr_const___override(v___x_6379_, v___x_6378_);
return v___x_6380_;
}
}
static lean_object* _init_l_Lean_Int_mkType(void){
_start:
{
lean_object* v___x_6381_; 
v___x_6381_ = lean_obj_once(&l_Lean_Int_mkType___closed__2, &l_Lean_Int_mkType___closed__2_once, _init_l_Lean_Int_mkType___closed__2);
return v___x_6381_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg___closed__2(void){
_start:
{
lean_object* v___x_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; 
v___x_6386_ = lean_box(0);
v___x_6387_ = ((lean_object*)(l_Lean_Int_mkInstNeg___closed__1));
v___x_6388_ = l_Lean_Expr_const___override(v___x_6387_, v___x_6386_);
return v___x_6388_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg(void){
_start:
{
lean_object* v___x_6389_; 
v___x_6389_ = lean_obj_once(&l_Lean_Int_mkInstNeg___closed__2, &l_Lean_Int_mkInstNeg___closed__2_once, _init_l_Lean_Int_mkInstNeg___closed__2);
return v___x_6389_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; 
v___x_6394_ = lean_box(0);
v___x_6395_ = ((lean_object*)(l_Lean_Int_mkInstAdd___closed__1));
v___x_6396_ = l_Lean_Expr_const___override(v___x_6395_, v___x_6394_);
return v___x_6396_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd(void){
_start:
{
lean_object* v___x_6397_; 
v___x_6397_ = lean_obj_once(&l_Lean_Int_mkInstAdd___closed__2, &l_Lean_Int_mkInstAdd___closed__2_once, _init_l_Lean_Int_mkInstAdd___closed__2);
return v___x_6397_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd___closed__0(void){
_start:
{
lean_object* v___x_6398_; lean_object* v___x_6399_; lean_object* v___x_6400_; lean_object* v___x_6401_; 
v___x_6398_ = l_Lean_Int_mkInstAdd;
v___x_6399_ = l_Lean_Int_mkType;
v___x_6400_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6401_ = l_Lean_mkAppB(v___x_6400_, v___x_6399_, v___x_6398_);
return v___x_6401_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd(void){
_start:
{
lean_object* v___x_6402_; 
v___x_6402_ = lean_obj_once(&l_Lean_Int_mkInstHAdd___closed__0, &l_Lean_Int_mkInstHAdd___closed__0_once, _init_l_Lean_Int_mkInstHAdd___closed__0);
return v___x_6402_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6407_; lean_object* v___x_6408_; lean_object* v___x_6409_; 
v___x_6407_ = lean_box(0);
v___x_6408_ = ((lean_object*)(l_Lean_Int_mkInstSub___closed__1));
v___x_6409_ = l_Lean_Expr_const___override(v___x_6408_, v___x_6407_);
return v___x_6409_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub(void){
_start:
{
lean_object* v___x_6410_; 
v___x_6410_ = lean_obj_once(&l_Lean_Int_mkInstSub___closed__2, &l_Lean_Int_mkInstSub___closed__2_once, _init_l_Lean_Int_mkInstSub___closed__2);
return v___x_6410_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub___closed__0(void){
_start:
{
lean_object* v___x_6411_; lean_object* v___x_6412_; lean_object* v___x_6413_; lean_object* v___x_6414_; 
v___x_6411_ = l_Lean_Int_mkInstSub;
v___x_6412_ = l_Lean_Int_mkType;
v___x_6413_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6414_ = l_Lean_mkAppB(v___x_6413_, v___x_6412_, v___x_6411_);
return v___x_6414_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub(void){
_start:
{
lean_object* v___x_6415_; 
v___x_6415_ = lean_obj_once(&l_Lean_Int_mkInstHSub___closed__0, &l_Lean_Int_mkInstHSub___closed__0_once, _init_l_Lean_Int_mkInstHSub___closed__0);
return v___x_6415_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6420_; lean_object* v___x_6421_; lean_object* v___x_6422_; 
v___x_6420_ = lean_box(0);
v___x_6421_ = ((lean_object*)(l_Lean_Int_mkInstMul___closed__1));
v___x_6422_ = l_Lean_Expr_const___override(v___x_6421_, v___x_6420_);
return v___x_6422_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul(void){
_start:
{
lean_object* v___x_6423_; 
v___x_6423_ = lean_obj_once(&l_Lean_Int_mkInstMul___closed__2, &l_Lean_Int_mkInstMul___closed__2_once, _init_l_Lean_Int_mkInstMul___closed__2);
return v___x_6423_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul___closed__0(void){
_start:
{
lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; lean_object* v___x_6427_; 
v___x_6424_ = l_Lean_Int_mkInstMul;
v___x_6425_ = l_Lean_Int_mkType;
v___x_6426_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6427_ = l_Lean_mkAppB(v___x_6426_, v___x_6425_, v___x_6424_);
return v___x_6427_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul(void){
_start:
{
lean_object* v___x_6428_; 
v___x_6428_ = lean_obj_once(&l_Lean_Int_mkInstHMul___closed__0, &l_Lean_Int_mkInstHMul___closed__0_once, _init_l_Lean_Int_mkInstHMul___closed__0);
return v___x_6428_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv___closed__1(void){
_start:
{
lean_object* v___x_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; 
v___x_6432_ = lean_box(0);
v___x_6433_ = ((lean_object*)(l_Lean_Int_mkInstDiv___closed__0));
v___x_6434_ = l_Lean_Expr_const___override(v___x_6433_, v___x_6432_);
return v___x_6434_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv(void){
_start:
{
lean_object* v___x_6435_; 
v___x_6435_ = lean_obj_once(&l_Lean_Int_mkInstDiv___closed__1, &l_Lean_Int_mkInstDiv___closed__1_once, _init_l_Lean_Int_mkInstDiv___closed__1);
return v___x_6435_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv___closed__0(void){
_start:
{
lean_object* v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___x_6439_; 
v___x_6436_ = l_Lean_Int_mkInstDiv;
v___x_6437_ = l_Lean_Int_mkType;
v___x_6438_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6439_ = l_Lean_mkAppB(v___x_6438_, v___x_6437_, v___x_6436_);
return v___x_6439_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv(void){
_start:
{
lean_object* v___x_6440_; 
v___x_6440_ = lean_obj_once(&l_Lean_Int_mkInstHDiv___closed__0, &l_Lean_Int_mkInstHDiv___closed__0_once, _init_l_Lean_Int_mkInstHDiv___closed__0);
return v___x_6440_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod___closed__1(void){
_start:
{
lean_object* v___x_6444_; lean_object* v___x_6445_; lean_object* v___x_6446_; 
v___x_6444_ = lean_box(0);
v___x_6445_ = ((lean_object*)(l_Lean_Int_mkInstMod___closed__0));
v___x_6446_ = l_Lean_Expr_const___override(v___x_6445_, v___x_6444_);
return v___x_6446_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod(void){
_start:
{
lean_object* v___x_6447_; 
v___x_6447_ = lean_obj_once(&l_Lean_Int_mkInstMod___closed__1, &l_Lean_Int_mkInstMod___closed__1_once, _init_l_Lean_Int_mkInstMod___closed__1);
return v___x_6447_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod___closed__0(void){
_start:
{
lean_object* v___x_6448_; lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; 
v___x_6448_ = l_Lean_Int_mkInstMod;
v___x_6449_ = l_Lean_Int_mkType;
v___x_6450_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6451_ = l_Lean_mkAppB(v___x_6450_, v___x_6449_, v___x_6448_);
return v___x_6451_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod(void){
_start:
{
lean_object* v___x_6452_; 
v___x_6452_ = lean_obj_once(&l_Lean_Int_mkInstHMod___closed__0, &l_Lean_Int_mkInstHMod___closed__0_once, _init_l_Lean_Int_mkInstHMod___closed__0);
return v___x_6452_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; 
v___x_6457_ = lean_box(0);
v___x_6458_ = ((lean_object*)(l_Lean_Int_mkInstPow___closed__1));
v___x_6459_ = l_Lean_Expr_const___override(v___x_6458_, v___x_6457_);
return v___x_6459_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow(void){
_start:
{
lean_object* v___x_6460_; 
v___x_6460_ = lean_obj_once(&l_Lean_Int_mkInstPow___closed__2, &l_Lean_Int_mkInstPow___closed__2_once, _init_l_Lean_Int_mkInstPow___closed__2);
return v___x_6460_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat___closed__0(void){
_start:
{
lean_object* v___x_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; lean_object* v___x_6464_; 
v___x_6461_ = l_Lean_Int_mkInstPow;
v___x_6462_ = l_Lean_Int_mkType;
v___x_6463_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6464_ = l_Lean_mkAppB(v___x_6463_, v___x_6462_, v___x_6461_);
return v___x_6464_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat(void){
_start:
{
lean_object* v___x_6465_; 
v___x_6465_ = lean_obj_once(&l_Lean_Int_mkInstPowNat___closed__0, &l_Lean_Int_mkInstPowNat___closed__0_once, _init_l_Lean_Int_mkInstPowNat___closed__0);
return v___x_6465_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow___closed__0(void){
_start:
{
lean_object* v___x_6466_; lean_object* v___x_6467_; lean_object* v___x_6468_; lean_object* v___x_6469_; lean_object* v___x_6470_; 
v___x_6466_ = l_Lean_Int_mkInstPowNat;
v___x_6467_ = l_Lean_Nat_mkType;
v___x_6468_ = l_Lean_Int_mkType;
v___x_6469_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6470_ = l_Lean_mkApp3(v___x_6469_, v___x_6468_, v___x_6467_, v___x_6466_);
return v___x_6470_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow(void){
_start:
{
lean_object* v___x_6471_; 
v___x_6471_ = lean_obj_once(&l_Lean_Int_mkInstHPow___closed__0, &l_Lean_Int_mkInstHPow___closed__0_once, _init_l_Lean_Int_mkInstHPow___closed__0);
return v___x_6471_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; 
v___x_6476_ = lean_box(0);
v___x_6477_ = ((lean_object*)(l_Lean_Int_mkInstLT___closed__1));
v___x_6478_ = l_Lean_Expr_const___override(v___x_6477_, v___x_6476_);
return v___x_6478_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT(void){
_start:
{
lean_object* v___x_6479_; 
v___x_6479_ = lean_obj_once(&l_Lean_Int_mkInstLT___closed__2, &l_Lean_Int_mkInstLT___closed__2_once, _init_l_Lean_Int_mkInstLT___closed__2);
return v___x_6479_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; 
v___x_6484_ = lean_box(0);
v___x_6485_ = ((lean_object*)(l_Lean_Int_mkInstLE___closed__1));
v___x_6486_ = l_Lean_Expr_const___override(v___x_6485_, v___x_6484_);
return v___x_6486_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE(void){
_start:
{
lean_object* v___x_6487_; 
v___x_6487_ = lean_obj_once(&l_Lean_Int_mkInstLE___closed__2, &l_Lean_Int_mkInstLE___closed__2_once, _init_l_Lean_Int_mkInstLE___closed__2);
return v___x_6487_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast___closed__2(void){
_start:
{
lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; 
v___x_6491_ = lean_box(0);
v___x_6492_ = ((lean_object*)(l_Lean_Int_mkInstNatCast___closed__1));
v___x_6493_ = l_Lean_Expr_const___override(v___x_6492_, v___x_6491_);
return v___x_6493_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast(void){
_start:
{
lean_object* v___x_6494_; 
v___x_6494_ = lean_obj_once(&l_Lean_Int_mkInstNatCast___closed__2, &l_Lean_Int_mkInstNatCast___closed__2_once, _init_l_Lean_Int_mkInstNatCast___closed__2);
return v___x_6494_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0(void){
_start:
{
lean_object* v___x_6495_; lean_object* v___x_6496_; lean_object* v___x_6497_; 
v___x_6495_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6496_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_6497_ = l_Lean_Expr_const___override(v___x_6496_, v___x_6495_);
return v___x_6497_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1(void){
_start:
{
lean_object* v___x_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; lean_object* v___x_6501_; 
v___x_6498_ = l_Lean_Int_mkInstNeg;
v___x_6499_ = l_Lean_Int_mkType;
v___x_6500_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__0, &l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0);
v___x_6501_ = l_Lean_mkAppB(v___x_6500_, v___x_6499_, v___x_6498_);
return v___x_6501_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn(void){
_start:
{
lean_object* v___x_6502_; 
v___x_6502_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__1, &l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1);
return v___x_6502_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0(void){
_start:
{
lean_object* v___x_6503_; lean_object* v___x_6504_; lean_object* v___x_6505_; lean_object* v___x_6506_; 
v___x_6503_ = l_Lean_Int_mkInstHAdd;
v___x_6504_ = l_Lean_Int_mkType;
v___x_6505_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6506_ = l_Lean_mkApp4(v___x_6505_, v___x_6504_, v___x_6504_, v___x_6504_, v___x_6503_);
return v___x_6506_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn(void){
_start:
{
lean_object* v___x_6507_; 
v___x_6507_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intAddFn___closed__0, &l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0);
return v___x_6507_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0(void){
_start:
{
lean_object* v___x_6508_; lean_object* v___x_6509_; lean_object* v___x_6510_; lean_object* v___x_6511_; 
v___x_6508_ = l_Lean_Int_mkInstHSub;
v___x_6509_ = l_Lean_Int_mkType;
v___x_6510_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6511_ = l_Lean_mkApp4(v___x_6510_, v___x_6509_, v___x_6509_, v___x_6509_, v___x_6508_);
return v___x_6511_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn(void){
_start:
{
lean_object* v___x_6512_; 
v___x_6512_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intSubFn___closed__0, &l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0);
return v___x_6512_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0(void){
_start:
{
lean_object* v___x_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; lean_object* v___x_6516_; 
v___x_6513_ = l_Lean_Int_mkInstHMul;
v___x_6514_ = l_Lean_Int_mkType;
v___x_6515_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6516_ = l_Lean_mkApp4(v___x_6515_, v___x_6514_, v___x_6514_, v___x_6514_, v___x_6513_);
return v___x_6516_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn(void){
_start:
{
lean_object* v___x_6517_; 
v___x_6517_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intMulFn___closed__0, &l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0);
return v___x_6517_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3(void){
_start:
{
lean_object* v___x_6523_; lean_object* v___x_6524_; lean_object* v___x_6525_; 
v___x_6523_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6524_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intDivFn___closed__2));
v___x_6525_ = l_Lean_Expr_const___override(v___x_6524_, v___x_6523_);
return v___x_6525_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4(void){
_start:
{
lean_object* v___x_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; 
v___x_6526_ = l_Lean_Int_mkInstHDiv;
v___x_6527_ = l_Lean_Int_mkType;
v___x_6528_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__3, &l___private_Lean_Expr_0__Lean_intDivFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3);
v___x_6529_ = l_Lean_mkApp4(v___x_6528_, v___x_6527_, v___x_6527_, v___x_6527_, v___x_6526_);
return v___x_6529_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn(void){
_start:
{
lean_object* v___x_6530_; 
v___x_6530_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__4, &l___private_Lean_Expr_0__Lean_intDivFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4);
return v___x_6530_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3(void){
_start:
{
lean_object* v___x_6536_; lean_object* v___x_6537_; lean_object* v___x_6538_; 
v___x_6536_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6537_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intModFn___closed__2));
v___x_6538_ = l_Lean_Expr_const___override(v___x_6537_, v___x_6536_);
return v___x_6538_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4(void){
_start:
{
lean_object* v___x_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; lean_object* v___x_6542_; 
v___x_6539_ = l_Lean_Int_mkInstHMod;
v___x_6540_ = l_Lean_Int_mkType;
v___x_6541_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__3, &l___private_Lean_Expr_0__Lean_intModFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3);
v___x_6542_ = l_Lean_mkApp4(v___x_6541_, v___x_6540_, v___x_6540_, v___x_6540_, v___x_6539_);
return v___x_6542_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn(void){
_start:
{
lean_object* v___x_6543_; 
v___x_6543_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__4, &l___private_Lean_Expr_0__Lean_intModFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4);
return v___x_6543_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0(void){
_start:
{
lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; 
v___x_6544_ = l_Lean_Int_mkInstHPow;
v___x_6545_ = l_Lean_Nat_mkType;
v___x_6546_ = l_Lean_Int_mkType;
v___x_6547_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6548_ = l_Lean_mkApp4(v___x_6547_, v___x_6546_, v___x_6545_, v___x_6546_, v___x_6544_);
return v___x_6548_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn(void){
_start:
{
lean_object* v___x_6549_; 
v___x_6549_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0, &l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0);
return v___x_6549_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3(void){
_start:
{
lean_object* v___x_6555_; lean_object* v___x_6556_; lean_object* v___x_6557_; 
v___x_6555_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6556_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2));
v___x_6557_ = l_Lean_Expr_const___override(v___x_6556_, v___x_6555_);
return v___x_6557_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4(void){
_start:
{
lean_object* v___x_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; 
v___x_6558_ = l_Lean_Int_mkInstNatCast;
v___x_6559_ = l_Lean_Int_mkType;
v___x_6560_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3);
v___x_6561_ = l_Lean_mkAppB(v___x_6560_, v___x_6559_, v___x_6558_);
return v___x_6561_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn(void){
_start:
{
lean_object* v___x_6562_; 
v___x_6562_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4);
return v___x_6562_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* v_a_6563_){
_start:
{
lean_object* v___x_6564_; lean_object* v___x_6565_; 
v___x_6564_ = l___private_Lean_Expr_0__Lean_intNegFn;
v___x_6565_ = l_Lean_Expr_app___override(v___x_6564_, v_a_6563_);
return v___x_6565_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* v_a_6566_, lean_object* v_b_6567_){
_start:
{
lean_object* v___x_6568_; lean_object* v___x_6569_; 
v___x_6568_ = l___private_Lean_Expr_0__Lean_intAddFn;
v___x_6569_ = l_Lean_mkAppB(v___x_6568_, v_a_6566_, v_b_6567_);
return v___x_6569_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* v_a_6570_, lean_object* v_b_6571_){
_start:
{
lean_object* v___x_6572_; lean_object* v___x_6573_; 
v___x_6572_ = l___private_Lean_Expr_0__Lean_intSubFn;
v___x_6573_ = l_Lean_mkAppB(v___x_6572_, v_a_6570_, v_b_6571_);
return v___x_6573_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* v_a_6574_, lean_object* v_b_6575_){
_start:
{
lean_object* v___x_6576_; lean_object* v___x_6577_; 
v___x_6576_ = l___private_Lean_Expr_0__Lean_intMulFn;
v___x_6577_ = l_Lean_mkAppB(v___x_6576_, v_a_6574_, v_b_6575_);
return v___x_6577_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* v_a_6578_, lean_object* v_b_6579_){
_start:
{
lean_object* v___x_6580_; lean_object* v___x_6581_; 
v___x_6580_ = l___private_Lean_Expr_0__Lean_intDivFn;
v___x_6581_ = l_Lean_mkAppB(v___x_6580_, v_a_6578_, v_b_6579_);
return v___x_6581_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* v_a_6582_, lean_object* v_b_6583_){
_start:
{
lean_object* v___x_6584_; lean_object* v___x_6585_; 
v___x_6584_ = l___private_Lean_Expr_0__Lean_intModFn;
v___x_6585_ = l_Lean_mkAppB(v___x_6584_, v_a_6582_, v_b_6583_);
return v___x_6585_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* v_a_6586_){
_start:
{
lean_object* v___x_6587_; lean_object* v___x_6588_; 
v___x_6587_ = l___private_Lean_Expr_0__Lean_intNatCastFn;
v___x_6588_ = l_Lean_Expr_app___override(v___x_6587_, v_a_6586_);
return v___x_6588_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object* v_a_6589_, lean_object* v_b_6590_){
_start:
{
lean_object* v___x_6591_; lean_object* v___x_6592_; 
v___x_6591_ = l___private_Lean_Expr_0__Lean_intPowNatFn;
v___x_6592_ = l_Lean_mkAppB(v___x_6591_, v_a_6589_, v_b_6590_);
return v___x_6592_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0(void){
_start:
{
lean_object* v___x_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; lean_object* v___x_6596_; 
v___x_6593_ = l_Lean_Int_mkInstLE;
v___x_6594_ = l_Lean_Int_mkType;
v___x_6595_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6596_ = l_Lean_mkAppB(v___x_6595_, v___x_6594_, v___x_6593_);
return v___x_6596_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred(void){
_start:
{
lean_object* v___x_6597_; 
v___x_6597_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLEPred___closed__0, &l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0);
return v___x_6597_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* v_a_6598_, lean_object* v_b_6599_){
_start:
{
lean_object* v___x_6600_; lean_object* v___x_6601_; 
v___x_6600_ = l___private_Lean_Expr_0__Lean_intLEPred;
v___x_6601_ = l_Lean_mkAppB(v___x_6600_, v_a_6598_, v_b_6599_);
return v___x_6601_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3(void){
_start:
{
lean_object* v___x_6607_; lean_object* v___x_6608_; lean_object* v___x_6609_; 
v___x_6607_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6608_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intLTPred___closed__2));
v___x_6609_ = l_Lean_Expr_const___override(v___x_6608_, v___x_6607_);
return v___x_6609_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4(void){
_start:
{
lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; 
v___x_6610_ = l_Lean_Int_mkInstLT;
v___x_6611_ = l_Lean_Int_mkType;
v___x_6612_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__3, &l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3);
v___x_6613_ = l_Lean_mkAppB(v___x_6612_, v___x_6611_, v___x_6610_);
return v___x_6613_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred(void){
_start:
{
lean_object* v___x_6614_; 
v___x_6614_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__4, &l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4);
return v___x_6614_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object* v_a_6615_, lean_object* v_b_6616_){
_start:
{
lean_object* v___x_6617_; lean_object* v___x_6618_; 
v___x_6617_ = l___private_Lean_Expr_0__Lean_intLTPred;
v___x_6618_ = l_Lean_mkAppB(v___x_6617_, v_a_6615_, v_b_6616_);
return v___x_6618_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0(void){
_start:
{
lean_object* v___x_6619_; lean_object* v___x_6620_; lean_object* v___x_6621_; 
v___x_6619_ = l_Lean_Int_mkType;
v___x_6620_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6621_ = l_Lean_Expr_app___override(v___x_6620_, v___x_6619_);
return v___x_6621_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred(void){
_start:
{
lean_object* v___x_6622_; 
v___x_6622_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intEqPred___closed__0, &l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0);
return v___x_6622_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* v_a_6623_, lean_object* v_b_6624_){
_start:
{
lean_object* v___x_6625_; lean_object* v___x_6626_; 
v___x_6625_ = l___private_Lean_Expr_0__Lean_intEqPred;
v___x_6626_ = l_Lean_mkAppB(v___x_6625_, v_a_6623_, v_b_6624_);
return v___x_6626_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__3(void){
_start:
{
lean_object* v___x_6632_; lean_object* v___x_6633_; lean_object* v___x_6634_; 
v___x_6632_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6633_ = ((lean_object*)(l_Lean_mkIntDvd___closed__2));
v___x_6634_ = l_Lean_Expr_const___override(v___x_6633_, v___x_6632_);
return v___x_6634_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__6(void){
_start:
{
lean_object* v___x_6639_; lean_object* v___x_6640_; lean_object* v___x_6641_; 
v___x_6639_ = lean_box(0);
v___x_6640_ = ((lean_object*)(l_Lean_mkIntDvd___closed__5));
v___x_6641_ = l_Lean_Expr_const___override(v___x_6640_, v___x_6639_);
return v___x_6641_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* v_a_6642_, lean_object* v_b_6643_){
_start:
{
lean_object* v___x_6644_; lean_object* v___x_6645_; lean_object* v___x_6646_; lean_object* v___x_6647_; 
v___x_6644_ = lean_obj_once(&l_Lean_mkIntDvd___closed__3, &l_Lean_mkIntDvd___closed__3_once, _init_l_Lean_mkIntDvd___closed__3);
v___x_6645_ = l_Lean_Int_mkType;
v___x_6646_ = lean_obj_once(&l_Lean_mkIntDvd___closed__6, &l_Lean_mkIntDvd___closed__6_once, _init_l_Lean_mkIntDvd___closed__6);
v___x_6647_ = l_Lean_mkApp4(v___x_6644_, v___x_6645_, v___x_6646_, v_a_6642_, v_b_6643_);
return v___x_6647_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__2(void){
_start:
{
lean_object* v___x_6651_; lean_object* v___x_6652_; lean_object* v___x_6653_; 
v___x_6651_ = lean_box(0);
v___x_6652_ = ((lean_object*)(l_Lean_mkIntLit___closed__1));
v___x_6653_ = l_Lean_Expr_const___override(v___x_6652_, v___x_6651_);
return v___x_6653_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__3(void){
_start:
{
lean_object* v___x_6654_; lean_object* v___x_6655_; 
v___x_6654_ = lean_unsigned_to_nat(0u);
v___x_6655_ = lean_nat_to_int(v___x_6654_);
return v___x_6655_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* v_n_6656_){
_start:
{
lean_object* v___x_6657_; lean_object* v_r_6658_; lean_object* v___x_6659_; lean_object* v___x_6660_; lean_object* v___x_6661_; lean_object* v___x_6662_; lean_object* v_r_6663_; lean_object* v___x_6664_; uint8_t v___x_6665_; 
v___x_6657_ = lean_nat_abs(v_n_6656_);
v_r_6658_ = l_Lean_mkRawNatLit(v___x_6657_);
v___x_6659_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_6660_ = l_Lean_Int_mkType;
v___x_6661_ = lean_obj_once(&l_Lean_mkIntLit___closed__2, &l_Lean_mkIntLit___closed__2_once, _init_l_Lean_mkIntLit___closed__2);
lean_inc_ref(v_r_6658_);
v___x_6662_ = l_Lean_Expr_app___override(v___x_6661_, v_r_6658_);
v_r_6663_ = l_Lean_mkApp3(v___x_6659_, v___x_6660_, v_r_6658_, v___x_6662_);
v___x_6664_ = lean_obj_once(&l_Lean_mkIntLit___closed__3, &l_Lean_mkIntLit___closed__3_once, _init_l_Lean_mkIntLit___closed__3);
v___x_6665_ = lean_int_dec_lt(v_n_6656_, v___x_6664_);
if (v___x_6665_ == 0)
{
return v_r_6663_;
}
else
{
lean_object* v___x_6666_; 
v___x_6666_ = l_Lean_mkIntNeg(v_r_6663_);
return v___x_6666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* v_n_6667_){
_start:
{
lean_object* v_res_6668_; 
v_res_6668_ = l_Lean_mkIntLit(v_n_6667_);
lean_dec(v_n_6667_);
return v_res_6668_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6673_; lean_object* v___x_6674_; 
v___x_6673_ = lean_box(0);
v___x_6674_ = l_Lean_Level_succ___override(v___x_6673_);
return v___x_6674_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; 
v___x_6675_ = lean_box(0);
v___x_6676_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__2, &l_Lean_reflBoolTrue___closed__2_once, _init_l_Lean_reflBoolTrue___closed__2);
v___x_6677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6677_, 0, v___x_6676_);
lean_ctor_set(v___x_6677_, 1, v___x_6675_);
return v___x_6677_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6678_; lean_object* v___x_6679_; lean_object* v___x_6680_; 
v___x_6678_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__3, &l_Lean_reflBoolTrue___closed__3_once, _init_l_Lean_reflBoolTrue___closed__3);
v___x_6679_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__1));
v___x_6680_ = l_Lean_Expr_const___override(v___x_6679_, v___x_6678_);
return v___x_6680_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__6(void){
_start:
{
lean_object* v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; 
v___x_6683_ = lean_box(0);
v___x_6684_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__5));
v___x_6685_ = l_Lean_Expr_const___override(v___x_6684_, v___x_6683_);
return v___x_6685_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__7(void){
_start:
{
lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; 
v___x_6686_ = lean_box(0);
v___x_6687_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_6688_ = l_Lean_Expr_const___override(v___x_6687_, v___x_6686_);
return v___x_6688_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__8(void){
_start:
{
lean_object* v___x_6689_; lean_object* v___x_6690_; lean_object* v___x_6691_; lean_object* v___x_6692_; 
v___x_6689_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6690_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6691_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6692_ = l_Lean_mkAppB(v___x_6691_, v___x_6690_, v___x_6689_);
return v___x_6692_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue(void){
_start:
{
lean_object* v___x_6693_; 
v___x_6693_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__8, &l_Lean_reflBoolTrue___closed__8_once, _init_l_Lean_reflBoolTrue___closed__8);
return v___x_6693_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6694_; lean_object* v___x_6695_; lean_object* v___x_6696_; 
v___x_6694_ = lean_box(0);
v___x_6695_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_6696_ = l_Lean_Expr_const___override(v___x_6695_, v___x_6694_);
return v___x_6696_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6697_; lean_object* v___x_6698_; lean_object* v___x_6699_; lean_object* v___x_6700_; 
v___x_6697_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6698_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6699_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6700_ = l_Lean_mkAppB(v___x_6699_, v___x_6698_, v___x_6697_);
return v___x_6700_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse(void){
_start:
{
lean_object* v___x_6701_; 
v___x_6701_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
return v___x_6701_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6705_; lean_object* v___x_6706_; lean_object* v___x_6707_; 
v___x_6705_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6706_ = ((lean_object*)(l_Lean_eagerReflBoolTrue___closed__1));
v___x_6707_ = l_Lean_Expr_const___override(v___x_6706_, v___x_6705_);
return v___x_6707_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6708_; lean_object* v___x_6709_; lean_object* v___x_6710_; lean_object* v___x_6711_; 
v___x_6708_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6709_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6710_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6711_ = l_Lean_mkApp3(v___x_6710_, v___x_6709_, v___x_6708_, v___x_6708_);
return v___x_6711_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6712_; lean_object* v___x_6713_; lean_object* v___x_6714_; lean_object* v___x_6715_; 
v___x_6712_ = l_Lean_reflBoolTrue;
v___x_6713_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__3, &l_Lean_eagerReflBoolTrue___closed__3_once, _init_l_Lean_eagerReflBoolTrue___closed__3);
v___x_6714_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6715_ = l_Lean_mkAppB(v___x_6714_, v___x_6713_, v___x_6712_);
return v___x_6715_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue(void){
_start:
{
lean_object* v___x_6716_; 
v___x_6716_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__4, &l_Lean_eagerReflBoolTrue___closed__4_once, _init_l_Lean_eagerReflBoolTrue___closed__4);
return v___x_6716_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6717_; lean_object* v___x_6718_; lean_object* v___x_6719_; lean_object* v___x_6720_; 
v___x_6717_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6718_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6719_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6720_ = l_Lean_mkApp3(v___x_6719_, v___x_6718_, v___x_6717_, v___x_6717_);
return v___x_6720_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6721_; lean_object* v___x_6722_; lean_object* v___x_6723_; lean_object* v___x_6724_; 
v___x_6721_ = l_Lean_reflBoolFalse;
v___x_6722_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__0, &l_Lean_eagerReflBoolFalse___closed__0_once, _init_l_Lean_eagerReflBoolFalse___closed__0);
v___x_6723_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6724_ = l_Lean_mkAppB(v___x_6723_, v___x_6722_, v___x_6721_);
return v___x_6724_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse(void){
_start:
{
lean_object* v___x_6725_; 
v___x_6725_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__1, &l_Lean_eagerReflBoolFalse___closed__1_once, _init_l_Lean_eagerReflBoolFalse___closed__1);
return v___x_6725_;
}
}
static lean_object* _init_l_Lean_Expr_replaceFn___closed__2(void){
_start:
{
lean_object* v___x_6728_; lean_object* v___x_6729_; lean_object* v___x_6730_; lean_object* v___x_6731_; lean_object* v___x_6732_; lean_object* v___x_6733_; 
v___x_6728_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__1));
v___x_6729_ = lean_unsigned_to_nat(9u);
v___x_6730_ = lean_unsigned_to_nat(2458u);
v___x_6731_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__0));
v___x_6732_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_6733_ = l_mkPanicMessageWithDecl(v___x_6732_, v___x_6731_, v___x_6730_, v___x_6729_, v___x_6728_);
return v___x_6733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object* v_e_6734_, lean_object* v_declName_6735_){
_start:
{
switch(lean_obj_tag(v_e_6734_))
{
case 5:
{
lean_object* v_fn_6736_; lean_object* v_arg_6737_; lean_object* v___x_6738_; lean_object* v___x_6739_; 
v_fn_6736_ = lean_ctor_get(v_e_6734_, 0);
lean_inc_ref(v_fn_6736_);
v_arg_6737_ = lean_ctor_get(v_e_6734_, 1);
lean_inc_ref(v_arg_6737_);
lean_dec_ref_known(v_e_6734_, 2);
v___x_6738_ = l_Lean_Expr_replaceFn(v_fn_6736_, v_declName_6735_);
v___x_6739_ = l_Lean_Expr_app___override(v___x_6738_, v_arg_6737_);
return v___x_6739_;
}
case 4:
{
lean_object* v_us_6740_; lean_object* v___x_6741_; 
v_us_6740_ = lean_ctor_get(v_e_6734_, 1);
lean_inc(v_us_6740_);
lean_dec_ref_known(v_e_6734_, 2);
v___x_6741_ = l_Lean_Expr_const___override(v_declName_6735_, v_us_6740_);
return v___x_6741_;
}
default: 
{
lean_object* v___x_6742_; lean_object* v___x_6743_; 
lean_dec(v_declName_6735_);
lean_dec_ref(v_e_6734_);
v___x_6742_ = lean_obj_once(&l_Lean_Expr_replaceFn___closed__2, &l_Lean_Expr_replaceFn___closed__2_once, _init_l_Lean_Expr_replaceFn___closed__2);
v___x_6743_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_6742_);
return v___x_6743_;
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
